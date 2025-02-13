#include <string.h>
#include <iostream>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <functional>
#include <algorithm>
#include <assert.h>
#include <tuple>
#include <exception>
#include "Core.h"
#include "cavity.h"

using namespace std;

template<class T>
void cumulativeSum(Message<T> & message, int startIdx, int endIdx)
{
    T result = message(0, 0);
    for (int colIdx = message.size() - 2; colIdx >= startIdx; --colIdx) {
        result = message(colIdx, message.size() - 1);
        message(colIdx, message.size() - 1) += message(colIdx + 1, message.size() - 1);
        for (int rowIdx = message.size() - 2; rowIdx >= endIdx; --rowIdx) {
            result += message(colIdx, rowIdx);
            message(colIdx, rowIdx) = result + message(colIdx + 1, rowIdx);
        }
    }
    for (int rowIdx = message.size() - 2; rowIdx >= endIdx; --rowIdx)
        message(message.size() - 1, rowIdx) += message(message.size() - 1, rowIdx + 1);
}

void FactorGraph::addTime(int nodeIdx, times_t timePoint)
{
    addNode(nodeIdx);
    Node & node = nodes[nodeIdx];
    if (timePoint == node.times[node.times.size() - 2]
        || timePoint == *lower_bound(node.times.begin(), node.times.end(), timePoint))
        return;
    if (timePoint > node.times[node.times.size() - 2]) {
        node.pushBackTime(timePoint);
        for (int j = 0; j < int(node.neighbors.size()); ++j) {
            node.neighbors[j].time.back() = node.times.size() - 1;
        }
        return;
    }
    cerr << timePoint << " < " << node.times[node.times.size() - 2] << endl;
    throw invalid_argument("time of observation is too small and doesn't exist");
}

void FactorGraph::addObservation(int nodeIdx, shared_ptr<Test> const & observation, times_t timePoint)
{
    addNode(nodeIdx);
    addTime(nodeIdx, timePoint);
    if (observation != params.fakeObservation)
        nodes[nodeIdx].observations.push_back(make_tuple(timePoint, observation));
}

Message & operator++(Message & msg)
{
    int oldSize = msg.size;
    msg.size++;
    int newSize = msg.size;
    msg.resize(msg.size * msg.size);

    for (int colIdx = oldSize - 1; colIdx >= 0; --colIdx) {
        for (int rowIdx = oldSize - 1; rowIdx >= 0; --rowIdx) {
            msg(rowIdx, colIdx) = msg[oldSize * colIdx + rowIdx];
        }
    }
    msg(newSize - 1, newSize - 1) = msg(newSize - 2, newSize - 2);
    for (int i = 0; i < newSize; ++i) {
        msg(i, newSize - 1) = msg(i, newSize - 2);
        msg(newSize - 1, i) = msg(newSize - 2, i);
    }
    return msg;
}

Message & operator--(Message & msg)
{
    int size = msg.size;
    msg.size--;
    for (int colIdx = 0; colIdx < size - 1; ++colIdx) {
        for (int rowIdx = 0; rowIdx < size - 1; ++rowIdx) {
            msg(rowIdx, colIdx) = msg[size * (rowIdx + 1) + (colIdx + 1)];
        }
    }
    msg.resize(msg.size * msg.size);
    return msg;
}

void FactorGraph::removeContacts(times_t timePoint)
{
    for (size_t i = 0; i < nodes.size(); ++i) {
        Node & node = nodes[i];
        for (size_t j = 0; j < node.neighbors.size(); ++j) {
            if (node.times[node.neighbors[j].time[0]] < timePoint)
                throw invalid_argument("can only remove first contact");
            else if (node.times[node.neighbors[j].time[0]] == timePoint) {
                node.neighbors[j].time.erase(node.neighbors[j].time.begin(), node.neighbors[j].time.begin() + 1);
                node.neighbors[j].lambdas.erase(node.neighbors[j].lambdas.begin(), node.neighbors[j].lambdas.begin() + 1);
                --node.neighbors[j].message;
            }
        }
    }
}

void FactorGraph::checkIfNeighbors(int node1Idx, int node2Idx)
{
    if (node1Idx == node2Idx)
        throw invalid_argument("self loops are not allowed");
    addNode(node1Idx);
    addNode(node2Idx);
    Node & node1 = nodes[node1Idx];
    Node & node2 = nodes[node2Idx];
    int neighborIdx1 = findNeighbor(node1Idx, node2Idx);
    int neighborIdx2 = findNeighbor(node2Idx, node1Idx);
    if (neighborIdx1 == int(node1.neighbors.size())) {
        assert(neighborIdx2 == int(node2.neighbors.size()));
        node1.neighbors.push_back(Neighbor(node2Idx, neighborIdx2));
        node2.neighbors.push_back(Neighbor(node1Idx, neighborIdx1));
    }
}

void FactorGraph::addSingleContact(int node1Idx, int node2Idx, times_t timePoint, real_t lambdaValue)
{
    Node & node1 = nodes[node1Idx];
    int node1TimeSize = node1.times.size();
    if (node1.times[node1TimeSize - 2] > timePoint)
        throw invalid_argument("time of contacts should be ordered");
    int neighborIdx1 = findNeighbor(node1Idx, node2Idx);
    Neighbor & neighbor1 = node1.neighbors[neighborIdx1];
    if (node1.times[node1TimeSize - 2] < timePoint) {
        node1.pushBackTime(timePoint);
        ++node1TimeSize;
    }
    if (neighbor1.time.size() < 2 || neighbor1.time[neighbor1.time.size() - 2] < node1TimeSize - 2) {
        neighbor1.time.back() = node1TimeSize - 2;
        neighbor1.time.push_back(node1TimeSize - 1);
        if (lambdaValue != DO_NOT_OVERWRITE)
            neighbor1.lambdas.back() = lambdaValue;
        neighbor1.lambdas.push_back(0.0);
        ++neighbor1.message;
    } else if (neighbor1.time[neighbor1.time.size() - 2] == node1TimeSize - 2) {
        if (lambdaValue != DO_NOT_OVERWRITE)
            neighbor1.lambdas[neighbor1.time.size() - 2] = lambdaValue;
    } else {
        throw invalid_argument("time of contacts should be ordered");
    }
    for (int k = 0; k < int(node1.neighbors.size()); ++k) {
        node1.neighbors[k].time.back() = node1TimeSize - 1;
    }
}

void FactorGraph::addContact(int node1Idx, int node2Idx, times_t timePoint, real_t lambdaValue1, real_t lambdaValue2)
{
    if (node1Idx == node2Idx)
        throw invalid_argument("self loops are not allowed");
    addNode(node1Idx);
    addNode(node2Idx);
    Node & node1 = nodes[node1Idx];
    Node & node2 = nodes[node2Idx];
    int node1TimeSize = node1.times.size();
    int node2TimeSize = node2.times.size();
    if (node1.times[node1TimeSize - 2] > timePoint || node2.times[node2TimeSize - 2] > timePoint)
        throw invalid_argument("time of contacts should be ordered");

    int neighborIdx1 = findNeighbor(node1Idx, node2Idx);
    int neighborIdx2 = findNeighbor(node2Idx, node1Idx);
    if (neighborIdx1 == int(node1.neighbors.size())) {
        assert(neighborIdx2 == int(node2.neighbors.size()));
        node1.neighbors.push_back(Neighbor(node2Idx, neighborIdx2));
        node2.neighbors.push_back(Neighbor(node1Idx, neighborIdx1));
    }

    Neighbor & neighbor1 = node1.neighbors[neighborIdx1];
    Neighbor & neighbor2 = node2.neighbors[neighborIdx2];

    if (node1.times[node1TimeSize - 2] < timePoint) {
        node1.pushBackTime(timePoint);
        ++node1TimeSize;
    }
    if (node2.times[node2TimeSize - 2] < timePoint) {
        node2.pushBackTime(timePoint);
        ++node2TimeSize;
    }

    if (neighbor1.time.size() < 2 || neighbor1.time[neighbor1.time.size() - 2] < node1TimeSize - 2) {
        neighbor1.time.back() = node1TimeSize - 2;
        neighbor2.time.back() = node2TimeSize - 2;
        neighbor1.time.push_back(node1TimeSize - 1);
        neighbor2.time.push_back(node2TimeSize - 1);
        if (lambdaValue1 != DO_NOT_OVERWRITE)
            neighbor1.lambdas.back() = lambdaValue1;
        if (lambdaValue2 != DO_NOT_OVERWRITE)
            neighbor2.lambdas.back() = lambdaValue2;
        neighbor1.lambdas.push_back(0.0);
        neighbor2.lambdas.push_back(0.0);
        ++neighbor1.message;
        ++neighbor2.message;
    } else if (neighbor1.time[neighbor1.time.size() - 2] == node1TimeSize - 2) {
        if (lambdaValue1 != DO_NOT_OVERWRITE)
            neighbor1.lambdas[neighbor1.time.size() - 2] = lambdaValue1;
        if (lambdaValue2 != DO_NOT_OVERWRITE)
            neighbor2.lambdas[neighbor2.time.size() - 2] = lambdaValue2;
    } else {
        throw invalid_argument("time of contacts should be ordered");
    }
    for (int k = 0; k < int(node1.neighbors.size()); ++k) {
        node1.neighbors[k].time.back() = node1TimeSize - 1;
    }
}
