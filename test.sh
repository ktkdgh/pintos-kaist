#!/bin/bash

source ./activate
cd ./vm
make clean
make 
make check