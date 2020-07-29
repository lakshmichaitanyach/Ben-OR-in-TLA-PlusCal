# Ben-OR-in-TLA-PlusCal
Implementation of Binary Consensus algorithm Ben-OR in TLA+  
Ben-Or is a consensus algorithm which was proposed by Ben Or. It takes only binary input as it is not a leader-based algorithm so in order to avoid tie in system. The protocol is fault resilient as long as f < n/2 and it also takes the assumption that all the channels are FIFO.   
-It consists of indefinite number repetition of “asynchronous rounds”. The process which gets a round number are able to be processed for the rounds. These rounds are common for all “n-f” nodes. These “n-f” values are in the Input set, where “n” refers number of nodes/processes and “f” refers to number of faulty nodes.  
-With each round, we have two phases, in first phase, every node/process is figuring out which is the value that is in majority amongst them so that it can propose that value for the next phase. 
-If there is no majority amongst these values then default value “-1” is sent to next phase by all the nodes, in order to help the system towards making a decision so that the system can reach a consensus value in the next round.  
-In second phase, based on the values received from the first phase, the node finalizes its decision if the same value is proposed by at least f+1 node. If a node sees a value from another node, it adopts the value for its p1v value. This is done so that at least one node sees a majority in the p1v values.   
-Otherwise if none of this works for the system then it “randomly” selects value amongst 0 and 1 and assigns those values to its p1v values which would shift the system to have a majority and
makes a decision. In this round, every node broadcast it’s p2v to p2Msg till there is at least “n-f” values in the channel.
