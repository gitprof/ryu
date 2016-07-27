
------- static_routing app -----

Location:
./ryu/app/static_routing.py

Main Concepts:
* The app set static forwarding according to predetemined paths between end-points
* Has 2 basic functionalities:
  1. set forwarding on topology initialzation
  2. reset forwarding after a link failure (can recover only one link failure)
* Uses OpticalNetwork object

Operations:
* The App recognize every node / link up. when the whole topology is up (as indicated by OpticalNetwork object) -> forwarding rules are set.
* Upon link failure -> query OpticalNetwork for alternative routing paths and reset forwarding rules
* Upon link recover -> query and  reset again
# Doesnt support a failure of more than one link in paralell !
