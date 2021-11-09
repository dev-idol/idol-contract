// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

/*
           ████████   ████████████████                 █████                     ███████
           ████████   ███████████████████          ███████████████████           ████████
          ████████   ██████████████████████      █████      ██  █████████       ████████
          ████████   ████████     ██████████    ████      █   █   ████████      ████████
          ███████   ████████        ████████   ███       █  █    █████████     ████████
         ████████   ████████        ████████  ████         ████████████████    ████████
         ████████   ███████         ████████  ████████████████████████   ██    ████████
        ████████   ████████        ████████   █████████████████████     ██    ████████
        ████████   ████████       █████████    █████████████████        ██    ████████
        ███████   █████████     ██████████      █  █████████████      ███        ████
       ████████   ██████████████████████      ████ ████████████      ██      ██████████████████
       ████████  ██████████████████████      █ ██  ███████████    ███       ████ ██████████████
      ████████   ██████████████████         █ ██      █████████████        ██ █ ███████████████
                                           █ █            ████            ██ █ ███████████████
                                          ███                   ██      █████
                                         ███       ██     █   ████    ██  █
                                        ██      ██ ██    █   ██ █   ███ ███
                                      ███     ██ ████  ███ ██   ████  █  █  ██
                                    ████    ██ ██   ██  ███              ███
                                     ██   ██ █
                                     ██ ██
                                      ██
*/

contract IDOLTokenDummy is ERC20("IDOL Dummy", "IDOL-D") {
    constructor() {
        _mint(msg.sender, 45001000000000000000000000);
    }
}