// SPDX-License-Identifier: MIT

//Paymaster for zkBitcoin contract.  Paymaster will auto launch new contract for mining.   Paymaster pays all transaction fees so long as the minted zkBitcoin is less than transaction cost!
    
pragma solidity ^0.8.0;

//import "@openzeppelin/contracts/token/ERC20/IERC20.sol";

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}




interface IERC721 {
    function transferFrom(address from, address to, uint256 tokenId) external;
}
interface IERC1155 {
    function safeTransferFrom(address from, address to, uint256 id, uint256 amount, bytes calldata data) external;
}

contract PaymasterZKBitcoin_Pool {
	address public allowedToken;
	address public Paymaster;
	address public AddressToUse;
	uint public NumberofMints = 0;
    constructor(address zkBTCToken, address _Paymaster, address _AddressToUse) {
    	allowedToken = zkBTCToken;
    	Paymaster = _Paymaster;
    	AddressToUse = _AddressToUse;
    }
    
    

	function MultiMint_Paymaster(uint[] memory nonces, uint nonceLength, uint requiredZKBTC) public returns (bool){
		uint nonceLength = nonceLength;
		 // Create a new array with the desired length
		uint[] memory firstNonces = new uint[](nonceLength);
		    
		// Copy the first 'newLength' elements from 'nonces' to 'firstTenNonces'
		for (uint i = 0; i < nonceLength; i++) {
			firstNonces[i] = nonces[i];
		}		
		
		/*
		for(uint x=0; x< nonceLength; x++){
		 zkBitcoin2(allowedToken).mintTo(nonces[x], address(this));
		 
		
		}*/
		zkBitcoin2(allowedToken).multiMint_SameAddress(address(this), firstNonces);
		uint totReward = nonceLength * zkBitcoin2(allowedToken).getMiningReward();
		require(requiredZKBTC <= totReward, "Must MUST MUST be profitable to mint.");
		require(nonceLength * zkBitcoin2(allowedToken).getMiningReward() <= IERC20(allowedToken).balanceOf(address(this)),"Problem with multiMint seems not all your answers were correct.");
		//so we only send what we minted with paymaster, no need to overpay and send all the tokens.
		IERC20(allowedToken).transfer(Paymaster, totReward);
		NumberofMints = NumberofMints + nonceLength;
	}
	
	//This is the non-Paymaster Mint method, use this to mint your tokens without a Paymaster to your address!
	function PoolContract_Mint_No_Paymaster(uint[] memory nonces) public returns (bool){
		
		zkBitcoin2(allowedToken).multiMint_SameAddress(address(this), nonces);
		IERC20(allowedToken).transfer(AddressToUse, IERC20(allowedToken).balanceOf(address(this)));
	}
	
	
	
	//Only for use to estimate gas because MultiMint_Paymaster fails in estimateGas so we use this function instead below.
	function estimateGas_Paymaster(uint[] memory nonces, uint nonceLength) public returns (bool){
		 // Create a new array with the desired length
		uint[] memory firstNonces = new uint[](nonceLength);
		    
		// Copy the first 'newLength' elements from 'nonces' to 'firstTenNonces'
		for (uint i = 0; i < nonceLength; i++) {
			firstNonces[i] = nonces[i];
		}		
		
		/*
		for(uint x=0; x< nonceLength; x++){
		 zkBitcoin2(allowedToken).mintTo(nonces[x], address(this));
		 
		
		}*/
		zkBitcoin2(allowedToken).multiMint_SameAddress(address(this), firstNonces);
		IERC20(allowedToken).transfer(Paymaster, IERC20(allowedToken).balanceOf(address(this)));
	}


	 // Function to send ETH
    function withdrawETH(uint _amount) public {
        require(address(this).balance >= _amount, "Insufficient balance in contract");
        // Transfer ETH
        (bool sent, ) = AddressToUse.call{value: _amount}("");
        require(sent, "Failed to send ETH");
    }
    
    // Function to withdraw ERC20 tokens
    function withdrawERC20(address token, uint256 amount) public {
        require(IERC20(token).transfer(AddressToUse, amount), "Transfer failed");
    }

    // Function to withdraw ERC721 tokens
    function withdrawERC721(address token, uint256 tokenId) public {
        IERC721(token).transferFrom(address(this), AddressToUse, tokenId);
    }

    // Function to withdraw ERC1155 tokens
    function withdrawERC1155(address token, uint256 tokenId, uint256 amount, bytes calldata data) public {
        IERC1155(token).safeTransferFrom(address(this), AddressToUse, tokenId, amount, data);
    }
    
    
    
}
























//import {IPaymaster, ExecutionResult, PAYMASTER_VALIDATION_SUCCESS_MAGIC} from "@matterlabs/zksync-contracts/l2/system-contracts/interfaces/IPaymaster.sol";


//import "../libraries/TransactionHelper.sol";


//import "../openzeppelin/token/ERC20/utils/SafeERC20.sol";

//import "../IERC20.sol";
//import "../extensions/IERC20Permit.sol";

interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

//import "../../../utils/Address.sol";
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://consensys.net/diligence/blog/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(
            address(this).balance >= amount,
            "Address: insufficient balance"
        );

        (bool success, ) = recipient.call{value: amount}("");
        require(
            success,
            "Address: unable to send value, recipient may have reverted"
        );
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data)
        internal
        returns (bytes memory)
    {
        return
            functionCallWithValue(
                target,
                data,
                0,
                "Address: low-level call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return
            functionCallWithValue(
                target,
                data,
                value,
                "Address: low-level call with value failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(
            address(this).balance >= value,
            "Address: insufficient balance for call"
        );
        (bool success, bytes memory returndata) = target.call{value: value}(
            data
        );
        return
            verifyCallResultFromTarget(
                target,
                success,
                returndata,
                errorMessage
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data)
        internal
        view
        returns (bytes memory)
    {
        return
            functionStaticCall(
                target,
                data,
                "Address: low-level static call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return
            verifyCallResultFromTarget(
                target,
                success,
                returndata,
                errorMessage
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data)
        internal
        returns (bytes memory)
    {
        return
            functionDelegateCall(
                target,
                data,
                "Address: low-level delegate call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return
            verifyCallResultFromTarget(
                target,
                success,
                returndata,
                errorMessage
            );
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage)
        private
        pure
    {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transfer.selector, to, value)
        );
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transferFrom.selector, from, to, value)
        );
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.approve.selector, spender, value)
        );
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(
                token.approve.selector,
                spender,
                newAllowance
            )
        );
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(
                oldAllowance >= value,
                "SafeERC20: decreased allowance below zero"
            );
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(
                token,
                abi.encodeWithSelector(
                    token.approve.selector,
                    spender,
                    newAllowance
                )
            );
        }
    }

    function safePermit(
        IERC20Permit token,
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        uint256 nonceBefore = token.nonces(owner);
        token.permit(owner, spender, value, deadline, v, r, s);
        uint256 nonceAfter = token.nonces(owner);
        require(
            nonceAfter == nonceBefore + 1,
            "SafeERC20: permit did not succeed"
        );
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address-functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(
            data,
            "SafeERC20: low-level call failed"
        );
        if (returndata.length > 0) {
            // Return data is optional
            require(
                abi.decode(returndata, (bool)),
                "SafeERC20: ERC20 operation did not succeed"
            );
        }
    }
}



//import "../interfaces/IPaymasterFlow.sol";
/**
 * @author Matter Labs
 * @dev The interface that is used for encoding/decoding of
 * different types of paymaster flows.
 * @notice This is NOT an interface to be implementated
 * by contracts. It is just used for encoding.
 */
interface IPaymasterFlow {
    function general(bytes calldata input) external;

    function approvalBased(address _token, uint256 _minAllowance, bytes calldata _innerInput) external;
}




//import "../interfaces/IContractDeployer.sol";




interface IContractDeployer {
    /// @notice Defines the version of the account abstraction protocol
    /// that a contract claims to follow.
    /// - `None` means that the account is just a contract and it should never be interacted
    /// with as a custom account
    /// - `Version1` means that the account follows the first version of the account abstraction protocol
    enum AccountAbstractionVersion {
        None,
        Version1
    }

    /// @notice Defines the nonce ordering used by the account
    /// - `Sequential` means that it is expected that the nonces are monotonic and increment by 1
    /// at a time (the same as EOAs).
    /// - `Arbitrary` means that the nonces for the accounts can be arbitrary. The operator
    /// should serve the transactions from such an account on a first-come-first-serve basis.
    /// @dev This ordering is more of a suggestion to the operator on how the AA expects its transactions
    /// to be processed and is not considered as a system invariant.
    enum AccountNonceOrdering {
        Sequential,
        Arbitrary
    }

    struct AccountInfo {
        AccountAbstractionVersion supportedAAVersion;
        AccountNonceOrdering nonceOrdering;
    }

    event ContractDeployed(
        address indexed deployerAddress,
        bytes32 indexed bytecodeHash,
        address indexed contractAddress
    );

    event AccountNonceOrderingUpdated(address indexed accountAddress, AccountNonceOrdering nonceOrdering);

    event AccountVersionUpdated(address indexed accountAddress, AccountAbstractionVersion aaVersion);

    function getNewAddressCreate2(
        address _sender,
        bytes32 _bytecodeHash,
        bytes32 _salt,
        bytes calldata _input
    ) external view returns (address newAddress);

    function getNewAddressCreate(address _sender, uint256 _senderNonce) external pure returns (address newAddress);

    function create2(
        bytes32 _salt,
        bytes32 _bytecodeHash,
        bytes calldata _input
    ) external payable returns (address newAddress);

    function create2Account(
        bytes32 _salt,
        bytes32 _bytecodeHash,
        bytes calldata _input,
        AccountAbstractionVersion _aaVersion
    ) external payable returns (address newAddress);

    /// @dev While the `_salt` parameter is not used anywhere here,
    /// it is still needed for consistency between `create` and
    /// `create2` functions (required by the compiler).
    function create(
        bytes32 _salt,
        bytes32 _bytecodeHash,
        bytes calldata _input
    ) external payable returns (address newAddress);

    /// @dev While `_salt` is never used here, we leave it here as a parameter
    /// for the consistency with the `create` function.
    function createAccount(
        bytes32 _salt,
        bytes32 _bytecodeHash,
        bytes calldata _input,
        AccountAbstractionVersion _aaVersion
    ) external payable returns (address newAddress);

    /// @notice Returns the information about a certain AA.
    function getAccountInfo(address _address) external view returns (AccountInfo memory info);

    /// @notice Can be called by an account to update its account version
    function updateAccountVersion(AccountAbstractionVersion _version) external;

    /// @notice Can be called by an account to update its nonce ordering
    function updateNonceOrdering(AccountNonceOrdering _nonceOrdering) external;
}



//import "./interfaces/IEthToken.sol";




interface IEthToken {
    function balanceOf(uint256) external view returns (uint256);

    function transferFromTo(address _from, address _to, uint256 _amount) external;

    function totalSupply() external view returns (uint256);

    function name() external pure returns (string memory);

    function symbol() external pure returns (string memory);

    function decimals() external pure returns (uint8);

    function mint(address _account, uint256 _amount) external;

    function withdraw(address _l1Receiver) external payable;

    event Mint(address indexed account, uint256 amount);

    event Transfer(address indexed from, address indexed to, uint256 value);

    event Withdrawal(address indexed _l2Sender, address indexed _l1Receiver, uint256 _amount);
}
uint160 constant SYSTEM_CONTRACTS_OFFSET = 0x8000; // 2^15

IEthToken constant ETH_TOKEN_SYSTEM_CONTRACT = IEthToken(address(SYSTEM_CONTRACTS_OFFSET + 0x0a));
address payable constant BOOTLOADER_FORMAL_ADDRESS = payable(address(SYSTEM_CONTRACTS_OFFSET + 0x01));

//import {ETH_TOKEN_SYSTEM_CONTRACT, BOOTLOADER_FORMAL_ADDRESS} from "../Constants.sol"; above


//import "./RLPEncoder.sol";
library RLPEncoder {
    function encodeAddress(address _val) internal pure returns (bytes memory encoded) {
        // The size is equal to 20 bytes of the address itself + 1 for encoding bytes length in RLP.
        encoded = new bytes(0x15);

        bytes20 shiftedVal = bytes20(_val);
        assembly {
            // In the first byte we write the encoded length as 0x80 + 0x14 == 0x94.
            mstore(add(encoded, 0x20), 0x9400000000000000000000000000000000000000000000000000000000000000)
            // Write address data without stripping zeros.
            mstore(add(encoded, 0x21), shiftedVal)
        }
    }

    function encodeUint256(uint256 _val) internal pure returns (bytes memory encoded) {
        unchecked {
            if (_val < 128) {
                encoded = new bytes(1);
                // Handle zero as a non-value, since stripping zeroes results in an empty byte array
                encoded[0] = (_val == 0) ? bytes1(uint8(128)) : bytes1(uint8(_val));
            } else {
                uint256 hbs = _highestByteSet(_val);

                encoded = new bytes(hbs + 2);
                encoded[0] = bytes1(uint8(hbs + 0x81));

                uint256 lbs = 31 - hbs;
                uint256 shiftedVal = _val << (lbs * 8);

                assembly {
                    mstore(add(encoded, 0x21), shiftedVal)
                }
            }
        }
    }

    /// @notice Encodes the size of bytes in RLP format.
    /// @param _len The length of the bytes to encode. It has a `uint64` type since as larger values are not supported.
    /// NOTE: panics if the length is 1 since the length encoding is ambiguous in this case.
    function encodeNonSingleBytesLen(uint64 _len) internal pure returns (bytes memory) {
        assert(_len != 1);
        return _encodeLength(_len, 0x80);
    }

    /// @notice Encodes the size of list items in RLP format.
    /// @param _len The length of the bytes to encode. It has a `uint64` type since as larger values are not supported.
    function encodeListLen(uint64 _len) internal pure returns (bytes memory) {
        return _encodeLength(_len, 0xc0);
    }

    function _encodeLength(uint64 _len, uint256 _offset) private pure returns (bytes memory encoded) {
        unchecked {
            if (_len < 56) {
                encoded = new bytes(1);
                encoded[0] = bytes1(uint8(_len + _offset));
            } else {
                uint256 hbs = _highestByteSet(uint256(_len));

                encoded = new bytes(hbs + 2);
                encoded[0] = bytes1(uint8(_offset + hbs + 56));

                uint256 lbs = 31 - hbs;
                uint256 shiftedVal = uint256(_len) << (lbs * 8);

                assembly {
                    mstore(add(encoded, 0x21), shiftedVal)
                }
            }
        }
    }

    /// @notice Computes the index of the highest byte set in number.
    /// @notice Uses little endian ordering (The least significant byte has index `0`).
    /// NOTE: returns `0` for `0`
    function _highestByteSet(uint256 _number) private pure returns (uint256 hbs) {
        unchecked {
            if (_number > type(uint128).max) {
                _number >>= 128;
                hbs += 16;
            }
            if (_number > type(uint64).max) {
                _number >>= 64;
                hbs += 8;
            }
            if (_number > type(uint32).max) {
                _number >>= 32;
                hbs += 4;
            }
            if (_number > type(uint16).max) {
                _number >>= 16;
                hbs += 2;
            }
            if (_number > type(uint8).max) {
                hbs += 1;
            }
        }
    }
}



//import "./EfficientCall.sol";
//inside is this
//import "./SystemContractHelper.sol";

//import {MAX_SYSTEM_CONTRACT_ADDRESS, MSG_VALUE_SYSTEM_CONTRACT} from "../Constants.sol";
uint160 constant MAX_SYSTEM_CONTRACT_ADDRESS = 0xffff; // 2^16 - 1
address constant MSG_VALUE_SYSTEM_CONTRACT = address(SYSTEM_CONTRACTS_OFFSET + 0x09);

//import "./SystemContractsCaller.sol";
uint256 constant MSG_VALUE_SIMULATOR_IS_SYSTEM_BIT = 1;


//import {MSG_VALUE_SYSTEM_CONTRACT, MSG_VALUE_SIMULATOR_IS_SYSTEM_BIT} from "../Constants.sol";
//import "./Utils.sol";
//import "./EfficientCall.sol"; already imported

/**
 * @author Matter Labs
 * @dev Common utilities used in zkSync system contracts
 */
library Utils {
    /// @dev Bit mask of bytecode hash "isConstructor" marker
    bytes32 constant IS_CONSTRUCTOR_BYTECODE_HASH_BIT_MASK =
        0x00ff000000000000000000000000000000000000000000000000000000000000;

    /// @dev Bit mask to set the "isConstructor" marker in the bytecode hash
    bytes32 constant SET_IS_CONSTRUCTOR_MARKER_BIT_MASK =
        0x0001000000000000000000000000000000000000000000000000000000000000;

    function safeCastToU128(uint256 _x) internal pure returns (uint128) {
        require(_x <= type(uint128).max, "Overflow");

        return uint128(_x);
    }

    function safeCastToU32(uint256 _x) internal pure returns (uint32) {
        require(_x <= type(uint32).max, "Overflow");

        return uint32(_x);
    }

    function safeCastToU24(uint256 _x) internal pure returns (uint24) {
        require(_x <= type(uint24).max, "Overflow");

        return uint24(_x);
    }

    /// @return codeLength The bytecode length in bytes
    function bytecodeLenInBytes(bytes32 _bytecodeHash) internal pure returns (uint256 codeLength) {
        codeLength = bytecodeLenInWords(_bytecodeHash) << 5; // _bytecodeHash * 32
    }

    /// @return codeLengthInWords The bytecode length in machine words
    function bytecodeLenInWords(bytes32 _bytecodeHash) internal pure returns (uint256 codeLengthInWords) {
        unchecked {
            codeLengthInWords = uint256(uint8(_bytecodeHash[2])) * 256 + uint256(uint8(_bytecodeHash[3]));
        }
    }

    /// @notice Denotes whether bytecode hash corresponds to a contract that already constructed
    function isContractConstructed(bytes32 _bytecodeHash) internal pure returns (bool) {
        return _bytecodeHash[1] == 0x00;
    }

    /// @notice Denotes whether bytecode hash corresponds to a contract that is on constructor or has already been constructed
    function isContractConstructing(bytes32 _bytecodeHash) internal pure returns (bool) {
        return _bytecodeHash[1] == 0x01;
    }

    /// @notice Sets "isConstructor" flag to TRUE for the bytecode hash
    /// @param _bytecodeHash The bytecode hash for which it is needed to set the constructing flag
    /// @return The bytecode hash with "isConstructor" flag set to TRUE
    function constructingBytecodeHash(bytes32 _bytecodeHash) internal pure returns (bytes32) {
        // Clear the "isConstructor" marker and set it to 0x01.
        return constructedBytecodeHash(_bytecodeHash) | SET_IS_CONSTRUCTOR_MARKER_BIT_MASK;
    }

    /// @notice Sets "isConstructor" flag to FALSE for the bytecode hash
    /// @param _bytecodeHash The bytecode hash for which it is needed to set the constructing flag
    /// @return The bytecode hash with "isConstructor" flag set to FALSE
    function constructedBytecodeHash(bytes32 _bytecodeHash) internal pure returns (bytes32) {
        return _bytecodeHash & ~IS_CONSTRUCTOR_BYTECODE_HASH_BIT_MASK;
    }

    /// @notice Validate the bytecode format and calculate its hash.
    /// @param _bytecode The bytecode to hash.
    /// @return hashedBytecode The 32-byte hash of the bytecode.
    /// Note: The function reverts the execution if the bytecode has non expected format:
    /// - Bytecode bytes length is not a multiple of 32
    /// - Bytecode bytes length is not less than 2^21 bytes (2^16 words)
    /// - Bytecode words length is not odd
    function hashL2Bytecode(bytes calldata _bytecode) internal view returns (bytes32 hashedBytecode) {
        // Note that the length of the bytecode must be provided in 32-byte words.
        require(_bytecode.length % 32 == 0, "po");

        uint256 bytecodeLenInWords = _bytecode.length / 32;
        require(bytecodeLenInWords < 2 ** 16, "pp"); // bytecode length must be less than 2^16 words
        require(bytecodeLenInWords % 2 == 1, "pr"); // bytecode length in words must be odd
        hashedBytecode =
            EfficientCall.sha(_bytecode) &
            0x00000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
        // Setting the version of the hash
        hashedBytecode = (hashedBytecode | bytes32(uint256(1 << 248)));
        // Setting the length
        hashedBytecode = hashedBytecode | bytes32(bytecodeLenInWords << 224);
    }
}

// Addresses used for the compiler to be replaced with the
// zkSync-specific opcodes during the compilation.
// IMPORTANT: these are just compile-time constants and are used
// only if used in-place by Yul optimizer.
address constant TO_L1_CALL_ADDRESS = address((1 << 16) - 1);
address constant CODE_ADDRESS_CALL_ADDRESS = address((1 << 16) - 2);
address constant PRECOMPILE_CALL_ADDRESS = address((1 << 16) - 3);
address constant META_CALL_ADDRESS = address((1 << 16) - 4);
address constant MIMIC_CALL_CALL_ADDRESS = address((1 << 16) - 5);
address constant SYSTEM_MIMIC_CALL_CALL_ADDRESS = address((1 << 16) - 6);
address constant MIMIC_CALL_BY_REF_CALL_ADDRESS = address((1 << 16) - 7);
address constant SYSTEM_MIMIC_CALL_BY_REF_CALL_ADDRESS = address((1 << 16) - 8);
address constant RAW_FAR_CALL_CALL_ADDRESS = address((1 << 16) - 9);
address constant RAW_FAR_CALL_BY_REF_CALL_ADDRESS = address((1 << 16) - 10);
address constant SYSTEM_CALL_CALL_ADDRESS = address((1 << 16) - 11);
address constant SYSTEM_CALL_BY_REF_CALL_ADDRESS = address((1 << 16) - 12);
address constant SET_CONTEXT_VALUE_CALL_ADDRESS = address((1 << 16) - 13);
address constant SET_PUBDATA_PRICE_CALL_ADDRESS = address((1 << 16) - 14);
address constant INCREMENT_TX_COUNTER_CALL_ADDRESS = address((1 << 16) - 15);
address constant PTR_CALLDATA_CALL_ADDRESS = address((1 << 16) - 16);
address constant CALLFLAGS_CALL_ADDRESS = address((1 << 16) - 17);
address constant PTR_RETURNDATA_CALL_ADDRESS = address((1 << 16) - 18);
address constant EVENT_INITIALIZE_ADDRESS = address((1 << 16) - 19);
address constant EVENT_WRITE_ADDRESS = address((1 << 16) - 20);
address constant LOAD_CALLDATA_INTO_ACTIVE_PTR_CALL_ADDRESS = address((1 << 16) - 21);
address constant LOAD_LATEST_RETURNDATA_INTO_ACTIVE_PTR_CALL_ADDRESS = address((1 << 16) - 22);
address constant PTR_ADD_INTO_ACTIVE_CALL_ADDRESS = address((1 << 16) - 23);
address constant PTR_SHRINK_INTO_ACTIVE_CALL_ADDRESS = address((1 << 16) - 24);
address constant PTR_PACK_INTO_ACTIVE_CALL_ADDRESS = address((1 << 16) - 25);
address constant MULTIPLICATION_HIGH_ADDRESS = address((1 << 16) - 26);
address constant GET_EXTRA_ABI_DATA_ADDRESS = address((1 << 16) - 27);

// All the offsets are in bits
uint256 constant META_GAS_PER_PUBDATA_BYTE_OFFSET = 0 * 8;
uint256 constant META_HEAP_SIZE_OFFSET = 8 * 8;
uint256 constant META_AUX_HEAP_SIZE_OFFSET = 12 * 8;
uint256 constant META_SHARD_ID_OFFSET = 28 * 8;
uint256 constant META_CALLER_SHARD_ID_OFFSET = 29 * 8;
uint256 constant META_CODE_SHARD_ID_OFFSET = 30 * 8;

/// @notice The way to forward the calldata:
/// - Use the current heap (i.e. the same as on EVM).
/// - Use the auxiliary heap.
/// - Forward via a pointer
/// @dev Note, that currently, users do not have access to the auxiliary
/// heap and so the only type of forwarding that will be used by the users
/// are UseHeap and ForwardFatPointer for forwarding a slice of the current calldata
/// to the next call.
enum CalldataForwardingMode {
    UseHeap,
    ForwardFatPointer,
    UseAuxHeap
}

/**
 * @author Matter Labs
 * @notice A library that allows calling contracts with the `isSystem` flag.
 * @dev It is needed to call ContractDeployer and NonceHolder.
 */
library SystemContractsCaller {
    /// @notice Makes a call with the `isSystem` flag.
    /// @param gasLimit The gas limit for the call.
    /// @param to The address to call.
    /// @param value The value to pass with the transaction.
    /// @param data The calldata.
    /// @return success Whether the transaction has been successful.
    /// @dev Note, that the `isSystem` flag can only be set when calling system contracts.
    function systemCall(uint32 gasLimit, address to, uint256 value, bytes memory data) internal returns (bool success) {
        address callAddr = SYSTEM_CALL_CALL_ADDRESS;

        uint32 dataStart;
        assembly {
            dataStart := add(data, 0x20)
        }
        uint32 dataLength = uint32(Utils.safeCastToU32(data.length));

        uint256 farCallAbi = SystemContractsCaller.getFarCallABI(
            0,
            0,
            dataStart,
            dataLength,
            gasLimit,
            // Only rollup is supported for now
            0,
            CalldataForwardingMode.UseHeap,
            false,
            true
        );

        if (value == 0) {
            // Doing the system call directly
            assembly {
                success := call(to, callAddr, 0, 0, farCallAbi, 0, 0)
            }
        } else {
            address msgValueSimulator = MSG_VALUE_SYSTEM_CONTRACT;
            // We need to supply the mask to the MsgValueSimulator to denote
            // that the call should be a system one.
            uint256 forwardMask = MSG_VALUE_SIMULATOR_IS_SYSTEM_BIT;

            assembly {
                success := call(msgValueSimulator, callAddr, value, to, farCallAbi, forwardMask, 0)
            }
        }
    }

    /// @notice Makes a call with the `isSystem` flag.
    /// @param gasLimit The gas limit for the call.
    /// @param to The address to call.
    /// @param value The value to pass with the transaction.
    /// @param data The calldata.
    /// @return success Whether the transaction has been successful.
    /// @return returnData The returndata of the transaction (revert reason in case the transaction has failed).
    /// @dev Note, that the `isSystem` flag can only be set when calling system contracts.
    function systemCallWithReturndata(
        uint32 gasLimit,
        address to,
        uint128 value,
        bytes memory data
    ) internal returns (bool success, bytes memory returnData) {
        success = systemCall(gasLimit, to, value, data);

        uint256 size;
        assembly {
            size := returndatasize()
        }

        returnData = new bytes(size);
        assembly {
            returndatacopy(add(returnData, 0x20), 0, size)
        }
    }

    /// @notice Makes a call with the `isSystem` flag.
    /// @param gasLimit The gas limit for the call.
    /// @param to The address to call.
    /// @param value The value to pass with the transaction.
    /// @param data The calldata.
    /// @return returnData The returndata of the transaction. In case the transaction reverts, the error
    /// bubbles up to the parent frame.
    /// @dev Note, that the `isSystem` flag can only be set when calling system contracts.
    function systemCallWithPropagatedRevert(
        uint32 gasLimit,
        address to,
        uint128 value,
        bytes memory data
    ) internal returns (bytes memory returnData) {
        bool success;
        (success, returnData) = systemCallWithReturndata(gasLimit, to, value, data);

        if (!success) {
            assembly {
                let size := mload(returnData)
                revert(add(returnData, 0x20), size)
            }
        }
    }

    /// @notice Calculates the packed representation of the FarCallABI.
    /// @param dataOffset Calldata offset in memory. Provide 0 unless using custom pointer.
    /// @param memoryPage Memory page to use. Provide 0 unless using custom pointer.
    /// @param dataStart The start of the calldata slice. Provide the offset in memory
    /// if not using custom pointer.
    /// @param dataLength The calldata length. Provide the length of the calldata in bytes
    /// unless using custom pointer.
    /// @param gasPassed The gas to pass with the call.
    /// @param shardId Of the account to call. Currently only 0 is supported.
    /// @param forwardingMode The forwarding mode to use:
    /// - provide CalldataForwardingMode.UseHeap when using your current memory
    /// - provide CalldataForwardingMode.ForwardFatPointer when using custom pointer.
    /// @param isConstructorCall Whether the call will be a call to the constructor
    /// (ignored when the caller is not a system contract).
    /// @param isSystemCall Whether the call will have the `isSystem` flag.
    /// @return farCallAbi The far call ABI.
    /// @dev The `FarCallABI` has the following structure:
    /// pub struct FarCallABI {
    ///     pub memory_quasi_fat_pointer: FatPointer,
    ///     pub gas_passed: u32,
    ///     pub shard_id: u8,
    ///     pub forwarding_mode: FarCallForwardPageType,
    ///     pub constructor_call: bool,
    ///     pub to_system: bool,
    /// }
    ///
    /// The FatPointer struct:
    ///
    /// pub struct FatPointer {
    ///     pub offset: u32, // offset relative to `start`
    ///     pub memory_page: u32, // memory page where slice is located
    ///     pub start: u32, // absolute start of the slice
    ///     pub length: u32, // length of the slice
    /// }
    ///
    /// @dev Note, that the actual layout is the following:
    ///
    /// [0..32) bits -- the calldata offset
    /// [32..64) bits -- the memory page to use. Can be left blank in most of the cases.
    /// [64..96) bits -- the absolute start of the slice
    /// [96..128) bits -- the length of the slice.
    /// [128..192) bits -- empty bits.
    /// [192..224) bits -- gasPassed.
    /// [224..232) bits -- forwarding_mode
    /// [232..240) bits -- shard id.
    /// [240..248) bits -- constructor call flag
    /// [248..256] bits -- system call flag
    function getFarCallABI(
        uint32 dataOffset,
        uint32 memoryPage,
        uint32 dataStart,
        uint32 dataLength,
        uint32 gasPassed,
        uint8 shardId,
        CalldataForwardingMode forwardingMode,
        bool isConstructorCall,
        bool isSystemCall
    ) internal pure returns (uint256 farCallAbi) {
        // Fill in the call parameter fields
        farCallAbi = getFarCallABIWithEmptyFatPointer(
            gasPassed,
            shardId,
            forwardingMode,
            isConstructorCall,
            isSystemCall
        );
        // Fill in the fat pointer fields
        farCallAbi |= dataOffset;
        farCallAbi |= (uint256(memoryPage) << 32);
        farCallAbi |= (uint256(dataStart) << 64);
        farCallAbi |= (uint256(dataLength) << 96);
    }

    /// @notice Calculates the packed representation of the FarCallABI with zero fat pointer fields.
    /// @param gasPassed The gas to pass with the call.
    /// @param shardId Of the account to call. Currently only 0 is supported.
    /// @param forwardingMode The forwarding mode to use:
    /// - provide CalldataForwardingMode.UseHeap when using your current memory
    /// - provide CalldataForwardingMode.ForwardFatPointer when using custom pointer.
    /// @param isConstructorCall Whether the call will be a call to the constructor
    /// (ignored when the caller is not a system contract).
    /// @param isSystemCall Whether the call will have the `isSystem` flag.
    /// @return farCallAbiWithEmptyFatPtr The far call ABI with zero fat pointer fields.
    function getFarCallABIWithEmptyFatPointer(
        uint32 gasPassed,
        uint8 shardId,
        CalldataForwardingMode forwardingMode,
        bool isConstructorCall,
        bool isSystemCall
    ) internal pure returns (uint256 farCallAbiWithEmptyFatPtr) {
        farCallAbiWithEmptyFatPtr |= (uint256(gasPassed) << 192);
        farCallAbiWithEmptyFatPtr |= (uint256(forwardingMode) << 224);
        farCallAbiWithEmptyFatPtr |= (uint256(shardId) << 232);
        if (isConstructorCall) {
            farCallAbiWithEmptyFatPtr |= (1 << 240);
        }
        if (isSystemCall) {
            farCallAbiWithEmptyFatPtr |= (1 << 248);
        }
    }
}

//import "./Utils.sol"; already imprted

uint256 constant UINT32_MASK = 0xffffffff;
uint256 constant UINT128_MASK = 0xffffffffffffffffffffffffffffffff;
/// @dev The mask that is used to convert any uint256 to a proper address.
/// It needs to be padded with `00` to be treated as uint256 by Solidity
uint256 constant ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;

struct ZkSyncMeta {
    uint32 gasPerPubdataByte;
    uint32 heapSize;
    uint32 auxHeapSize;
    uint8 shardId;
    uint8 callerShardId;
    uint8 codeShardId;
}

enum Global {
    CalldataPtr,
    CallFlags,
    ExtraABIData1,
    ExtraABIData2,
    ReturndataPtr
}

/**
 * @author Matter Labs
 * @notice Library used for accessing zkEVM-specific opcodes, needed for the development
 * of system contracts.
 * @dev While this library will be eventually available to public, some of the provided
 * methods won't work for non-system contracts. We will not recommend this library
 * for external use.
 */
library SystemContractHelper {
    /// @notice Send an L2Log to L1.
    /// @param _isService The `isService` flag.
    /// @param _key The `key` part of the L2Log.
    /// @param _value The `value` part of the L2Log.
    /// @dev The meaning of all these parameters is context-dependent, but they
    /// have no intrinsic meaning per se.
    function toL1(bool _isService, bytes32 _key, bytes32 _value) internal {
        address callAddr = TO_L1_CALL_ADDRESS;
        assembly {
            // Ensuring that the type is bool
            _isService := and(_isService, 1)
            // This `success` is always 0, but the method always succeeds
            // (except for the cases when there is not enough gas)
            let success := call(_isService, callAddr, _key, _value, 0xFFFF, 0, 0)
        }
    }

    /// @notice Get address of the currently executed code.
    /// @dev This allows differentiating between `call` and `delegatecall`.
    /// During the former `this` and `codeAddress` are the same, while
    /// during the latter they are not.
    function getCodeAddress() internal view returns (address addr) {
        address callAddr = CODE_ADDRESS_CALL_ADDRESS;
        assembly {
            addr := staticcall(0, callAddr, 0, 0xFFFF, 0, 0)
        }
    }

    /// @notice Provide a compiler hint, by placing calldata fat pointer into virtual `ACTIVE_PTR`,
    /// that can be manipulated by `ptr.add`/`ptr.sub`/`ptr.pack`/`ptr.shrink` later.
    /// @dev This allows making a call by forwarding calldata pointer to the child call.
    /// It is a much more efficient way to forward calldata, than standard EVM bytes copying.
    function loadCalldataIntoActivePtr() internal view {
        address callAddr = LOAD_CALLDATA_INTO_ACTIVE_PTR_CALL_ADDRESS;
        assembly {
            pop(staticcall(0, callAddr, 0, 0xFFFF, 0, 0))
        }
    }

    /// @notice Compiler simulation of the `ptr.pack` opcode for the virtual `ACTIVE_PTR` pointer.
    /// @dev Do the concatenation between lowest part of `ACTIVE_PTR` and highest part of `_farCallAbi`
    /// forming packed fat pointer for a far call or ret ABI when necessary.
    /// Note: Panics if the lowest 128 bits of `_farCallAbi` are not zeroes.
    function ptrPackIntoActivePtr(uint256 _farCallAbi) internal view {
        address callAddr = PTR_PACK_INTO_ACTIVE_CALL_ADDRESS;
        assembly {
            pop(staticcall(_farCallAbi, callAddr, 0, 0xFFFF, 0, 0))
        }
    }

    /// @notice Compiler simulation of the `ptr.add` opcode for the virtual `ACTIVE_PTR` pointer.
    /// @dev Transforms `ACTIVE_PTR.offset` into `ACTIVE_PTR.offset + u32(_value)`. If overflow happens then it panics.
    function ptrAddIntoActive(uint32 _value) internal view {
        address callAddr = PTR_ADD_INTO_ACTIVE_CALL_ADDRESS;
        uint256 cleanupMask = UINT32_MASK;
        assembly {
            // Clearing input params as they are not cleaned by Solidity by default
            _value := and(_value, cleanupMask)
            pop(staticcall(_value, callAddr, 0, 0xFFFF, 0, 0))
        }
    }

    /// @notice Compiler simulation of the `ptr.shrink` opcode for the virtual `ACTIVE_PTR` pointer.
    /// @dev Transforms `ACTIVE_PTR.length` into `ACTIVE_PTR.length - u32(_shrink)`. If underflow happens then it panics.
    function ptrShrinkIntoActive(uint32 _shrink) internal view {
        address callAddr = PTR_SHRINK_INTO_ACTIVE_CALL_ADDRESS;
        uint256 cleanupMask = UINT32_MASK;
        assembly {
            // Clearing input params as they are not cleaned by Solidity by default
            _shrink := and(_shrink, cleanupMask)
            pop(staticcall(_shrink, callAddr, 0, 0xFFFF, 0, 0))
        }
    }

    /// @notice packs precompile parameters into one word
    /// @param _inputMemoryOffset The memory offset in 32-byte words for the input data for calling the precompile.
    /// @param _inputMemoryLength The length of the input data in words.
    /// @param _outputMemoryOffset The memory offset in 32-byte words for the output data.
    /// @param _outputMemoryLength The length of the output data in words.
    /// @param _perPrecompileInterpreted The constant, the meaning of which is defined separately for
    /// each precompile. For information, please read the documentation of the precompilecall log in
    /// the VM.
    function packPrecompileParams(
        uint32 _inputMemoryOffset,
        uint32 _inputMemoryLength,
        uint32 _outputMemoryOffset,
        uint32 _outputMemoryLength,
        uint64 _perPrecompileInterpreted
    ) internal pure returns (uint256 rawParams) {
        rawParams = _inputMemoryOffset;
        rawParams |= uint256(_inputMemoryLength) << 32;
        rawParams |= uint256(_outputMemoryOffset) << 64;
        rawParams |= uint256(_outputMemoryLength) << 96;
        rawParams |= uint256(_perPrecompileInterpreted) << 192;
    }

    /// @notice Call precompile with given parameters.
    /// @param _rawParams The packed precompile params. They can be retrieved by
    /// the `packPrecompileParams` method.
    /// @param _gasToBurn The number of gas to burn during this call.
    /// @return success Whether the call was successful.
    /// @dev The list of currently available precompiles sha256, keccak256, ecrecover.
    /// NOTE: The precompile type depends on `this` which calls precompile, which means that only
    /// system contracts corresponding to the list of precompiles above can do `precompileCall`.
    /// @dev If used not in the `sha256`, `keccak256` or `ecrecover` contracts, it will just burn the gas provided.
    function precompileCall(uint256 _rawParams, uint32 _gasToBurn) internal view returns (bool success) {
        address callAddr = PRECOMPILE_CALL_ADDRESS;

        // After `precompileCall` gas will be burned down to 0 if there are not enough of them,
        // thats why it should be checked before the call.
        require(gasleft() >= _gasToBurn);
        uint256 cleanupMask = UINT32_MASK;
        assembly {
            // Clearing input params as they are not cleaned by Solidity by default
            _gasToBurn := and(_gasToBurn, cleanupMask)
            success := staticcall(_rawParams, callAddr, _gasToBurn, 0xFFFF, 0, 0)
        }
    }

    /// @notice Set `msg.value` to next far call.
    /// @param _value The msg.value that will be used for the *next* call.
    /// @dev If called not in kernel mode, it will result in a revert (enforced by the VM)
    function setValueForNextFarCall(uint128 _value) internal returns (bool success) {
        uint256 cleanupMask = UINT128_MASK;
        address callAddr = SET_CONTEXT_VALUE_CALL_ADDRESS;
        assembly {
            // Clearing input params as they are not cleaned by Solidity by default
            _value := and(_value, cleanupMask)
            success := call(0, callAddr, _value, 0, 0xFFFF, 0, 0)
        }
    }

    /// @notice Initialize a new event.
    /// @param initializer The event initializing value.
    /// @param value1 The first topic or data chunk.
    function eventInitialize(uint256 initializer, uint256 value1) internal {
        address callAddr = EVENT_INITIALIZE_ADDRESS;
        assembly {
            pop(call(initializer, callAddr, value1, 0, 0xFFFF, 0, 0))
        }
    }

    /// @notice Continue writing the previously initialized event.
    /// @param value1 The first topic or data chunk.
    /// @param value2 The second topic or data chunk.
    function eventWrite(uint256 value1, uint256 value2) internal {
        address callAddr = EVENT_WRITE_ADDRESS;
        assembly {
            pop(call(value1, callAddr, value2, 0, 0xFFFF, 0, 0))
        }
    }

    /// @notice Get the packed representation of the `ZkSyncMeta` from the current context.
    /// @return meta The packed representation of the ZkSyncMeta.
    /// @dev The fields in ZkSyncMeta are NOT tightly packed, i.e. there is a special rule on how
    /// they are packed. For more information, please read the documentation on ZkSyncMeta.
    function getZkSyncMetaBytes() internal view returns (uint256 meta) {
        address callAddr = META_CALL_ADDRESS;
        assembly {
            meta := staticcall(0, callAddr, 0, 0xFFFF, 0, 0)
        }
    }

    /// @notice Returns the bits [offset..offset+size-1] of the meta.
    /// @param meta Packed representation of the ZkSyncMeta.
    /// @param offset The offset of the bits.
    /// @param size The size of the extracted number in bits.
    /// @return result The extracted number.
    function extractNumberFromMeta(uint256 meta, uint256 offset, uint256 size) internal pure returns (uint256 result) {
        // Firstly, we delete all the bits after the field
        uint256 shifted = (meta << (256 - size - offset));
        // Then we shift everything back
        result = (shifted >> (256 - size));
    }

    /// @notice Given the packed representation of `ZkSyncMeta`, retrieves the number of gas
    /// that a single byte sent to L1 as pubdata costs.
    /// @param meta Packed representation of the ZkSyncMeta.
    /// @return gasPerPubdataByte The current price in gas per pubdata byte.
    function getGasPerPubdataByteFromMeta(uint256 meta) internal pure returns (uint32 gasPerPubdataByte) {
        gasPerPubdataByte = uint32(extractNumberFromMeta(meta, META_GAS_PER_PUBDATA_BYTE_OFFSET, 32));
    }

    /// @notice Given the packed representation of `ZkSyncMeta`, retrieves the number of the current size
    /// of the heap in bytes.
    /// @param meta Packed representation of the ZkSyncMeta.
    /// @return heapSize The size of the memory in bytes byte.
    /// @dev The following expression: getHeapSizeFromMeta(getZkSyncMetaBytes()) is
    /// equivalent to the MSIZE in Solidity.
    function getHeapSizeFromMeta(uint256 meta) internal pure returns (uint32 heapSize) {
        heapSize = uint32(extractNumberFromMeta(meta, META_HEAP_SIZE_OFFSET, 32));
    }

    /// @notice Given the packed representation of `ZkSyncMeta`, retrieves the number of the current size
    /// of the auxilary heap in bytes.
    /// @param meta Packed representation of the ZkSyncMeta.
    /// @return auxHeapSize The size of the auxilary memory in bytes byte.
    /// @dev You can read more on auxilary memory in the VM1.2 documentation.
    function getAuxHeapSizeFromMeta(uint256 meta) internal pure returns (uint32 auxHeapSize) {
        auxHeapSize = uint32(extractNumberFromMeta(meta, META_AUX_HEAP_SIZE_OFFSET, 32));
    }

    /// @notice Given the packed representation of `ZkSyncMeta`, retrieves the shardId of `this`.
    /// @param meta Packed representation of the ZkSyncMeta.
    /// @return shardId The shardId of `this`.
    /// @dev Currently only shard 0 (zkRollup) is supported.
    function getShardIdFromMeta(uint256 meta) internal pure returns (uint8 shardId) {
        shardId = uint8(extractNumberFromMeta(meta, META_SHARD_ID_OFFSET, 8));
    }

    /// @notice Given the packed representation of `ZkSyncMeta`, retrieves the shardId of
    /// the msg.sender.
    /// @param meta Packed representation of the ZkSyncMeta.
    /// @return callerShardId The shardId of the msg.sender.
    /// @dev Currently only shard 0 (zkRollup) is supported.
    function getCallerShardIdFromMeta(uint256 meta) internal pure returns (uint8 callerShardId) {
        callerShardId = uint8(extractNumberFromMeta(meta, META_CALLER_SHARD_ID_OFFSET, 8));
    }

    /// @notice Given the packed representation of `ZkSyncMeta`, retrieves the shardId of
    /// the currently executed code.
    /// @param meta Packed representation of the ZkSyncMeta.
    /// @return codeShardId The shardId of the currently executed code.
    /// @dev Currently only shard 0 (zkRollup) is supported.
    function getCodeShardIdFromMeta(uint256 meta) internal pure returns (uint8 codeShardId) {
        codeShardId = uint8(extractNumberFromMeta(meta, META_CODE_SHARD_ID_OFFSET, 8));
    }

    /// @notice Retrieves the ZkSyncMeta structure.
    /// @return meta The ZkSyncMeta execution context parameters.
    function getZkSyncMeta() internal view returns (ZkSyncMeta memory meta) {
        uint256 metaPacked = getZkSyncMetaBytes();
        meta.gasPerPubdataByte = getGasPerPubdataByteFromMeta(metaPacked);
        meta.shardId = getShardIdFromMeta(metaPacked);
        meta.callerShardId = getCallerShardIdFromMeta(metaPacked);
        meta.codeShardId = getCodeShardIdFromMeta(metaPacked);
    }

    /// @notice Returns the call flags for the current call.
    /// @return callFlags The bitmask of the callflags.
    /// @dev Call flags is the value of the first register
    /// at the start of the call.
    /// @dev The zero bit of the callFlags indicates whether the call is
    /// a constructor call. The first bit of the callFlags indicates whether
    /// the call is a system one.
    function getCallFlags() internal view returns (uint256 callFlags) {
        address callAddr = CALLFLAGS_CALL_ADDRESS;
        assembly {
            callFlags := staticcall(0, callAddr, 0, 0xFFFF, 0, 0)
        }
    }

    /// @notice Returns the current calldata pointer.
    /// @return ptr The current calldata pointer.
    /// @dev NOTE: This file is just an integer and it can not be used
    /// to forward the calldata to the next calls in any way.
    function getCalldataPtr() internal view returns (uint256 ptr) {
        address callAddr = PTR_CALLDATA_CALL_ADDRESS;
        assembly {
            ptr := staticcall(0, callAddr, 0, 0xFFFF, 0, 0)
        }
    }

    /// @notice Returns the N-th extraAbiParam for the current call.
    /// @return extraAbiData The value of the N-th extraAbiParam for this call.
    /// @dev It is equal to the value of the (N+2)-th register
    /// at the start of the call.
    function getExtraAbiData(uint256 index) internal view returns (uint256 extraAbiData) {
        require(index < 10, "There are only 10 accessible registers");

        address callAddr = GET_EXTRA_ABI_DATA_ADDRESS;
        assembly {
            extraAbiData := staticcall(index, callAddr, 0, 0xFFFF, 0, 0)
        }
    }

    /// @notice Retuns whether the current call is a system call.
    /// @return `true` or `false` based on whether the current call is a system call.
    function isSystemCall() internal view returns (bool) {
        uint256 callFlags = getCallFlags();
        // When the system call is passed, the 2-bit it set to 1
        return (callFlags & 2) != 0;
    }

    /// @notice Returns whether the address is a system contract.
    /// @param _address The address to test
    /// @return `true` or `false` based on whether the `_address` is a system contract.
    function isSystemContract(address _address) internal pure returns (bool) {
        return uint160(_address) <= uint160(MAX_SYSTEM_CONTRACT_ADDRESS);
    }
}

/// @dev Solidity does not allow exporting modifiers via libraries, so
/// the only way to do reuse modifiers is to have a base contract
abstract contract ISystemContract {
    /// @notice Modifier that makes sure that the method
    /// can only be called via a system call.
    modifier onlySystemCall() {
        require(
            SystemContractHelper.isSystemCall() || SystemContractHelper.isSystemContract(msg.sender),
            "This method require system call flag"
        );
        _;
    }
}

//import "./Utils.sol"; already imported
//import {SHA256_SYSTEM_CONTRACT, KECCAK256_SYSTEM_CONTRACT} from "../Constants.sol";
address constant SHA256_SYSTEM_CONTRACT = address(0x02);
address constant KECCAK256_SYSTEM_CONTRACT = address(SYSTEM_CONTRACTS_OFFSET + 0x10);

/**
 * @author Matter Labs
 * @notice This library is used to perform ultra-efficient calls using zkEVM-specific features.
 * @dev EVM calls always accept a memory slice as input and return a memory slice as output.
 * Therefore, even if the user has a ready-made calldata slice, they still need to copy it to memory
 * before calling. This is especially inefficient for large inputs (proxies, multi-calls, etc.).
 * In turn, zkEVM operates over a fat pointer, which is a set of (memory page, offset, start, length) in the memory/calldata/returndata.
 * This allows forwarding the calldata slice as is, without copying it to memory.
 * @dev Fat pointer is not just an integer, it is an extended data type supported on the VM level.
 * zkEVM creates the wellformed fat pointers for all the calldata/returndata regions, later
 * the contract may manipulate the already created fat pointers to forward a slice of the data, but not
 * to create new fat pointers!
 * @dev The allowed operation on fat pointers are:
 * 1. `ptr.add` - Transforms `ptr.offset` into `ptr.offset + u32(_value)`. If overflow happens then it panics.
 * 2. `ptr.sub` - Transforms `ptr.offset` into `ptr.offset - u32(_value)`. If underflow happens then it panics.
 * 3. `ptr.pack` - Do the concatenation between the lowest 128 bits of the pointer itself and the highest 128 bits of `_value`. It is typically used to prepare the ABI for external calls.
 * 4. `ptr.shrink` - Transforms `ptr.length` into `ptr.length - u32(_shrink)`. If underflow happens then it panics.
 * @dev The call opcodes accept the fat pointer and change it to its canonical form before passing it to the child call
 * 1. `ptr.start` is transformed into `ptr.offset + ptr.start`
 * 2. `ptr.length` is transformed into `ptr.length - ptr.offset`
 * 3. `ptr.offset` is transformed into `0`
 */
library EfficientCall {
    /// @notice Call the `keccak256` without copying calldata to memory.
    /// @param _data The preimage data.
    /// @return The `keccak256` hash.
    function keccak(bytes calldata _data) internal view returns (bytes32) {
        bytes memory returnData = staticCall(gasleft(), KECCAK256_SYSTEM_CONTRACT, _data);
        require(returnData.length == 32, "keccak256 returned invalid data");
        return bytes32(returnData);
    }

    /// @notice Call the `sha256` precompile without copying calldata to memory.
    /// @param _data The preimage data.
    /// @return The `sha256` hash.
    function sha(bytes calldata _data) internal view returns (bytes32) {
        bytes memory returnData = staticCall(gasleft(), SHA256_SYSTEM_CONTRACT, _data);
        require(returnData.length == 32, "sha returned invalid data");
        return bytes32(returnData);
    }

    /// @notice Perform a `call` without copying calldata to memory.
    /// @param _gas The gas to use for the call.
    /// @param _address The address to call.
    /// @param _value The `msg.value` to send.
    /// @param _data The calldata to use for the call.
    /// @param _isSystem Whether the call should contain the `isSystem` flag.
    /// @return returnData The copied to memory return data.
    function call(
        uint256 _gas,
        address _address,
        uint256 _value,
        bytes calldata _data,
        bool _isSystem
    ) internal returns (bytes memory returnData) {
        bool success = rawCall(_gas, _address, _value, _data, _isSystem);
        returnData = _verifyCallResult(success);
    }

    /// @notice Perform a `staticCall` without copying calldata to memory.
    /// @param _gas The gas to use for the call.
    /// @param _address The address to call.
    /// @param _data The calldata to use for the call.
    /// @return returnData The copied to memory return data.
    function staticCall(
        uint256 _gas,
        address _address,
        bytes calldata _data
    ) internal view returns (bytes memory returnData) {
        bool success = rawStaticCall(_gas, _address, _data);
        returnData = _verifyCallResult(success);
    }

    /// @notice Perform a `delegateCall` without copying calldata to memory.
    /// @param _gas The gas to use for the call.
    /// @param _address The address to call.
    /// @param _data The calldata to use for the call.
    /// @return returnData The copied to memory return data.
    function delegateCall(
        uint256 _gas,
        address _address,
        bytes calldata _data
    ) internal returns (bytes memory returnData) {
        bool success = rawDelegateCall(_gas, _address, _data);
        returnData = _verifyCallResult(success);
    }

    /// @notice Perform a `mimicCall` (a call with custom msg.sender) without copying calldata to memory.
    /// @param _gas The gas to use for the call.
    /// @param _address The address to call.
    /// @param _data The calldata to use for the call.
    /// @param _whoToMimic The `msg.sender` for the next call.
    /// @param _isConstructor Whether the call should contain the `isConstructor` flag.
    /// @param _isSystem Whether the call should contain the `isSystem` flag.
    /// @return returnData The copied to memory return data.
    function mimicCall(
        uint256 _gas,
        address _address,
        bytes calldata _data,
        address _whoToMimic,
        bool _isConstructor,
        bool _isSystem
    ) internal returns (bytes memory returnData) {
        bool success = rawMimicCall(_gas, _address, _data, _whoToMimic, _isConstructor, _isSystem);
        returnData = _verifyCallResult(success);
    }

    /// @notice Perform a `call` without copying calldata to memory.
    /// @param _gas The gas to use for the call.
    /// @param _address The address to call.
    /// @param _value The `msg.value` to send.
    /// @param _data The calldata to use for the call.
    /// @param _isSystem Whether the call should contain the `isSystem` flag.
    /// @return success whether the call was successful.
    function rawCall(
        uint256 _gas,
        address _address,
        uint256 _value,
        bytes calldata _data,
        bool _isSystem
    ) internal returns (bool success) {
        if (_value == 0) {
            _loadFarCallABIIntoActivePtr(_gas, _data, false, _isSystem);

            address callAddr = RAW_FAR_CALL_BY_REF_CALL_ADDRESS;
            assembly {
                success := call(_address, callAddr, 0, 0, 0xFFFF, 0, 0)
            }
        } else {
            _loadFarCallABIIntoActivePtr(_gas, _data, false, true);

            // If there is provided `msg.value` call the `MsgValueSimulator` to forward ether.
            address msgValueSimulator = MSG_VALUE_SYSTEM_CONTRACT;
            address callAddr = SYSTEM_CALL_BY_REF_CALL_ADDRESS;
            // We need to supply the mask to the MsgValueSimulator to denote
            // that the call should be a system one.
            uint256 forwardMask = _isSystem ? MSG_VALUE_SIMULATOR_IS_SYSTEM_BIT : 0;

            assembly {
                success := call(msgValueSimulator, callAddr, _value, _address, 0xFFFF, forwardMask, 0)
            }
        }
    }

    /// @notice Perform a `staticCall` without copying calldata to memory.
    /// @param _gas The gas to use for the call.
    /// @param _address The address to call.
    /// @param _data The calldata to use for the call.
    /// @return success whether the call was successful.
    function rawStaticCall(uint256 _gas, address _address, bytes calldata _data) internal view returns (bool success) {
        _loadFarCallABIIntoActivePtr(_gas, _data, false, false);

        address callAddr = RAW_FAR_CALL_BY_REF_CALL_ADDRESS;
        assembly {
            success := staticcall(_address, callAddr, 0, 0xFFFF, 0, 0)
        }
    }

    /// @notice Perform a `delegatecall` without copying calldata to memory.
    /// @param _gas The gas to use for the call.
    /// @param _address The address to call.
    /// @param _data The calldata to use for the call.
    /// @return success whether the call was successful.
    function rawDelegateCall(uint256 _gas, address _address, bytes calldata _data) internal returns (bool success) {
        _loadFarCallABIIntoActivePtr(_gas, _data, false, false);

        address callAddr = RAW_FAR_CALL_BY_REF_CALL_ADDRESS;
        assembly {
            success := delegatecall(_address, callAddr, 0, 0xFFFF, 0, 0)
        }
    }

    /// @notice Perform a `mimicCall` (call with custom msg.sender) without copying calldata to memory.
    /// @param _gas The gas to use for the call.
    /// @param _address The address to call.
    /// @param _data The calldata to use for the call.
    /// @param _whoToMimic The `msg.sender` for the next call.
    /// @param _isConstructor Whether the call should contain the `isConstructor` flag.
    /// @param _isSystem Whether the call should contain the `isSystem` flag.
    /// @return success whether the call was successful.
    /// @dev If called not in kernel mode, it will result in a revert (enforced by the VM)
    function rawMimicCall(
        uint256 _gas,
        address _address,
        bytes calldata _data,
        address _whoToMimic,
        bool _isConstructor,
        bool _isSystem
    ) internal returns (bool success) {
        _loadFarCallABIIntoActivePtr(_gas, _data, _isConstructor, _isSystem);

        address callAddr = MIMIC_CALL_BY_REF_CALL_ADDRESS;
        uint256 cleanupMask = ADDRESS_MASK;
        assembly {
            // Clearing values before usage in assembly, since Solidity
            // doesn't do it by default
            _whoToMimic := and(_whoToMimic, cleanupMask)

            success := call(_address, callAddr, 0, 0, _whoToMimic, 0, 0)
        }
    }

    /// @dev Verify that a low-level call was successful, and revert if it wasn't, by bubbling the revert reason.
    /// @param _success Whether the call was successful.
    /// @return returnData The copied to memory return data.
    function _verifyCallResult(bool _success) private pure returns (bytes memory returnData) {
        if (_success) {
            uint256 size;
            assembly {
                size := returndatasize()
            }

            returnData = new bytes(size);
            assembly {
                returndatacopy(add(returnData, 0x20), 0, size)
            }
        } else {
            propagateRevert();
        }
    }

    /// @dev Propagate the revert reason from the current call to the caller.
    function propagateRevert() internal pure {
        assembly {
            let size := returndatasize()
            returndatacopy(0, 0, size)
            revert(0, size)
        }
    }

    /// @dev Load the far call ABI into active ptr, that will be used for the next call by reference.
    /// @param _gas The gas to be passed to the call.
    /// @param _data The calldata to be passed to the call.
    /// @param _isConstructor Whether the call is a constructor call.
    /// @param _isSystem Whether the call is a system call.
    function _loadFarCallABIIntoActivePtr(
        uint256 _gas,
        bytes calldata _data,
        bool _isConstructor,
        bool _isSystem
    ) private view {
        SystemContractHelper.loadCalldataIntoActivePtr();

        // Currently, zkEVM considers the pointer valid if(ptr.offset < ptr.length || (ptr.length == 0 && ptr.offset == 0)), otherwise panics.
        // So, if the data is empty we need to make the `ptr.length = ptr.offset = 0`, otherwise follow standard logic.
        if (_data.length == 0) {
            // Safe to cast, offset is never bigger than `type(uint32).max`
            SystemContractHelper.ptrShrinkIntoActive(uint32(msg.data.length));
        } else {
            uint256 dataOffset;
            assembly {
                dataOffset := _data.offset
            }

            // Safe to cast, offset is never bigger than `type(uint32).max`
            SystemContractHelper.ptrAddIntoActive(uint32(dataOffset));
            // Safe to cast, `data.length` is never bigger than `type(uint32).max`
            uint32 shrinkTo = uint32(msg.data.length - (_data.length + dataOffset));
            SystemContractHelper.ptrShrinkIntoActive(shrinkTo);
        }

        uint32 gas = Utils.safeCastToU32(_gas);
        uint256 farCallAbi = SystemContractsCaller.getFarCallABIWithEmptyFatPointer(
            gas,
            // Only rollup is supported for now
            0,
            CalldataForwardingMode.ForwardFatPointer,
            _isConstructor,
            _isSystem
        );
        SystemContractHelper.ptrPackIntoActivePtr(farCallAbi);
    }
}




/// @dev The type id of zkSync's EIP-712-signed transaction.
uint8 constant EIP_712_TX_TYPE = 0x71;

/// @dev The type id of legacy transactions.
uint8 constant LEGACY_TX_TYPE = 0x0;
/// @dev The type id of legacy transactions.
uint8 constant EIP_2930_TX_TYPE = 0x01;
/// @dev The type id of EIP1559 transactions.
uint8 constant EIP_1559_TX_TYPE = 0x02;

/// @notice Structure used to represent zkSync transaction.
struct Transaction {
    // The type of the transaction.
    uint256 txType;
    // The caller.
    uint256 from;
    // The callee.
    uint256 to;
    // The gasLimit to pass with the transaction.
    // It has the same meaning as Ethereum's gasLimit.
    uint256 gasLimit;
    // The maximum amount of gas the user is willing to pay for a byte of pubdata.
    uint256 gasPerPubdataByteLimit;
    // The maximum fee per gas that the user is willing to pay.
    // It is akin to EIP1559's maxFeePerGas.
    uint256 maxFeePerGas;
    // The maximum priority fee per gas that the user is willing to pay.
    // It is akin to EIP1559's maxPriorityFeePerGas.
    uint256 maxPriorityFeePerGas;
    // The transaction's paymaster. If there is no paymaster, it is equal to 0.
    uint256 paymaster;
    // The nonce of the transaction.
    uint256 nonce;
    // The value to pass with the transaction.
    uint256 value;
    // In the future, we might want to add some
    // new fields to the struct. The `txData` struct
    // is to be passed to account and any changes to its structure
    // would mean a breaking change to these accounts. In order to prevent this,
    // we should keep some fields as "reserved".
    // It is also recommended that their length is fixed, since
    // it would allow easier proof integration (in case we will need
    // some special circuit for preprocessing transactions).
    uint256[4] reserved;
    // The transaction's calldata.
    bytes data;
    // The signature of the transaction.
    bytes signature;
    // The properly formatted hashes of bytecodes that must be published on L1
    // with the inclusion of this transaction. Note, that a bytecode has been published
    // before, the user won't pay fees for its republishing.
    bytes32[] factoryDeps;
    // The input to the paymaster.
    bytes paymasterInput;
    // Reserved dynamic type for the future use-case. Using it should be avoided,
    // But it is still here, just in case we want to enable some additional functionality.
    bytes reservedDynamic;
}

/**
 * @author Matter Labs
 * @notice Library is used to help custom accounts to work with common methods for the Transaction type.
 */
library TransactionHelper {
    using SafeERC20 for IERC20;

    /// @notice The EIP-712 typehash for the contract's domain
    bytes32 constant EIP712_DOMAIN_TYPEHASH = keccak256("EIP712Domain(string name,string version,uint256 chainId)");

    bytes32 constant EIP712_TRANSACTION_TYPE_HASH =
        keccak256(
            "Transaction(uint256 txType,uint256 from,uint256 to,uint256 gasLimit,uint256 gasPerPubdataByteLimit,uint256 maxFeePerGas,uint256 maxPriorityFeePerGas,uint256 paymaster,uint256 nonce,uint256 value,bytes data,bytes32[] factoryDeps,bytes paymasterInput)"
        );

    /// @notice Whether the token is Ethereum.
    /// @param _addr The address of the token
    /// @return `true` or `false` based on whether the token is Ether.
    /// @dev This method assumes that address is Ether either if the address is 0 (for convenience)
    /// or if the address is the address of the L2EthToken system contract.
    function isEthToken(uint256 _addr) internal pure returns (bool) {
        return _addr == uint256(uint160(address(ETH_TOKEN_SYSTEM_CONTRACT))) || _addr == 0;
    }

    /// @notice Calculate the suggested signed hash of the transaction,
    /// i.e. the hash that is signed by EOAs and is recommended to be signed by other accounts.
    function encodeHash(Transaction calldata _transaction) internal view returns (bytes32 resultHash) {
        if (_transaction.txType == LEGACY_TX_TYPE) {
            resultHash = _encodeHashLegacyTransaction(_transaction);
        } else if (_transaction.txType == EIP_712_TX_TYPE) {
            resultHash = _encodeHashEIP712Transaction(_transaction);
        } else if (_transaction.txType == EIP_1559_TX_TYPE) {
            resultHash = _encodeHashEIP1559Transaction(_transaction);
        } else if (_transaction.txType == EIP_2930_TX_TYPE) {
            resultHash = _encodeHashEIP2930Transaction(_transaction);
        } else {
            // Currently no other transaction types are supported.
            // Any new transaction types will be processed in a similar manner.
            revert("Encoding unsupported tx");
        }
    }

    /// @notice Encode hash of the zkSync native transaction type.
    /// @return keccak256 hash of the EIP-712 encoded representation of transaction
    function _encodeHashEIP712Transaction(Transaction calldata _transaction) private view returns (bytes32) {
        bytes32 structHash = keccak256(
            abi.encode(
                EIP712_TRANSACTION_TYPE_HASH,
                _transaction.txType,
                _transaction.from,
                _transaction.to,
                _transaction.gasLimit,
                _transaction.gasPerPubdataByteLimit,
                _transaction.maxFeePerGas,
                _transaction.maxPriorityFeePerGas,
                _transaction.paymaster,
                _transaction.nonce,
                _transaction.value,
                EfficientCall.keccak(_transaction.data),
                keccak256(abi.encodePacked(_transaction.factoryDeps)),
                EfficientCall.keccak(_transaction.paymasterInput)
            )
        );

        bytes32 domainSeparator = keccak256(
            abi.encode(EIP712_DOMAIN_TYPEHASH, keccak256("zkSync"), keccak256("2"), block.chainid)
        );

        return keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));
    }

    /// @notice Encode hash of the legacy transaction type.
    /// @return keccak256 of the serialized RLP encoded representation of transaction
    function _encodeHashLegacyTransaction(Transaction calldata _transaction) private view returns (bytes32) {
        // Hash of legacy transactions are encoded as one of the:
        // - RLP(nonce, gasPrice, gasLimit, to, value, data, chainId, 0, 0)
        // - RLP(nonce, gasPrice, gasLimit, to, value, data)
        //
        // In this RLP encoding, only the first one above list appears, so we encode each element
        // inside list and then concatenate the length of all elements with them.

        bytes memory encodedNonce = RLPEncoder.encodeUint256(_transaction.nonce);
        // Encode `gasPrice` and `gasLimit` together to prevent "stack too deep error".
        bytes memory encodedGasParam;
        {
            bytes memory encodedGasPrice = RLPEncoder.encodeUint256(_transaction.maxFeePerGas);
            bytes memory encodedGasLimit = RLPEncoder.encodeUint256(_transaction.gasLimit);
            encodedGasParam = bytes.concat(encodedGasPrice, encodedGasLimit);
        }

        bytes memory encodedTo = RLPEncoder.encodeAddress(address(uint160(_transaction.to)));
        bytes memory encodedValue = RLPEncoder.encodeUint256(_transaction.value);
        // Encode only the length of the transaction data, and not the data itself,
        // so as not to copy to memory a potentially huge transaction data twice.
        bytes memory encodedDataLength;
        {
            // Safe cast, because the length of the transaction data can't be so large.
            uint64 txDataLen = uint64(_transaction.data.length);
            if (txDataLen != 1) {
                // If the length is not equal to one, then only using the length can it be encoded definitely.
                encodedDataLength = RLPEncoder.encodeNonSingleBytesLen(txDataLen);
            } else if (_transaction.data[0] >= 0x80) {
                // If input is a byte in [0x80, 0xff] range, RLP encoding will concatenates 0x81 with the byte.
                encodedDataLength = hex"81";
            }
            // Otherwise the length is not encoded at all.
        }

        // Encode `chainId` according to EIP-155, but only if the `chainId` is specified in the transaction.
        bytes memory encodedChainId;
        if (_transaction.reserved[0] != 0) {
            encodedChainId = bytes.concat(RLPEncoder.encodeUint256(block.chainid), hex"80_80");
        }

        bytes memory encodedListLength;
        unchecked {
            uint256 listLength = encodedNonce.length +
                encodedGasParam.length +
                encodedTo.length +
                encodedValue.length +
                encodedDataLength.length +
                _transaction.data.length +
                encodedChainId.length;

            // Safe cast, because the length of the list can't be so large.
            encodedListLength = RLPEncoder.encodeListLen(uint64(listLength));
        }

        return
            keccak256(
                bytes.concat(
                    encodedListLength,
                    encodedNonce,
                    encodedGasParam,
                    encodedTo,
                    encodedValue,
                    encodedDataLength,
                    _transaction.data,
                    encodedChainId
                )
            );
    }

    /// @notice Encode hash of the EIP2930 transaction type.
    /// @return keccak256 of the serialized RLP encoded representation of transaction
    function _encodeHashEIP2930Transaction(Transaction calldata _transaction) private view returns (bytes32) {
        // Hash of EIP2930 transactions is encoded the following way:
        // H(0x01 || RLP(chain_id, nonce, gas_price, gas_limit, destination, amount, data, access_list))
        //
        // Note, that on zkSync access lists are not supported and should always be empty.

        // Encode all fixed-length params to avoid "stack too deep error"
        bytes memory encodedFixedLengthParams;
        {
            bytes memory encodedChainId = RLPEncoder.encodeUint256(block.chainid);
            bytes memory encodedNonce = RLPEncoder.encodeUint256(_transaction.nonce);
            bytes memory encodedGasPrice = RLPEncoder.encodeUint256(_transaction.maxFeePerGas);
            bytes memory encodedGasLimit = RLPEncoder.encodeUint256(_transaction.gasLimit);
            bytes memory encodedTo = RLPEncoder.encodeAddress(address(uint160(_transaction.to)));
            bytes memory encodedValue = RLPEncoder.encodeUint256(_transaction.value);
            encodedFixedLengthParams = bytes.concat(
                encodedChainId,
                encodedNonce,
                encodedGasPrice,
                encodedGasLimit,
                encodedTo,
                encodedValue
            );
        }

        // Encode only the length of the transaction data, and not the data itself,
        // so as not to copy to memory a potentially huge transaction data twice.
        bytes memory encodedDataLength;
        {
            // Safe cast, because the length of the transaction data can't be so large.
            uint64 txDataLen = uint64(_transaction.data.length);
            if (txDataLen != 1) {
                // If the length is not equal to one, then only using the length can it be encoded definitely.
                encodedDataLength = RLPEncoder.encodeNonSingleBytesLen(txDataLen);
            } else if (_transaction.data[0] >= 0x80) {
                // If input is a byte in [0x80, 0xff] range, RLP encoding will concatenates 0x81 with the byte.
                encodedDataLength = hex"81";
            }
            // Otherwise the length is not encoded at all.
        }

        // On zkSync, access lists are always zero length (at least for now).
        bytes memory encodedAccessListLength = RLPEncoder.encodeListLen(0);

        bytes memory encodedListLength;
        unchecked {
            uint256 listLength = encodedFixedLengthParams.length +
                encodedDataLength.length +
                _transaction.data.length +
                encodedAccessListLength.length;

            // Safe cast, because the length of the list can't be so large.
            encodedListLength = RLPEncoder.encodeListLen(uint64(listLength));
        }

        return
            keccak256(
                bytes.concat(
                    "\x01",
                    encodedListLength,
                    encodedFixedLengthParams,
                    encodedDataLength,
                    _transaction.data,
                    encodedAccessListLength
                )
            );
    }

    /// @notice Encode hash of the EIP1559 transaction type.
    /// @return keccak256 of the serialized RLP encoded representation of transaction
    function _encodeHashEIP1559Transaction(Transaction calldata _transaction) private view returns (bytes32) {
        // Hash of EIP1559 transactions is encoded the following way:
        // H(0x02 || RLP(chain_id, nonce, max_priority_fee_per_gas, max_fee_per_gas, gas_limit, destination, amount, data, access_list))
        //
        // Note, that on zkSync access lists are not supported and should always be empty.

        // Encode all fixed-length params to avoid "stack too deep error"
        bytes memory encodedFixedLengthParams;
        {
            bytes memory encodedChainId = RLPEncoder.encodeUint256(block.chainid);
            bytes memory encodedNonce = RLPEncoder.encodeUint256(_transaction.nonce);
            bytes memory encodedMaxPriorityFeePerGas = RLPEncoder.encodeUint256(_transaction.maxPriorityFeePerGas);
            bytes memory encodedMaxFeePerGas = RLPEncoder.encodeUint256(_transaction.maxFeePerGas);
            bytes memory encodedGasLimit = RLPEncoder.encodeUint256(_transaction.gasLimit);
            bytes memory encodedTo = RLPEncoder.encodeAddress(address(uint160(_transaction.to)));
            bytes memory encodedValue = RLPEncoder.encodeUint256(_transaction.value);
            encodedFixedLengthParams = bytes.concat(
                encodedChainId,
                encodedNonce,
                encodedMaxPriorityFeePerGas,
                encodedMaxFeePerGas,
                encodedGasLimit,
                encodedTo,
                encodedValue
            );
        }

        // Encode only the length of the transaction data, and not the data itself,
        // so as not to copy to memory a potentially huge transaction data twice.
        bytes memory encodedDataLength;
        {
            // Safe cast, because the length of the transaction data can't be so large.
            uint64 txDataLen = uint64(_transaction.data.length);
            if (txDataLen != 1) {
                // If the length is not equal to one, then only using the length can it be encoded definitely.
                encodedDataLength = RLPEncoder.encodeNonSingleBytesLen(txDataLen);
            } else if (_transaction.data[0] >= 0x80) {
                // If input is a byte in [0x80, 0xff] range, RLP encoding will concatenates 0x81 with the byte.
                encodedDataLength = hex"81";
            }
            // Otherwise the length is not encoded at all.
        }

        // On zkSync, access lists are always zero length (at least for now).
        bytes memory encodedAccessListLength = RLPEncoder.encodeListLen(0);

        bytes memory encodedListLength;
        unchecked {
            uint256 listLength = encodedFixedLengthParams.length +
                encodedDataLength.length +
                _transaction.data.length +
                encodedAccessListLength.length;

            // Safe cast, because the length of the list can't be so large.
            encodedListLength = RLPEncoder.encodeListLen(uint64(listLength));
        }

        return
            keccak256(
                bytes.concat(
                    "\x02",
                    encodedListLength,
                    encodedFixedLengthParams,
                    encodedDataLength,
                    _transaction.data,
                    encodedAccessListLength
                )
            );
    }

    /// @notice Processes the common paymaster flows, e.g. setting proper allowance
    /// for tokens, etc. For more information on the expected behavior, check out
    /// the "Paymaster flows" section in the documentation.
    function processPaymasterInput(Transaction calldata _transaction) internal {
        require(_transaction.paymasterInput.length >= 4, "The standard paymaster input must be at least 4 bytes long");

        bytes4 paymasterInputSelector = bytes4(_transaction.paymasterInput[0:4]);
        if (paymasterInputSelector == IPaymasterFlow.approvalBased.selector) {
            require(
                _transaction.paymasterInput.length >= 68,
                "The approvalBased paymaster input must be at least 68 bytes long"
            );

            // While the actual data consists of address, uint256 and bytes data,
            // the data is needed only for the paymaster, so we ignore it here for the sake of optimization
            (address token, uint256 minAllowance) = abi.decode(_transaction.paymasterInput[4:68], (address, uint256));
            address paymaster = address(uint160(_transaction.paymaster));

            uint256 currentAllowance = IERC20(token).allowance(address(this), paymaster);
            if (currentAllowance < minAllowance) {
                // Some tokens, e.g. USDT require that the allowance is firsty set to zero
                // and only then updated to the new value.

                IERC20(token).safeApprove(paymaster, 0);
                IERC20(token).safeApprove(paymaster, minAllowance);
            }
        } else if (paymasterInputSelector == IPaymasterFlow.general.selector) {
            // Do nothing. general(bytes) paymaster flow means that the paymaster must interpret these bytes on his own.
        } else {
            revert("Unsupported paymaster flow");
        }
    }

    /// @notice Pays the required fee for the transaction to the bootloader.
    /// @dev Currently it pays the maximum amount "_transaction.maxFeePerGas * _transaction.gasLimit",
    /// it will change in the future.
    function payToTheBootloader(Transaction calldata _transaction) internal returns (bool success) {
        address bootloaderAddr = BOOTLOADER_FORMAL_ADDRESS;
        uint256 amount = _transaction.maxFeePerGas * _transaction.gasLimit;

        assembly {
            success := call(gas(), bootloaderAddr, amount, 0, 0, 0, 0)
        }
    }

    // Returns the balance required to process the transaction.
    function totalRequiredBalance(Transaction calldata _transaction) internal pure returns (uint256 requiredBalance) {
        if (address(uint160(_transaction.paymaster)) != address(0)) {
            // Paymaster pays for the fee
            requiredBalance = _transaction.value;
        } else {
            // The user should have enough balance for both the fee and the value of the transaction
            requiredBalance = _transaction.maxFeePerGas * _transaction.gasLimit + _transaction.value;
        }
    }
}






enum ExecutionResult {
    Revert,
    Success
}

bytes4 constant PAYMASTER_VALIDATION_SUCCESS_MAGIC = IPaymaster.validateAndPayForPaymasterTransaction.selector;

interface IPaymaster {
    /// @dev Called by the bootloader to verify that the paymaster agrees to pay for the
    /// fee for the transaction. This transaction should also send the necessary amount of funds onto the bootloader
    /// address.
    /// @param _txHash The hash of the transaction
    /// @param _suggestedSignedHash The hash of the transaction that is signed by an EOA
    /// @param _transaction The transaction itself.
    /// @return magic The value that should be equal to the signature of the validateAndPayForPaymasterTransaction
    /// if the paymaster agrees to pay for the transaction.
    /// @return context The "context" of the transaction: an array of bytes of length at most 1024 bytes, which will be
    /// passed to the `postTransaction` method of the account.
    /// @dev The developer should strive to preserve as many steps as possible both for valid
    /// and invalid transactions as this very method is also used during the gas fee estimation
    /// (without some of the necessary data, e.g. signature).
    function validateAndPayForPaymasterTransaction(
        bytes32 _txHash,
        bytes32 _suggestedSignedHash,
        Transaction calldata _transaction
    ) external payable returns (bytes4 magic, bytes memory context);

    /// @dev Called by the bootloader after the execution of the transaction. Please note that
    /// there is no guarantee that this method will be called at all. Unlike the original EIP4337,
    /// this method won't be called if the transaction execution results in out-of-gas.
    /// @param _context, the context of the execution, returned by the "validateAndPayForPaymasterTransaction" method.
    /// @param  _transaction, the users' transaction.
    /// @param _txResult, the result of the transaction execution (success or failure).
    /// @param _maxRefundedGas, the upper bound on the amout of gas that could be refunded to the paymaster.
    /// @dev The exact amount refunded depends on the gas spent by the "postOp" itself and so the developers should
    /// take that into account.
    function postTransaction(
        bytes calldata _context,
        Transaction calldata _transaction,
        bytes32 _txHash,
        bytes32 _suggestedSignedHash,
        ExecutionResult _txResult,
        uint256 _maxRefundedGas
    ) external payable;
}























//import {TransactionHelper, Transaction} from "@matterlabs/zksync-contracts/l2/system-contracts/libraries/TransactionHelper.sol";
//already imported above
//import "@matterlabs/zksync-contracts/l2/system-contracts/Constants.sol";
//inside below
//import "./interfaces/IAccountCodeStorage.sol";

interface IAccountCodeStorage {
    function storeAccountConstructingCodeHash(address _address, bytes32 _hash) external;

    function storeAccountConstructedCodeHash(address _address, bytes32 _hash) external;

    function markAccountCodeHashAsConstructed(address _address) external;

    function getRawCodeHash(address _address) external view returns (bytes32 codeHash);

    function getCodeHash(uint256 _input) external view returns (bytes32 codeHash);

    function getCodeSize(uint256 _input) external view returns (uint256 codeSize);
}

//import "./interfaces/INonceHolder.sol";
interface INonceHolder {
    event ValueSetUnderNonce(address indexed accountAddress, uint256 indexed key, uint256 value);

    /// @dev Returns the current minimal nonce for account.
    function getMinNonce(address _address) external view returns (uint256);

    /// @dev Returns the raw version of the current minimal nonce
    /// (equal to minNonce + 2^128 * deployment nonce).
    function getRawNonce(address _address) external view returns (uint256);

    /// @dev Increases the minimal nonce for the msg.sender.
    function increaseMinNonce(uint256 _value) external returns (uint256);

    /// @dev Sets the nonce value `key` as used.
    function setValueUnderNonce(uint256 _key, uint256 _value) external;

    /// @dev Gets the value stored inside a custom nonce.
    function getValueUnderNonce(uint256 _key) external view returns (uint256);

    /// @dev A convenience method to increment the minimal nonce if it is equal
    /// to the `_expectedNonce`.
    function incrementMinNonceIfEquals(uint256 _expectedNonce) external;

    /// @dev Returns the deployment nonce for the accounts used for CREATE opcode.
    function getDeploymentNonce(address _address) external view returns (uint256);

    /// @dev Increments the deployment nonce for the account and returns the previous one.
    function incrementDeploymentNonce(address _address) external returns (uint256);

    /// @dev Determines whether a certain nonce has been already used for an account.
    function validateNonceUsage(address _address, uint256 _key, bool _shouldBeUsed) external view;

    /// @dev Returns whether a nonce has been used for an account.
    function isNonceUsed(address _address, uint256 _nonce) external view returns (bool);
}


//import "./interfaces/IKnownCodesStorage.sol";
interface IKnownCodesStorage {
    event MarkedAsKnown(bytes32 indexed bytecodeHash, bool indexed sendBytecodeToL1);

    function markFactoryDeps(bool _shouldSendToL1, bytes32[] calldata _hashes) external;

    function markBytecodeAsPublished(
        bytes32 _bytecodeHash,
        bytes32 _l1PreimageHash,
        uint256 _l1PreimageBytesLen
    ) external;

    function getMarker(bytes32 _hash) external view returns (uint256);
}

//import "./interfaces/IImmutableSimulator.sol";
struct ImmutableData {
    uint256 index;
    bytes32 value;
}

interface IImmutableSimulator {
    function getImmutable(address _dest, uint256 _index) external view returns (bytes32);

    function setImmutables(address _dest, ImmutableData[] calldata _immutables) external;
}

//import "./interfaces/IL1Messenger.sol";

interface IL1Messenger {
    // Possibly in the future we will be able to track the messages sent to L1 with
    // some hooks in the VM. For now, it is much easier to track them with L2 events.
    event L1MessageSent(address indexed _sender, bytes32 indexed _hash, bytes _message);

    function sendToL1(bytes memory _message) external returns (bytes32);
}

//import "./interfaces/ISystemContext.sol";
interface ISystemContext {
    function chainId() external view returns (uint256);

    function origin() external view returns (address);

    function gasPrice() external view returns (uint256);

    function blockGasLimit() external view returns (uint256);

    function coinbase() external view returns (address);

    function difficulty() external view returns (uint256);

    function baseFee() external view returns (uint256);

    function blockHash(uint256 _block) external view returns (bytes32);

    function getBlockHashEVM(uint256 _block) external view returns (bytes32);

    function getBlockNumberAndTimestamp() external view returns (uint256 blockNumber, uint256 blockTimestamp);

    // Note, that for now, the implementation of the bootloader allows this variables to
    // be incremented multiple times inside a block, so it should not relied upon right now.
    function getBlockNumber() external view returns (uint256);

    function getBlockTimestamp() external view returns (uint256);
}

//import "./interfaces/IBytecodeCompressor.sol";
interface IBytecodeCompressor {
    function publishCompressedBytecode(
        bytes calldata _bytecode,
        bytes calldata _rawCompressedData
    ) external payable returns (bytes32 bytecodeHash);
}

//import "./BootloaderUtilities.sol";

//import "../libraries/TransactionHelper.sol"; already imported

interface IBootloaderUtilities {
    function getTransactionHashes(
        Transaction calldata _transaction
    ) external view returns (bytes32 txHash, bytes32 signedTxHash);
}

/// @dev All the system contracts introduced by zkSync have their addresses
/// started from 2^15 in order to avoid collision with Ethereum precompiles.

/// @dev All the system contracts must be located in the kernel space,
/// i.e. their addresses must be below 2^16.

address constant ECRECOVER_SYSTEM_CONTRACT = address(0x01);

/// @dev The current maximum deployed precompile address.
/// Note: currently only two precompiles are deployed:
/// 0x01 - ecrecover
/// 0x02 - sha256
/// Important! So the constant should be updated if more precompiles are deployed.
uint256 constant CURRENT_MAX_PRECOMPILE_ADDRESS = uint256(uint160(SHA256_SYSTEM_CONTRACT));

IAccountCodeStorage constant ACCOUNT_CODE_STORAGE_SYSTEM_CONTRACT = IAccountCodeStorage(
    address(SYSTEM_CONTRACTS_OFFSET + 0x02)
);
INonceHolder constant NONCE_HOLDER_SYSTEM_CONTRACT = INonceHolder(address(SYSTEM_CONTRACTS_OFFSET + 0x03));
IKnownCodesStorage constant KNOWN_CODE_STORAGE_CONTRACT = IKnownCodesStorage(address(SYSTEM_CONTRACTS_OFFSET + 0x04));
IImmutableSimulator constant IMMUTABLE_SIMULATOR_SYSTEM_CONTRACT = IImmutableSimulator(
    address(SYSTEM_CONTRACTS_OFFSET + 0x05)
);
IContractDeployer constant DEPLOYER_SYSTEM_CONTRACT = IContractDeployer(address(SYSTEM_CONTRACTS_OFFSET + 0x06));

// A contract that is allowed to deploy any codehash
// on any address. To be used only during an upgrade.
address constant FORCE_DEPLOYER = address(SYSTEM_CONTRACTS_OFFSET + 0x07);
IL1Messenger constant L1_MESSENGER_CONTRACT = IL1Messenger(address(SYSTEM_CONTRACTS_OFFSET + 0x08));



ISystemContext constant SYSTEM_CONTEXT_CONTRACT = ISystemContext(payable(address(SYSTEM_CONTRACTS_OFFSET + 0x0b)));
//load bootloaderutilites

pragma solidity ^0.8.0;

//import "./interfaces/IBootloaderUtilities.sol"; already loaded
//import "./libraries/TransactionHelper.sol"; already loaded
//import "./libraries/RLPEncoder.sol"; already loaded
//import "./libraries/EfficientCall.sol"; already loaded

/**
 * @author Matter Labs
 * @notice A contract that provides some utility methods for the bootloader
 * that is very hard to write in Yul.
 */
contract BootloaderUtilities is IBootloaderUtilities {
    using TransactionHelper for *;

    /// @notice Calculates the canonical transaction hash and the recommended transaction hash.
    /// @param _transaction The transaction.
    /// @return txHash and signedTxHash of the transaction, i.e. the transaction hash to be used in the explorer and commits to all
    /// the fields of the transaction and the recommended hash to be signed for this transaction.
    /// @dev txHash must be unique for all transactions.
    function getTransactionHashes(
        Transaction calldata _transaction
    ) external view override returns (bytes32 txHash, bytes32 signedTxHash) {
        signedTxHash = _transaction.encodeHash();
        if (_transaction.txType == EIP_712_TX_TYPE) {
            txHash = keccak256(bytes.concat(signedTxHash, EfficientCall.keccak(_transaction.signature)));
        } else if (_transaction.txType == LEGACY_TX_TYPE) {
            txHash = encodeLegacyTransactionHash(_transaction);
        } else if (_transaction.txType == EIP_1559_TX_TYPE) {
            txHash = encodeEIP1559TransactionHash(_transaction);
        } else if (_transaction.txType == EIP_2930_TX_TYPE) {
            txHash = encodeEIP2930TransactionHash(_transaction);
        } else {
            revert("Unsupported tx type");
        }
    }

    /// @notice Calculates the hash for a legacy transaction.
    /// @param _transaction The legacy transaction.
    /// @return txHash The hash of the transaction.
    function encodeLegacyTransactionHash(Transaction calldata _transaction) internal view returns (bytes32 txHash) {
        // Hash of legacy transactions are encoded as one of the:
        // - RLP(nonce, gasPrice, gasLimit, to, value, data, chainId, 0, 0)
        // - RLP(nonce, gasPrice, gasLimit, to, value, data)
        //
        // In this RLP encoding, only the first one above list appears, so we encode each element
        // inside list and then concatenate the length of all elements with them.

        bytes memory encodedNonce = RLPEncoder.encodeUint256(_transaction.nonce);
        // Encode `gasPrice` and `gasLimit` together to prevent "stack too deep error".
        bytes memory encodedGasParam;
        {
            bytes memory encodedGasPrice = RLPEncoder.encodeUint256(_transaction.maxFeePerGas);
            bytes memory encodedGasLimit = RLPEncoder.encodeUint256(_transaction.gasLimit);
            encodedGasParam = bytes.concat(encodedGasPrice, encodedGasLimit);
        }

        bytes memory encodedTo = RLPEncoder.encodeAddress(address(uint160(_transaction.to)));
        bytes memory encodedValue = RLPEncoder.encodeUint256(_transaction.value);
        // Encode only the length of the transaction data, and not the data itself,
        // so as not to copy to memory a potentially huge transaction data twice.
        bytes memory encodedDataLength;
        {
            // Safe cast, because the length of the transaction data can't be so large.
            uint64 txDataLen = uint64(_transaction.data.length);
            if (txDataLen != 1) {
                // If the length is not equal to one, then only using the length can it be encoded definitely.
                encodedDataLength = RLPEncoder.encodeNonSingleBytesLen(txDataLen);
            } else if (_transaction.data[0] >= 0x80) {
                // If input is a byte in [0x80, 0xff] range, RLP encoding will concatenates 0x81 with the byte.
                encodedDataLength = hex"81";
            }
            // Otherwise the length is not encoded at all.
        }

        bytes memory rEncoded;
        {
            uint256 rInt = uint256(bytes32(_transaction.signature[0:32]));
            rEncoded = RLPEncoder.encodeUint256(rInt);
        }
        bytes memory sEncoded;
        {
            uint256 sInt = uint256(bytes32(_transaction.signature[32:64]));
            sEncoded = RLPEncoder.encodeUint256(sInt);
        }
        bytes memory vEncoded;
        {
            uint256 vInt = uint256(uint8(_transaction.signature[64]));
            require(vInt == 27 || vInt == 28, "Invalid v value");

            // If the `chainId` is specified in the transaction, then the `v` value is encoded as
            // `35 + y + 2 * chainId == vInt + 8 + 2 * chainId`, where y - parity bit (see EIP-155).
            if (_transaction.reserved[0] != 0) {
                vInt += 8 + block.chainid * 2;
            }

            vEncoded = RLPEncoder.encodeUint256(vInt);
        }

        bytes memory encodedListLength;
        unchecked {
            uint256 listLength = encodedNonce.length +
                encodedGasParam.length +
                encodedTo.length +
                encodedValue.length +
                encodedDataLength.length +
                _transaction.data.length +
                rEncoded.length +
                sEncoded.length +
                vEncoded.length;

            // Safe cast, because the length of the list can't be so large.
            encodedListLength = RLPEncoder.encodeListLen(uint64(listLength));
        }

        return
            keccak256(
                bytes.concat(
                    encodedListLength,
                    encodedNonce,
                    encodedGasParam,
                    encodedTo,
                    encodedValue,
                    encodedDataLength,
                    _transaction.data,
                    vEncoded,
                    rEncoded,
                    sEncoded
                )
            );
    }

    /// @notice Calculates the hash for an EIP2930 transaction.
    /// @param _transaction The EIP2930 transaction.
    /// @return txHash The hash of the transaction.
    function encodeEIP2930TransactionHash(Transaction calldata _transaction) internal view returns (bytes32) {
        // Encode all fixed-length params to avoid "stack too deep error"
        bytes memory encodedFixedLengthParams;
        {
            bytes memory encodedChainId = RLPEncoder.encodeUint256(block.chainid);
            bytes memory encodedNonce = RLPEncoder.encodeUint256(_transaction.nonce);
            bytes memory encodedGasPrice = RLPEncoder.encodeUint256(_transaction.maxFeePerGas);
            bytes memory encodedGasLimit = RLPEncoder.encodeUint256(_transaction.gasLimit);
            bytes memory encodedTo = RLPEncoder.encodeAddress(address(uint160(_transaction.to)));
            bytes memory encodedValue = RLPEncoder.encodeUint256(_transaction.value);
            encodedFixedLengthParams = bytes.concat(
                encodedChainId,
                encodedNonce,
                encodedGasPrice,
                encodedGasLimit,
                encodedTo,
                encodedValue
            );
        }

        // Encode only the length of the transaction data, and not the data itself,
        // so as not to copy to memory a potentially huge transaction data twice.
        bytes memory encodedDataLength;
        {
            // Safe cast, because the length of the transaction data can't be so large.
            uint64 txDataLen = uint64(_transaction.data.length);
            if (txDataLen != 1) {
                // If the length is not equal to one, then only using the length can it be encoded definitely.
                encodedDataLength = RLPEncoder.encodeNonSingleBytesLen(txDataLen);
            } else if (_transaction.data[0] >= 0x80) {
                // If input is a byte in [0x80, 0xff] range, RLP encoding will concatenates 0x81 with the byte.
                encodedDataLength = hex"81";
            }
            // Otherwise the length is not encoded at all.
        }

        // On zkSync, access lists are always zero length (at least for now).
        bytes memory encodedAccessListLength = RLPEncoder.encodeListLen(0);

        bytes memory rEncoded;
        {
            uint256 rInt = uint256(bytes32(_transaction.signature[0:32]));
            rEncoded = RLPEncoder.encodeUint256(rInt);
        }
        bytes memory sEncoded;
        {
            uint256 sInt = uint256(bytes32(_transaction.signature[32:64]));
            sEncoded = RLPEncoder.encodeUint256(sInt);
        }
        bytes memory vEncoded;
        {
            uint256 vInt = uint256(uint8(_transaction.signature[64]));
            require(vInt == 27 || vInt == 28, "Invalid v value");

            vEncoded = RLPEncoder.encodeUint256(vInt - 27);
        }

        bytes memory encodedListLength;
        unchecked {
            uint256 listLength = encodedFixedLengthParams.length +
                encodedDataLength.length +
                _transaction.data.length +
                encodedAccessListLength.length +
                rEncoded.length +
                sEncoded.length +
                vEncoded.length;

            // Safe cast, because the length of the list can't be so large.
            encodedListLength = RLPEncoder.encodeListLen(uint64(listLength));
        }

        return
            keccak256(
                bytes.concat(
                    "\x01",
                    encodedListLength,
                    encodedFixedLengthParams,
                    encodedDataLength,
                    _transaction.data,
                    encodedAccessListLength,
                    vEncoded,
                    rEncoded,
                    sEncoded
                )
            );
    }

    /// @notice Calculates the hash for an EIP1559 transaction.
    /// @param _transaction The legacy transaction.
    /// @return txHash The hash of the transaction.
    function encodeEIP1559TransactionHash(Transaction calldata _transaction) internal view returns (bytes32) {
        // The formula for hash of EIP1559 transaction in the original proposal:
        // https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1559.md

        // Encode all fixed-length params to avoid "stack too deep error"
        bytes memory encodedFixedLengthParams;
        {
            bytes memory encodedChainId = RLPEncoder.encodeUint256(block.chainid);
            bytes memory encodedNonce = RLPEncoder.encodeUint256(_transaction.nonce);
            bytes memory encodedMaxPriorityFeePerGas = RLPEncoder.encodeUint256(_transaction.maxPriorityFeePerGas);
            bytes memory encodedMaxFeePerGas = RLPEncoder.encodeUint256(_transaction.maxFeePerGas);
            bytes memory encodedGasLimit = RLPEncoder.encodeUint256(_transaction.gasLimit);
            bytes memory encodedTo = RLPEncoder.encodeAddress(address(uint160(_transaction.to)));
            bytes memory encodedValue = RLPEncoder.encodeUint256(_transaction.value);
            encodedFixedLengthParams = bytes.concat(
                encodedChainId,
                encodedNonce,
                encodedMaxPriorityFeePerGas,
                encodedMaxFeePerGas,
                encodedGasLimit,
                encodedTo,
                encodedValue
            );
        }

        // Encode only the length of the transaction data, and not the data itself,
        // so as not to copy to memory a potentially huge transaction data twice.
        bytes memory encodedDataLength;
        {
            // Safe cast, because the length of the transaction data can't be so large.
            uint64 txDataLen = uint64(_transaction.data.length);
            if (txDataLen != 1) {
                // If the length is not equal to one, then only using the length can it be encoded definitely.
                encodedDataLength = RLPEncoder.encodeNonSingleBytesLen(txDataLen);
            } else if (_transaction.data[0] >= 0x80) {
                // If input is a byte in [0x80, 0xff] range, RLP encoding will concatenates 0x81 with the byte.
                encodedDataLength = hex"81";
            }
            // Otherwise the length is not encoded at all.
        }

        // On zkSync, access lists are always zero length (at least for now).
        bytes memory encodedAccessListLength = RLPEncoder.encodeListLen(0);

        bytes memory rEncoded;
        {
            uint256 rInt = uint256(bytes32(_transaction.signature[0:32]));
            rEncoded = RLPEncoder.encodeUint256(rInt);
        }
        bytes memory sEncoded;
        {
            uint256 sInt = uint256(bytes32(_transaction.signature[32:64]));
            sEncoded = RLPEncoder.encodeUint256(sInt);
        }
        bytes memory vEncoded;
        {
            uint256 vInt = uint256(uint8(_transaction.signature[64]));
            require(vInt == 27 || vInt == 28, "Invalid v value");

            vEncoded = RLPEncoder.encodeUint256(vInt - 27);
        }

        bytes memory encodedListLength;
        unchecked {
            uint256 listLength = encodedFixedLengthParams.length +
                encodedDataLength.length +
                _transaction.data.length +
                encodedAccessListLength.length +
                rEncoded.length +
                sEncoded.length +
                vEncoded.length;

            // Safe cast, because the length of the list can't be so large.
            encodedListLength = RLPEncoder.encodeListLen(uint64(listLength));
        }

        return
            keccak256(
                bytes.concat(
                    "\x02",
                    encodedListLength,
                    encodedFixedLengthParams,
                    encodedDataLength,
                    _transaction.data,
                    encodedAccessListLength,
                    vEncoded,
                    rEncoded,
                    sEncoded
                )
            );
    }
}

BootloaderUtilities constant BOOTLOADER_UTILITIES = BootloaderUtilities(address(SYSTEM_CONTRACTS_OFFSET + 0x0c));

address constant EVENT_WRITER_CONTRACT = address(SYSTEM_CONTRACTS_OFFSET + 0x0d);

IBytecodeCompressor constant BYTECODE_COMPRESSOR_CONTRACT = IBytecodeCompressor(
    address(SYSTEM_CONTRACTS_OFFSET + 0x0e)
);


/// @dev The maximal msg.value that context can have
uint256 constant MAX_MSG_VALUE = 2 ** 128 - 1;

/// @dev Prefix used during derivation of account addresses using CREATE2
/// @dev keccak256("zksyncCreate2")
bytes32 constant CREATE2_PREFIX = 0x2020dba91b30cc0006188af794c2fb30dd8520db7e2c088b7fc7c103c00ca494;
/// @dev Prefix used during derivation of account addresses using CREATE
/// @dev keccak256("zksyncCreate")
bytes32 constant CREATE_PREFIX = 0x63bae3a9951d38e8a3fbb7b70909afc1200610fc5bc55ade242f815974674f23;




// Define the TokenAmount struct
struct TokenAmount {
    address token;     // Address of the token
    uint256 amount;    // Amount of the token
}

// Define the SwapStep struct
struct SwapStep {
    address pool;          // Address of the liquidity pool
    bytes data;           // Additional data for the swap
    address callback;      // Address for the callback function
    bytes callbackData;    // Data for the callback function
}

// Define the SwapPath struct
struct SwapPath {
    SwapStep[] steps;     // Array of swap steps
    address tokenIn;      // Address of the input token
    uint256 amountIn;     // Amount of the input token
}

interface IRouter {
    /**
     * @dev Performs a swap.
     * @param paths The array of swap paths.
     * @param amountOutMin The minimum amount of output tokens to receive.
     * @param deadline The time by which the swap must be completed.
     * @return amountOut The amount of output tokens received.
     */
    function swap(
        SwapPath[] memory paths,
        uint256 amountOutMin,
        uint256 deadline
    ) external payable returns (TokenAmount memory amountOut);
    
    
}




interface zkBitcoin2 {
    function mintTo(uint256 nonce, address mintToAddress) external;
    function multiMint_SameAddress(address mintToAddress, uint256[] memory nonce) external;
    function getMiningReward() external view returns (uint);
    function blocksToReadjust() external view returns (uint blocks);
}


interface Paymaster2 {
    	function NumberofMints() external view returns (uint);
    	function AddressToUse() external view returns (address);
        function PoolContract_Mint_No_Paymaster(uint256[] memory nonce) external;
        function MultiMint_Paymaster(uint256[] memory nonce, uint nonceLength, uint requiredZKBTCz) external;
 	function estimateGas_Paymaster(uint256[] memory nonce, uint nonceLength) external;
 	function withdrawERC20(address token, uint256 amount) external;
 	function withdrawERC721(address token, uint256 tokenId) external;
 	function withdrawERC1155(address token, uint256 tokenId, uint256 amount, bytes calldata data) external;
	function withdrawETH(uint256 amount) external;
}


interface IUniswapV2Pair {
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1);
}




contract MyPaymaster is IPaymaster {


    mapping(address=>address) public AllowedToUsePaymaster;
    mapping(address=>bool) public mintedETH;

    address public allowedToken;

    address public constant WETH = 0x000000000000000000000000000000000000800A; // Wrapped ETH address
    address public pairAddress = 0x7002d33C756f593AB41aF4a236005766E80dC960;  //Mainnet = 0x7002d33C756f593AB41aF4a236005766E80dC960
    address public zeroAddress = address(0);
    address public IrouterAddress = 0x9B5def958d0f3b6955cBEa4D5B7809b2fb26b059;  //Mainnet = 0x9B5def958d0f3b6955cBEa4D5B7809b2fb26b059

    address public mainWithdrawler = msg.sender; // Address to withdraw Paymaster zkBTC to
    address public mainUpdater = msg.sender; // Address to Update Token Price
    address public owner = msg.sender;  //Main contract owner
    address public mainDiscounter = msg.sender; //Address to update discount
    uint public TokenPrice = getPriceX();
    
     //If under 10 good blocks add GasBuffer if 10 good blocks and over add GasBuffer2
    uint public goodLoopsGasExtra=10;

    //30% discount for using Paymaster
    uint public discount=30;

////
//PayMaster Stuff First then Minting
////
    constructor(address _allowedToken){
    	allowedToken = _allowedToken;
    }
       
    
    function setOwner(address _owner) public onlyOwner {
        owner = _owner;
    }
    
    
    function setGoodLoopsGasExtra (uint256 extraLoops)public onlyOwner {
	    goodLoopsGasExtra = extraLoops;
    }
    
    
    

    function setDiscount(uint _discount) public onlyDiscounter {
    	require(_discount<90,"Max discount is 90%");
    	discount = _discount;
    }
    
    
    function getDiscount ()public view returns (uint) {
	    return discount;
    }
    
    
    function setMainDiscounter(address _mainDiscounter) public onlyDiscounter {
    	mainDiscounter = _mainDiscounter;
    }
    
    function setMainWithdrawler(address _mainWithdrawler) public onlyMainWithdrawler {
    	mainWithdrawler = _mainWithdrawler;
    }
    
    function setMainUpdater(address _mainUpdater) public onlyMainUpdater {
    	mainUpdater = _mainUpdater;
    }
    
    function setTokenPrice() public onlyMainUpdater {
    	TokenPrice = getPriceX();
    }
    
    
    function withdrawAll(uint amountETH, uint amountZKBTCF) public onlyMainWithdrawler {
    	IERC20(allowedToken).transfer(mainWithdrawler, amountZKBTCF);
    	require(address(this).balance >= amountETH, "Insufficient balance in contract");
        // Transfer ETH
        (bool sent, ) = mainWithdrawler.call{value: amountETH}("");
        require(sent, "Failed to send ETH");
    }
    
    function withdrawETH(uint amountETH) public onlyMainWithdrawler {
    	require(address(this).balance >= amountETH, "Insufficient balance in contract");
        // Transfer ETH
        (bool sent, ) = mainWithdrawler.call{value: amountETH}("");
        require(sent, "Failed to send ETH");
    }
    
    function withdrawToken(address Token_addy, uint amountTOKEN) public onlyMainWithdrawler {
    	IERC20(Token_addy).transfer(mainWithdrawler, amountTOKEN);
    	
    }
    
    
    function getMainWithdrawler() public view returns (address) {
    	return mainWithdrawler;
    }
    
    function getMainUpdater() public view returns (address) {
    	return mainUpdater;
    }
    
    
    
    
    function getGoodLoopsGasExtra  ()public view returns (uint) {
	    return goodLoopsGasExtra;
    }
    
    // Returns the price of `token` in terms of ETH x1000
    function  getPriceX() public view returns (uint) {

        IUniswapV2Pair pair = IUniswapV2Pair(pairAddress);
        (uint reserves0, uint reserves1) = pair.getReserves();

        // Ensure that reserves are returned in the correct order (token, WETH)
        (uint tokenReserves, uint ethReserves) = address(this) < WETH ? (reserves0, reserves1) : (reserves1, reserves0);
	
	
        return (tokenReserves * 10**3) / ethReserves; // Normalize to token's decimals if necessary
    }
    
    modifier onlyMainWithdrawler() {
        require(msg.sender == mainWithdrawler || owner == msg.sender, "only mainWithdrawler/owner can call this function");
        _;
    }
    modifier onlyMainUpdater() {
        require(msg.sender == mainUpdater || owner == msg.sender, "only mainUpdater/owner can call this function");
        _;
    }
    
    modifier onlyDiscounter() {
        require(msg.sender == mainDiscounter || owner == msg.sender, "only mainUpdater/owner can call this function");
        _;
    }

    modifier onlyBootloader() {
        require(
            msg.sender == BOOTLOADER_FORMAL_ADDRESS,
            "Only bootloader can call this method"
        );
        // Continue execution if called from the bootloader.
        _;
    }    
    
    modifier onlyOwner() {
        require(msg.sender == owner, "only owner");
        _;
    }
    
    function validateAndPayForPaymasterTransaction(
    bytes32,
    bytes32,
    Transaction calldata _transaction
)
    external
    payable
    onlyBootloader
    returns (bytes4 magic, bytes memory context)

{

    magic = PAYMASTER_VALIDATION_SUCCESS_MAGIC;
    require(
        _transaction.paymasterInput.length >= 4,
        "The standard paymaster input must be at least 4 bytes long"
    );
    bytes4 paymasterInputSelector = bytes4(_transaction.paymasterInput[0:4]);
    if (paymasterInputSelector == IPaymasterFlow.approvalBased.selector) {
        address whoSentTx =  address(uint160(_transaction.from));
        require(address(this) == address(uint160(_transaction.to)), "Must only send Paymaster Transaction to THIS address, cant use any other address");
        
        
        bytes4 functionSelector = bytes4(_transaction.data[:4]);
        require(functionSelector == 0x62344a13, "MUst be the correct function, we only are allowed to call the MultiMint_Paymaster function on this contract");
        address mintToAddress;
        uint256[] memory nonce;
        uint mintsgreaterthan25 = 0;
        
        (mintToAddress, nonce) = abi.decode(_transaction.data[4:], (address, uint256[]));
	uint nonceLength = nonce.length;
	uint256 requiredETH = _transaction.gasLimit * _transaction.maxFeePerGas;

        uint price = TokenPrice;
        uint curPrice = getPriceX();
        //Allows token price to fall and stay correct
        if(price < curPrice){
        	price = curPrice;
        }
        uint totalZKBTC = (requiredETH * price) / (10**3);


	uint256 blocksToReadjustment = zkBitcoin2(allowedToken).blocksToReadjust();
	if(blocksToReadjustment < nonceLength){
		nonceLength = blocksToReadjustment;
	}
	uint buffer = 100;
	address WhatSubContractToUse = AllowedToUsePaymaster[mintToAddress];
	if(WhatSubContractToUse != address(0)){
		Paymaster2(WhatSubContractToUse).MultiMint_Paymaster(nonce, nonceLength, totalZKBTC);
		mintsgreaterthan25 = External_NumberOfMints(whoSentTx);
		totalZKBTC = totalZKBTC * (100 - discount) / 100;  //Discount mints 30% about to start but not the first one!
	}
	else{
		deployNewContract(whoSentTx);
		for(uint xx=0; xx<nonceLength; xx++){
			zkBitcoin2(allowedToken).mintTo(nonce[xx], address(this));
		}
		buffer = buffer + 100;
	}

	
        
	uint rewardAmtz = zkBitcoin2(allowedToken).getMiningReward();
	uint mintAmount = nonceLength * rewardAmtz;



	//SET TO 10 to start for easy testing, should test it to 100
	//if(mintsgreaterthan25 > 100 && mintedETH[whoSentTx] == false ){
	if(mintsgreaterthan25 > 25 && mintedETH[WhatSubContractToUse] == false && whoSentTx == mintToAddress ){

			mintedETH[WhatSubContractToUse] = true;
			uint sendAmount = mintAmount - totalZKBTC;
			uint timeStampz = block.timestamp + 120;
			performSwap(sendAmount, allowedToken, mintToAddress, 0, timeStampz);
			totalZKBTC = totalZKBTC * 100 / (100 - discount); //No discounts when doing a swap one.
			buffer = buffer + 150;

		
	}else{
		
		IERC20(allowedToken).transfer(mintToAddress, mintAmount - totalZKBTC);
	}
	
	if(goodLoopsGasExtra > nonceLength){
		buffer = buffer + 100;
	}
	require(gasleft() > buffer * _transaction.gasLimit / 1000,"Not enough gas for transaction , most likely not enough gas provided");
	    
   	(bool success, ) = payable(BOOTLOADER_FORMAL_ADDRESS).call{value: requiredETH}("");
        require(success, "Failed to transfer tx fee to the bootloader. Paymaster balance might not be enough gas provided");
	    
       } else {
        revert("Unsupported paymaster flow");
    }
}

    

    function postTransaction(
        bytes calldata _context,
        Transaction calldata _transaction,
        bytes32,
        bytes32,
        ExecutionResult _txResult,
        uint256 _maxRefundedGas
    ) external payable override onlyBootloader { 
    	//Post Transaction code here
    
    }
   


      function performSwap(uint tokenAmountIn, address tokenIn2, address userAccount, uint256 amountOutMin, uint256 deadline) internal {
        // Approve the token for the router
        IERC20(tokenIn2).approve(IrouterAddress, tokenAmountIn);
        
        // Create encoded data
        bytes memory encodedData = abi.encode(tokenIn2, userAccount, 1); // 1 signals ETH payout.
	SwapStep[] memory employee = new SwapStep[](1);
	employee[0].pool = pairAddress;
	employee[0].data = encodedData; 
	employee[0].callback = zeroAddress;
	employee[0].callbackData = new bytes(0);


        // Create a SwapPath instance
        
	SwapPath[] memory employee22 = new SwapPath[](1);
        employee22[0].steps = employee;
        employee22[0].tokenIn = tokenIn2;
        employee22[0].amountIn = tokenAmountIn;
        
        
        // Call the swap function
        IRouter(IrouterAddress).swap(employee22, 0, deadline);
    }

    
    
    
	
	
	// Function to deploy a new contract and store its address
	function deployNewContract(address sender) public {
		// Deploy the new contract
    		require(AllowedToUsePaymaster[sender] == address(0), "Must not already have a contract to use");

		PaymasterZKBitcoin_Pool newContract = new PaymasterZKBitcoin_Pool(allowedToken, address(this), sender);
        
		// Store the address of the newly deployed contract
		address deployedContractAddress = address(newContract);
		AllowedToUsePaymaster[sender] = deployedContractAddress;
	}

	function YourPaymasterAddress(address userAddress) public view returns (address){
		return AllowedToUsePaymaster[userAddress];
	
	}
	
	//For use in estimateing Gas, this will either 
	//A) Deploy you a new Pool contract if one hasnt been deployed while submitting answers to this contract. 
	//B) Submit your answers to the Pool contract to test parameters and figure out approxemently around how much gas we will use
	//ALL minted tokens in estimateGas are used to pay the Paymaster, you wont recieve any by calling this function because its just to test estimateGas.
	
	
	function estimateGas(address userAddress, uint[] memory nonces) public returns (bool){
	
	
		uint nonceLength = nonces.length;
		
		uint256 blocksToReadjustment = zkBitcoin2(allowedToken).blocksToReadjust();
		if(blocksToReadjustment < nonceLength){
			nonceLength = blocksToReadjustment;
		}
		
	
	
		address WhatSubContractToUse = AllowedToUsePaymaster[userAddress];
		if(WhatSubContractToUse != address(0)){
			Paymaster2(WhatSubContractToUse).estimateGas_Paymaster(nonces, nonceLength);
		}
		else{
			deployNewContract(userAddress);
			for(uint xx=0; xx<nonceLength; xx++){
				zkBitcoin2(allowedToken).mintTo(nonces[xx], address(this));
			}
		}
		return true;
	}
	
	//Allows users to MultiMint to their contract without the Paymaster, keeping their mining contracts working forever!.
	
	function ContractMultiMint_No_Paymaster(address userAddress, uint[] memory nonces)public returns (bool){
		address WhatSubContractToUse = AllowedToUsePaymaster[userAddress];
		if(WhatSubContractToUse != address(0)){
			Paymaster2(WhatSubContractToUse).PoolContract_Mint_No_Paymaster(nonces);
		}else{
			deployNewContract(userAddress);
			zkBitcoin2(allowedToken).multiMint_SameAddress(userAddress, nonces);
			
		}
		return true;
	}
	
	
 	function External_recieveETH_From_SubContract(address user, uint amount) public{
		address WhatSubContractToUse = AllowedToUsePaymaster[user];
		
		Paymaster2(WhatSubContractToUse).withdrawETH(amount);
	}
	
 	function External_recieveERC20_From_SubContract(address user, address token, uint amount) public{
		address WhatSubContractToUse = AllowedToUsePaymaster[user];
		
		Paymaster2(WhatSubContractToUse).withdrawERC20(token, amount);
	}
	
	function External_recieveNFT721_From_SubContract(address user, address token, uint NFT_ID) public{
	
		address WhatSubContractToUse = AllowedToUsePaymaster[user];
		
		Paymaster2(WhatSubContractToUse).withdrawERC721(token, NFT_ID);
	
	}
	
	function External_recieveNFT115_From_SubContract(address user, address token, uint256 tokenId, uint256 amount, bytes calldata data) public{
	
	
		address WhatSubContractToUse = AllowedToUsePaymaster[user];
		
		Paymaster2(WhatSubContractToUse).withdrawERC1155(token, tokenId, amount, data);
	
	}
	function External_NumberOfMints(address user) public view returns (uint){
	
	
		address WhatSubContractToUse = AllowedToUsePaymaster[user];
		
		return Paymaster2(WhatSubContractToUse).NumberofMints();
	
	}
	
	function MultiMint_Paymaster(address MintToAddress, uint[] memory nonces) public returns (bool)
	{
		return true;
	}
	
    receive() external payable {}
    
    
    }
    
    
    

