/* Standard includes. */
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stddef.h>

struct xDNSAnswerRecord {
  uint16_t usType;
  uint16_t usClass;
  uint32_t ulTTL;
  uint16_t usDataLength;
};

typedef struct xDNSAnswerRecord DNSAnswerRecord_t;

struct xDNSMessage {
  uint16_t usIdentifier;
  uint16_t usFlags;
  uint16_t usQuestions;
  uint16_t usAnswers;
  uint16_t usAuthorityRRs;
  uint16_t usAdditionalRRs;
};

typedef struct xDNSMessage DNSMessage_t;

#define dnsNAME_IS_OFFSET ((uint8_t)0xc0)
#define dnsPARSE_ERROR 0UL
#define ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY (6)
#define pdFALSE ((BaseType_t)0)
#define pdTRUE ((BaseType_t)1)
#define ipSIZE_OF_IPv4_ADDRESS 4U
#define dnsTYPE_A_HOST 0x01U
#define dnsRX_FLAGS_MASK                                                       \
  0x0f80U /* The bits of interest in the flags field of incoming DNS messages. \
           */
#define dnsEXPECTED_RX_FLAGS                                                   \
  0x0080U /* Should be a response, without any errors. */
#define ipFALSE_BOOL (1 == 2)

#define FreeRTOS_printf(MSG)                                                   \
  do {                                                                         \
  } while (ipFALSE_BOOL)
#define ipconfigDNS_CACHE_NAME_LENGTH 254

// for now
#define ipconfigUSE_DNS_CACHE 1

typedef long BaseType_t;

#define ipPOINTER_CAST(TYPE, pointer) ((TYPE)(pointer))
#define FreeRTOS_htons(x) ((uint16_t)(x))
#define FreeRTOS_ntohs(x) FreeRTOS_htons(x)

/*@
  predicate is_uint8_t(integer n) =
      0 <= n <= UCHAR_MAX;
  
  predicate is_uint16_t(integer n) =
      0 <= n <= USHRT_MAX;
  
  predicate is_uint32_t(integer n) =
      0 <= n <= UINT_MAX;

  predicate in_range(uint8_t * ptr, uint8_t *buffer, size_t bufferLen) = 
    buffer <= ptr <= buffer + bufferLen - 1;
*/

/*@
  assigns \nothing;
*/
static uint16_t usChar2u16(const uint8_t *apChr);
static uint16_t usChar2u16(const uint8_t *apChr) {
  return (uint16_t)((((uint32_t)apChr[0]) << 8) | (((uint32_t)apChr[1])));
}

/*@
  assigns \nothing;
*/
void *memcpy(void *dest, const void *src, size_t n);

/*@
    requires \valid(pucByte + (0 .. uxLength - 1));
    
	assigns \nothing;

	ensures 0 <= \result <= uxLength;
*/
static size_t prvSkipNameField(const uint8_t *pucByte, size_t uxLength) {
  size_t uxChunkLength;
  size_t uxSourceLenCpy = uxLength;
  size_t uxIndex = 0U;

  if (uxSourceLenCpy == 0U) {
    uxIndex = 0U;
  }
  /* Determine if the name is the fully coded name, or an offset to the name
  elsewhere in the message. */
  else if ((pucByte[uxIndex] & dnsNAME_IS_OFFSET) == dnsNAME_IS_OFFSET) {
    /* Jump over the two byte offset. */
    if (uxSourceLenCpy > sizeof(uint16_t)) {
      uxIndex += sizeof(uint16_t);
    } else {
      uxIndex = 0U;
    }
  } else {
    /* pucByte points to the full name. Walk over the string. */
    /*@
                    loop invariant uxIndex + uxSourceLenCpy == uxLength;
                    loop invariant 0 <= uxIndex < uxLength;
        loop assigns uxChunkLength, uxSourceLenCpy, uxIndex;
        loop variant uxSourceLenCpy;
    */
    while ((pucByte[uxIndex] != 0U) && (uxSourceLenCpy > 1U)) {
      /* Conversion to size_t causes addition to be done
      in size_t */
      uxChunkLength = ((size_t)pucByte[uxIndex]) + 1U;

      if (uxSourceLenCpy > uxChunkLength) {
        uxSourceLenCpy -= uxChunkLength;
        uxIndex += uxChunkLength;
      } else {
        uxIndex = 0U;
        break;
      }
    }

    /* Confirm that a fully formed name was found. */
    if (uxIndex > 0U) {
      if (pucByte[uxIndex] == 0U) {
        uxIndex++;
      } else {
        uxIndex = 0U;
      }
    }
  }

  return uxIndex;
}

/*@
    requires \valid(pucByte + (0 .. uxRemainingBytes - 1));
    requires \valid(pcName + (0 .. uxDestLen - 1));

    assigns pcName[0 .. uxDestLen - 1];

    ensures 0 <= \result <= uxRemainingBytes;
*/
static size_t prvReadNameField(const uint8_t *pucByte, size_t uxRemainingBytes,
                               char *pcName, size_t uxDestLen) {
  size_t uxNameLen = 0U;
  size_t uxIndex = 0U;
  size_t uxSourceLen = uxRemainingBytes;

  /* uxCount gets the valus from pucByte and counts down to 0.
  No need to have a different type than that of pucByte */
  size_t uxCount;

  if (uxSourceLen == (size_t)0U) {
    /* Return 0 value in case of error. */
    uxIndex = 0U;
  }
  /* Determine if the name is the fully coded name, or an offset to the name
  elsewhere in the message. */
  else if ((pucByte[uxIndex] & dnsNAME_IS_OFFSET) == dnsNAME_IS_OFFSET) {
    /* Jump over the two byte offset. */
    if (uxSourceLen > sizeof(uint16_t)) {
      uxIndex += sizeof(uint16_t);
    } else {
      uxIndex = 0U;
    }
  } else {
    /* 'uxIndex' points to the full name. Walk over the string. */
    // loop variant uxSourceLen - uxIndex;
    /*@
         loop invariant 0 <= uxIndex <= uxSourceLen;
         loop invariant 0 <= uxNameLen <= uxDestLen;
         loop assigns pcName[0 .. uxDestLen - 1], uxNameLen, uxIndex, uxCount;
     */
    while ((uxIndex < uxSourceLen) && (pucByte[uxIndex] != (uint8_t)0x00U)) {
      /* If this is not the first time through the loop, then add a
      separator in the output. */
      if ((uxNameLen > 0U)) {
        if (uxNameLen >= uxDestLen) {
          uxIndex = 0U;
          /* coverity[break_stmt] : Break statement terminating the loop */
          break;
        }
        pcName[uxNameLen] = '.';
        uxNameLen++;
      }

      /* Process the first/next sub-string. */
      uxCount = (size_t)pucByte[uxIndex];
      uxIndex++;
      if ((uxIndex + uxCount) > uxSourceLen) {
        uxIndex = 0U;
        break;
      }

      /*@
          loop invariant 0 <= uxIndex <= uxSourceLen;
          loop invariant 0 <= uxNameLen <= uxDestLen;
          loop assigns pcName[0 .. uxDestLen - 1], uxNameLen, uxIndex, uxCount;
      */
      while ((uxCount-- != 0U) && (uxIndex < uxSourceLen)) {
        if (uxNameLen >= uxDestLen) {
          uxIndex = 0U;
          break;
          /* break out of inner loop here
          break out of outer loop at the test uxNameLen >= uxDestLen. */
        }
        pcName[uxNameLen] = (char)pucByte[uxIndex];
        uxNameLen++;
        uxIndex++;
      }
      // One of these two seems essential, but not both
      //@ assert \at(pcName, Pre) == \at(pcName, Here);
      //@ assert \at(pucByte, Pre) == \at(pucByte, Here);
    }

    /* Confirm that a fully formed name was found. */
    if (uxIndex > 0U) {
      if ((uxNameLen < uxDestLen) && (uxIndex < uxSourceLen) &&
          (pucByte[uxIndex] == 0U)) {
        pcName[uxNameLen] = '\0';
        uxIndex++;
      } else {
        uxIndex = 0U;
      }
    }
  }

  return uxIndex;
}

/*@
        assigns \nothing;
*/
static BaseType_t prvProcessDNSCache(const char *pcName, uint32_t *pulIP,
                                     uint32_t ulTTL, BaseType_t xLookUp);

/*@
  requires \valid(buffer + (0 .. offset + 1));
  assigns \nothing;
*/
static uint16_t getUint16(uint8_t *buffer, size_t offset) {
    return (uint16_t)(*(buffer + offset) * 2^8 +  *(buffer + offset + 1));
}

/*@
  requires \valid(buffer + (0 .. offset + 3));
  assigns \nothing;
  // ensures is_uint32_t(\result);
*/
static uint32_t getUint32(uint8_t *buffer, size_t offset) {
    return (uint32_t)(*(buffer + offset) * 2^24 +  *(buffer + offset + 1) * 2^16 +  *(buffer + offset + 2) * 2^8 +  *(buffer + offset + 3));  
}

/*@
  requires \valid(buffer + (0 .. 1));
  assigns \nothing;
  ensures is_uint16_t(\result);
*/
static uint16_t getUsIdentifier(uint8_t *buffer) {
  size_t offset = offsetof(struct xDNSMessage, usIdentifier);
  return getUint16(buffer, offset);
}

/*@
  requires \valid(buffer + (0 .. 3));
  assigns \nothing;
  ensures is_uint16_t(\result);
*/
static uint16_t getUsFlags(uint8_t *buffer) {
  size_t offset = offsetof(struct xDNSMessage, usFlags);
  return getUint16(buffer, offset);
}

/*@
  requires \valid(buffer + (0 .. 5));
  assigns \nothing;
  ensures is_uint16_t(\result);
*/
static uint16_t getUsQuestions(uint8_t *buffer) {
  size_t offset = offsetof(struct xDNSMessage, usQuestions);
  return getUint16(buffer, offset);
}

/*@
  requires \valid(buffer + (0 .. 7));
  assigns \nothing;
  ensures is_uint16_t(\result);
*/
static uint16_t getUsAnswers(uint8_t *buffer) {
  size_t offset = offsetof(struct xDNSMessage, usAnswers);
  return getUint16(buffer, offset);
}

/*@
  requires \valid(buffer + (0 .. 7));
  assigns \nothing;
  ensures is_uint32_t(\result);
*/
static uint32_t getUlTTL(uint8_t *buffer) {
  size_t offset = offsetof(struct xDNSAnswerRecord, ulTTL);
  return getUint32(buffer, offset);
}

/*@
  requires \valid(buffer + (0 .. 9));
  assigns \nothing;
  ensures is_uint16_t(\result);
*/
static uint16_t getUsDataLength(uint8_t *buffer) {
  size_t offset = offsetof(struct xDNSAnswerRecord, usDataLength);
  return getUint16(buffer, offset);
}

/*@
  requires \valid(pucUDPPayloadBuffer + (0 .. uxBufferLength - 1));
  requires \forall size_t i; 0 <= i < uxBufferLength ==> is_uint8_t(*(pucUDPPayloadBuffer + i));
  requires \forall size_t i; 0 <= i < uxBufferLength ==> is_uint16_t(*(pucUDPPayloadBuffer + i) * 2^8);
  requires \forall size_t i; 0 <= i < uxBufferLength ==> is_uint32_t(*(pucUDPPayloadBuffer + i) * 2^24);

  assigns \nothing;

  ensures is_uint32_t(\result);
*/
static uint32_t prvParseDNSReply(uint8_t *pucUDPPayloadBuffer,
                                 size_t uxBufferLength, BaseType_t xExpected) {
  uint32_t ulIPAddress = 0UL;
  uint8_t *pucByte;
  size_t uxSourceBytesRemaining;
  uint16_t x, usDataLength, usQuestions, usAnswers, usFlags, usIdentifier;
  uint16_t usType = 0U;
  BaseType_t xDoStore = xExpected;
  char pcName[ipconfigDNS_CACHE_NAME_LENGTH] = "";

  /* Ensure that the buffer is of at least minimal DNS message length. */
  // changed the following line (from < to <=):
  if (uxBufferLength <= sizeof(DNSMessage_t)) {
    return dnsPARSE_ERROR;
  }

  uxSourceBytesRemaining = uxBufferLength;

  /* Parse the DNS message header.
  MISRA c 2012 rule 11.3 relaxed to make byte by byte traversal easier */
  usIdentifier = getUsIdentifier(pucUDPPayloadBuffer);
  usFlags = getUsFlags(pucUDPPayloadBuffer);
  usQuestions = getUsQuestions(pucUDPPayloadBuffer);
  usAnswers = getUsAnswers(pucUDPPayloadBuffer);

  /* Introduce a do {} while (0) to allow the use of breaks. */
  // loop contract
  /*
          loop invariant uxSourceBytesRemaining <= uxBufferLength;
  */
  // do
  // {
  size_t uxBytesRead = 0U;
  size_t uxResult;

  /* Start at the first byte after the header. */
  pucByte = &(pucUDPPayloadBuffer[sizeof(DNSMessage_t)]);
  //@assert  pucByte == &(pucUDPPayloadBuffer[sizeof(DNSMessage_t)]);
  //@assert in_range(pucByte, pucUDPPayloadBuffer, uxBufferLength);
  uxSourceBytesRemaining -= sizeof(DNSMessage_t);
  // assert \valid(pucByte + (0 .. uxSourceBytesRemaining));

//valid up to here

// first for loop reads the first question and then skips all the next questions (each question is a name followed by 2 uint16_t's i.e. uint32_t)
  /*@
    loop assigns uxResult, x, pcName[0 .. sizeof(pcName) - 1], pucByte, uxBytesRead, uxSourceBytesRemaining, uxResult;
    loop invariant 0 <= x <= usQuestions;
    loop invariant \valid(pucUDPPayloadBuffer + (0 .. uxBufferLength));
    loop invariant uxSourceBytesRemaining <= uxBufferLength;
    loop invariant pucUDPPayloadBuffer - pucByte <= uxSourceBytesRemaining;
    loop invariant \valid(pucByte + (0 .. uxSourceBytesRemaining));
    // loop invariant in_range(pucByte, pucUDPPayloadBuffer, uxBufferLength);
    loop variant usQuestions - x;
  */
  for (x = 0U; x < usQuestions; x++) {
    //@ assert \at(pucUDPPayloadBuffer, Pre) == \at(pucUDPPayloadBuffer, Here);
    //@ assert \at(uxBufferLength, Pre) == \at(uxBufferLength, Here);
    if (x == 0U) {
      //@ assert \valid(pcName + (0 .. sizeof(pcName) - 1));
      //@ assert \valid(pucByte + (0 .. uxSourceBytesRemaining));
      uxResult = prvReadNameField(pucByte, uxSourceBytesRemaining, pcName,
                                  sizeof(pcName));

      //@assert uxResult <= uxSourceBytesRemaining;
      //@assert uxResult <= uxBufferLength;     
      /* Check for a malformed response. */
      if (uxResult == 0U) {
        return dnsPARSE_ERROR;
      }
      uxBytesRead += uxResult;
      // @assert in_range(pucByte, pucUDPPayloadBuffer, uxBufferLength);
      // @assert in_range(&(pucByte[uxResult]), pucUDPPayloadBuffer, uxBufferLength);
      pucByte = &(pucByte[uxResult]);
      // @assert in_range(pucByte, pucUDPPayloadBuffer, uxBufferLength);
      uxSourceBytesRemaining -= uxResult;
      // @assert pucUDPPayloadBuffer - pucByte == uxSourceBytesRemaining;

    } else
    {
      /* Skip the variable length pcName field. */
      uxResult = prvSkipNameField(pucByte, uxSourceBytesRemaining);

      /* Check for a malformed response. */
      if (uxResult == 0U) {
        return dnsPARSE_ERROR;
      }
      uxBytesRead += uxResult;
      pucByte = &(pucByte[uxResult]);
      uxSourceBytesRemaining -= uxResult;
    }

    /* Check the remaining buffer size. */
    // @assert in_range(pucByte, pucUDPPayloadBuffer, uxBufferLength);
    if (uxSourceBytesRemaining >= sizeof(uint32_t)) {
      /* Skip the type and class fields. */
      pucByte = &(pucByte[sizeof(uint32_t)]);
      uxSourceBytesRemaining -= sizeof(uint32_t);

    } else {
      return dnsPARSE_ERROR;
    }
    // @assert in_range(pucByte, pucUDPPayloadBuffer, uxBufferLength);
  }



  return ulIPAddress;
}