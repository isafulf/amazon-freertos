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
#define ipconfigUSE_LLMNR 0

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
*/

/*@
  requires \valid(apChr + (0 .. 1));
  assigns \nothing;
  ensures is_uint16_t(\result);
*/
static uint16_t usChar2u16(const uint8_t *apChr);
static uint16_t usChar2u16(const uint8_t *apChr) {
  return apChr[0] * 256 + apChr[1];
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
  requires \valid(buffer + (offset .. offset + 1));
  assigns \nothing;
*/
static uint16_t getUint16(uint8_t *buffer, size_t offset) {
    return (uint16_t)(*(buffer + offset) * 2^16 +  *(buffer + offset + 1));
}

/*@
  requires \valid(buffer + (offset .. offset + 3));
  assigns \nothing;
*/
static uint32_t getUint32(uint8_t *buffer, size_t offset) {
    return (uint32_t)(*(buffer + offset) * 2^24 +  *(buffer + offset + 1) * 2^16 +  *(buffer + offset + 2) * 2 ^ 8 +  *(buffer + offset + 3));
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
  assigns \nothing;
  ensures is_uint32_t(\result);
*/
static uint32_t prvParseDNSReply(uint8_t *pucUDPPayloadBuffer,
                                 size_t uxBufferLength, BaseType_t xExpected) {
  uint32_t ulIPAddress = 0UL;
#if (ipconfigUSE_LLMNR == 1)
  char *pcRequestedName = NULL;
#endif
  uint8_t *pucByte;
  size_t uxSourceBytesRemaining;
  uint16_t x, usDataLength, usQuestions, usAnswers, usFlags, usIdentifier;
  uint16_t usType = 0U;
#if (ipconfigUSE_LLMNR == 1)
  uint16_t usClass = 0U;
#endif
#if (ipconfigUSE_DNS_CACHE == 1) || (ipconfigDNS_USE_CALLBACKS == 1)
  BaseType_t xDoStore = xExpected;
  char pcName[ipconfigDNS_CACHE_NAME_LENGTH] = "";
#endif

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

  // pucByte = &(pucUDPPayloadBuffer[sizeof(DNSMessage_t)]);
  // uxSourceBytesRemaining -= sizeof(DNSMessage_t);

  /* Introduce a do {} while (0) to allow the use of breaks. */
  /*@
    loop assigns \nothing;
    loop invariant sizeof(DNSMessage_t) <= uxSourceBytesRemaining <= uxBufferLength;
  */
  do
  {
  size_t uxBytesRead = 0U;
  size_t uxResult;

  /* Start at the first byte after the header. */
  pucByte = &(pucUDPPayloadBuffer[sizeof(DNSMessage_t)]);
  uxSourceBytesRemaining -= sizeof(DNSMessage_t);

/*@
  loop assigns uxResult;
  loop assigns x;
  loop assigns pcName[0 .. sizeof(pcName) - 1];
  loop assigns pucByte;
  loop assigns uxBytesRead;
  loop assigns uxSourceBytesRemaining;
  loop assigns uxResult;
  loop invariant \valid(pucByte + (0 .. uxSourceBytesRemaining - 1));
  loop variant usQuestions - x;
*/
  for (x = 0U; x < usQuestions; x++) {
#if (ipconfigUSE_LLMNR == 1)
    {
      if (x == 0U) {
        pcRequestedName = (char *)pucByte;
      }
    }
#endif

#if (ipconfigUSE_DNS_CACHE == 1) || (ipconfigDNS_USE_CALLBACKS == 1)
    if (x == 0U) {
      uxResult = prvReadNameField(pucByte, uxSourceBytesRemaining, pcName,
                                  sizeof(pcName));

      /* Check for a malformed response. */
      if (uxResult == 0U) {
        return dnsPARSE_ERROR;
      }
      uxBytesRead += uxResult;
      pucByte = &(pucByte[uxResult]);
      uxSourceBytesRemaining -= uxResult;

    } else
#endif /* ipconfigUSE_DNS_CACHE || ipconfigDNS_USE_CALLBACKS */
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
    if (uxSourceBytesRemaining >= sizeof(uint32_t)) {
#if (ipconfigUSE_LLMNR == 1)
      {
        /* usChar2u16 returns value in host endianness. */
        usType = usChar2u16(pucByte);
        usClass = usChar2u16(&(pucByte[2]));
      }
#endif /* ipconfigUSE_LLMNR */

      /* Skip the type and class fields. */
      pucByte = &(pucByte[sizeof(uint32_t)]);
      uxSourceBytesRemaining -= sizeof(uint32_t);

    } else {
      return dnsPARSE_ERROR;
    }
  }

  if ((usFlags & dnsRX_FLAGS_MASK) ==
      dnsEXPECTED_RX_FLAGS) {
    const uint16_t usCount = (uint16_t)ipconfigDNS_CACHE_ADDRESSES_PER_ENTRY;

    /*@
      loop assigns ulIPAddress;
      loop assigns pucByte;
      loop assigns uxSourceBytesRemaining;
      loop assigns usQuestions;
      loop assigns usType;
      loop assigns xDoStore;
      loop assigns uxBytesRead;
      loop assigns uxResult;
      loop assigns usDataLength;
      loop assigns x;
      loop invariant \valid(pucByte + (0 .. uxSourceBytesRemaining - 1));
      loop variant usAnswers - x;
    */
    for (x = 0U; (x < usAnswers) && (x < usCount); x++) {
      BaseType_t xDoAccept;

      uxResult = prvSkipNameField(pucByte, uxSourceBytesRemaining);

      /* Check for a malformed response. */
      if (uxResult == 0U) {
        return dnsPARSE_ERROR;
      }

      uxBytesRead += uxResult;
      pucByte = &(pucByte[uxResult]);
      uxSourceBytesRemaining -= uxResult;

      /* Is there enough data for an IPv4 A record answer and, if so,
      is this an A record? */
      if (uxSourceBytesRemaining < sizeof(uint16_t)) {
        return dnsPARSE_ERROR;
      }
      usType = usChar2u16(pucByte);

      if (usType == (uint16_t)dnsTYPE_A_HOST) {
        if (uxSourceBytesRemaining >=
            (sizeof(DNSAnswerRecord_t) + ipSIZE_OF_IPv4_ADDRESS)) {
          xDoAccept = pdTRUE;
        } else {
          xDoAccept = pdFALSE;
        }
      } else {
        /* Unknown host type. */
        xDoAccept = pdFALSE;
      }
      if (xDoAccept != pdFALSE) {
        /* This is the required record type and is of sufficient size. */
        /* MISRA c 2012 rule 11.3 relaxed. pucByte is used for byte-by-byte
        traversal. */
        uint32_t ulTTL = getUlTTL(pucByte);
        uint16_t usDatalength = getUsDataLength(pucByte);

        /* Sanity check the data length of an IPv4 answer. */
        if (usDataLength ==
            (uint16_t)sizeof(uint32_t)) {
          /* Copy the IP address out of the record. */
          /* MISRA c 2012 rule 21.15 relaxed here since this seems
          to be the least cumbersome way to get the IP address
          from the record. */
          (void)memcpy(&(ulIPAddress), &(pucByte[sizeof(DNSAnswerRecord_t)]),
                       sizeof(uint32_t));

#if (ipconfigDNS_USE_CALLBACKS == 1)
          {
            /* See if any asynchronous call was made to
             * FreeRTOS_gethostbyname_a() */
            if (xDNSDoCallback((TickType_t)usIdentifier,
                               pcName, ulIPAddress) != pdFALSE) {
              /* This device has requested this DNS look-up.
              The result may be stored in the DNS cache. */
              xDoStore = pdTRUE;
            }
          }
#endif /* ipconfigDNS_USE_CALLBACKS == 1 */
#if (ipconfigUSE_DNS_CACHE == 1)
          {
            /* The reply will only be stored in the DNS cache when the
            request was issued by this device. */
            if (xDoStore != pdFALSE) {
              (void)prvProcessDNSCache(pcName, &ulIPAddress,
                                       ulTTL, pdFALSE);
            }

            /* Show what has happened. */
	    //@ loop assigns \nothing;
            FreeRTOS_printf(
                ("DNS[0x%04lX]: The answer to '%s' (%lxip) will%s be stored\n",
                 (UBaseType_t)usIdentifier, pcName,
                 (UBaseType_t)FreeRTOS_ntohl(ulIPAddress),
                 (xDoStore != 0) ? "" : " NOT"));
          }
#endif /* ipconfigUSE_DNS_CACHE */
        }

        pucByte = &(pucByte[sizeof(DNSAnswerRecord_t) + sizeof(uint32_t)]);
        uxSourceBytesRemaining -=
            (sizeof(DNSAnswerRecord_t) + sizeof(uint32_t));
      } else if (uxSourceBytesRemaining >= sizeof(DNSAnswerRecord_t)) {
        /* It's not an A record, so skip it. Get the header location
        and then jump over the header. */

        /* MISRA c 2012 rule 11.3 relaxed as pucByte is being used in
        various places to point to various parts of the DNS records */
        usDataLength = getUsDataLength(pucByte);

        pucByte = &(pucByte[sizeof(DNSAnswerRecord_t)]);
        uxSourceBytesRemaining -= sizeof(DNSAnswerRecord_t);

        /* Determine the length of the answer data from the header. */

        /* Jump over the answer. */
        if (uxSourceBytesRemaining >= usDataLength) {
          pucByte = &(pucByte[usDataLength]);
          uxSourceBytesRemaining -= usDataLength;
        } else {
          /* Malformed response. */
          return dnsPARSE_ERROR;
        }
      } else {
        /* Do nothing */
      }
    }
  }

#if (ipconfigUSE_LLMNR == 1)
  else if ((usQuestions != (uint16_t)0U) && (usType == dnsTYPE_A_HOST) &&
           (usClass == dnsCLASS_IN) && (pcRequestedName != NULL)) {
    /* If this is not a reply to our DNS request, it might an LLMNR
    request. */
    if (xApplicationDNSQueryHook(&(pcRequestedName[1])) != pdFALSE) {
      int16_t usLength;
      NetworkBufferDescriptor_t *pxNewBuffer = NULL;
      NetworkBufferDescriptor_t *pxNetworkBuffer =
          pxUDPPayloadBuffer_to_NetworkBuffer(pucUDPPayloadBuffer);
      LLMNRAnswer_t *pxAnswer;
      uint8_t *pucNewBuffer = NULL;

      if ((xBufferAllocFixedSize == pdFALSE) && (pxNetworkBuffer != NULL)) {
        size_t uxDataLength = uxBufferLength + sizeof(UDPHeader_t) +
                              sizeof(EthernetHeader_t) + sizeof(IPHeader_t);

        /* Set the size of the outgoing packet. */
        pxNetworkBuffer->xDataLength = uxDataLength;
        pxNewBuffer = pxDuplicateNetworkBufferWithDescriptor(
            pxNetworkBuffer, uxDataLength + sizeof(LLMNRAnswer_t));

        if (pxNewBuffer != NULL) {
          BaseType_t xOffset1, xOffset2;

          xOffset1 = (BaseType_t)(pucByte - pucUDPPayloadBuffer);
          xOffset2 =
              (BaseType_t)(((uint8_t *)pcRequestedName) - pucUDPPayloadBuffer);

          pxNetworkBuffer = pxNewBuffer;
          pucNewBuffer =
              &(pxNetworkBuffer->pucEthernetBuffer[ipUDP_PAYLOAD_OFFSET_IPv4]);

          pucByte = &(pucNewBuffer[xOffset1]);
          pcRequestedName = (char *)&(pucNewBuffer[xOffset2]);
          pxDNSMessageHeader = ipPOINTER_CAST(DNSMessage_t *, pucNewBuffer);
        } else {
          /* Just to indicate that the message may not be answered. */
          pxNetworkBuffer = NULL;
        }
      }

      /* The test on 'pucNewBuffer' is only to satisfy lint. */
      if ((pxNetworkBuffer != NULL) && (pucNewBuffer != NULL)) {
        pxAnswer = ipPOINTER_CAST(LLMNRAnswer_t *, pucByte);

/* We leave 'usIdentifier' and 'usQuestions' untouched */
#ifndef _lint
        vSetField16(pxDNSMessageHeader, DNSMessage_t, usFlags,
                    dnsLLMNR_FLAGS_IS_REPONSE); /* Set the response flag */
        vSetField16(pxDNSMessageHeader, DNSMessage_t, usAnswers,
                    1); /* Provide a single answer */
        vSetField16(pxDNSMessageHeader, DNSMessage_t, usAuthorityRRs,
                    0); /* No authority */
        vSetField16(pxDNSMessageHeader, DNSMessage_t, usAdditionalRRs,
                    0); /* No additional info */
#endif                  /* lint */

        pxAnswer->ucNameCode = dnsNAME_IS_OFFSET;
        pxAnswer->ucNameOffset =
            (uint8_t)(pcRequestedName - (char *)pucNewBuffer);

#ifndef _lint
        vSetField16(pxAnswer, LLMNRAnswer_t, usType,
                    dnsTYPE_A_HOST); /* Type A: host */
        vSetField16(pxAnswer, LLMNRAnswer_t, usClass,
                    dnsCLASS_IN); /* 1: Class IN */
        vSetField32(pxAnswer, LLMNRAnswer_t, ulTTL, dnsLLMNR_TTL_VALUE);
        vSetField16(pxAnswer, LLMNRAnswer_t, usDataLength, 4);
        vSetField32(pxAnswer, LLMNRAnswer_t, ulIPAddress,
                    FreeRTOS_ntohl(*ipLOCAL_IP_ADDRESS_POINTER));
#endif /* lint */
        usLength =
            (int16_t)(sizeof(*pxAnswer) + (size_t)(pucByte - pucNewBuffer));

        prvReplyDNSMessage(pxNetworkBuffer, usLength);

        if (pxNewBuffer != NULL) {
          vReleaseNetworkBufferAndDescriptor(pxNewBuffer);
        }
      }
    }
  } else {
    /* Not an expected reply. */
  }
#endif /* ipconfigUSE_LLMNR == 1 */
  (void)uxBytesRead;
  } while( ipFALSE_BOOL );

  if (xExpected == pdFALSE) {
    /* Do not return a valid IP-address in case the reply was not expected. */
    ulIPAddress = 0UL;
  }
#if (ipconfigUSE_DNS_CACHE == 1) || (ipconfigDNS_USE_CALLBACKS == 1)
  (void)xDoStore;
#endif

  return ulIPAddress;
}
