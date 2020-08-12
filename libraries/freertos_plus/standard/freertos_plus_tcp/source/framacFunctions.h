#ifndef FRAMAC_FUNCTIONS_H
#define FRAMAC_FUNCTIONS_H

/* Standard includes. */
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stddef.h>

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

/*@
    assigns \nothing;
*/
void *memcpy(void *dest, const void *src, size_t n);

/*@
    requires \valid(pucByte + (0 .. uxLength - 1));
    assigns \nothing;
    ensures 0 <= \result <= uxLength;
*/
static size_t prvSkipNameField(const uint8_t *pucByte, size_t uxLength);

/*@
    requires \valid(pucByte + (0 .. uxRemainingBytes - 1));
    requires \valid(pcName + (0 .. uxDestLen - 1));
    assigns pcName[0 .. uxDestLen - 1];
    ensures 0 <= \result <= uxRemainingBytes;
*/
static size_t prvReadNameField(const uint8_t *pucByte, size_t uxRemainingBytes,
                               char *pcName, size_t uxDestLen);
/*@
    assigns \nothing;
*/
static BaseType_t prvProcessDNSCache(const char *pcName, uint32_t *pulIP,
                                     uint32_t ulTTL, BaseType_t xLookUp);

/*@
    requires \valid(buffer + (offset .. offset + 1));
    assigns \nothing;
*/
static uint16_t getUint16(uint8_t *buffer, size_t offset);

/*@
    requires \valid(buffer + (offset .. offset + 3));
    assigns \nothing;
*/
static uint32_t getUint32(uint8_t *buffer, size_t offset);

/*@
    requires \valid(buffer + (0 .. 1));
    assigns \nothing;
    ensures is_uint16_t(\result);
*/
static uint16_t getUsIdentifier(uint8_t *buffer);

/*@
    requires \valid(buffer + (0 .. 3));
    assigns \nothing;
    ensures is_uint16_t(\result);
*/
static uint16_t getUsFlags(uint8_t *buffer);

/*@
    requires \valid(buffer + (0 .. 5));
    assigns \nothing;
    ensures is_uint16_t(\result);
*/
static uint16_t getUsQuestions(uint8_t *buffer);

/*@
    requires \valid(buffer + (0 .. 7));
    assigns \nothing;
    ensures is_uint16_t(\result);
*/
static uint16_t getUsAnswers(uint8_t *buffer);

/*@
    requires \valid(buffer + (0 .. 7));
    assigns \nothing;
    ensures is_uint32_t(\result);
*/
static uint32_t getUlTTL(uint8_t *buffer);

/*@
    requires \valid(buffer + (0 .. 9));
    assigns \nothing;
    ensures is_uint16_t(\result);
*/
static uint16_t getUsDataLength(uint8_t *buffer);

/*@
    requires \valid(pucUDPPayloadBuffer + (0 .. uxBufferLength - 1));
    assigns \nothing;
    ensures is_uint32_t(\result);
*/
static uint32_t prvParseDNSReply(uint8_t *pucUDPPayloadBuffer, 
                                size_t uxBufferLength, BaseType_t xExpected);

#endif