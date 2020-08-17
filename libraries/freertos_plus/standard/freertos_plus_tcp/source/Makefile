FREERTOS=$(abspath ../../../../..)

DEFINES = \
	-Dfreertos_EXPORTS \

INCLUDES = \
	-I. \
	-I/usr/include \
	-I/usr/include/x86_64-linux-gnu \
	-I$(FREERTOS)/tools/framac \
	-I$(FREERTOS)/freertos_kernel/include \
	-I$(FREERTOS)/freertos_kernel/portable/MSVC-MingW \
	-I$(FREERTOS)/freertos_kernel/portable/ARMv8M/non_secure/GCC/ARM_CM23 \
	-I$(FREERTOS)/vendors/pc/boards/windows/aws_demos/config_files \
	-I$(FREERTOS)/vendors/pc/boards/windows/aws_demos/application_code \
	-I$(FREERTOS)/demos/include \
	-I$(FREERTOS)/demos/network_manager \
	-I$(FREERTOS)/libraries/c_sdk/standard/common/include/private \
	-I$(FREERTOS)/libraries/c_sdk/standard/common/include \
	-I$(FREERTOS)/libraries/abstractions/platform/include \
	-I$(FREERTOS)/libraries/abstractions/platform/freertos/include \
	-I$(FREERTOS)/libraries/abstractions/secure_sockets/include \
	-I$(FREERTOS)/libraries/freertos_plus/standard/freertos_plus_tcp/test \
	-I$(FREERTOS)/libraries/freertos_plus/standard/freertos_plus_tcp/include \
	-I$(FREERTOS)/libraries/freertos_plus/standard/freertos_plus_tcp/source/portable/Compiler/MSVC \
	-I$(FREERTOS)/libraries/freertos_plus/standard/tls/include \
	-I$(FREERTOS)/libraries/freertos_plus/standard/crypto/include \
	-I$(FREERTOS)/libraries/freertos_plus/standard/pkcs11/include \
	-I$(FREERTOS)/libraries/abstractions/pkcs11/include \
	-I$(FREERTOS)/libraries/freertos_plus/standard/utils/include \
	-I$(FREERTOS)/demos/dev_mode_key_provisioning/include \
	-I$(FREERTOS)/libraries/c_sdk/aws/defender/include \
	-I$(FREERTOS)/libraries/c_sdk/standard/mqtt/include \
	-I$(FREERTOS)/libraries/c_sdk/standard/serializer/include \
	-I$(FREERTOS)/libraries/c_sdk/aws/shadow/include \
	-I$(FREERTOS)/libraries/c_sdk/standard/https/include \
	-I$(FREERTOS)/libraries/freertos_plus/aws/greengrass/include \
	-I$(FREERTOS)/libraries/freertos_plus/aws/ota/src \
	-I$(FREERTOS)/libraries/freertos_plus/aws/ota/include \
	-I$(FREERTOS)/libraries/3rdparty/mbedtls/include \
	-I$(FREERTOS)/libraries/abstractions/posix/include \
	-I$(FREERTOS)/vendors/pc/boards/windows/ports/posix \
	-I$(FREERTOS)/libraries/freertos_plus/standard/freertos_plus_posix/include \
	-I$(FREERTOS)/libraries/3rdparty/tracealyzer_recorder/Include \
	-I$(FREERTOS)/libraries/3rdparty/win_pcap \
	-I$(FREERTOS)/libraries/3rdparty/pkcs11 \
	-I$(FREERTOS)/libraries/abstractions/pkcs11/mbedtls \
	-I$(FREERTOS)/libraries/3rdparty/mbedtls/include/mbedtls \
	-I$(FREERTOS)/libraries/3rdparty/mbedtls_utils \
	-I$(FREERTOS)/libraries/3rdparty/mbedtls_config \
	-I$(FREERTOS)/libraries/3rdparty/tinycbor \
	-I$(FREERTOS)/libraries/3rdparty/http_parser \
	-I$(FREERTOS)/libraries/3rdparty/jsmn \
	-I$(FREERTOS)/tools/cbmc/include \
	-I$(FREERTOS)/tools/cbmc/windows \
	-I$(FREERTOS)/tools/cbmc/windows2 \

CFLAGS = \
	-fPIC \
	-std=gnu90 \

FRAMAC = \
	-cpp-extra-args="$(DEFINES) $(INCLUDES) $(CFLAGS)" \

default:
	frama-c -wp-fct=prvParseDNSReply,prvReadNameField,prvSkipNameField -rte -wp-timeout 10 $(FRAMAC) FreeRTOS_DNS.c -then -report 
