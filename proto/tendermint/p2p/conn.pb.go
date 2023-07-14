// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: tendermint/p2p/conn.proto

package p2p

import (
	fmt "fmt"
	crypto "github.com/cometbft/cometbft/proto/tendermint/crypto"
	_ "github.com/cosmos/gogoproto/gogoproto"
	proto "github.com/cosmos/gogoproto/proto"
	io "io"
	math "math"
	math_bits "math/bits"
)

// Reference imports to suppress errors if they are not otherwise used.
var _ = proto.Marshal
var _ = fmt.Errorf
var _ = math.Inf

// This is a compile-time assertion to ensure that this generated file
// is compatible with the proto package it is being compiled against.
// A compilation error at this line likely means your copy of the
// proto package needs to be updated.
const _ = proto.GoGoProtoPackageIsVersion3 // please upgrade the proto package

type PacketPing struct {
}

func (m *PacketPing) Reset()         { *m = PacketPing{} }
func (m *PacketPing) String() string { return proto.CompactTextString(m) }
func (*PacketPing) ProtoMessage()    {}
func (*PacketPing) Descriptor() ([]byte, []int) {
	return fileDescriptor_22474b5527c8fa9f, []int{0}
}
func (m *PacketPing) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *PacketPing) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_PacketPing.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *PacketPing) XXX_Merge(src proto.Message) {
	xxx_messageInfo_PacketPing.Merge(m, src)
}
func (m *PacketPing) XXX_Size() int {
	return m.Size()
}
func (m *PacketPing) XXX_DiscardUnknown() {
	xxx_messageInfo_PacketPing.DiscardUnknown(m)
}

var xxx_messageInfo_PacketPing proto.InternalMessageInfo

type PacketPong struct {
}

func (m *PacketPong) Reset()         { *m = PacketPong{} }
func (m *PacketPong) String() string { return proto.CompactTextString(m) }
func (*PacketPong) ProtoMessage()    {}
func (*PacketPong) Descriptor() ([]byte, []int) {
	return fileDescriptor_22474b5527c8fa9f, []int{1}
}
func (m *PacketPong) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *PacketPong) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_PacketPong.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *PacketPong) XXX_Merge(src proto.Message) {
	xxx_messageInfo_PacketPong.Merge(m, src)
}
func (m *PacketPong) XXX_Size() int {
	return m.Size()
}
func (m *PacketPong) XXX_DiscardUnknown() {
	xxx_messageInfo_PacketPong.DiscardUnknown(m)
}

var xxx_messageInfo_PacketPong proto.InternalMessageInfo

type PacketMsg struct {
	ChannelID int32  `protobuf:"varint,1,opt,name=channel_id,json=channelId,proto3" json:"channel_id,omitempty"`
	EOF       bool   `protobuf:"varint,2,opt,name=eof,proto3" json:"eof,omitempty"`
	Data      []byte `protobuf:"bytes,3,opt,name=data,proto3" json:"data,omitempty"`
}

func (m *PacketMsg) Reset()         { *m = PacketMsg{} }
func (m *PacketMsg) String() string { return proto.CompactTextString(m) }
func (*PacketMsg) ProtoMessage()    {}
func (*PacketMsg) Descriptor() ([]byte, []int) {
	return fileDescriptor_22474b5527c8fa9f, []int{2}
}
func (m *PacketMsg) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *PacketMsg) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_PacketMsg.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *PacketMsg) XXX_Merge(src proto.Message) {
	xxx_messageInfo_PacketMsg.Merge(m, src)
}
func (m *PacketMsg) XXX_Size() int {
	return m.Size()
}
func (m *PacketMsg) XXX_DiscardUnknown() {
	xxx_messageInfo_PacketMsg.DiscardUnknown(m)
}

var xxx_messageInfo_PacketMsg proto.InternalMessageInfo

func (m *PacketMsg) GetChannelID() int32 {
	if m != nil {
		return m.ChannelID
	}
	return 0
}

func (m *PacketMsg) GetEOF() bool {
	if m != nil {
		return m.EOF
	}
	return false
}

func (m *PacketMsg) GetData() []byte {
	if m != nil {
		return m.Data
	}
	return nil
}

type Packet struct {
	// Types that are valid to be assigned to Sum:
	//
	//	*Packet_PacketPing
	//	*Packet_PacketPong
	//	*Packet_PacketMsg
	Sum isPacket_Sum `protobuf_oneof:"sum"`
}

func (m *Packet) Reset()         { *m = Packet{} }
func (m *Packet) String() string { return proto.CompactTextString(m) }
func (*Packet) ProtoMessage()    {}
func (*Packet) Descriptor() ([]byte, []int) {
	return fileDescriptor_22474b5527c8fa9f, []int{3}
}
func (m *Packet) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *Packet) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_Packet.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *Packet) XXX_Merge(src proto.Message) {
	xxx_messageInfo_Packet.Merge(m, src)
}
func (m *Packet) XXX_Size() int {
	return m.Size()
}
func (m *Packet) XXX_DiscardUnknown() {
	xxx_messageInfo_Packet.DiscardUnknown(m)
}

var xxx_messageInfo_Packet proto.InternalMessageInfo

type isPacket_Sum interface {
	isPacket_Sum()
	MarshalTo([]byte) (int, error)
	Size() int
}

type Packet_PacketPing struct {
	PacketPing *PacketPing `protobuf:"bytes,1,opt,name=packet_ping,json=packetPing,proto3,oneof" json:"packet_ping,omitempty"`
}
type Packet_PacketPong struct {
	PacketPong *PacketPong `protobuf:"bytes,2,opt,name=packet_pong,json=packetPong,proto3,oneof" json:"packet_pong,omitempty"`
}
type Packet_PacketMsg struct {
	PacketMsg *PacketMsg `protobuf:"bytes,3,opt,name=packet_msg,json=packetMsg,proto3,oneof" json:"packet_msg,omitempty"`
}

func (*Packet_PacketPing) isPacket_Sum() {}
func (*Packet_PacketPong) isPacket_Sum() {}
func (*Packet_PacketMsg) isPacket_Sum()  {}

func (m *Packet) GetSum() isPacket_Sum {
	if m != nil {
		return m.Sum
	}
	return nil
}

func (m *Packet) GetPacketPing() *PacketPing {
	if x, ok := m.GetSum().(*Packet_PacketPing); ok {
		return x.PacketPing
	}
	return nil
}

func (m *Packet) GetPacketPong() *PacketPong {
	if x, ok := m.GetSum().(*Packet_PacketPong); ok {
		return x.PacketPong
	}
	return nil
}

func (m *Packet) GetPacketMsg() *PacketMsg {
	if x, ok := m.GetSum().(*Packet_PacketMsg); ok {
		return x.PacketMsg
	}
	return nil
}

// XXX_OneofWrappers is for the internal use of the proto package.
func (*Packet) XXX_OneofWrappers() []interface{} {
	return []interface{}{
		(*Packet_PacketPing)(nil),
		(*Packet_PacketPong)(nil),
		(*Packet_PacketMsg)(nil),
	}
}

type AuthSigMessage struct {
	PubKey crypto.PublicKey `protobuf:"bytes,1,opt,name=pub_key,json=pubKey,proto3" json:"pub_key"`
	Sig    []byte           `protobuf:"bytes,2,opt,name=sig,proto3" json:"sig,omitempty"`
	Nni    string           `protobuf:"bytes,3,opt,name=nni,proto3" json:"nni,omitempty"`
}

func (m *AuthSigMessage) Reset()         { *m = AuthSigMessage{} }
func (m *AuthSigMessage) String() string { return proto.CompactTextString(m) }
func (*AuthSigMessage) ProtoMessage()    {}
func (*AuthSigMessage) Descriptor() ([]byte, []int) {
	return fileDescriptor_22474b5527c8fa9f, []int{4}
}
func (m *AuthSigMessage) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *AuthSigMessage) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_AuthSigMessage.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *AuthSigMessage) XXX_Merge(src proto.Message) {
	xxx_messageInfo_AuthSigMessage.Merge(m, src)
}
func (m *AuthSigMessage) XXX_Size() int {
	return m.Size()
}
func (m *AuthSigMessage) XXX_DiscardUnknown() {
	xxx_messageInfo_AuthSigMessage.DiscardUnknown(m)
}

var xxx_messageInfo_AuthSigMessage proto.InternalMessageInfo

func (m *AuthSigMessage) GetPubKey() crypto.PublicKey {
	if m != nil {
		return m.PubKey
	}
	return crypto.PublicKey{}
}

func (m *AuthSigMessage) GetSig() []byte {
	if m != nil {
		return m.Sig
	}
	return nil
}

func (m *AuthSigMessage) GetNni() string {
	if m != nil {
		return m.Nni
	}
	return ""
}

type GatewayMasqueradeReq struct {
	RemSig        *AuthSigMessage `protobuf:"bytes,2,opt,name=rem_sig,json=remSig,proto3" json:"rem_sig,omitempty"`
	MasqChallenge []byte          `protobuf:"bytes,3,opt,name=masq_challenge,json=masqChallenge,proto3" json:"masq_challenge,omitempty"`
	Nni           string          `protobuf:"bytes,4,opt,name=nni,proto3" json:"nni,omitempty"`
}

func (m *GatewayMasqueradeReq) Reset()         { *m = GatewayMasqueradeReq{} }
func (m *GatewayMasqueradeReq) String() string { return proto.CompactTextString(m) }
func (*GatewayMasqueradeReq) ProtoMessage()    {}
func (*GatewayMasqueradeReq) Descriptor() ([]byte, []int) {
	return fileDescriptor_22474b5527c8fa9f, []int{5}
}
func (m *GatewayMasqueradeReq) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *GatewayMasqueradeReq) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_GatewayMasqueradeReq.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *GatewayMasqueradeReq) XXX_Merge(src proto.Message) {
	xxx_messageInfo_GatewayMasqueradeReq.Merge(m, src)
}
func (m *GatewayMasqueradeReq) XXX_Size() int {
	return m.Size()
}
func (m *GatewayMasqueradeReq) XXX_DiscardUnknown() {
	xxx_messageInfo_GatewayMasqueradeReq.DiscardUnknown(m)
}

var xxx_messageInfo_GatewayMasqueradeReq proto.InternalMessageInfo

func (m *GatewayMasqueradeReq) GetRemSig() *AuthSigMessage {
	if m != nil {
		return m.RemSig
	}
	return nil
}

func (m *GatewayMasqueradeReq) GetMasqChallenge() []byte {
	if m != nil {
		return m.MasqChallenge
	}
	return nil
}

func (m *GatewayMasqueradeReq) GetNni() string {
	if m != nil {
		return m.Nni
	}
	return ""
}

func init() {
	proto.RegisterType((*PacketPing)(nil), "tendermint.p2p.PacketPing")
	proto.RegisterType((*PacketPong)(nil), "tendermint.p2p.PacketPong")
	proto.RegisterType((*PacketMsg)(nil), "tendermint.p2p.PacketMsg")
	proto.RegisterType((*Packet)(nil), "tendermint.p2p.Packet")
	proto.RegisterType((*AuthSigMessage)(nil), "tendermint.p2p.AuthSigMessage")
	proto.RegisterType((*GatewayMasqueradeReq)(nil), "tendermint.p2p.GatewayMasqueradeReq")
}

func init() { proto.RegisterFile("tendermint/p2p/conn.proto", fileDescriptor_22474b5527c8fa9f) }

var fileDescriptor_22474b5527c8fa9f = []byte{
	// 476 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x74, 0x52, 0x4f, 0x8b, 0xda, 0x40,
	0x1c, 0x35, 0xd5, 0xd5, 0x3a, 0xba, 0x52, 0x86, 0x3d, 0xa8, 0x2c, 0x51, 0x84, 0x82, 0x87, 0x12,
	0xa9, 0x3d, 0x14, 0x5a, 0x7a, 0x68, 0xb6, 0xff, 0x16, 0x91, 0x4a, 0xf6, 0xd6, 0x4b, 0x98, 0x24,
	0xbf, 0x9d, 0x0c, 0x9a, 0x99, 0x31, 0x33, 0xa1, 0xe4, 0x1b, 0xf4, 0xd8, 0x8f, 0xb5, 0xbd, 0xed,
	0xb1, 0x27, 0x29, 0xf1, 0x8b, 0x94, 0x24, 0xba, 0x6a, 0xe9, 0xde, 0xde, 0x7b, 0xbf, 0x79, 0xbf,
	0x79, 0x8f, 0x19, 0xd4, 0xd3, 0xc0, 0x03, 0x88, 0x23, 0xc6, 0xf5, 0x44, 0x4e, 0xe5, 0xc4, 0x17,
	0x9c, 0x5b, 0x32, 0x16, 0x5a, 0xe0, 0xce, 0x61, 0x64, 0xc9, 0xa9, 0xec, 0x5f, 0x50, 0x41, 0x45,
	0x31, 0x9a, 0xe4, 0xa8, 0x3c, 0xd5, 0xbf, 0x3c, 0x5a, 0xe0, 0xc7, 0xa9, 0xd4, 0x62, 0xb2, 0x84,
	0x54, 0x95, 0xd3, 0x51, 0x1b, 0xa1, 0x05, 0xf1, 0x97, 0xa0, 0x17, 0x8c, 0xd3, 0x23, 0x26, 0x38,
	0x1d, 0x85, 0xa8, 0x59, 0xb2, 0xb9, 0xa2, 0xf8, 0x05, 0x42, 0x7e, 0x48, 0x38, 0x87, 0x95, 0xcb,
	0x82, 0xae, 0x31, 0x34, 0xc6, 0x67, 0xf6, 0x79, 0xb6, 0x19, 0x34, 0xaf, 0x4a, 0xf5, 0xfa, 0x83,
	0xd3, 0xdc, 0x1d, 0xb8, 0x0e, 0x70, 0x0f, 0x55, 0x41, 0xdc, 0x76, 0x9f, 0x0c, 0x8d, 0xf1, 0x53,
	0xbb, 0x91, 0x6d, 0x06, 0xd5, 0x8f, 0x5f, 0x3f, 0x39, 0xb9, 0x86, 0x31, 0xaa, 0x05, 0x44, 0x93,
	0x6e, 0x75, 0x68, 0x8c, 0xdb, 0x4e, 0x81, 0x47, 0xbf, 0x0c, 0x54, 0x2f, 0xaf, 0xc2, 0xef, 0x50,
	0x4b, 0x16, 0xc8, 0x95, 0x8c, 0xd3, 0xe2, 0xa2, 0xd6, 0xb4, 0x6f, 0x9d, 0x56, 0xb5, 0x0e, 0x99,
	0xbf, 0x54, 0x1c, 0x24, 0x1f, 0xd8, 0xb1, 0x5d, 0x70, 0x5a, 0x04, 0x78, 0xdc, 0x2e, 0x4e, 0xec,
	0x82, 0x53, 0xfc, 0x06, 0xed, 0x98, 0x1b, 0x29, 0x5a, 0x44, 0x6c, 0x4d, 0x7b, 0xff, 0x77, 0xcf,
	0x55, 0x6e, 0x6e, 0xca, 0x3d, 0xb1, 0xcf, 0x50, 0x55, 0x25, 0xd1, 0x68, 0x8d, 0x3a, 0xef, 0x13,
	0x1d, 0xde, 0x30, 0x3a, 0x07, 0xa5, 0x08, 0x05, 0xfc, 0x16, 0x35, 0x64, 0xe2, 0xb9, 0x4b, 0x48,
	0x77, 0x75, 0x2e, 0x8f, 0x37, 0x96, 0x6f, 0x62, 0x2d, 0x12, 0x6f, 0xc5, 0xfc, 0x19, 0xa4, 0x76,
	0xed, 0x6e, 0x33, 0xa8, 0x38, 0x75, 0x99, 0x78, 0x33, 0x48, 0xf1, 0x33, 0x54, 0x55, 0xac, 0x2c,
	0xd2, 0x76, 0x72, 0x98, 0x2b, 0x9c, 0xb3, 0x22, 0x5c, 0xd3, 0xc9, 0xe1, 0xe8, 0x87, 0x81, 0x2e,
	0x3e, 0x13, 0x0d, 0xdf, 0x49, 0x3a, 0x27, 0x6a, 0x9d, 0x40, 0x4c, 0x02, 0x70, 0x60, 0x8d, 0x5f,
	0xa3, 0x46, 0x0c, 0x91, 0xbb, 0x5f, 0xd0, 0x9a, 0x9a, 0xff, 0x76, 0x39, 0x8d, 0xea, 0xd4, 0x63,
	0x88, 0x6e, 0x18, 0xc5, 0xcf, 0x51, 0x27, 0x22, 0x6a, 0xed, 0xfa, 0x21, 0x59, 0xad, 0x80, 0x53,
	0xd8, 0x3d, 0xd7, 0x79, 0xae, 0x5e, 0xed, 0xc5, 0x7d, 0x94, 0xda, 0x43, 0x14, 0x7b, 0x76, 0x97,
	0x99, 0xc6, 0x7d, 0x66, 0x1a, 0x7f, 0x32, 0xd3, 0xf8, 0xb9, 0x35, 0x2b, 0xf7, 0x5b, 0xb3, 0xf2,
	0x7b, 0x6b, 0x56, 0xbe, 0xbd, 0xa4, 0x4c, 0x87, 0x89, 0x67, 0xf9, 0x22, 0x9a, 0xf8, 0x22, 0x02,
	0xed, 0xdd, 0xea, 0x03, 0x28, 0xbf, 0xed, 0xe9, 0x5f, 0xf7, 0xea, 0x85, 0xfa, 0xea, 0x6f, 0x00,
	0x00, 0x00, 0xff, 0xff, 0xb0, 0x16, 0x32, 0x08, 0x04, 0x03, 0x00, 0x00,
}

func (m *PacketPing) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *PacketPing) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *PacketPing) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	return len(dAtA) - i, nil
}

func (m *PacketPong) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *PacketPong) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *PacketPong) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	return len(dAtA) - i, nil
}

func (m *PacketMsg) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *PacketMsg) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *PacketMsg) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.Data) > 0 {
		i -= len(m.Data)
		copy(dAtA[i:], m.Data)
		i = encodeVarintConn(dAtA, i, uint64(len(m.Data)))
		i--
		dAtA[i] = 0x1a
	}
	if m.EOF {
		i--
		if m.EOF {
			dAtA[i] = 1
		} else {
			dAtA[i] = 0
		}
		i--
		dAtA[i] = 0x10
	}
	if m.ChannelID != 0 {
		i = encodeVarintConn(dAtA, i, uint64(m.ChannelID))
		i--
		dAtA[i] = 0x8
	}
	return len(dAtA) - i, nil
}

func (m *Packet) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *Packet) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *Packet) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.Sum != nil {
		{
			size := m.Sum.Size()
			i -= size
			if _, err := m.Sum.MarshalTo(dAtA[i:]); err != nil {
				return 0, err
			}
		}
	}
	return len(dAtA) - i, nil
}

func (m *Packet_PacketPing) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *Packet_PacketPing) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	if m.PacketPing != nil {
		{
			size, err := m.PacketPing.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintConn(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}
func (m *Packet_PacketPong) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *Packet_PacketPong) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	if m.PacketPong != nil {
		{
			size, err := m.PacketPong.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintConn(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x12
	}
	return len(dAtA) - i, nil
}
func (m *Packet_PacketMsg) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *Packet_PacketMsg) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	if m.PacketMsg != nil {
		{
			size, err := m.PacketMsg.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintConn(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x1a
	}
	return len(dAtA) - i, nil
}
func (m *AuthSigMessage) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *AuthSigMessage) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *AuthSigMessage) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.Nni) > 0 {
		i -= len(m.Nni)
		copy(dAtA[i:], m.Nni)
		i = encodeVarintConn(dAtA, i, uint64(len(m.Nni)))
		i--
		dAtA[i] = 0x1a
	}
	if len(m.Sig) > 0 {
		i -= len(m.Sig)
		copy(dAtA[i:], m.Sig)
		i = encodeVarintConn(dAtA, i, uint64(len(m.Sig)))
		i--
		dAtA[i] = 0x12
	}
	{
		size, err := m.PubKey.MarshalToSizedBuffer(dAtA[:i])
		if err != nil {
			return 0, err
		}
		i -= size
		i = encodeVarintConn(dAtA, i, uint64(size))
	}
	i--
	dAtA[i] = 0xa
	return len(dAtA) - i, nil
}

func (m *GatewayMasqueradeReq) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *GatewayMasqueradeReq) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *GatewayMasqueradeReq) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.Nni) > 0 {
		i -= len(m.Nni)
		copy(dAtA[i:], m.Nni)
		i = encodeVarintConn(dAtA, i, uint64(len(m.Nni)))
		i--
		dAtA[i] = 0x22
	}
	if len(m.MasqChallenge) > 0 {
		i -= len(m.MasqChallenge)
		copy(dAtA[i:], m.MasqChallenge)
		i = encodeVarintConn(dAtA, i, uint64(len(m.MasqChallenge)))
		i--
		dAtA[i] = 0x1a
	}
	if m.RemSig != nil {
		{
			size, err := m.RemSig.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintConn(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x12
	}
	return len(dAtA) - i, nil
}

func encodeVarintConn(dAtA []byte, offset int, v uint64) int {
	offset -= sovConn(v)
	base := offset
	for v >= 1<<7 {
		dAtA[offset] = uint8(v&0x7f | 0x80)
		v >>= 7
		offset++
	}
	dAtA[offset] = uint8(v)
	return base
}
func (m *PacketPing) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	return n
}

func (m *PacketPong) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	return n
}

func (m *PacketMsg) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.ChannelID != 0 {
		n += 1 + sovConn(uint64(m.ChannelID))
	}
	if m.EOF {
		n += 2
	}
	l = len(m.Data)
	if l > 0 {
		n += 1 + l + sovConn(uint64(l))
	}
	return n
}

func (m *Packet) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.Sum != nil {
		n += m.Sum.Size()
	}
	return n
}

func (m *Packet_PacketPing) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.PacketPing != nil {
		l = m.PacketPing.Size()
		n += 1 + l + sovConn(uint64(l))
	}
	return n
}
func (m *Packet_PacketPong) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.PacketPong != nil {
		l = m.PacketPong.Size()
		n += 1 + l + sovConn(uint64(l))
	}
	return n
}
func (m *Packet_PacketMsg) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.PacketMsg != nil {
		l = m.PacketMsg.Size()
		n += 1 + l + sovConn(uint64(l))
	}
	return n
}
func (m *AuthSigMessage) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	l = m.PubKey.Size()
	n += 1 + l + sovConn(uint64(l))
	l = len(m.Sig)
	if l > 0 {
		n += 1 + l + sovConn(uint64(l))
	}
	l = len(m.Nni)
	if l > 0 {
		n += 1 + l + sovConn(uint64(l))
	}
	return n
}

func (m *GatewayMasqueradeReq) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.RemSig != nil {
		l = m.RemSig.Size()
		n += 1 + l + sovConn(uint64(l))
	}
	l = len(m.MasqChallenge)
	if l > 0 {
		n += 1 + l + sovConn(uint64(l))
	}
	l = len(m.Nni)
	if l > 0 {
		n += 1 + l + sovConn(uint64(l))
	}
	return n
}

func sovConn(x uint64) (n int) {
	return (math_bits.Len64(x|1) + 6) / 7
}
func sozConn(x uint64) (n int) {
	return sovConn(uint64((x << 1) ^ uint64((int64(x) >> 63))))
}
func (m *PacketPing) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConn
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: PacketPing: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: PacketPing: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		default:
			iNdEx = preIndex
			skippy, err := skipConn(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConn
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func (m *PacketPong) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConn
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: PacketPong: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: PacketPong: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		default:
			iNdEx = preIndex
			skippy, err := skipConn(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConn
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func (m *PacketMsg) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConn
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: PacketMsg: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: PacketMsg: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field ChannelID", wireType)
			}
			m.ChannelID = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.ChannelID |= int32(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		case 2:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field EOF", wireType)
			}
			var v int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				v |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			m.EOF = bool(v != 0)
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Data", wireType)
			}
			var byteLen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				byteLen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if byteLen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + byteLen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.Data = append(m.Data[:0], dAtA[iNdEx:postIndex]...)
			if m.Data == nil {
				m.Data = []byte{}
			}
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipConn(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConn
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func (m *Packet) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConn
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: Packet: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: Packet: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field PacketPing", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				msglen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if msglen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			v := &PacketPing{}
			if err := v.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			m.Sum = &Packet_PacketPing{v}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field PacketPong", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				msglen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if msglen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			v := &PacketPong{}
			if err := v.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			m.Sum = &Packet_PacketPong{v}
			iNdEx = postIndex
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field PacketMsg", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				msglen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if msglen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			v := &PacketMsg{}
			if err := v.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			m.Sum = &Packet_PacketMsg{v}
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipConn(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConn
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func (m *AuthSigMessage) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConn
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: AuthSigMessage: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: AuthSigMessage: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field PubKey", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				msglen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if msglen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if err := m.PubKey.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Sig", wireType)
			}
			var byteLen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				byteLen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if byteLen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + byteLen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.Sig = append(m.Sig[:0], dAtA[iNdEx:postIndex]...)
			if m.Sig == nil {
				m.Sig = []byte{}
			}
			iNdEx = postIndex
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Nni", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				stringLen |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			intStringLen := int(stringLen)
			if intStringLen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.Nni = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipConn(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConn
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func (m *GatewayMasqueradeReq) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConn
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: GatewayMasqueradeReq: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: GatewayMasqueradeReq: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field RemSig", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				msglen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if msglen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.RemSig == nil {
				m.RemSig = &AuthSigMessage{}
			}
			if err := m.RemSig.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field MasqChallenge", wireType)
			}
			var byteLen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				byteLen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if byteLen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + byteLen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.MasqChallenge = append(m.MasqChallenge[:0], dAtA[iNdEx:postIndex]...)
			if m.MasqChallenge == nil {
				m.MasqChallenge = []byte{}
			}
			iNdEx = postIndex
		case 4:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Nni", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConn
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				stringLen |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			intStringLen := int(stringLen)
			if intStringLen < 0 {
				return ErrInvalidLengthConn
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthConn
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.Nni = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipConn(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConn
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func skipConn(dAtA []byte) (n int, err error) {
	l := len(dAtA)
	iNdEx := 0
	depth := 0
	for iNdEx < l {
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return 0, ErrIntOverflowConn
			}
			if iNdEx >= l {
				return 0, io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= (uint64(b) & 0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		wireType := int(wire & 0x7)
		switch wireType {
		case 0:
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return 0, ErrIntOverflowConn
				}
				if iNdEx >= l {
					return 0, io.ErrUnexpectedEOF
				}
				iNdEx++
				if dAtA[iNdEx-1] < 0x80 {
					break
				}
			}
		case 1:
			iNdEx += 8
		case 2:
			var length int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return 0, ErrIntOverflowConn
				}
				if iNdEx >= l {
					return 0, io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				length |= (int(b) & 0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if length < 0 {
				return 0, ErrInvalidLengthConn
			}
			iNdEx += length
		case 3:
			depth++
		case 4:
			if depth == 0 {
				return 0, ErrUnexpectedEndOfGroupConn
			}
			depth--
		case 5:
			iNdEx += 4
		default:
			return 0, fmt.Errorf("proto: illegal wireType %d", wireType)
		}
		if iNdEx < 0 {
			return 0, ErrInvalidLengthConn
		}
		if depth == 0 {
			return iNdEx, nil
		}
	}
	return 0, io.ErrUnexpectedEOF
}

var (
	ErrInvalidLengthConn        = fmt.Errorf("proto: negative length found during unmarshaling")
	ErrIntOverflowConn          = fmt.Errorf("proto: integer overflow")
	ErrUnexpectedEndOfGroupConn = fmt.Errorf("proto: unexpected end of group")
)
