#include "sha-2/sha-256.h"
#include <stdint.h>
#include <stdio.h>
#include <math.h>
#include <time.h>
#include <stdlib.h>

#define TOTAL_LEN_LEN 8
typedef struct nft
{
    char img[50][50];
    int cost;
    int timestamp;
    int nonce;
    int nftid;
    int lines;
} nft;

typedef struct block
{

    uint8_t hash[32];
    uint8_t prevhash[32];
    struct block *prev;
    nft data;
} block;

typedef struct wallet
{
    int walletid;
    int amount;
    block *nft;
    int nftnum;
} wallet;

/*
 * Comments from pseudo-code at https://en.wikipedia.org/wiki/SHA-2 are reproduced here.
 * When useful for clarification, portions of the pseudo-code are reproduced here too.
 */

/*
 * @brief Rotate a 32-bit value by a number of bits to the right.
 * @param value The value to be rotated.
 * @param count The number of bits to rotate by.
 * @return The rotated value.
 */
static inline uint32_t right_rot(uint32_t value, unsigned int count)
{
    /*
     * Defined behaviour in standard C for all count where 0 < count < 32, which is what we need here.
     */
    return value >> count | value << (32 - count);
}

/*
 * @brief Update a hash value under calculation with a new chunk of data.
 * @param h Pointer to the first hash item, of a total of eight.
 * @param p Pointer to the chunk data, which has a standard length.
 *
 * @note This is the SHA-256 work horse.
 */
static inline void consume_chunk(uint32_t *h, const uint8_t *p)
{
    unsigned i, j;
    uint32_t ah[8];

    /* Initialize working variables to current hash value: */
    for (i = 0; i < 8; i++)
        ah[i] = h[i];

    /*
     * The w-array is really w[64], but since we only need 16 of them at a time, we save stack by
     * calculating 16 at a time.
     *
     * This optimization was not there initially and the rest of the comments about w[64] are kept in their
     * initial state.
     */

    /*
     * create a 64-entry message schedule array w[0..63] of 32-bit words (The initial values in w[0..63]
     * don't matter, so many implementations zero them here) copy chunk into first 16 words w[0..15] of the
     * message schedule array
     */
    uint32_t w[16];

    /* Compression function main loop: */
    for (i = 0; i < 4; i++)
    {
        for (j = 0; j < 16; j++)
        {
            if (i == 0)
            {
                w[j] =
                    (uint32_t)p[0] << 24 | (uint32_t)p[1] << 16 | (uint32_t)p[2] << 8 | (uint32_t)p[3];
                p += 4;
            }
            else
            {
                /* Extend the first 16 words into the remaining 48 words w[16..63] of the
                 * message schedule array: */
                const uint32_t s0 = right_rot(w[(j + 1) & 0xf], 7) ^ right_rot(w[(j + 1) & 0xf], 18) ^
                                    (w[(j + 1) & 0xf] >> 3);
                const uint32_t s1 = right_rot(w[(j + 14) & 0xf], 17) ^
                                    right_rot(w[(j + 14) & 0xf], 19) ^ (w[(j + 14) & 0xf] >> 10);
                w[j] = w[j] + s0 + w[(j + 9) & 0xf] + s1;
            }
            const uint32_t s1 = right_rot(ah[4], 6) ^ right_rot(ah[4], 11) ^ right_rot(ah[4], 25);
            const uint32_t ch = (ah[4] & ah[5]) ^ (~ah[4] & ah[6]);

            /*
             * Initialize array of round constants:
             * (first 32 bits of the fractional parts of the cube roots of the first 64 primes 2..311):
             */
            static const uint32_t k[] = {
                0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
                0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
                0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
                0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
                0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
                0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
                0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
                0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
                0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
                0xc67178f2};

            const uint32_t temp1 = ah[7] + s1 + ch + k[i << 4 | j] + w[j];
            const uint32_t s0 = right_rot(ah[0], 2) ^ right_rot(ah[0], 13) ^ right_rot(ah[0], 22);
            const uint32_t maj = (ah[0] & ah[1]) ^ (ah[0] & ah[2]) ^ (ah[1] & ah[2]);
            const uint32_t temp2 = s0 + maj;

            ah[7] = ah[6];
            ah[6] = ah[5];
            ah[5] = ah[4];
            ah[4] = ah[3] + temp1;
            ah[3] = ah[2];
            ah[2] = ah[1];
            ah[1] = ah[0];
            ah[0] = temp1 + temp2;
        }
    }

    /* Add the compressed chunk to the current hash value: */
    for (i = 0; i < 8; i++)
        h[i] += ah[i];
}

/*
 * Public functions. See header file for documentation.
 */

void sha_256_init(struct Sha_256 *sha_256, uint8_t hash[SIZE_OF_SHA_256_HASH])
{
    sha_256->hash = hash;
    sha_256->chunk_pos = sha_256->chunk;
    sha_256->space_left = SIZE_OF_SHA_256_CHUNK;
    sha_256->total_len = 0;
    /*
     * Initialize hash values (first 32 bits of the fractional parts of the square roots of the first 8 primes
     * 2..19):
     */
    sha_256->h[0] = 0x6a09e667;
    sha_256->h[1] = 0xbb67ae85;
    sha_256->h[2] = 0x3c6ef372;
    sha_256->h[3] = 0xa54ff53a;
    sha_256->h[4] = 0x510e527f;
    sha_256->h[5] = 0x9b05688c;
    sha_256->h[6] = 0x1f83d9ab;
    sha_256->h[7] = 0x5be0cd19;
}

void sha_256_write(struct Sha_256 *sha_256, const void *data, size_t len)
{
    sha_256->total_len += len;

    const uint8_t *p = data;

    while (len > 0)
    {
        /*
         * If the input chunks have sizes that are multiples of the calculation chunk size, no copies are
         * necessary. We operate directly on the input data instead.
         */
        if (sha_256->space_left == SIZE_OF_SHA_256_CHUNK && len >= SIZE_OF_SHA_256_CHUNK)
        {
            consume_chunk(sha_256->h, p);
            len -= SIZE_OF_SHA_256_CHUNK;
            p += SIZE_OF_SHA_256_CHUNK;
            continue;
        }
        /* General case, no particular optimization. */
        const size_t consumed_len = len < sha_256->space_left ? len : sha_256->space_left;
        memcpy(sha_256->chunk_pos, p, consumed_len);
        sha_256->space_left -= consumed_len;
        len -= consumed_len;
        p += consumed_len;
        if (sha_256->space_left == 0)
        {
            consume_chunk(sha_256->h, sha_256->chunk);
            sha_256->chunk_pos = sha_256->chunk;
            sha_256->space_left = SIZE_OF_SHA_256_CHUNK;
        }
        else
        {
            sha_256->chunk_pos += consumed_len;
        }
    }
}

uint8_t *sha_256_close(struct Sha_256 *sha_256)
{
    uint8_t *pos = sha_256->chunk_pos;
    size_t space_left = sha_256->space_left;
    uint32_t *const h = sha_256->h;

    /*
     * The current chunk cannot be full. Otherwise, it would already have be consumed. I.e. there is space left for
     * at least one byte. The next step in the calculation is to add a single one-bit to the data.
     */
    *pos++ = 0x80;
    --space_left;

    /*
     * Now, the last step is to add the total data length at the end of the last chunk, and zero padding before
     * that. But we do not necessarily have enough space left. If not, we pad the current chunk with zeroes, and add
     * an extra chunk at the end.
     */
    if (space_left < TOTAL_LEN_LEN)
    {
        memset(pos, 0x00, space_left);
        consume_chunk(h, sha_256->chunk);
        pos = sha_256->chunk;
        space_left = SIZE_OF_SHA_256_CHUNK;
    }
    const size_t left = space_left - TOTAL_LEN_LEN;
    memset(pos, 0x00, left);
    pos += left;
    size_t len = sha_256->total_len;
    pos[7] = (uint8_t)(len << 3);
    len >>= 5;
    int i;
    for (i = 6; i >= 0; --i)
    {
        pos[i] = (uint8_t)len;
        len >>= 8;
    }
    consume_chunk(h, sha_256->chunk);
    /* Produce the final hash value (big-endian): */
    int j;
    uint8_t *const hash = sha_256->hash;
    for (i = 0, j = 0; i < 8; i++)
    {
        hash[j++] = (uint8_t)(h[i] >> 24);
        hash[j++] = (uint8_t)(h[i] >> 16);
        hash[j++] = (uint8_t)(h[i] >> 8);
        hash[j++] = (uint8_t)h[i];
    }
    return sha_256->hash;
}

void calc_sha_256(uint8_t hash[SIZE_OF_SHA_256_HASH], const void *input, size_t len)
{
    struct Sha_256 sha_256;
    sha_256_init(&sha_256, hash);
    sha_256_write(&sha_256, input, len);
    (void)sha_256_close(&sha_256);
}
// calc_sha_256(dst, data, strlen(data));

void mineblock(block *newblock)
{
    time_t seconds;

    seconds = time(0);

    char src[30];
    uint32_t code = 0, counter = 1;

    for (int i = 0; i < 11; i++)
    {
        for (int j = 0; j < 30; j++)
        {
            code += newblock->data.img[i][j];
        }
    }
    code = code + pow(newblock->data.nonce, (newblock->data.nonce % 15) + 1) + newblock->data.timestamp;

    src[0] = (code * 78) % 127;
    src[1] = (code * 56) % 127;
    src[2] = (code * 91) % 127;
    src[3] = (code * 69) % 127;
    src[4] = (code * 42) % 127;
    src[5] = (code * 39) % 127;
    src[6] = (code * 25) % 127;
    src[7] = (code * 74) % 127;
    src[8] = (code * 83) % 127;
    src[9] = (code * 17) % 127;
    src[10] = (code * 19) % 127;
    src[11] = (code * 23) % 127;
    src[12] = (code * 38) % 127;
    src[13] = (code * 47) % 127;
    src[14] = (code * 52) % 127;
    src[15] = (code * 67) % 127;
    src[16] = (code * 73) % 127;
    src[17] = (code * 81) % 127;
    src[18] = (code * 95) % 127;
    src[19] = (code * 37) % 127;
    src[20] = (code * 19) % 127;
    src[21] = (code * 23) % 127;
    src[22] = (code * 38) % 127;
    src[23] = (code * 47) % 127;
    src[24] = (code * 52) % 127;
    src[25] = (code * 67) % 127;
    src[26] = (code * 73) % 127;
    src[27] = (code * 81) % 127;
    src[28] = (code * 95) % 127;
    src[29] = (code * 37) % 127;

    code = newblock->data.nftid + newblock->data.timestamp + newblock->data.nonce;

    calc_sha_256(newblock->hash, src, sizeof(src));

    while ((int)newblock->hash[0] % 100 != 00)
    {

        newblock->data.nonce++;
        code = code + newblock->data.timestamp + pow(newblock->data.nonce, (newblock->data.nonce % 15) + 1);

        src[0] = (code * 78);
        src[1] = (code * 56);
        src[2] = (code * 91);
        src[3] = (code * 69);
        src[4] = (code * 42);
        src[5] = (code * 39);
        src[6] = (code * 25);
        src[7] = (code * 74);
        src[8] = (code * 83);
        src[9] = (code * 17);
        src[10] = (code * 19);
        src[11] = (code * 23);
        src[12] = (code * 38);
        src[13] = (code * 47);
        src[14] = (code * 52);
        src[15] = (code * 67);
        src[16] = (code * 73);
        src[17] = (code * 81);
        src[18] = (code * 95);
        src[19] = (code * 37);
        src[20] = (code * 19);
        src[21] = (code * 23);
        src[22] = (code * 38);
        src[23] = (code * 47);
        src[24] = (code * 52);
        src[25] = (code * 67);
        src[26] = (code * 73);
        src[27] = (code * 81);
        src[28] = (code * 95);
        src[29] = (code * 37);

        calc_sha_256(newblock->hash, src, sizeof(src));

        for (int i = 0; i < 32; i++)
        {
            printf("%d ", newblock->hash[i]);
        }

        counter++;
    }
}
void createblock(block *prev, int cost, block *newblock)
{

    time_t seconds;

    seconds = time(NULL);

    for (int i = 0; i < 32; i++)
    {
        newblock->prevhash[i] = prev->hash[i];
    }
    newblock->data.nftid = prev->data.nftid;
    newblock->data.timestamp = seconds;
    newblock->data.cost = cost;
    newblock->data.nonce = 1;
    newblock->data.lines = prev->data.lines;
    memcpy(newblock->data.img, prev->data.img, sizeof(struct block));
    newblock->prev = prev;

    mineblock(newblock);
}
int hashcmp(uint8_t hash1[32], uint8_t hash2[32])
{

    for (int i = 0; i < 32; i++)
    {
        if (hash1[i] != hash2[i])
            return 1;
    }
    return 0;
}
int bidding(int *winner)
{
    int i, j, current_bid, previous_bid = -1;
    int rounds, bidd, buyer;
    srand(time(0));
    rounds = (rand() % 4) + 2;
    bidd = 2;
    printf("Bidding starts now !!!\n\n");
    printf("There will be %d rounds\n\n", rounds);
    printf("%d bidders will participate \n\n", bidd);
    for (i = 1; i <= rounds; i++)
    {
        buyer = (rand() % 2) + 1;

        printf(" \n%d round begins now\n ", i);
        for (j = 1; j <= rand() % 5 + 3; j++)
        {

            current_bid = (rand() % 96) + 5;

            if (current_bid < previous_bid)
                current_bid = current_bid + previous_bid;
            printf(" bid by %d is of %dMC \n", buyer % 2 + 1, current_bid);

            previous_bid = current_bid;

            buyer++;
        }
    }
    printf("\n Highest bid was of %dMC by %d!$!$!$\n", current_bid, (buyer - 1) % 2 + 1);
    *winner = buyer;
    return current_bid;
}
void readwallet(wallet *wal)
{
    srand(time(0));

    wal->walletid = rand();
    wal->amount = (rand() % 99999) + 10000;
    wal->nft = (block *)malloc(sizeof(block) * 10);
    wal->nftnum = 0;
}
int chainverify(block *nft)
{

    block *address = nft->prev;

    do
    {

        for (int i = 0; i < 32; i++)
            if (nft->prevhash[i] != nft->prev->hash[i])
                return 1;

        address = address->prev;
    } while (address != NULL);

    return 0;
}
void transaction(wallet *from, wallet *to, int i, int cost)
{

    createblock(&from->nft[i], cost, &to->nft[to->nftnum]);

    printf("\n\nNFT SOLD for %d MC\n\n", cost);
    for (int i = 0; i < to->nft[to->nftnum].data.lines; i++)
    {
        printf("%s", to->nft[to->nftnum].data.img[i]);
    }

    free(from->nft[i].data.img);

    to->amount -= cost;
    from->amount += cost;

    int verify = chainverify(&to->nft[to->nftnum]);

    if (verify == 1)
    {

        printf("\nChain is flase\n");
    }

    else if (verify == 0)
        printf("\nChain verfied\n");

    printf("\n\ntransaction complete!!\n\n");

    to->nftnum++;
}
int main(int argc, char const *argv[])
{
    srand(time(0));
    FILE *ptr;
    wallet marketplace, buyer1, buyer2;
    int j, choice, bid, buyer;

    time_t seconds;

    seconds = time(NULL);

    readwallet(&buyer1);
    readwallet(&buyer2);
    readwallet(&marketplace);

    printf("SELECT NFT\n\n\n");
    for (int i = 0; i < 5; i++)
    {
        FILE *ptr;
        if (i == 0)
        {
            printf("1 FOR THE CODER\n\n");
            ptr = fopen("nftsfolder/nft1.txt", "r"); // coder
        }
        else if (i == 1)
        {
            printf("2 FOR THE MEXICAN\n\n");
            ptr = fopen("nftsfolder/nft2.txt", "r"); // mushtache man
        }
        else if (i == 2)
        {
            printf("3 FOR THE GLASSES\n\n");
            ptr = fopen("nftsfolder/nft3.txt", "r"); // GLASSES
        }
        else if (i == 3)
        {
            printf("4 FOR THE GUN SKIN\n\n");
            ptr = fopen("nftsfolder/nft4.txt", "r"); // gun skin
        }
        else if (i == 4)
        {
            printf("5 FOR THE 007 LOGO\n\n");
            ptr = fopen("nftsfolder/nft5.txt", "r"); // 007
        }

        marketplace.nftnum++;
        j = 0;
        marketplace.nft[i].data.lines = 0;
        while (!feof(ptr))
        {
            fgets(marketplace.nft[i].data.img[j], 50, ptr);
            fputs(marketplace.nft[i].data.img[j], stdout);
            marketplace.nft[i].data.lines++;
            j++;
        }
        mineblock(&marketplace.nft[i]);
        marketplace.nft[i].data.nftid = rand() % 96 + 5;
        marketplace.nft[i].prev = NULL;
        marketplace.nft[i].data.cost = 0;
        marketplace.nft[i].data.timestamp = seconds;
        printf("\n\n\n");

        free(ptr);
    }
    choice = rand() % 4 + 1;

    printf("Selected choice is %d\n\n SELECTED NFT\n\n", choice);
    for (int i = 0; i < marketplace.nft[choice - 1].data.lines; i++)
    {
        printf("%s", marketplace.nft[choice - 1].data.img[i]);
    }
    printf("\n\n");

    bid = bidding(&buyer);

    printf("\n\n");

    if (buyer == 1)
    {
        if (choice == 1)
        {
            transaction(&marketplace, &buyer1, 0, bid);
        }
        if (choice == 2)
        {
            transaction(&marketplace, &buyer1, 1, bid);
        }
        if (choice == 3)
        {
            transaction(&marketplace, &buyer1, 2, bid);
        }
        if (choice == 4)
        {
            transaction(&marketplace, &buyer1, 3, bid);
        }
        if (choice == 5)
        {
            transaction(&marketplace, &buyer1, 4, bid);
        }
    }
    else
    {

        if (choice == 1)
        {
            transaction(&marketplace, &buyer2, 0, bid);
        }
        if (choice == 2)
        {
            transaction(&marketplace, &buyer2, 1, bid);
        }
        if (choice == 3)
        {
            transaction(&marketplace, &buyer2, 2, bid);
        }
        if (choice == 4)
        {
            transaction(&marketplace, &buyer2, 3, bid);
        }
        if (choice == 5)
        {
            transaction(&marketplace, &buyer2, 4, bid);
        }
    }

    return 0;
}
