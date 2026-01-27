from mlabe import *
from random import randbytes
from unittest import TestCase

class TestMlAbe(TestCase):
    def test_gadget(self):
        u = rand_uniform_mat(1, 1)
        x = gadget_inv(u)
        self.assertEqual(gadget(x), u)

        u = rand_uniform_mat(3, 1)
        x = gadget_inv(u)
        self.assertEqual(gadget(x), u)

        u = rand_uniform_mat(3, 4)
        x = gadget_inv(u)
        self.assertEqual(gadget(x), u)

    def test_identity(self):
        X = rand_uniform_mat(4, 4)
        self.assertEqual(X*identity_mat(4), X)
        self.assertEqual(identity_mat(4)*X, X)

    def test_trapdoor(self):
        N = 2
        H = identity_mat(N)
        (A, R) = trapdoor(H)

        u = rand_uniform_mat(N, 1)
        w = gadget_inv(H.inverse() * u)
        x = R * w
        self.assertEqual(A * x, u)

        x = sample_trapdoor(H, A, R, u)
        self.assertEqual(A * x, u)

    def test_policy(self):
        N = 2
        test_cases = [
            {
                'enc_attributes': [],
                'dec_attributes': [],
                'expect_valid': True,
            },
            {
                'enc_attributes': [b'EU'],
                'dec_attributes': [b'EU'],
                'expect_valid': True,
            },
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'EU', b'prod'],
                'expect_valid': True,
            },
            {
                'enc_attributes': [b'EU', None],
                'dec_attributes': [b'EU', b'prod'],
                'expect_valid': True,
            },
        {
                'enc_attributes': [None, None],
                'dec_attributes': [b'EU', b'prod'],
                'expect_valid': True,
            },
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'Bikini Bottom', b'prod'],
                'expect_valid': False,
            },
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'EU', b'staging'],
                'expect_valid': False,
            },
        ]

        for t in test_cases:
            self.assertEqual(len(t['enc_attributes']), len(t['dec_attributes']))

            H_enc = enc_attr_to_tags(N, t['enc_attributes'])
            H_dec = dec_attr_to_tags(N, t['dec_attributes'])
            self.assertEqual(len(H_enc), len(H_dec))
            num_tags = len(H_enc)
            V = zero_mat(N, N)
            for i in range(num_tags):
                V += H_enc[i] * H_dec[i]

            self.assertEqual(V.is_zero(), t['expect_valid'], 'test case: {}\n{}'.format(t, V))

    def test_roundtrip(self):
        N = 2
        plaintext = randbytes(D // 8)

        test_cases = [
            {
                'enc_attributes': [],
                'dec_attributes': [],
                'expect_success': True,
            },
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'EU', b'prod'],
                'expect_success': True,
            },
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'EU', b'prod'],
                'expect_success': True,
            },
            {
                'enc_attributes': [None, b'prod'],
                'dec_attributes': [b'EU', b'prod'],
                'expect_success': True,
            },
            {
                'enc_attributes': [b'EU', None],
                'dec_attributes': [b'EU', b'prod'],
                'expect_success': True,
            },
            {
                'enc_attributes': [None, None],
                'dec_attributes': [b'EU', b'prod'],
                'expect_success': True,
            },
            {
                'enc_attributes': [b'Margaritaville', b'prod'],
                'dec_attributes': [b'EU', b'prod'],
                'expect_success': False,
            },
        ]

        for (i, t) in enumerate(test_cases):
            assert len(t['enc_attributes']) == len(t['dec_attributes'])
            num_attrs = len(t['enc_attributes'])
            (mpk, msk) = setup(N, num_attrs)
            sk = key_gen(mpk, msk, t['dec_attributes'])
            ciphertext = encrypt(mpk, t['enc_attributes'], plaintext)
            self.assertEqual(plaintext == decrypt(sk, ciphertext), t['expect_success'], f'test case {i}')
