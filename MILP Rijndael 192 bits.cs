
/*
		 * Mixed-Integer Linear Programming (MILP).
		 *
		 * (c) 2017 Hassan Mansour
		 * Generate Mixed-Integer Linear Programming (MILP) in Related-key setting to obtain security bounds of the minimum number of active S-boxes
		 it apply for both key schedule and state of AES 192-bit
		 * - Original AES Rijndael 192-bit
		 * - key size = 192 bits
		 * - number of rounds = 12
		 * The produce MILP problem is in lp format.
		 */

public static class minimize
{
	
		  public static int ROUNDS = 12; // number of rounds
		  public static int keyBits = 192; // number of key bits
	public static readonly int blockBits = 192; // number of block bits

	public static readonly int MAXKC = 6; // maximum key size in bits, divided by 32
	public static readonly int MAXBC = 6; // maximum block size in bits, divided by 32
	public static readonly int MAXROUNDS = 12; // maximum number of rounds for AES
		  public static int next = 0; // next unused state byte or key byte variable index
		  public static int dummy = 0; // next unused dummy variable index
		  public static int KC = 6;
		  public static int BC = 6;

	public static FILE[] tmp;

	internal int[,,] shifts =
	{
		{
			{0, 0},
			{1, 3},
			{2, 2},
			{3, 1}
		},
		{
			{0, 0},
			{1, 5},
			{2, 4},
			{3, 3}
		},
		{
			{0, 0},
			{1, 7},
			{3, 5},
			{4, 4}
		}
	};

	//ORIGINAL LINE: #define SC ((BC - 6) >> 1)

	public static List<int> sbox_input = new List<int>();
	public static std::vector<int> atleast_one = new std::vector<int>();

	/* minimize active S-boxes = keep track of S-box inputs */
	public static int S(int x)
	{
	  sbox_input.Add(x);
	  return x;
	}

	/* equations for XOR operation */
	public static int Xor(int x, int y)
	{
	  fprintf(tmp,"x%i + x%i + x%i - 2 d%i >= 0\n", x, y, next, dummy);
	  fprintf(tmp,"d%i - x%i >= 0\n", dummy, x);
	  fprintf(tmp,"d%i - x%i >= 0\n", dummy, y);
	  fprintf(tmp,"d%i - x%i >= 0\n", dummy, next);

	  dummy++;
	  return next++;
	}

	/* calculate round keys */
	public static void KeySchedule(int[,] k, int keyBits, int blockBits, int[,,] W)
	{

		  int i; // int i , j , t , RCpointer = 1;
		  int j;
		  int t = 0;
		  int[,] tk = new int[6, MAXKC]; // word8 tk[6][MAXKC];

		  for (j = 0; j < KC; j++)
		  {
		  for (i = 0; i < 6; i++)
		  {
				tk[i, j] = k[i, j];
		  }
		  }
		t = 0;

		 /* copy values into round key array */

		for (j = 0; (j < KC) && (t < (ROUNDS + 1) * BC); j++, t++) // for(j = 0 ; (j< KC) && ( t < (ROUNDS+1) * BC) ; j++ , t++)
		{

		for (i = 0 ; i < 6 ; i++)
		{
			W[t / BC, i, t % BC] = tk[i, j]; // for(i = 0; i < 6; i++) W[t / BC][i][t % BC] = tk[i][j];
		}
		}


		 while (t < (ROUNDS + 1) * BC) //     while (t < (ROUNDS+1)*BC)

		 {
			  /* while not enough round key material calculated */
			/* calculate new values */

				for (j = 0; (j < 1) && (t < (ROUNDS + 1) * BC); j++, t++)
				{
																					 //	for(i = 0; i < 6; i++)
				for (i = 0; i < 6 ; i++)
				{


		 W[t / BC, i, t % BC] = tk[i, j] = Xor(tk[i, j], S(tk[(i + 1) % 6, KC - 1])); //  tk[i][0] ^= S[tk[(i+1) %6] [KC-1]];
				}
				}

																					// tk[0][0] ^= RC[RCopinter++];

			 if (KC == 6)
			 {
				for (j = 1; (j < KC) && (t < (ROUNDS + 1) * BC); j++, t++) // for (j =1 ; j< KC; i++)
				{

				for (i = 0; i < 6; i++)
				{
					W[t / BC, i, t % BC] = tk[i, j] = Xor(tk[i, j], tk[i, j - 1]); //     for (i =0 ; i < 6 ; i++) tk [i][j] ^= tk[i][j-1];
				}
				}
			 }

			 else
			 {
			for (j = 1; (j < KC / 2) && (t < (ROUNDS + 1) * BC); j++, t++) // for ( j=  1; j< KC ; j++)
			{

			for (i = 0; i < 6; i++)
			{
				W[t / BC, i, t % BC] = tk[i, j] = Xor(tk[i, j], tk[i, j - 1]); //  for(i =0 ; i < 6 ; i++) tk [i][j] ^= tk[i][j-1];
			}
			}

			for (j = KC / 2; (j < KC / 2 + 1) && (t < (ROUNDS + 1) * BC); j++, t++) //    for (i =0 ; i <6 ; i++) tk[i][6] ^= S[tk[i][3]];
			{

																								 //  for(j = 5 ; j < KC ; i++)
		 for (i = 0; i < 6; i++)
		 {
			 W[t / BC, i, t % BC] = tk[i, j] = Xor(tk[i, j], S(tk[i, j - 1])); // for( i = 0 ; i < 6; i++) tk[i][j] ^= tk[i][j-1];
		 }
			}



			 }
		//	  copy values into round key array 

				for (j = KC / 2 + 1; (j < KC) && (t < (ROUNDS + 1) * BC); j++, t++) // for(j = 0; ( j < KC ) && (t< (ROUNDS+1) *BC); j++ , t++)
				{

			  for (i = 0; i < 6; i++)
			  {
				  W[t / BC, i, t % BC] = tk[i, j] = Xor(tk[i, j], tk[i, j - 1]); // for (i =0 ; i < 6 ; i++) W[t/ BC] [i][t % BC] ^=tk[i][j];
			  }
				}



		 }
	}

	internal static void KeyAddition(int[,] a, int[,] rk, int BC)
	{
		/* Exor corresponding text input and round key input bytes
		 */
		int i;
		int j;

		for (i = 0; i < 4; i++)
		{
			   for (j = 0; j < BC; j++)
			   {
				   a[i, j] = Xor(a[i, j], rk[i, j]);
			   }
		}
	}

	internal static void Substitution(int[,] a, int BC)
	{
		/* Replace every byte of the input by the byte at that place
		 * in the nonlinear S-box
		 */
		int i;
		int j;

		for (i = 0; i < 6; i++)
		{
			for (j = 0; j < BC; j++)
			{
				a[i, j] = S(a[i, j]);
			}
		}
	}

	internal static void ShiftRows(int[,] a, int d, int BC)
	{
		/* Row 0 remains unchanged
		 * The other three rows are shifted a variable amount
		 */
		int[] tmp = new int[MAXBC];
		int i;
		int j;

		for (i = 1; i < 6; i++)
		{
			for (j = 0; j < BC; j++)
			{
				tmp[j] = a[i, (j + shifts[((BC - 6) >> 1), i, d]) % BC];
			}
			for (j = 0; j < BC; j++)
			{
				a[i, j] = tmp[j];
			}
		}
	}

	internal static void MixColumns(int[,] a, int BC)
	{
	  int i;
	  int j;

	  for (j = 0; j < BC; j++)
	  {
		for (i = 0; i < 6; i++)
		{
			fprintf(tmp,"x%i + ",a[i, j]);
		}
		for (i = 0; i < 3; i++)
		{
			fprintf(tmp,"x%i + ",next + i);
		}
		fprintf(tmp,"x%i - 5 d%i >= 0\n",next + 3,dummy);

		for (i = 0; i < 6; i++)
		{
		  fprintf(tmp,"d%i - x%i >= 0\n",dummy,a[i, j]);
		}
		for (i = 0; i < 6; i++)
		{
		  fprintf(tmp,"d%i - x%i >= 0\n",dummy,a[i, j] = next++);
		}
		dummy++;
	  }
	}

	//int main(int argc, const char * argv[]) 
		static int Main()
		{
	  int[,] a = new int[6, MAXBC]; // the bytes of the AES state
	  int[,] k = new int[6, MAXKC]; // the bytes of the AES key
	  int[,,] rk = new int[MAXROUNDS + 1, 6, MAXBC]; // AES round keys

	  tmp = tmpfile();

	  Console.Write("\\ AES keysize: {0:D}, rounds: {1:D}\n", keyBits, ROUNDS);

	  for (int i = 0; i < 6; i++)
	  {
		for (int j = 0; j < KC; j++)
		{ // initialize variable indices
		  atleast_one.push_back(next);
		  k[i, j] = next++;
		}
	  }

	  KeySchedule(k, keyBits, blockBits, rk);

	  for (int i = 0; i < 6; i++)
	  {
		for (int j = 0; j < BC; j++)
		{ // initialize variable indices
		  atleast_one.push_back(next);
		  a[i, j] = next++;
		}
	  }

	  KeyAddition(a, rk[0], BC);

	   /* ROUNDS-1 ordinary rounds */
	  for (int r = 1; r < ROUNDS; r++)
	  {
		Substitution(a, BC);
		ShiftRows(a, 0, BC);
		MixColumns(a, BC);
		KeyAddition(a, rk[r], BC);
	  }

	  Substitution(a, BC);
	  ShiftRows(a, 0, BC);
	  KeyAddition(a, rk[ROUNDS], BC);

	  /* at least one S-box must be active */
	  for (size_t i = 0; i != atleast_one.size() - 1; i++)
	  {
		fprintf(tmp,"x%i + ",atleast_one.at(i));
	  }
	  fprintf(tmp,"x%i >= 1\n\n",atleast_one.back());

	  fprintf(tmp,"Binary\n"); // binary constraints
	  for (int i = 0; i < next; i++)
	  {
		  fprintf(tmp,"x%i\n",i);
	  }
	  for (int i = 0; i < dummy; i++)
	  {
		  fprintf(tmp,"d%i\n",i);
	  }

	  fprintf(tmp,"End\n");

	  Console.Write("Minimize\n"); // print objective function
	  for (size_t i = 0; i != sbox_input.Count - 1; i++)
	  {
		Console.Write("x{0:D} + ",sbox_input[i]);
	  }
	  Console.Write("x{0:D}\n\n",sbox_input[sbox_input.Count - 1]);

	  Console.Write("Subject To\n"); // round function constraints

	  {
		string buf = new string(new char[4096]);
		rewind(tmp);
		while (fgets(buf, sizeof(sbyte), tmp) != null)
		{
		  Console.Write("{0}",buf);
		}
	  }
	  fclose(tmp);

	  return 0;
		}

}