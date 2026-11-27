import OMAReductions.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1

-- Step Erdos828.erdos_828.variants.lehmer_conjecture.R1.H2: hypothesis H2 of reduction
-- Erdos828.erdos_828.variants.lehmer_conjecture.R1
-- Credit: @JamesSlash. For a prime n, phi n = n - 1 (Nat.totient_prime).

theorem OMA.solution : OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1.H2 := by
  intro n _ hp
  exact (Nat.totient_prime (Nat.prime_iff.mpr hp)) ▸ dvd_rfl
