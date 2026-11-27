import OMAReductions.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1

-- Step Erdos828.erdos_828.variants.lehmer_conjecture.R1.H1: hypothesis H1 of reduction
-- Erdos828.erdos_828.variants.lehmer_conjecture.R1 (PR 8046)
-- Credit: @JamesSlash. If p * p divides n then p divides phi n (Nat.totient_mul_of_prime_of_dvd);
-- p also divides n, so p cannot divide n - 1.

theorem OMA.solution : OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1.H1 := by
  intro n hn hsq hdvd
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  simp only [not_forall, not_not] at hsq
  obtain ⟨p, hp, hpp⟩ := hsq
  obtain ⟨m, rfl⟩ := hpp
  have h1 : p ∣ Nat.totient (p * p * m) := by
    rw [mul_assoc, Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_right p m)]
    exact dvd_mul_right _ _
  have h2 : p ∣ p * p * m - 1 := h1.trans hdvd
  have h3 : p ∣ p * p * m := dvd_mul_of_dvd_left (dvd_mul_right p p) m
  have h4 := Nat.dvd_sub h3 h2
  have h5 : p * p * m - (p * p * m - 1) = 1 := by omega
  rw [h5] at h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
