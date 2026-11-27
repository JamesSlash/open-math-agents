import OMAReductions.R_OeisA232616_conjecture_3_R1

-- Step OeisA232616.conjecture_3.R1.H2: hypothesis H2 of reduction OeisA232616.conjecture_3.R1
-- Credit: @JamesSlash. 5^2 + 2 = 27 = 3^3 and 5^3 + 3 = 128 = 2^7.

theorem OMA.solution : OMA.R_OeisA232616_conjecture_3_R1.H2 := by
  rintro x y n m - - - - (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> norm_num
