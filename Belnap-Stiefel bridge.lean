import Mathlib

open Matrix

variable {d r rT rF : ℕ} (h : rT * d + rF * d = r * d)

noncomputable def V_T (V : Matrix (Fin (r * d)) (Fin d) ℂ) :
    Matrix (Fin (rT * d)) (Fin d) ℂ :=
  V.submatrix (fun i => Fin.castLE (by omega) i) id

noncomputable def V_F (V : Matrix (Fin (r * d)) (Fin d) ℂ) :
    Matrix (Fin (rF * d)) (Fin d) ℂ :=
  V.submatrix (fun i => Fin.cast h (Fin.natAdd (rT * d) i)) id

noncomputable def choiMap (μT μF : ℝ) (V : Matrix (Fin (r * d)) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (μT : ℂ) • ((V_T h V)ᴴ * (V_T h V)) + (μF : ℂ) • ((V_F h V)ᴴ * (V_F h V))

theorem VT_dagger_VT_add_VF_dagger_VF
    (V : Matrix (Fin (r * d)) (Fin d) ℂ) (hV : Vᴴ * V = 1) :
    (V_T h V)ᴴ * (V_T h V) + (V_F h V)ᴴ * (V_F h V) = (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rw [← hV]
  ext i j
  unfold V_T V_F
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, id_eq]
  have key : ∑ x : Fin (r*d), star (V x i) * V x j
      = ∑ k : Fin (rT*d + rF*d), star (V (finCongr h k) i) * V (finCongr h k) j :=
    (Equiv.sum_comp (finCongr h) (fun z => star (V z i) * V z j)).symm
  rw [key, Fin.sum_univ_add]
  congr 1

theorem choiMap_sub_one (μT μF : ℝ) (hsum : μT + μF = 1)
    (V : Matrix (Fin (r * d)) (Fin d) ℂ) (hV : Vᴴ * V = 1) :
    choiMap h μT μF V - 1 =
      -((μF:ℂ) • (1:Matrix (Fin d) (Fin d) ℂ) + ((μT - μF : ℝ):ℂ) • ((V_F h V)ᴴ * (V_F h V))) := by
  unfold choiMap
  have hsplit := VT_dagger_VT_add_VF_dagger_VF h V hV
  have hA : (V_T h V)ᴴ * (V_T h V) = 1 - (V_F h V)ᴴ * (V_F h V) := eq_sub_of_add_eq hsplit
  rw [hA]
  have hcast : ((μT - μF : ℝ):ℂ) = (μT:ℂ) - (μF:ℂ) := by push_cast; ring
  have hcastT : (μT:ℂ) = 1 - (μF:ℂ) := by
    have h3 : μT = 1 - μF := by linarith
    exact_mod_cast h3
  rw [hcast, hcastT]
  module

theorem trace_conjTranspose_mul_self_nonneg {n d : ℕ} (B : Matrix (Fin n) (Fin d) ℂ) :
    0 ≤ (Matrix.trace (Bᴴ * B)).re := by
  have h1 : Matrix.trace (Bᴴ * B) = ∑ i : Fin d, ∑ k : Fin n, (Complex.normSq (B k i) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm, ← starRingEnd_apply, Complex.mul_conj]
  rw [h1]
  have h2 : (∑ i : Fin d, ∑ k : Fin n, (Complex.normSq (B k i) : ℂ))
      = ((∑ i : Fin d, ∑ k : Fin n, Complex.normSq (B k i) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h2, Complex.ofReal_re]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro k _
  exact Complex.normSq_nonneg _

theorem R_min_bound {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (hB_herm : Bᴴ = B) (hB_tr : 0 ≤ (Matrix.trace B).re)
    (hB2_tr : 0 ≤ (Matrix.trace (B * B)).re)
    (μF κ : ℝ) (hμF : 0 ≤ μF) (hκ : 0 ≤ κ) :
    (μF^2 * d : ℝ) ≤ (Matrix.trace (((μF:ℂ) • (1:Matrix (Fin d) (Fin d) ℂ) + (κ:ℂ) • B)ᴴ *
      ((μF:ℂ) • (1:Matrix (Fin d) (Fin d) ℂ) + (κ:ℂ) • B))).re := by
  have hstarμF : star ((μF:ℝ):ℂ) = (μF:ℂ) := by
    rw [← starRingEnd_apply]; exact Complex.conj_ofReal μF
  have hstarκ : star ((κ:ℝ):ℂ) = (κ:ℂ) := by
    rw [← starRingEnd_apply]; exact Complex.conj_ofReal κ
  have hM_herm : ((μF:ℂ) • (1:Matrix (Fin d) (Fin d) ℂ) + (κ:ℂ) • B)ᴴ
      = (μF:ℂ) • (1:Matrix (Fin d) (Fin d) ℂ) + (κ:ℂ) • B := by
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, hB_herm,
        conjTranspose_one, hstarμF, hstarκ]
  rw [hM_herm]
  have hBim : (Matrix.trace B).im = 0 := by
    have h1 : Matrix.trace B = Matrix.trace Bᴴ := by rw [hB_herm]
    rw [Matrix.trace_conjTranspose] at h1
    have h2 : (Matrix.trace B).im = -(Matrix.trace B).im := by
      conv_lhs => rw [h1]; simp [Complex.conj_im]
    linarith
  have hBBim : (Matrix.trace (B * B)).im = 0 := by
    have hBB_herm : (B * B)ᴴ = B * B := by rw [conjTranspose_mul, hB_herm]
    have h1 : Matrix.trace (B * B) = Matrix.trace (B * B)ᴴ := by rw [hBB_herm]
    rw [Matrix.trace_conjTranspose] at h1
    have h2 : (Matrix.trace (B * B)).im = -(Matrix.trace (B * B)).im := by
      conv_lhs => rw [h1]; simp [Complex.conj_im]
    linarith
  have hexpand : Matrix.trace (((μF:ℂ) • (1:Matrix (Fin d) (Fin d) ℂ) + (κ:ℂ) • B) *
      ((μF:ℂ) • (1:Matrix (Fin d) (Fin d) ℂ) + (κ:ℂ) • B))
      = (μF:ℂ)^2 * d + 2*(μF:ℂ)*(κ:ℂ) * Matrix.trace B + (κ:ℂ)^2 * Matrix.trace (B*B) := by
    simp [add_mul, mul_add, smul_smul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
    ring
  have hBreal : Matrix.trace B = ((Matrix.trace B).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hBim]
  have hBBreal : Matrix.trace (B * B) = ((Matrix.trace (B * B)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hBBim]
  have hexpand_real : Matrix.trace (((μF:ℂ) • (1:Matrix (Fin d) (Fin d) ℂ) + (κ:ℂ) • B) *
      ((μF:ℂ) • (1:Matrix (Fin d) (Fin d) ℂ) + (κ:ℂ) • B))
      = ((μF^2 * d + 2*μF*κ*(Matrix.trace B).re + κ^2*(Matrix.trace (B*B)).re : ℝ) : ℂ) := by
    rw [hexpand, hBreal, hBBreal]
    simp only [Complex.ofReal_re]
    push_cast
    ring
  rw [hexpand_real, Complex.ofReal_re]
  nlinarith [mul_nonneg (mul_nonneg hμF hκ) hB_tr, mul_nonneg (sq_nonneg κ) hB2_tr]

theorem R_min_final (μT μF : ℝ) (hsum : μT + μF = 1) (hμF : 0 ≤ μF) (hμT : μF ≤ μT)
    (V : Matrix (Fin (r * d)) (Fin d) ℂ) (hV : Vᴴ * V = 1) :
    (μF^2 * d : ℝ) ≤ (Matrix.trace ((choiMap h μT μF V - 1)ᴴ * (choiMap h μT μF V - 1))).re := by
  rw [choiMap_sub_one h μT μF hsum V hV, conjTranspose_neg, neg_mul_neg]
  have hB_herm : ((V_F h V)ᴴ * (V_F h V))ᴴ = (V_F h V)ᴴ * (V_F h V) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hB_tr : 0 ≤ (Matrix.trace ((V_F h V)ᴴ * (V_F h V))).re :=
    trace_conjTranspose_mul_self_nonneg (V_F h V)
  have hB2_tr : 0 ≤ (Matrix.trace (((V_F h V)ᴴ * (V_F h V)) * ((V_F h V)ᴴ * (V_F h V)))).re := by
    have hh := trace_conjTranspose_mul_self_nonneg ((V_F h V)ᴴ * (V_F h V))
    rwa [hB_herm] at hh
  have hκ : 0 ≤ μT - μF := by linarith
  have result := R_min_bound ((V_F h V)ᴴ * (V_F h V)) hB_herm hB_tr hB2_tr μF (μT - μF) hμF hκ
  push_cast at result ⊢
  linarith [result]
