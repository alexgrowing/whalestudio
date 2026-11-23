import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.FormalDegreeBessel.StatementG
open Matrix

namespace GlobalTheory.CompanionTheory.EichlerTransf

open scoped ComplexOrder

variable {n m : ℕ}

theorem mulVec_column {p q r : ℕ} (N : Matrix (Fin p) (Fin q) ℂ) (M : Matrix (Fin q) (Fin r) ℂ)
    (i : Fin r) : (N *ᵥ fun j => M j i) = fun j => (N * M) j i := by
  ext k; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem mulVec_mem_of_columns {p q : ℕ} (G : Submodule ℂ (Fin p → ℂ))
    (M : Matrix (Fin p) (Fin q) ℂ) (h : ∀ i, (fun j => M j i) ∈ G) (z : Fin q → ℂ) :
    M *ᵥ z ∈ G := by
  have e : M *ᵥ z = ∑ i, z i • (fun j => M j i) := by
    ext k; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (h i))

theorem isUnit_gram (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hPh : Pᴴ = P) (hPP : P * P = P) (hb : b * a = P) :
    IsUnit (aᴴ * a + (1 - P)) := by
  have hQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hPh]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hB : aᴴ * a + (1 - P) = (fromRows a (1 - P))ᴴ * fromRows a (1 - P) := by
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, hQ]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [hB, Matrix.conjTranspose_mul_self_mulVec_eq_zero, fromRows_mulVec] at hz
  have h1 : a *ᵥ v = 0 := by
    ext k; simpa using congrFun hz (Sum.inl k)
  have h2 : (1 - P) *ᵥ v = 0 := by
    ext k; simpa using congrFun hz (Sum.inr k)
  have h3 : P *ᵥ v = 0 := by
    rw [← hb, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  apply hv
  rw [Matrix.sub_mulVec, h3, Matrix.one_mulVec, sub_zero] at h2
  exact h2

theorem exists_gram_inverse (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hPh : Pᴴ = P) (hPP : P * P = P) (hb : b * a = P)
    (hap : a * P = a) :
    ∃ C H : Matrix (Fin m) (Fin m) ℂ, C * H = P ∧ aᴴ * a * C = P ∧ C * P = C := by
  have hu := isUnit_gram a b P hPh hPP hb
  set H := aᴴ * a + (1 - P) with hH
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hl : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ hdet
  have hr : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hPa : P * aᴴ = aᴴ := by
    have := congrArg conjTranspose hap
    rwa [conjTranspose_mul, hPh] at this
  have HP : H * P = aᴴ * a := by
    rw [hH, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self, add_zero,
      Matrix.mul_assoc, hap]
  have PH : P * H = aᴴ * a := by
    rw [hH, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, add_zero,
      ← Matrix.mul_assoc, hPa]
  have comm : H⁻¹ * P = P * H⁻¹ := by
    calc H⁻¹ * P = H⁻¹ * (P * H) * H⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hr, Matrix.mul_one]
      _ = H⁻¹ * (H * P) * H⁻¹ := by rw [PH, HP]
      _ = P * H⁻¹ := by rw [← Matrix.mul_assoc, hl, Matrix.one_mul]
  refine ⟨H⁻¹ * P, H, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, PH, ← HP, ← Matrix.mul_assoc, hl, Matrix.one_mul]
  · calc aᴴ * a * (H⁻¹ * P) = H * (P * H⁻¹) * P := by
          rw [← HP]; simp only [Matrix.mul_assoc]
      _ = H * H⁻¹ * (P * P) := by rw [← comm]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hr, Matrix.one_mul, hPP]
  · rw [Matrix.mul_assoc, hPP]

theorem eichler_isometry (J : Matrix (Fin n) (Fin n) ℂ) (a d : Matrix (Fin n) (Fin m) ℂ)
    (F : Matrix (Fin m) (Fin m) ℂ) (hJh : Jᴴ = J) (h1 : aᴴ * J * a = 0) (h2 : aᴴ * J * d = 0)
    (hF : F + Fᴴ = dᴴ * J * d) :
    (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J))ᴴ * J *
      (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J)) = J := by
  have h3 : dᴴ * J * a = 0 := by
    have := congrArg conjTranspose h2
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have key : (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J))ᴴ * J =
      J - J * d * (aᴴ * J) - J * a * Fᴴ * (aᴴ * J) + J * a * (dᴴ * J) := by
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_neg,
      conjTranspose_one, conjTranspose_conjTranspose, hJh, Matrix.add_mul, Matrix.sub_mul,
      Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [key]
  generalize hL : aᴴ * J = L at *
  generalize hD : dᴴ * J = D at *
  set N := 1 + a * (-D - F * L) + d * L with hN
  have hLN : L * N = L := by
    simp only [hN, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, h1, h2, Matrix.zero_mul,
      add_zero]
  have hDN : D * N = D + (F + Fᴴ) * L := by
    rw [hF]
    simp only [hN, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, h3, Matrix.zero_mul,
      add_zero]
  calc (J - J * d * L - J * a * Fᴴ * L + J * a * D) * N
      = J * N - J * d * (L * N) - J * a * Fᴴ * (L * N) + J * a * (D * N) := by
        simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
    _ = J := by
        rw [hLN, hDN, hN]
        simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_neg, Matrix.mul_one,
          Matrix.mul_assoc]
        abel

theorem eichler_of_involution (J : Matrix (Fin n) (Fin n) ℂ) (hJJ : J * J = 1) (hJh : Jᴴ = J)
    (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m))
    (hxx : xᴴ * J * x = 0) (hxy : xᴴ * J * y = 1) :
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * J ∈ Formalism.QuantumDeterminants.UH J ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => y j i)),
        J *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => y j i)) := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin m) (Fin m) ℂ,
      P = diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) := ⟨_, rfl⟩
  have hPh : Pᴴ = P := by
    rw [hPdef, diagonal_conjTranspose]
    congr 1
    ext i
    by_cases h : i ∈ A <;> simp [h]
  have hPP : P * P = P := by
    rw [hPdef, diagonal_mul_diagonal]
    congr 1
    ext i
    by_cases h : i ∈ A <;> simp [h]
  have colP : ∀ {r : ℕ} (M : Matrix (Fin r) (Fin m) ℂ) (v : Fin r) (i : Fin m),
      (M * P) v i = M v i * (if i ∈ A then (1 : ℂ) else 0) := by
    intro r M v i
    rw [hPdef, Matrix.mul_diagonal]
  have rowP : ∀ {r : ℕ} (M : Matrix (Fin m) (Fin r) ℂ) (i : Fin m) (v : Fin r),
      (P * M) i v = (if i ∈ A then (1 : ℂ) else 0) * M i v := by
    intro r M i v
    rw [hPdef, Matrix.diagonal_mul]
  obtain ⟨a, ha⟩ : ∃ a, a = x * P := ⟨_, rfl⟩
  have hap : a * P = a := by rw [ha, Matrix.mul_assoc, hPP]
  have haH : aᴴ = P * xᴴ := by rw [ha, conjTranspose_mul, hPh]
  have hPaH : P * aᴴ = aᴴ := by rw [haH, ← Matrix.mul_assoc, hPP]
  have haJa : aᴴ * J * a = 0 := by
    calc aᴴ * J * a = P * (xᴴ * J * x) * P := by rw [haH, ha]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hxx]; simp
  have haJy : aᴴ * J * y = P := by
    calc aᴴ * J * y = P * (xᴴ * J * y) := by rw [haH]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hxy, Matrix.mul_one]
  have hyJx : yᴴ * J * x = 1 := by
    have := congrArg conjTranspose hxy
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hb : (yᴴ * J) * a = P := by rw [ha, ← Matrix.mul_assoc, hyJx, Matrix.one_mul]
  obtain ⟨C, H, hCH, haaC, hCP⟩ := exists_gram_inverse a (yᴴ * J) P hPh hPP hb hap
  obtain ⟨y₂, hy₂⟩ : ∃ y₂, y₂ = J * a * C := ⟨_, rfl⟩
  have hJy₂ : J * y₂ = a * C := by
    rw [hy₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJa : J * a = y₂ * H := by
    rw [hy₂, Matrix.mul_assoc, hCH, Matrix.mul_assoc, hap]
  have hy₂P : y₂ * P = y₂ := by rw [hy₂, Matrix.mul_assoc, hCP]
  have hay₂ : aᴴ * J * y₂ = P := by
    rw [Matrix.mul_assoc, hJy₂, ← Matrix.mul_assoc, haaC]
  obtain ⟨d, hd⟩ : ∃ d, d = y₂ - y * P := ⟨_, rfl⟩
  have had : aᴴ * J * d = 0 := by
    rw [hd, Matrix.mul_sub, hay₂, ← Matrix.mul_assoc, haJy, hPP, sub_self]
  have hdP : d * P = d := by
    rw [hd, Matrix.sub_mul, hy₂P, Matrix.mul_assoc, hPP]
  have hPdH : P * dᴴ = dᴴ := by
    have := congrArg conjTranspose hdP
    rwa [conjTranspose_mul, hPh] at this
  obtain ⟨F, hFdef⟩ : ∃ F, F = (1 / 2 : ℂ) • (dᴴ * J * d) := ⟨_, rfl⟩
  have hEh : (dᴴ * J * d)ᴴ = dᴴ * J * d := by
    simp [conjTranspose_mul, hJh, Matrix.mul_assoc]
  have hF : F + Fᴴ = dᴴ * J * d := by
    rw [hFdef, conjTranspose_smul, hEh]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← add_smul]
    norm_num
  have hPF : P * F = F := by
    rw [hFdef, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPdH]
  obtain ⟨u, hu⟩ : ∃ u, u = -(dᴴ * J) - F * (aᴴ * J) := ⟨_, rfl⟩
  have hPu : P * u = u := by
    rw [hu, Matrix.mul_sub, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPdH, hPF]
  have hua : u * a = 0 := by
    have h3 : dᴴ * J * a = 0 := by
      have := congrArg conjTranspose had
      simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
    rw [hu, Matrix.sub_mul, Matrix.neg_mul, h3, Matrix.mul_assoc F, haJa]
    simp
  have hxu : x * u = a * u := by rw [ha, Matrix.mul_assoc, hPu]
  have hdx : d * xᴴ * J = d * (aᴴ * J) := by
    rw [haH, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hdP]
  have hN : 1 + x * u + d * xᴴ * J = 1 + a * u + d * (aᴴ * J) := by rw [hxu, hdx]
  have hiso := eichler_isometry J a d F hJh haJa had hF
  refine ⟨u, d, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v hi
    rw [← hPu, rowP]
    simp [hi]
  · intro v i hi
    rw [← hdP, colP]
    simp [hi]
  · intro i j hj
    have h0 : (u * a) i j = 0 := by rw [hua]; rfl
    rw [ha, ← Matrix.mul_assoc, colP] at h0
    simpa [hj] using h0
  · rw [hN, hu]
    exact hiso
  · rw [hN]
    obtain ⟨N, hNdef⟩ : ∃ N, N = 1 + a * u + d * (aᴴ * J) := ⟨_, rfl⟩
    rw [← hNdef]
    have hNa : N * a = a := by
      rw [hNdef, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc a, hua,
        Matrix.mul_assoc d, haJa]
      simp
    have hNy : N * (y * P) = y₂ + a * (u * (y * P)) := by
      have e : d * (aᴴ * J) * (y * P) = d := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (aᴴ * J), haJy, hPP, hdP]
      rw [hNdef, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc a, e, hd]
      abel
    have colx : ∀ i : A, (fun j => x j i) = fun j => a j i := by
      intro i
      ext j
      rw [ha, colP]
      simp [i.2]
    have coly : ∀ i : A, (fun j => y j i) = fun j => (y * P) j i := by
      intro i
      ext j
      rw [colP]
      simp [i.2]
    have hgx : ∀ i : A, (N *ᵥ fun j => x j i) = fun j => a j i := by
      intro i
      rw [colx, mulVec_column, hNa]
    have hgy : ∀ i : A, (N *ᵥ fun j => y j i) =
        (fun j => y₂ j i) + a *ᵥ (fun j => (u * (y * P)) j i) := by
      intro i
      rw [coly, mulVec_column, hNy, mulVec_column]
      ext j
      simp
    set G := Submodule.span ℂ (Set.range (fun i : A => N *ᵥ fun j => x j i) ∪
      Set.range (fun i : A => N *ᵥ fun j => y j i)) with hG
    have sub1 : ∀ i : A, (N *ᵥ fun j => x j i) ∈ G :=
      fun i => Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    have sub2 : ∀ i : A, (N *ᵥ fun j => y j i) ∈ G :=
      fun i => Submodule.subset_span (Or.inr ⟨i, rfl⟩)
    have haG : ∀ z, a *ᵥ z ∈ G := by
      refine mulVec_mem_of_columns G a (fun i => ?_)
      by_cases h : i ∈ A
      · have := sub1 ⟨i, h⟩
        rwa [hgx] at this
      · have e : (fun j => a j i) = 0 := by
          ext j
          rw [← hap, colP]
          simp [h]
        rw [e]
        exact G.zero_mem
    have hyG : ∀ z, y₂ *ᵥ z ∈ G := by
      refine mulVec_mem_of_columns G y₂ (fun i => ?_)
      by_cases h : i ∈ A
      · have h1 := sub2 ⟨i, h⟩
        rw [hgy] at h1
        have h2 := G.sub_mem h1 (haG (fun j => (u * (y * P)) j i))
        rwa [add_sub_cancel_right] at h2
      · have e : (fun j => y₂ j i) = 0 := by
          ext j
          rw [← hy₂P, colP]
          simp [h]
        rw [e]
        exact G.zero_mem
    have J1 : ∀ z, J *ᵥ (a *ᵥ z) ∈ G := by
      intro z
      rw [Matrix.mulVec_mulVec, hJa, ← Matrix.mulVec_mulVec]
      exact hyG _
    have J2 : ∀ z, J *ᵥ (y₂ *ᵥ z) ∈ G := by
      intro z
      rw [Matrix.mulVec_mulVec, hJy₂, ← Matrix.mulVec_mulVec]
      exact haG _
    have hle : G ≤ G.comap (Matrix.mulVecLin J) := by
      refine Submodule.span_le.2 ?_
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · change J *ᵥ (N *ᵥ fun j => x j i) ∈ G
        have e : (fun j => a j i) = a *ᵥ (fun j => P j i) := by
          rw [mulVec_column, hap]
        rw [hgx, e]
        exact J1 _
      · change J *ᵥ (N *ᵥ fun j => y j i) ∈ G
        have e : (fun j => y₂ j i) = y₂ *ᵥ (fun j => P j i) := by
          rw [mulVec_column, hy₂P]
        rw [hgy, e, Matrix.mulVec_add]
        exact G.add_mem (J2 _) (J1 _)
    intro v hv
    exact hle hv

theorem eichler_transformation : ∀ {n m : ℕ} (ε : Fin n → Bool) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    xᴴ * Formalism.REAL.Jm ε * x = 0 → xᴴ * Formalism.REAL.Jm ε * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * Formalism.REAL.Jm ε ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)) :=
  fun ε x y A h1 h2 => eichler_of_involution (Formalism.REAL.Jm ε) (Formalism.REAL.Jm_mul_self ε)
    (Formalism.REAL.Jm_conjTranspose ε) x y A h1 h2

end GlobalTheory.CompanionTheory.EichlerTransf
