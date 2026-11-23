import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyTransformMemRationalUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinBasisCoeffsEmbeddingsEvalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormOneCmFieldDetOneAddNeZeroCharZeroStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.UnitaryDense

open Matrix

noncomputable def cayMat {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  (1 - M) * (1 + M)⁻¹

theorem map_inv_fieldHom {F E : Type} [Field F] [Field E] (f : F →+* E) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : (A.adjugate).map f = (A.map f).adjugate := RingHom.map_adjugate f A
  have h2 : f A.det = (A.map f).det := RingHom.map_det f A
  rw [Matrix.inv_def, Matrix.inv_def, ← h1, ← h2]
  ext i j
  simp [Ring.inverse_eq_inv']

theorem cayMat_map {F E : Type} [Field F] [Field E] (f : F →+* E) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : (cayMat A).map f = cayMat (A.map f) := by
  unfold cayMat
  rw [Matrix.map_mul, map_inv_fieldHom, Matrix.map_sub f (map_sub f), Matrix.map_add f (map_add f),
    Matrix.map_one _ (map_zero f) (map_one f)]

theorem eq_zero_of_rat_points {V K : Type} [Field K] [CharZero K] (q : MvPolynomial V K)
    (h : ∀ x : V → ℚ, MvPolynomial.eval (fun v => (x v : K)) q = 0) : q = 0 := by
  refine MvPolynomial.funext_set (p := q) (q := 0) (fun _ => Set.range (Rat.cast : ℚ → K))
    (fun _ => Set.infinite_range_of_injective Rat.cast_injective) ?_
  intro x hx
  choose y hy using fun v => hx v (Set.mem_univ v)
  rw [map_zero]
  have hxy : x = fun v => (y v : K) := funext fun v => (hy v).symm
  subst hxy
  exact h y

theorem cayMat_transpose {K : Type} [Field K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) K)
    (hNM : N * Mᵀ = 1) (hM : (1 + M).det ≠ 0) (hN : (1 + N).det ≠ 0) :
    cayMat N = -(cayMat M)ᵀ := by
  have hTN : Mᵀ * N = 1 := mul_eq_one_comm.mp hNM
  have hdT : (1 + Mᵀ).det ≠ 0 := by
    rw [← transpose_one, ← transpose_add, det_transpose]; exact hM
  have key : (1 + Mᵀ) * (1 - N) = -((1 - Mᵀ) * (1 + N)) := by
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hTN]
    abel
  have hu1 : IsUnit (1 + Mᵀ).det := isUnit_iff_ne_zero.mpr hdT
  have hu2 : IsUnit (1 + N).det := isUnit_iff_ne_zero.mpr hN
  unfold cayMat
  rw [transpose_mul, transpose_nonsing_inv, transpose_add, transpose_sub, transpose_one]
  calc (1 - N) * (1 + N)⁻¹ = (1 + Mᵀ)⁻¹ * ((1 + Mᵀ) * (1 - N)) * (1 + N)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu1, Matrix.one_mul]
    _ = -((1 + Mᵀ)⁻¹ * (1 - Mᵀ)) := by
        rw [key]
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, mul_nonsing_inv _ hu2, Matrix.mul_one]

section
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K] [CharZero K] (n : ℕ)

noncomputable def linPoly (σ : L →+* K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K) :=
  Matrix.of fun a b => ∑ i, MvPolynomial.C (σ (Module.finBasis ℚ L i)) * MvPolynomial.X (i, a, b)

noncomputable def skewPoly (σ : L →+* K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K) :=
  linPoly L K n σ - (linPoly L K n (σ.comp (IsCMField.complexConj L : L →+* L)))ᵀ

noncomputable def skewRat (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → ℚ) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun a b => (∑ i, (x (i, a, b) : L) * Module.finBasis ℚ L i) -
    (IsCMField.complexConj L : L →+* L) (∑ i, (x (i, b, a) : L) * Module.finBasis ℚ L i)

theorem eval_skewPoly (σ : L →+* K) (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → K) (a b : Fin n) :
    MvPolynomial.eval x (skewPoly L K n σ a b) =
      ∑ i, σ (Module.finBasis ℚ L i) * x (i, a, b) -
        ∑ i, σ ((IsCMField.complexConj L : L →+* L) (Module.finBasis ℚ L i)) * x (i, b, a) := by
  simp [skewPoly, linPoly, Matrix.sub_apply, Matrix.transpose_apply, map_sum]

theorem skewRat_map (σ : L →+* K) (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → ℚ) :
    (skewRat L n x).map σ = (skewPoly L K n σ).map (MvPolynomial.eval (fun v => (x v : K))) := by
  ext a b
  rw [Matrix.map_apply, Matrix.map_apply, eval_skewPoly]
  simp [skewRat, map_sum, map_sub, mul_comm]

theorem skewRat_skew (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → ℚ) :
    skewRat L n x + ((skewRat L n x).map (IsCMField.complexConj L : L →+* L))ᵀ = 0 := by
  ext a b
  simp [skewRat, Matrix.add_apply, Matrix.transpose_apply, map_sub, complexConj_invol]

end
end GlobalTheory.UnitaryDense

namespace GlobalTheory.UnitaryDense

theorem clear_denom : ∀ {V W K : Type} [Field K] (g : MvPolynomial V K) (f : W → MvPolynomial V K) (P : MvPolynomial W K), ∃ (q : MvPolynomial V K) (k : ℕ), ∀ x : V → K, MvPolynomial.eval x g ≠ 0 → MvPolynomial.eval (fun w => MvPolynomial.eval x (f w) / MvPolynomial.eval x g) P * (MvPolynomial.eval x g) ^ k = MvPolynomial.eval x q := by
  intro V W K _ g f P
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, 0, fun x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨q1, k1, h1⟩ := hp
    obtain ⟨q2, k2, h2⟩ := hq
    refine ⟨q1 * g ^ k2 + q2 * g ^ k1, k1 + k2, fun x hx => ?_⟩
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← h1 x hx, ← h2 x hx]
    ring
  | mul_X p w hp =>
    obtain ⟨q1, k1, h1⟩ := hp
    refine ⟨q1 * f w, k1 + 1, fun x hx => ?_⟩
    rw [map_mul, map_mul, ← h1 x hx, MvPolynomial.eval_X]
    field_simp
    ring

theorem cay_invol : ∀ {K : Type} [Field K] [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K), (1 + M).det ≠ 0 → (1 + (1 - M) * (1 + M)⁻¹).det ≠ 0 ∧ (1 - (1 - M) * (1 + M)⁻¹) * (1 + (1 - M) * (1 + M)⁻¹)⁻¹ = M := by
  intro K _ _ n M hM
  have hu : IsUnit (1 + M).det := isUnit_iff_ne_zero.mpr hM
  have hc : (1 - M) * (1 + M)⁻¹ = (1 + M)⁻¹ * (1 - M) := by
    have h1 : (1 + M) * (1 - M) = (1 - M) * (1 + M) := by
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
    calc (1 - M) * (1 + M)⁻¹ = (1 + M)⁻¹ * ((1 + M) * (1 - M)) * (1 + M)⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = (1 + M)⁻¹ * (1 - M) := by
          rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hp : 1 + (1 - M) * (1 + M)⁻¹ = (2 : K) • (1 + M)⁻¹ := by
    calc 1 + (1 - M) * (1 + M)⁻¹ = ((1 + M) + (1 - M)) * (1 + M)⁻¹ := by
          rw [Matrix.add_mul, Matrix.mul_nonsing_inv _ hu]
      _ = (2 : K) • (1 + M)⁻¹ := by
          rw [show (1 + M) + (1 - M) = (2 : K) • (1 : Matrix (Fin n) (Fin n) K) by
            rw [two_smul]; abel, Matrix.smul_mul, Matrix.one_mul]
  have hm : 1 - (1 - M) * (1 + M)⁻¹ = (2 : K) • (M * (1 + M)⁻¹) := by
    calc 1 - (1 - M) * (1 + M)⁻¹ = ((1 + M) - (1 - M)) * (1 + M)⁻¹ := by
          rw [Matrix.sub_mul (1 + M) (1 - M), Matrix.mul_nonsing_inv _ hu]
      _ = (2 : K) • (M * (1 + M)⁻¹) := by
          rw [show (1 + M) - (1 - M) = (2 : K) • M by rw [two_smul]; abel, Matrix.smul_mul]
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hdinv : ((1 + M)⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hM
  refine ⟨?_, ?_⟩
  · rw [hp, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ h2) hdinv
  · have hinv : ((2 : K) • (1 + M)⁻¹)⁻¹ = (2 : K)⁻¹ • (1 + M) := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul,
        Matrix.mul_nonsing_inv _ hu]
    rw [hp, hm, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h2, one_smul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
end GlobalTheory.UnitaryDense

namespace GlobalTheory.UnitaryDense
open Matrix

section
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K] [CharZero K] (n : ℕ)

theorem family_surj (Wf : (L →+* K) → Matrix (Fin n) (Fin n) K)
    (hW : ∀ σ, Wf (σ.comp (IsCMField.complexConj L : L →+* L)) = -(Wf σ)ᵀ) :
    ∃ x : Fin (Module.finrank ℚ L) × Fin n × Fin n → K,
      ∀ σ, (skewPoly L K n σ).map (MvPolynomial.eval x) = Wf σ := by
  choose y hy using fun ab : Fin n × Fin n => GlobalTheory.T.exists_finBasis_coeffs_embeddings_eval L K (fun σ => Wf σ ab.1 ab.2 / 2)
  refine ⟨fun v => y (v.2.1, v.2.2) v.1, fun σ => ?_⟩
  ext a b
  rw [Matrix.map_apply, eval_skewPoly]
  have h1 := hy (a, b) σ
  have h2 := hy (b, a) (σ.comp (IsCMField.complexConj L : L →+* L))
  simp only [RingHom.comp_apply] at h2
  simp only
  rw [h1, h2, hW σ]
  simp only [Matrix.neg_apply, Matrix.transpose_apply]
  ring

theorem generic_vanish [Nonempty (L →+* K)] (P : MvPolynomial ((L →+* K) × Fin n × Fin n) K)
    (hP : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) P = 0)
    (x : Fin (Module.finrank ℚ L) × Fin n × Fin n → K)
    (hx : ∀ σ, (1 + (skewPoly L K n σ).map (MvPolynomial.eval x)).det ≠ 0) :
    MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n =>
      cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval x)) p.2.1 p.2.2) P = 0 := by
  classical
  let d : (L →+* K) → MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K :=
    fun σ => (1 + skewPoly L K n σ).det
  let g := ∏ σ, d σ
  let f : (L →+* K) × Fin n × Fin n → MvPolynomial (Fin (Module.finrank ℚ L) × Fin n × Fin n) K :=
    fun p => ((1 - skewPoly L K n p.1) * (1 + skewPoly L K n p.1).adjugate) p.2.1 p.2.2 *
      ∏ τ ∈ Finset.univ.erase p.1, d τ
  have hd : ∀ y σ, MvPolynomial.eval y (d σ) = (1 + (skewPoly L K n σ).map (MvPolynomial.eval y)).det := by
    intro y σ
    simp only [d]
    rw [RingHom.map_det, map_add, map_one, RingHom.mapMatrix_apply]
  have hg : ∀ y, MvPolynomial.eval y g = ∏ σ, MvPolynomial.eval y (d σ) := fun y => map_prod _ _ _
  have hev : ∀ y, (∀ σ, MvPolynomial.eval y (d σ) ≠ 0) → ∀ p : (L →+* K) × Fin n × Fin n,
      MvPolynomial.eval y (f p) / MvPolynomial.eval y g =
        cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval y)) p.2.1 p.2.2 := by
    intro y hy p
    have hE : MvPolynomial.eval y (∏ τ ∈ Finset.univ.erase p.1, d τ) ≠ 0 := by
      rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun τ _ => hy τ
    have hsplit : MvPolynomial.eval y g = MvPolynomial.eval y (d p.1) *
        MvPolynomial.eval y (∏ τ ∈ Finset.univ.erase p.1, d τ) := by
      simp only [g]; rw [← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ _)]
    have hN : MvPolynomial.eval y (((1 - skewPoly L K n p.1) * (1 + skewPoly L K n p.1).adjugate) p.2.1 p.2.2) =
        ((1 - (skewPoly L K n p.1).map (MvPolynomial.eval y)) *
          (1 + (skewPoly L K n p.1).map (MvPolynomial.eval y)).adjugate) p.2.1 p.2.2 := by
      have e : (MvPolynomial.eval y).mapMatrix ((1 - skewPoly L K n p.1) * (1 + skewPoly L K n p.1).adjugate) =
          (1 - (skewPoly L K n p.1).map (MvPolynomial.eval y)) *
            (1 + (skewPoly L K n p.1).map (MvPolynomial.eval y)).adjugate := by
        rw [map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one]; rfl
      exact congrFun (congrFun e _) _
    simp only [f]
    rw [map_mul, hN, hsplit, mul_div_mul_right _ _ hE, hd]
    unfold cayMat
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨q, k, hq⟩ := clear_denom g f P
  have h0 : ∀ σ, skewPoly L K n σ = skewPoly L K n σ := fun _ => rfl
  have hq0 : q * g = 0 := by
    apply eq_zero_of_rat_points
    intro xr
    set y : Fin (Module.finrank ℚ L) × Fin n × Fin n → K := fun v => (xr v : K)
    rw [map_mul]
    by_cases hgy : MvPolynomial.eval y g = 0
    · rw [hgy, mul_zero]
    · have hy : ∀ σ, MvPolynomial.eval y (d σ) ≠ 0 := by
        rw [hg] at hgy; exact fun σ => (Finset.prod_ne_zero_iff.mp hgy) σ (Finset.mem_univ σ)
      rw [← hq y hgy]
      apply mul_eq_zero_of_left
      apply mul_eq_zero_of_left
      have hfun : (fun w => MvPolynomial.eval y (f w) / MvPolynomial.eval y g) =
          fun p : (L →+* K) × Fin n × Fin n => p.1 ((cayMat (skewRat L n xr)) p.2.1 p.2.2) := by
        funext p
        rw [hev y hy p, ← Matrix.map_apply (f := p.1), cayMat_map, skewRat_map]
      rw [hfun]
      set A := skewRat L n xr
      obtain σ₀ := Classical.arbitrary (L →+* K)
      have hA : (1 - -A).det ≠ 0 := by
        rw [sub_neg_eq_add]
        intro h
        apply hy σ₀
        rw [hd, ← skewRat_map, ← Matrix.map_one σ₀ (map_zero σ₀) (map_one σ₀),
          ← Matrix.map_add σ₀ (map_add σ₀), ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
      have hskew : -A + ((-A).map (IsCMField.complexConj L : L →+* L))ᵀ = 0 := by
        have := skewRat_skew L n xr
        rw [Matrix.map_neg _ (map_neg _), transpose_neg, ← neg_add, this, neg_zero]
      obtain ⟨γ₀, hγ, hγe⟩ := GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian L n (-A) hskew hA
      have : cayMat A = (γ₀ : Matrix (Fin n) (Fin n) L) := by
        rw [hγe, cayMat, sub_neg_eq_add, ← sub_eq_add_neg]
      rw [this]
      exact hP γ₀ hγ
  have hgne : g ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (0 : Fin (Module.finrank ℚ L) × Fin n × Fin n → K)) h
    rw [hg, map_zero] at this
    refine Finset.prod_ne_zero_iff.mpr (fun σ _ => ?_) this
    rw [hd]
    have : (skewPoly L K n σ).map (MvPolynomial.eval 0) = 0 := by
      ext a b; rw [Matrix.map_apply, eval_skewPoly]; simp
    rw [this, add_zero, det_one]; exact one_ne_zero
  have hq' : q = 0 := (mul_eq_zero.mp hq0).resolve_right hgne
  have hxd : ∀ σ, MvPolynomial.eval x (d σ) ≠ 0 := fun σ => by rw [hd]; exact hx σ
  have hgx : MvPolynomial.eval x g ≠ 0 := by
    rw [hg]; exact Finset.prod_ne_zero_iff.mpr fun σ _ => hxd σ
  have := hq x hgx
  rw [hq', map_zero] at this
  have h2 := (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hgx)
  have hfun : (fun w => MvPolynomial.eval x (f w) / MvPolynomial.eval x g) =
      fun p : (L →+* K) × Fin n × Fin n => cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval x)) p.2.1 p.2.2 :=
    funext (hev x hxd)
  rw [hfun] at h2
  exact h2

theorem vanish_good [Nonempty (L →+* K)] (P : MvPolynomial ((L →+* K) × Fin n × Fin n) K)
    (hP : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) P = 0)
    (B : (L →+* K) → Matrix (Fin n) (Fin n) K)
    (hB : ∀ σ, B (σ.comp (IsCMField.complexConj L : L →+* L)) * (B σ)ᵀ = 1)
    (hB1 : ∀ σ, (1 + B σ).det ≠ 0) :
    MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => B p.1 p.2.1 p.2.2) P = 0 := by
  have hW : ∀ σ, cayMat (B (σ.comp (IsCMField.complexConj L : L →+* L))) = -(cayMat (B σ))ᵀ :=
    fun σ => cayMat_transpose (B σ) _ (hB σ) (hB1 σ) (hB1 _)
  obtain ⟨x, hx⟩ := family_surj L K n (fun σ => cayMat (B σ)) hW
  have h := generic_vanish L K n P hP x (fun σ => by rw [hx σ]; exact (cay_invol (B σ) (hB1 σ)).1)
  have hfun : (fun p : (L →+* K) × Fin n × Fin n =>
      cayMat ((skewPoly L K n p.1).map (MvPolynomial.eval x)) p.2.1 p.2.2) =
      fun p : (L →+* K) × Fin n × Fin n => B p.1 p.2.1 p.2.2 := by
    funext p
    rw [hx p.1]
    exact congrFun (congrFun (cay_invol (B p.1) (hB1 p.1)).2 _) _
  rw [hfun] at h
  exact h

end

theorem unitary_points_dense : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] [CharZero K]
    (P : MvPolynomial ((L →+* K) × Fin n × Fin n) K),
    (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) P = 0) →
    ∀ B : (L →+* K) → GL (Fin n) K,
      (∀ σ : L →+* K, ((B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.transpose (((B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => ((B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2) P = 0 := by
  intro L _ _ _ n K _ _ P hP B hB
  classical
  rcases isEmpty_or_nonempty (L →+* K) with hS | hS
  · have h1 := hP 1 (one_mem _)
    have hfun : (fun p : (L →+* K) × Fin n × Fin n => ((B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2) =
        fun p : (L →+* K) × Fin n × Fin n => p.1 (((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2) := by
      funext p; exact (hS.false p.1).elim
    rw [hfun]; exact h1
  · set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
    let Bm : (L →+* K) → Matrix (Fin n) (Fin n) K := fun σ => ((B σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    have hBm : ∀ σ, Bm (σ.comp c) * (Bm σ)ᵀ = 1 := by
      intro σ
      simp only [Bm]
      rw [hB σ, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
    obtain ⟨u, hu, hdet⟩ := GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero_charZero L K n Bm
    have hσu : ∀ σ : L →+* K, σ (c u) * σ u = 1 := fun σ => by
      rw [← map_mul, mul_comm, hu, map_one]
    let B' : (L →+* K) → Matrix (Fin n) (Fin n) K := fun σ => σ u • Bm σ
    have hB' : ∀ σ, B' (σ.comp c) * (B' σ)ᵀ = 1 := by
      intro σ
      simp only [B', RingHom.comp_apply, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hBm σ, smul_smul]
      rw [mul_comm, hσu, one_smul]
    let P' := MvPolynomial.bind₁ (fun p : (L →+* K) × Fin n × Fin n =>
      MvPolynomial.C (p.1 (c u)) * MvPolynomial.X p) P
    have hP' : ∀ y, MvPolynomial.eval y P' = MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 (c u) * y p) P := by
      intro y
      simp only [P']
      change MvPolynomial.eval₂Hom (RingHom.id K) y _ = MvPolynomial.eval₂Hom (RingHom.id K) _ P
      rw [MvPolynomial.eval₂Hom_bind₁]
      simp
    have hcu : c u * u = 1 := by rw [mul_comm]; exact hu
    let s : GL (Fin n) L := ⟨Matrix.scalar (Fin n) (c u), Matrix.scalar (Fin n) u,
      by rw [← map_mul, hcu, map_one], by rw [← map_mul, hu, map_one]⟩
    have hs : s ∈ GQ0 L n := by
      show Matrix.scalar (Fin n) (c u) * conjT c (Matrix.scalar (Fin n) (c u)) = 1
      have : conjT c (Matrix.scalar (Fin n) (c u)) = Matrix.scalar (Fin n) u := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [conjT, hc, complexConj_invol]
        · simp [conjT, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
      rw [this, ← map_mul, hcu, map_one]
    have hQ : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
        MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) P' = 0 := by
      intro γ₀ hγ
      rw [hP']
      have := hP (s * γ₀) (mul_mem hs hγ)
      have e : (fun p : (L →+* K) × Fin n × Fin n => p.1 (c u) * p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) =
          fun p : (L →+* K) × Fin n × Fin n => p.1 (((s * γ₀ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2) := by
        funext p
        simp [s, Matrix.scalar_apply, Matrix.diagonal_mul, map_mul]
      rw [e]; exact this
    have h := vanish_good L K n P' hQ B' hB' hdet
    rw [hP'] at h
    have e : (fun p : (L →+* K) × Fin n × Fin n => p.1 (c u) * B' p.1 p.2.1 p.2.2) =
        fun p : (L →+* K) × Fin n × Fin n => ((B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2 := by
      funext p
      simp only [B', Bm, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hσu, one_mul]
    rw [e] at h; exact h

end GlobalTheory.UnitaryDense
