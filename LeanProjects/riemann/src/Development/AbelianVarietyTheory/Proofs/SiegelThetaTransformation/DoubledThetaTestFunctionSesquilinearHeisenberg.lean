import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConjKappa
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpecStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianHeisenbergOperatorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFnStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.SW.DblLin

section Algebra

variable {N : ℕ} (Z W : Matrix (Fin N) (Fin N) ℂ)

noncomputable def hD (u u' q q' : Fin N → ℂ) : ℂ := star q ⬝ᵥ W *ᵥ u + u' ⬝ᵥ W *ᵥ star q'

theorem two_I_imH : (2 * I) • imH Z = Z - Zᴴ := by
  rw [imH, smul_smul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero), one_smul]

theorem hD_per (h1 : W * imH Z = 1) (u u' d b : Fin N → ℂ) :
    hD W u u' (star b + Z *ᵥ star d) (b + d ᵥ* Z) =
      (b + d ᵥ* Z) ⬝ᵥ W *ᵥ u + u' ⬝ᵥ W *ᵥ (star b + Z *ᵥ star d) -
        2 * I * (d ⬝ᵥ u + u' ⬝ᵥ star d) := by
  have h2 : imH Z * W = 1 := mul_eq_one_comm.1 h1
  have e1 : star (star b + Z *ᵥ star d) = (b + d ᵥ* Z) - (2 * I) • (d ᵥ* imH Z) := by
    rw [← vecMul_smul, two_I_imH, vecMul_sub, star_add, star_star, star_mulVec, star_star]
    abel
  have e2 : star (b + d ᵥ* Z) = (star b + Z *ᵥ star d) - (2 * I) • (imH Z *ᵥ star d) := by
    rw [← smul_mulVec, two_I_imH, sub_mulVec, star_add, star_vecMul]
    abel
  rw [hD, e1, e2, mulVec_sub, mulVec_smul, mulVec_mulVec, h1, one_mulVec, sub_dotProduct,
    smul_dotProduct, dotProduct_mulVec (d ᵥ* imH Z), vecMul_vecMul, h2, vecMul_one,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem conj_hD (hW : W.IsHermitian) (u u' q q' : Fin N → ℂ) :
    conj (hD W u u' q q') = hD W q q' u u' := by
  have h (a c : Fin N → ℂ) : conj (a ⬝ᵥ W *ᵥ c) = star c ⬝ᵥ W *ᵥ star a := by
    have := star_dotProduct_star (W *ᵥ c) a
    rw [star_mulVec, hW.eq, ← dotProduct_mulVec] at this
    exact this.symm
  rw [hD, map_add, h, h, star_star, star_star, hD]

theorem hD_sub_conj (hW : W.IsHermitian) (h1 : W * imH Z = 1) (d b d' b' : Fin N → ℂ) :
    hD W (star b' + Z *ᵥ star d') (b' + d' ᵥ* Z) (star b + Z *ᵥ star d) (b + d ᵥ* Z) -
      conj (hD W (star b' + Z *ᵥ star d') (b' + d' ᵥ* Z) (star b + Z *ᵥ star d) (b + d ᵥ* Z)) =
      2 * I * ((b ⬝ᵥ star d' + d' ⬝ᵥ star b) - (b' ⬝ᵥ star d + d ⬝ᵥ star b')) := by
  rw [conj_hD W hW, hD_per Z W h1, hD_per Z W h1]
  simp only [dotProduct_add _ (star _), add_dotProduct _ _ (star _), ← dotProduct_mulVec,
    dotProduct_add d, dotProduct_add d']
  ring

theorem gauss_per (h1 : W * imH Z = 1) (u u' d b : Fin N → ℂ) :
    (u' + (b + d ᵥ* Z)) ⬝ᵥ W *ᵥ (u + (star b + Z *ᵥ star d)) =
      hD W (u + (1 / 2 : ℂ) • (star b + Z *ᵥ star d)) (u' + (1 / 2 : ℂ) • (b + d ᵥ* Z))
        (star b + Z *ᵥ star d) (b + d ᵥ* Z) + u' ⬝ᵥ W *ᵥ u +
      2 * I * (d ⬝ᵥ Z *ᵥ star d + d ⬝ᵥ u + u' ⬝ᵥ star d) + I * (b ⬝ᵥ star d + d ⬝ᵥ star b) := by
  have e1 : d ⬝ᵥ (star b + Z *ᵥ star d) = d ⬝ᵥ star b + d ⬝ᵥ Z *ᵥ star d := dotProduct_add _ _ _
  have e2 : (b + d ᵥ* Z) ⬝ᵥ star d = b ⬝ᵥ star d + d ⬝ᵥ Z *ᵥ star d := by
    rw [add_dotProduct, dotProduct_mulVec]
  rw [hD_per Z W h1]
  generalize star b + Z *ᵥ star d = q at e1 ⊢
  generalize b + d ᵥ* Z = q' at e2 ⊢
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, e1, e2]
  ring

theorem eq_zero_of_im (A τ : Matrix (Fin N) (Fin N) ℂ) (hA : IsUnit A.det)
    (hW : W * τ.map (fun z => (z.im : ℂ)) = 1) (c : Fin N → ℂ)
    (h1 : ∀ j, ((c ᵥ* A) j).im = 0) (h2 : ∀ j, ((c ᵥ* (A * τ)) j).im = 0) : c = 0 := by
  have h3 : (c ᵥ* A) ᵥ* τ.map (fun z => (z.im : ℂ)) = 0 := by
    funext j
    have h := h2 j
    rw [← vecMul_vecMul] at h
    generalize c ᵥ* A = e at h1 h
    simp only [vecMul, dotProduct, im_sum, mul_im, h1, zero_mul, add_zero] at h
    apply Complex.ext
    · simpa [vecMul, dotProduct, re_sum] using h
    · simp [vecMul, dotProduct, im_sum, h1]
  have h4 := congrArg (· ᵥ* (W * A⁻¹)) h3
  simpa [← Matrix.mul_assoc, Matrix.mul_assoc A, mul_eq_one_comm.1 hW, mul_nonsing_inv _ hA]
    using h4

end Algebra

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem eq_zero_of_im_per (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (c : Fin g → ℂ) (h : ∀ v, (c ⬝ᵥ (per X x v ∘ idx)).im = 0) : c = 0 := by
  refine eq_zero_of_im _ _ _ (isUnit_det_perMat idx hs hx) (imInv_mul_im idx hs hx) c
    (fun j => h _) fun j => ?_
  rw [tauMat, ← Matrix.mul_assoc, mul_eq_one_comm.1 (hMat_mul_perMat idx hs hx), Matrix.one_mul]
  exact h _

theorem lin_eq_zero (hs : IsSympl X bas) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (L : ((Fin g → ℂ) × (Fin g → ℂ)) →ₗ[ℂ] ℂ)
    (h : ∀ a₁ a₂, (L (per X x₁ a₁ ∘ idx, star (per X x₂ a₂ ∘ idx))).im = 0) : L = 0 := by
  have key (f : (Fin g → ℂ) →ₗ[ℂ] ℂ) (u) : f u = (fun i => f (Pi.single i 1)) ⬝ᵥ u := by
    rw [f.pi_apply_eq_sum_univ u]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have e1 := eq_zero_of_im_per idx hs h₁ (fun i => L.comp (LinearMap.inl ℂ _ _) (Pi.single i 1))
    fun v => by
      rw [← key]
      have := h v 0
      rw [per_zero] at this
      simpa using this
  have e2 := eq_zero_of_im_per idx hs h₂
    (star fun i => L.comp (LinearMap.inr ℂ _ _) (Pi.single i 1)) fun v => by
      rw [star_dotProduct, dotProduct_comm, ← key]
      have := h 0 v
      rw [per_zero] at this
      simpa using this
  refine LinearMap.prod_ext (LinearMap.ext fun u => ?_) (LinearMap.ext fun u => ?_)
  · rw [key, e1]; simp
  · rw [key, star_eq_zero.1 e2]; simp

variable (X) in

noncomputable def cz (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) :
    ((Fin g → ℂ) × (Fin g → ℂ)) →ₗ[ℂ] (Fin r → ℂ) where
  toFun p := (-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 *ᵥ (aAnti X x₁ x₂ τ)⁻¹ *ᵥ fun a =>
    if (a : ℕ) < X.p0 then p.1 (idx.symm (τ, a)) else p.2 (idx.symm (τ, a)))
  map_add' p q := by
    rw [← smul_add, ← mulVec_add, ← mulVec_add]
    congr 3; funext a; simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]; split_ifs <;> rfl
  map_smul' c p := by
    rw [RingHom.id_apply, smul_comm c, ← mulVec_smul _ c, ← mulVec_smul _ c]
    congr 3; funext a; simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd]; split_ifs <;> rfl

variable (X) in

noncomputable def cz' (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) :
    ((Fin g → ℂ) × (Fin g → ℂ)) →ₗ[ℂ] (Fin r → ℂ) where
  toFun p := (τ.1 X.κ0 / 2) • (((aLin X x₁ x₂ τ)⁻¹ *ᵥ fun a =>
    if (a : ℕ) < X.p0 then p.2 (idx.symm (τ, a)) else p.1 (idx.symm (τ, a))) ᵥ* X.Gm.map τ.1)
  map_add' p q := by
    rw [← smul_add, ← add_vecMul, ← mulVec_add]
    congr 3; funext a; simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]; split_ifs <;> rfl
  map_smul' c p := by
    rw [RingHom.id_apply, smul_comm c, ← smul_vecMul c, ← mulVec_smul _ c]
    congr 3; funext a; simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd]; split_ifs <;> rfl

theorem dblz_row {n : ℕ} (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) (τ : X.Ψ) (k : Fin n) :
    dblz X idx x₁ x₂ z w τ k = cz X idx x₁ x₂ τ (z k, w k) := rfl

theorem dblz'_row {n : ℕ} (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) (τ : X.Ψ) (k : Fin n) :
    dblz' X idx x₁ x₂ z w τ k = cz' X idx x₁ x₂ τ (z k, w k) := rfl

variable (X) in

noncomputable def bv (a₁ a₂ : Fin r → E) : Fin r → E := (X.κ0 / 4) • ((a₁ + a₂) ᵥ* X.Gm)

theorem cz_per (hs : IsSympl X bas) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (a₁ a₂ : Fin r → E) (τ : X.Ψ) :
    cz X idx x₁ x₂ τ (per X x₁ a₁ ∘ idx, star (per X x₂ a₂ ∘ idx)) =
      star (Data.emb τ.1 (bv X a₁ a₂)) + dblZ X x₁ x₂ τ *ᵥ star (Data.emb τ.1 (a₁ - a₂)) ∧
    cz' X idx x₁ x₂ τ (per X x₁ a₁ ∘ idx, star (per X x₂ a₂ ∘ idx)) =
      Data.emb τ.1 (bv X a₁ a₂) + Data.emb τ.1 (a₁ - a₂) ᵥ* dblZ X x₁ x₂ τ := by
  obtain ⟨e', e, -⟩ := DblPer.dbl_per E r X g bas idx 2 hs even_two x₁ h₁ x₂ h₂
    (Matrix.of fun _ => a₁) (Matrix.of fun _ => a₂)
  rw [DblPer.cols, toCols₁_fromCols, toCols₂_fromCols] at e e'
  refine ⟨(congrFun (e τ) 0).trans ?_, congrFun (e' τ) 0⟩
  funext a
  simp only [Matrix.add_apply, Pi.add_apply, mul_apply, mulVec, dotProduct, mul_comm (dblZ _ _ _ _ _ _)]
  rfl

theorem trace_pair (b d : Fin r → E) : ((Algebra.trace ℚ E (∑ a, b a * cc (d a)) : ℚ) : ℂ) =
    ∑ τ : X.Ψ, (Data.emb τ.1 b ⬝ᵥ star (Data.emb τ.1 d) +
      Data.emb τ.1 d ⬝ᵥ star (Data.emb τ.1 b)) := by
  rw [X.trace_eq_Psi]
  simp [dotProduct, Data.emb, DblPer.emb_cc, mul_comm]

theorem trace_bv (a₁ a₂ d : Fin r → E) :
    Algebra.trace ℚ E (∑ a, bv X a₁ a₂ a * cc (d a)) = -(1 / 2) * EF X (a₁ + a₂) d := by
  rw [EF_def, ← smul_eq_mul, ← map_smul, herm, Finset.sum_comm, Finset.mul_sum, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [bv, Pi.smul_apply, vecMul, dotProduct, smul_eq_mul, ← Finset.sum_mul, Rat.smul_def]
  push_cast
  ring

theorem hD_eq (hs : IsSympl X bas) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (y₁ y₂ : Fin r → E) (p : (Fin g → ℂ) × (Fin g → ℂ)) :
    ∑ τ, hD (imH (dblZ X x₁ x₂ τ))⁻¹ (cz X idx x₁ x₂ τ p) (cz' X idx x₁ x₂ τ p)
      (cz X idx x₁ x₂ τ (per X x₁ y₁ ∘ idx, star (per X x₂ y₂ ∘ idx)))
      (cz' X idx x₁ x₂ τ (per X x₁ y₁ ∘ idx, star (per X x₂ y₂ ∘ idx))) =
    hermForm (Hm X bas idx x₁) p.1 (per X x₁ y₁ ∘ idx) +
      hermForm (Hm X bas idx x₂) (per X x₂ y₂ ∘ idx) (star p.2) := by
  have hZ := (dblZ_mem_Hn E r X x₁ h₁ x₂ h₂).2.1
  let L : ((Fin g → ℂ) × (Fin g → ℂ)) →ₗ[ℂ] ℂ :=
    { toFun := fun p => ∑ τ, hD (imH (dblZ X x₁ x₂ τ))⁻¹ (cz X idx x₁ x₂ τ p) (cz' X idx x₁ x₂ τ p)
        (cz X idx x₁ x₂ τ (per X x₁ y₁ ∘ idx, star (per X x₂ y₂ ∘ idx)))
        (cz' X idx x₁ x₂ τ (per X x₁ y₁ ∘ idx, star (per X x₂ y₂ ∘ idx))) -
        (hermForm (Hm X bas idx x₁) p.1 (per X x₁ y₁ ∘ idx) +
          hermForm (Hm X bas idx x₂) (per X x₂ y₂ ∘ idx) (star p.2))
      map_add' := fun p q => by
        simp only [hD, hermForm, map_add, star_star, Prod.fst_add, Prod.snd_add, mulVec_add,
          dotProduct_add, add_dotProduct, Finset.sum_add_distrib]
        ring
      map_smul' := fun c p => by
        simp only [hD, hermForm, map_smul, star_star, Prod.smul_fst, Prod.smul_snd, mulVec_smul,
          dotProduct_smul, smul_dotProduct, smul_eq_mul, RingHom.id_apply, ← mul_add,
          ← Finset.mul_sum, mul_sub] }
  have hL := lin_eq_zero idx hs h₁ h₂ L fun a₁ a₂ => by
    have e := Finset.sum_congr (s₁ := Finset.univ) rfl fun (τ : X.Ψ) _ =>
      hD_sub_conj _ _ (hZ τ).inv.isHermitian (nonsing_inv_mul _ (hZ τ).det_pos.ne'.isUnit)
        (Data.emb τ.1 (y₁ - y₂)) (Data.emb τ.1 (bv X y₁ y₂))
        (Data.emb τ.1 (a₁ - a₂)) (Data.emb τ.1 (bv X a₁ a₂))
    rw [Finset.sum_sub_distrib, ← map_sum, sub_conj, ← Finset.mul_sum, Finset.sum_sub_distrib,
      ← trace_pair, ← trace_pair, trace_bv, trace_bv] at e
    have e2 : -(1 / 2) * EF X (y₁ + y₂) (a₁ - a₂) - -(1 / 2) * EF X (a₁ + a₂) (y₁ - y₂) =
        EF X a₁ y₁ + EF X y₂ a₂ := by
      have hn (v) : crd X bas (-v) = -crd X bas v := by
        simpa using crd_smul hs (-1) v
      simp only [EF_crd hs, sub_eq_add_neg, crd_add hs, hn, Pi.add_apply, Pi.neg_apply,
        ← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [← Rat.cast_sub, e2] at e
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, star_star, sub_im, add_im,
      im_hermForm_Hm idx hs h₁, im_hermForm_Hm idx hs h₂, (cz_per idx hs h₁ h₂ _ _ _).1,
      (cz_per idx hs h₁ h₂ _ _ _).2]
    generalize (Finset.sum _ _ : ℂ).im = S at e ⊢
    have e3 := congrArg Complex.im e
    simp at e3
    linarith
  exact sub_eq_zero.1 (LinearMap.congr_fun hL p)

end Frames

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem expo_row (hs : IsSympl X bas) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (y₁ y₂ : Fin r → E) (z w : Fin g → ℂ) :
    ∑ τ, cz' X idx x₁ x₂ τ (z + per X x₁ y₁ ∘ idx, w + star (per X x₂ y₂ ∘ idx)) ⬝ᵥ
      (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ
        cz X idx x₁ x₂ τ (z + per X x₁ y₁ ∘ idx, w + star (per X x₂ y₂ ∘ idx)) =
    hermForm (Hm X bas idx x₁) (z + (1 / 2 : ℂ) • (per X x₁ y₁ ∘ idx)) (per X x₁ y₁ ∘ idx) +
      conj (hermForm (Hm X bas idx x₂) (star w + (1 / 2 : ℂ) • (per X x₂ y₂ ∘ idx))
        (per X x₂ y₂ ∘ idx)) +
      ∑ τ, cz' X idx x₁ x₂ τ (z, w) ⬝ᵥ (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ cz X idx x₁ x₂ τ (z, w) +
      2 * I * ∑ τ : X.Ψ, (Data.emb τ.1 (y₁ - y₂) ⬝ᵥ dblZ X x₁ x₂ τ *ᵥ star (Data.emb τ.1 (y₁ - y₂)) +
        Data.emb τ.1 (y₁ - y₂) ⬝ᵥ cz X idx x₁ x₂ τ (z, w) +
        cz' X idx x₁ x₂ τ (z, w) ⬝ᵥ star (Data.emb τ.1 (y₁ - y₂))) +
      I * ((Algebra.trace ℚ E (∑ a, bv X y₁ y₂ a * cc ((y₁ - y₂) a)) : ℚ) : ℂ) := by
  have hZ := (dblZ_mem_Hn E r X x₁ h₁ x₂ h₂).2.1
  have h := hD_eq idx hs h₁ h₂ y₁ y₂
    ((z, w) + (1 / 2 : ℂ) • (per X x₁ y₁ ∘ idx, star (per X x₂ y₂ ∘ idx)))
  have hc : conj (hermForm (Hm X bas idx x₂) (star w + (1 / 2 : ℂ) • (per X x₂ y₂ ∘ idx))
      (per X x₂ y₂ ∘ idx)) = hermForm (Hm X bas idx x₂) (per X x₂ y₂ ∘ idx)
        (star (w + (1 / 2 : ℂ) • star (per X x₂ y₂ ∘ idx))) := by
    have := star_dotProduct_star (Hm X bas idx x₂ *ᵥ star (per X x₂ y₂ ∘ idx))
      (star w + (1 / 2 : ℂ) • (per X x₂ y₂ ∘ idx))
    rw [star_mulVec, (Hm_isHermitian idx hs h₂).eq, ← dotProduct_mulVec, star_star] at this
    refine this.symm.trans ?_
    simp [hermForm]
  rw [hc, trace_pair (X := X), Finset.mul_sum, Finset.mul_sum]
  erw [← h]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Prod.mk_add_mk]
  simp only [map_add, map_smul, (cz_per idx hs h₁ h₂ _ _ _).1, (cz_per idx hs h₁ h₂ _ _ _).2]
  exact gauss_per _ _ (nonsing_inv_mul _ (hZ τ).det_pos.ne'.isUnit) _ _ _ _

theorem thA_add (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {φ ψ : TF n g}
    (hφ : IsSB φ) (hψ : IsSB ψ) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (φ + ψ) x z = thA X bas idx φ x z + thA X bas idx ψ x z := by
  have hτ : tauMat X bas idx x ∈ Siegel (Fin g) :=
    ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩
  have h1 := (SiegelSum.summable_norm_thetaTerm _ _ φ hφ _ hτ
    fun k => hMat X bas idx x *ᵥ z k).of_norm
  have h2 := (SiegelSum.summable_norm_thetaTerm _ _ ψ hψ _ hτ
    fun k => hMat X bas idx x *ᵥ z k).of_norm
  unfold thA thS
  rw [← mul_add, ← h1.tsum_add h2]
  simp only [Pi.add_apply, add_mul]

theorem thA_smul (x : Frame X.Ψ r) (c : ℂ) (φ : TF n g) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (c • φ) x z = c * thA X bas idx φ x z := by
  unfold thA thS
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc c, tsum_mul_left]
  ring

omit [IsCMField E] in

theorem thH_smul {Ψ : Finset (E →+* ℂ)} {N : ℕ} (c : ℂ) (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (Z : CM Ψ N N) (z z' : CM Ψ n N) : thH Ψ (c • φ) Z z z' = c * thH Ψ φ Z z z' := by
  unfold thH
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc c, tsum_mul_left]

theorem thH_add {Ψ : Finset (E →+* ℂ)} {N : ℕ} (hΨ : IsType Ψ)
    {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (z z' : CM Ψ n N) :
    thH Ψ (φ + ψ) Z z z' = thH Ψ φ Z z z' + thH Ψ ψ Z z z' := by
  have h1 := ((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N φ hφ Z hZ).1 z z').of_norm
  have h2 := ((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N ψ hψ Z hZ).1 z z').of_norm
  unfold thH
  rw [← h1.tsum_add h2]
  simp only [Pi.add_apply, add_mul]

theorem isDbl_heis (hs : IsSympl X bas) (hn : Even n) {φ₁ φ₂ : TF n g} (hφ₁ : IsSB φ₁)
    (hφ₂ : IsSB φ₂) {ψ : Matrix (Fin n) (Fin r) E → ℂ} (hψ : IsSB ψ)
    (h : IsDbl X bas idx φ₁ φ₂ ψ) (y₁ y₂ : Matrix (Fin n) (Fin r) E) :
    IsDbl X bas idx (heisG X bas y₁ φ₁) (heisG X bas y₂ φ₂)
      (heisH (y₁ - y₂) ((X.κ0 / 4) • ((y₁ + y₂) * X.Gm)) ψ) := by
  intro x₁ h₁ x₂ h₂ z w
  obtain ⟨hΨ, hZ, -⟩ := dblZ_mem_Hn E r X x₁ h₁ x₂ h₂
  have hG := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have h' := h x₁ h₁ x₂ h₂ (fun k => z k + per X x₁ (y₁ k) ∘ idx)
    (fun k => w k + star (per X x₂ (y₂ k) ∘ idx))
  have a1 : dblz X idx x₁ x₂ (fun k => z k + per X x₁ (y₁ k) ∘ idx)
      (fun k => w k + star (per X x₂ (y₂ k) ∘ idx)) = fun τ => dblz X idx x₁ x₂ z w τ +
        (((X.κ0 / 4) • ((y₁ + y₂) * X.Gm)).map τ.1).map conj +
        ((y₁ - y₂).map τ.1).map conj * (dblZ X x₁ x₂ τ)ᵀ := by
    funext τ k
    rw [dblz_row, ← Prod.mk_add_mk, map_add, (cz_per idx hs h₁ h₂ _ _ _).1, ← add_assoc]
    funext a
    simp only [Matrix.add_apply, Pi.add_apply, mul_apply, mulVec, dotProduct,
      mul_comm (dblZ _ _ _ _ _ _)]
    rfl
  have a2 : dblz' X idx x₁ x₂ (fun k => z k + per X x₁ (y₁ k) ∘ idx)
      (fun k => w k + star (per X x₂ (y₂ k) ∘ idx)) = fun τ => dblz' X idx x₁ x₂ z w τ +
        ((X.κ0 / 4) • ((y₁ + y₂) * X.Gm)).map τ.1 + (y₁ - y₂).map τ.1 * dblZ X x₁ x₂ τ := by
    funext τ k
    rw [dblz'_row, ← Prod.mk_add_mk, map_add, (cz_per idx hs h₁ h₂ _ _ _).2, ← add_assoc]
    rfl
  have a3 : (fun k i => conj ((w k + star (per X x₂ (y₂ k) ∘ idx)) i)) =
      fun k => (fun i => conj (w k i)) + per X x₂ (y₂ k) ∘ idx := by
    funext k i; simp
  rw [a1, a2, a3] at h'
  rw [(hG y₁ φ₁ hφ₁).2.2.2.2 x₁ h₁, (hG y₂ φ₂ hφ₂).2.2.2.2 x₂ h₂,
    (GlobalTheory.T.hermitianHeisenbergOperator_laws E X.Ψ hΨ n r hn _ _ ψ hψ).2.1 _ hZ, map_mul, mul_mul_mul_comm, h',
    ← mul_assoc, ← mul_assoc]
  congr 1
  simp only [kZero, Finset.prod_mul_distrib, ← Complex.exp_sum, ← exp_conj]
  rw [mul_left_comm, mul_assoc (Finset.prod _ _), ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  have e := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
    expo_row idx hs h₁ h₂ (y₁ k) (y₂ k) (z k) (w k)
  simp only [Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin n))), ← Finset.mul_sum,
    hermForm_Hm, ← map_sum, ← Rat.cast_sum] at e
  simp only [← Finset.mul_sum, map_neg, map_mul, conj_ofReal, expo]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset X.Ψ))]
  exact (by intro _ _ _ _ _ _ h; rw [h]; ring : ∀ a b c d e f : ℂ,
    f = a + b + c + 2 * I * d + I * e →
      -(π * a) + -(π * b) + π * f = π * c + (2 * π * I * d + π * I * e)) _ _ _ _ _ _ e

theorem dbl_lin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → (∀ ψ, IsSB ψ → dbl X bas idx (φ₁ + ψ) φ₂ = dbl X bas idx φ₁ φ₂ + dbl X bas idx ψ φ₂ ∧ dbl X bas idx φ₁ (φ₂ + ψ) = dbl X bas idx φ₁ φ₂ + dbl X bas idx φ₁ ψ) ∧ (∀ a b : ℂ, dbl X bas idx (a • φ₁) (b • φ₂) = (a * conj b) • dbl X bas idx φ₁ φ₂) ∧ ∀ y₁ y₂ : Matrix (Fin n) (Fin r) E, dbl X bas idx (heisG X bas y₁ φ₁) (heisG X bas y₂ φ₂) = heisH (Matrix.fromCols y₁ y₂ * dblT X).toCols₁ (Matrix.fromCols y₁ y₂ * dblT X).toCols₂ (dbl X bas idx φ₁ φ₂) := by
  intro E _ _ _ r X g bas idx n hs hn φ₁ φ₂ hφ₁ hφ₂
  have ex := GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hs hn
  obtain ⟨s, d, -⟩ := ex φ₁ φ₂ hφ₁ hφ₂
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun a b => ?_, fun y₁ y₂ => ?_⟩
  · obtain ⟨s', d', -⟩ := ex ψ φ₂ hψ hφ₂
    refine ((ex _ _ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hφ₁ hψ).1 hφ₂).2.2 _ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ s s').1
      fun x₁ h₁ x₂ h₂ z w => ?_).symm
    obtain ⟨hΨ, hZ, -⟩ := dblZ_mem_Hn E r X x₁ h₁ x₂ h₂
    rw [thA_add idx hs h₁ hφ₁ hψ, thH_add hΨ s s' hZ, add_mul, mul_add, d x₁ h₁ x₂ h₂,
      d' x₁ h₁ x₂ h₂]
  · obtain ⟨s', d', -⟩ := ex φ₁ ψ hφ₁ hψ
    refine ((ex _ _ hφ₁ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hφ₂ hψ).1).2.2 _ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ s s').1
      fun x₁ h₁ x₂ h₂ z w => ?_).symm
    obtain ⟨hΨ, hZ, -⟩ := dblZ_mem_Hn E r X x₁ h₁ x₂ h₂
    rw [thA_add idx hs h₂ hφ₂ hψ, thH_add hΨ s s' hZ, map_add, mul_add, mul_add, d x₁ h₁ x₂ h₂,
      d' x₁ h₁ x₂ h₂]
  · refine ((ex _ _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hφ₁ hφ₁).2.1 a)
      ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hφ₂ hφ₂).2.1 b)).2.2 _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ s s).2.1 _)
      fun x₁ h₁ x₂ h₂ z w => ?_).symm
    rw [thA_smul, thA_smul, thH_smul, map_mul, mul_mul_mul_comm, d x₁ h₁ x₂ h₂, mul_left_comm]
  · have hG := (heisG_laws E r X g bas idx n hs hn).2.2.2
    rw [DblPer.cols, toCols₁_fromCols, toCols₂_fromCols]
    exact ((ex _ _ (hG y₁ φ₁ hφ₁).1 (hG y₂ φ₂ hφ₂).1).2.2 _
      (GlobalTheory.T.hermitianHeisenbergOperator_laws E X.Ψ X.cmType n r hn _ _ _ s).1 (isDbl_heis idx hs hn hφ₁ hφ₂ s d y₁ y₂)).symm

end Main

end GlobalTheory.SW.DblLin
