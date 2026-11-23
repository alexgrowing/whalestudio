import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentQuotientUnitVolumeStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.DescB.NextStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eq_zero_of_two_laws {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {χa χb : Chr F E}
    {za zb : ℝ} (hz : za < zb)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H t 1 m ∧ 1 < (absE F E t : ℝ))
    {T : UA σ W.J → ℂ} (ha : HasLaw W₁ H χa za T) (hb : HasLaw W₁ H χb zb T) : T = 0 := by
  obtain ⟨t, m, hm, ht⟩ := hlevi
  funext h
  show T h = 0
  by_contra hne
  have e1 := ha t m hm h
  have e2 := hb t m hm h
  have e : (χa t : ℂ) * (((absE F E t : ℝ) ^ za : ℝ) : ℂ) = (χb t : ℂ) * (((absE F E t : ℝ) ^ zb : ℝ) : ℂ) :=
    mul_right_cancel₀ hne (e1.symm.trans e2)
  have n := congrArg norm e
  rw [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _),
    abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n
  exact (Real.rpow_lt_rpow_of_exponent_lt ht hz).ne n

theorem skew_gram (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (ι : Matrix (Fin n) (Fin n₁) E) :
    ∀ k l, σ ((ιᵀ * J * ι.map σ) l k) = -(ιᵀ * J * ι.map σ) k l := by
  intro k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, Finset.sum_mul]
  simp only [hJ]
  refine Finset.sum_comm.trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

end GlobalTheory.ThK.DescB.NextStep

namespace GlobalTheory.ThK.DescB.NextStep

open GlobalTheory.LeviLine Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_levi_of {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} (hcm : IsCMExt F E σ)
    (hskew : ∀ i j, σ (Y.J j i) = -Y.J i j) (hxx' : form σ Y.J H.x H.x = 0) (hyy' : form σ Y.J H.y H.y = 0)
    (hxy' : form σ Y.J H.x H.y = 1)
    (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) :
    ∃ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m ∧ 1 < (absE F E t : ℝ) := by
  set c : AE F E →+* AE F E := (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom with hcdef
  have hc : ∀ r, c (c r) = r := cA_invol hcm
  have hJ : ∀ i j, c (incM F Y.J j i) = -incM F Y.J i j := by
    intro i j
    change cA σ (inclR (F := F) (AF F) (Y.J j i)) = -inclR (F := F) (AF F) (Y.J i j)
    rw [cA_inclR, hskew i j, map_neg]
  have hxx : sf c (incM F Y.J) (incV F H.x) (incV F H.x) = 0 := by rw [sf_inc, hxx', map_zero]
  have hyy : sf c (incM F Y.J) (incV F H.y) (incV F H.y) = 0 := by rw [sf_inc, hyy', map_zero]
  have hxy : sf c (incM F Y.J) (incV F H.x) (incV F H.y) = 1 := by rw [sf_inc, hxy', map_one]
  have hyx : sf c (incM F Y.J) (incV F H.y) (incV F H.x) = -1 := by rw [sf_skew c _ hc hJ, hxy, map_one]
  set t : (AE F E)ˣ := (GlobalTheory.Eis.Conv.halfE F E)⁻¹ with htdef
  have hts : (t : AE F E) * c (c (↑t⁻¹ : AE F E)) = 1 := by rw [hc, Units.mul_inv]
  have hst : c (↑t⁻¹ : AE F E) * c (t : AE F E) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  let L := levi c (incM F Y.J) (incV F H.x) (incV F H.y)
  let g : GL (Fin n) (AE F E) :=
    ⟨L t (c ↑t⁻¹), L ↑t⁻¹ (c t), by
      rw [levi_mul hc hJ hxx hyy hxy, Units.mul_inv, ← map_mul, Units.inv_mul, map_one, levi_one],
      by rw [levi_mul hc hJ hxx hyy hxy, Units.inv_mul, ← map_mul, Units.mul_inv, map_one, levi_one]⟩
  have hg : g ∈ UG (cA σ) (incM F Y.J) := levi_unitary hc hJ hxx hyy hxy hts hst
  refine ⟨t, ⟨g, hg⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · change L t (c ↑t⁻¹) *ᵥ incV F H.x = _
    rw [levi_mulVec, hxx, hxy]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) *ᵥ incV F H.y = c ↑t⁻¹ • incV F H.y
    rw [levi_mulVec, hyy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) * incM F H.ι = incM F H.ι * (1 : Matrix (Fin n₁) (Fin n₁) (AE F E))
    rw [Matrix.mul_one]
    refine ext_mulVec_single fun k => ?_
    have hcol : incM F H.ι *ᵥ Pi.single k 1 = incV F (H.ι *ᵥ Pi.single k 1) := by
      ext i
      simp [mulVec_single_one, incM, incV]
    rw [← mulVec_mulVec, hcol]
    exact levi_mulVec_of_orth _ _ _ _ (by rw [sf_inc, (horth _).1, map_zero]) (by rw [sf_inc, (horth _).2, map_zero])
  · have h1 := GlobalTheory.Eis.Conv.absE_halfE F E σ hcm
    have h2 : absE F E t * absE F E (GlobalTheory.Eis.Conv.halfE F E) = 1 := by
      rw [← map_mul, htdef, inv_mul_cancel, map_one]
    rw [h1] at h2
    have h3 : absE F E t = (4 : ℝ≥0) ^ Fintype.card (InfinitePlace F) := by
      rw [← mul_one (absE F E t), ← inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (4 : ℝ≥0) ≠ 0)), ← mul_assoc, h2, one_mul]
    rw [h3]
    have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    push_cast
    exact one_lt_pow₀ (by norm_num) hpos.ne'

theorem skew_sp (hσ : ∀ x, σ (σ x) = x) (B : Base F E) {d d₁ p : ℕ} {W : Spc F E d} (hW : ∀ i j, σ (W.J j i) = -W.J i j)
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
    {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} (hH : H'.IsAdapted σ B W (sp 0) i₀ i₁)
    (hiso : ∀ i < p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) :
    ∀ j ≤ p, ∀ k l, σ ((sp j).J l k) = -(sp j).J k l := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [← hH.gram]
    exact skew_gram hσ hW H'.ι
  | succ j ih =>
    intro hj
    rw [← (hiso j (by omega)).2.2.2.2.2.1]
    exact skew_gram hσ (ih (by omega)) (pl j).ι

end GlobalTheory.ThK.DescB.NextStep

namespace GlobalTheory.ThK.DescB.NextStep

open GlobalTheory.LeviLine

end GlobalTheory.ThK.DescB.NextStep
