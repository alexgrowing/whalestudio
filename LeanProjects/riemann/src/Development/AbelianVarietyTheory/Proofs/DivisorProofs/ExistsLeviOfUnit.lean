import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCentreLawZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainEmbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.DescB.CentreTwoExists

open GlobalTheory.LeviLine Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_levi_of_unit (hcm : IsCMExt F E σ) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁)
    (hskew : ∀ i j, σ (Y.J j i) = -Y.J i j) (hxx' : form σ Y.J H.x H.x = 0) (hyy' : form σ Y.J H.y H.y = 0)
    (hxy' : form σ Y.J H.x H.y = 1)
    (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) (t : (AE F E)ˣ) :
    ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H t 1 m := by
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
  have hts : (t : AE F E) * c (c (↑t⁻¹ : AE F E)) = 1 := by rw [hc, Units.mul_inv]
  have hst : c (↑t⁻¹ : AE F E) * c (t : AE F E) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  let L := levi c (incM F Y.J) (incV F H.x) (incV F H.y)
  let g : GL (Fin n) (AE F E) :=
    ⟨L t (c ↑t⁻¹), L ↑t⁻¹ (c t), by
      rw [levi_mul hc hJ hxx hyy hxy, Units.mul_inv, ← map_mul, Units.inv_mul, map_one, levi_one],
      by rw [levi_mul hc hJ hxx hyy hxy, Units.inv_mul, ← map_mul, Units.mul_inv, map_one, levi_one]⟩
  have hg : g ∈ UG (cA σ) (incM F Y.J) := levi_unitary hc hJ hxx hyy hxy hts hst
  refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
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

theorem skew_chain (hcm : IsCMExt F E σ) (B : Base F E) {d d₁ p : ℕ} {W : Spc F E d}
    (hW : ∀ i j, σ (W.J j i) = -W.J i j) {H' : Plane E d d₁} {i₀ i₁ : ℕ} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
    {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} (hH : H'.IsAdapted σ B W (sp 0) i₀ i₁)
    (hiso : ∀ i < p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) :
    ∀ j ≤ p, ∀ k l, σ ((sp j).J l k) = -(sp j).J k l := by
  intro j
  induction j with
  | zero =>
    intro _ k l
    rw [← hH.gram]
    exact LeviFirst.gram_skew hcm _ _ hW k l
  | succ j ih =>
    intro hj k l
    rw [← (hiso j (by omega)).2.2.2.2.2.1]
    exact LeviFirst.gram_skew hcm _ _ (ih (by omega)) k l

end GlobalTheory.ThK.DescB.CentreTwoExists

namespace GlobalTheory.ThK.DescB

open GlobalTheory.ThK.DescB.CentreTwoExists Matrix

end GlobalTheory.ThK.DescB

end
