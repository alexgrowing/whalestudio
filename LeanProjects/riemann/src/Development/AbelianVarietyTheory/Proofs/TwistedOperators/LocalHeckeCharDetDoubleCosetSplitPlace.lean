import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetVal

open Formalism.L2.Host (IsUnitAt IsUnifAt)

theorem isUnitAt_det_of_mem_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ GlobalTheory.LFun.KGL w n) :
    IsUnitAt w (Matrix.GeneralLinearGroup.det k) := by
  unfold GlobalTheory.LFun.KGL at hk
  obtain ⟨k', rfl⟩ := hk
  set c := Matrix.GeneralLinearGroup.det k' with hc
  have hdc : ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc (Formalism.UG.Ov E w).subtype k') :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = ((c : Formalism.UG.Ov E w) : w.adicCompletion E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hc, Matrix.GeneralLinearGroup.val_det_apply]
    unfold Formalism.UG.bc
    rw [Units.coe_map]
    exact (RingHom.map_det _ _).symm
  have hle : ∀ y : Formalism.UG.Ov E w, Valued.v (y : w.adicCompletion E) ≤ 1 := fun y =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers ..).1 y.2
  have h3 : Valued.v ((c : Formalism.UG.Ov E w) : w.adicCompletion E) *
      Valued.v ((↑c⁻¹ : Formalism.UG.Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
  unfold Formalism.L2.Host.IsUnitAt
  rw [hdc]
  refine le_antisymm (hle _) ?_
  rw [← h3]
  exact mul_le_of_le_one_right' (hle _)

theorem locChar_det_doubleCoset : ∀ (D : D7) (T : HSp D) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), UnrAt χ w → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ((locChar χ w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)))) : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ (∑ i, d i) := by
  intro D T χ v w h hχ e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨⟨a, -, hea⟩, -⟩ := he
  have hloc : ∀ g, locMat D.sp.cm.sig T.gram h g = a * e g * a⁻¹ := fun g => by
    rw [hea g]
    group
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    unfold IsUnifV at hϖ
    simp at hϖ
  set u : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ hϖ0 with hu
  have hprod : ∀ s : Finset (Fin T.rank), ∏ i ∈ s, u ^ d i = u ^ ∑ i ∈ s, d i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, _root_.zpow_add]
  have hdt : Matrix.GeneralLinearGroup.det t = u ^ ∑ i, d i := by
    rw [← hprod]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, ht, Matrix.det_diagonal, Units.coe_prod]
    simp only [Units.val_zpow_eq_zpow_val, hu, Units.val_mk0]
  have hdet : Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂))) =
      Matrix.GeneralLinearGroup.det k₁ * u ^ (∑ i, d i) * Matrix.GeneralLinearGroup.det k₂ := by
    simp only [hloc, MulEquiv.apply_symm_apply, map_mul, map_inv, hdt]
    rw [mul_comm (Matrix.GeneralLinearGroup.det a), mul_inv_cancel_right]
  have hunif := hχ.locChar_eq_val (x := u) (by
    show Valued.v (u : w.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ)
    rw [hu, Units.val_mk0, hϖ]
    rfl)
  rw [hdet, map_mul, map_mul, hχ _ (isUnitAt_det_of_mem_KGL _ hk₁), hχ _ (isUnitAt_det_of_mem_KGL _ hk₂),
    one_mul, mul_one, map_zpow, hunif, Units.val_zpow_eq_zpow_val]

end GlobalTheory.DetVal
