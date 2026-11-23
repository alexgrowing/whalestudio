import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

theorem phiQ_eq_viaRed_qLoc : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b k : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu ξ⁻¹ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v k mu Y = viaRed r (qLoc k PP ξ) Y := by
  intro D v φ PP r hr a b k mu ξ hmu Y
  classical
  unfold phiQ viaRed
  by_cases hint : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F
  swap
  · rw [dif_neg hint, dif_neg (fun h => hint h.2.2.1)]
  rw [dif_pos hint]

  set Yo : Matrix (Fin b) (Fin a) (v.adicCompletionIntegers D.host.F) := fun i j => ⟨Y i j, hint i j⟩ with hYo
  have hy : (Matrix.of fun i j => r ⟨Y i j, hint i j⟩) = Yo.map r := rfl
  have htopY : topL k Y = (topL k Yo).map (v.adicCompletionIntegers D.host.F).subtype := by
    ext i j
    simp only [topL, Matrix.map_apply]
    split_ifs <;> simp [Yo]
  have htopy : topL k (Yo.map r) = (topL k Yo).map r := by
    ext i j
    simp only [topL, Matrix.map_apply]
    split_ifs <;> simp
  set d := (topL k Yo).det with hd
  have hdetY : (topL k Y).det = (d : Fv D.host.F v) := by
    rw [htopY]; exact (RingHom.map_det (v.adicCompletionIntegers D.host.F).subtype _).symm
  have hdety : (topL k (Yo.map r)).det = r d := by
    rw [htopy]; exact (RingHom.map_det r _).symm
  have hle : Valued.v (d : Fv D.host.F v) ≤ 1 := d.2
  have hunit : IsUnit (r d) ↔ Valued.v (d : Fv D.host.F v) = 1 := by
    constructor
    · intro hu
      refine le_antisymm hle (not_lt.mp fun hlt => ?_)
      exact hu.ne_zero ((hr.2.1 d).mpr hlt)
    · intro h1
      have hne : (d : Fv D.host.F v) ≠ 0 := by
        intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
      have hinv : ((d : Fv D.host.F v))⁻¹ ∈ v.adicCompletionIntegers D.host.F := by
        show Valued.v ((d : Fv D.host.F v))⁻¹ ≤ 1
        rw [map_inv₀, h1, inv_one]
      have hdu : IsUnit d := by
        refine ⟨⟨d, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩ <;> ext <;> simp [hne]
      exact hdu.map r
  have hlow : LowZero k (Yo.map r) ↔ ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1 := by
    unfold LowZero
    refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => forall_congr' fun _ => ?_
    exact hr.2.1 (Yo i j)
  rw [hy]
  unfold qLoc
  by_cases hc : Valued.v (d : Fv D.host.F v) = 1 ∧ ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1
  · have hA : IsUnit (topL k Y).det ∧ Valued.v (topL k Y).det = 1 ∧ (∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F) ∧
        ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1 := by
      refine ⟨?_, by rw [hdetY]; exact hc.1, hint, hc.2⟩
      rw [hdetY, isUnit_iff_ne_zero]
      intro h0; have := hc.1; rw [h0, map_zero] at this; exact zero_ne_one this
    have hB : LowZero k (Yo.map r) ∧ IsUnit (topL k (Yo.map r)).det :=
      ⟨hlow.mpr hc.2, by rw [hdety]; exact hunit.mpr hc.1⟩
    rw [dif_pos hA, dif_pos hB]
    have hrel : RedRel φ PP ((hA.1.unit : Fv D.host.F v)) ((hB.2.unit : Formalism.L2.DIV.kP PP)) := by
      refine (hr.2.2.1 _ _).mpr ⟨by convert d.2 using 2; rw [IsUnit.unit_spec, hdetY], ?_⟩
      rw [IsUnit.unit_spec hB.2, hdety]
      congr 1
      apply Subtype.ext
      simp [IsUnit.unit_spec, hdetY]
    have hm := hmu _ _ hrel
    rw [hm, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
  · rw [dif_neg (fun h => hc ⟨by rw [← hdetY]; exact h.2.1, h.2.2.2⟩),
      dif_neg (fun h => hc ⟨hunit.mp (by rw [← hdety]; exact h.2), hlow.mp h.1⟩)]

end GlobalTheory.StepVec
