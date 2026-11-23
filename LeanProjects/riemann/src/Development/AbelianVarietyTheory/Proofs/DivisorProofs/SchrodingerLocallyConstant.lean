import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct GlobalTheory.VacAny
open Matrix

namespace GlobalTheory.SchrSmall

theorem schr_eventually_eq : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ φ ∈ SB (κ → Fv F v), ∀ᶠ w in nhds (0 : (κ → Fv F v) × (κ → Fv F v)), schr ψ w φ = φ := by
  intro F _ _ κ _ v ψ hψ φ hφ
  have hψl : IsLocallyConstant ψ := GlobalTheory.SchrSB.isLocallyConstant_addChar ψ hψ
  obtain ⟨hφl, hφc⟩ := hφ
  have hd : ∀ {Z : Type} [TopologicalSpace Z] {a b : Z → (κ → Fv F v)}, Continuous a → Continuous b →
      Continuous fun z => a z ⬝ᵥ b z := fun ha hb => ha.dotProduct hb
  have key : ∀ y ∈ tsupport φ, ∀ᶠ z : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) in
      nhds ((0 : (κ → Fv F v) × (κ → Fv F v)), y),
      (ψ (z.2 ⬝ᵥ z.1.2 + ⅟(2 : Fv F v) * (z.1.1 ⬝ᵥ z.1.2)) = 1 ∧ φ (z.2 + z.1.1) = φ z.2) ∧
      (ψ ((z.2 - z.1.1) ⬝ᵥ z.1.2 + ⅟(2 : Fv F v) * (z.1.1 ⬝ᵥ z.1.2)) = 1 ∧ φ (z.2 - z.1.1) = φ z.2) := by
    intro y _
    have c1 : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) =>
        z.2 ⬝ᵥ z.1.2 + ⅟(2 : Fv F v) * (z.1.1 ⬝ᵥ z.1.2) :=
      (hd continuous_snd (continuous_snd.comp continuous_fst)).add
        (continuous_const.mul (hd (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst)))
    have c2 : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) =>
        (z.2 - z.1.1) ⬝ᵥ z.1.2 + ⅟(2 : Fv F v) * (z.1.1 ⬝ᵥ z.1.2) :=
      (hd (continuous_snd.sub (continuous_fst.comp continuous_fst)) (continuous_snd.comp continuous_fst)).add
        (continuous_const.mul (hd (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst)))
    have c3 : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) => z.2 + z.1.1 :=
      continuous_snd.add (continuous_fst.comp continuous_fst)
    have c4 : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) => z.2 - z.1.1 :=
      continuous_snd.sub (continuous_fst.comp continuous_fst)
    have e1 := (hψl.comp_continuous c1).eventually_eq (x := ((0 : (κ → Fv F v) × (κ → Fv F v)), y))
    have e2 := (hψl.comp_continuous c2).eventually_eq (x := ((0 : (κ → Fv F v) × (κ → Fv F v)), y))
    have e3 := (hφl.comp_continuous c3).eventually_eq (x := ((0 : (κ → Fv F v) × (κ → Fv F v)), y))
    have e4 := (hφl.comp_continuous c4).eventually_eq (x := ((0 : (κ → Fv F v) × (κ → Fv F v)), y))
    have e5 := (hφl.comp_continuous continuous_snd).eventually_eq (x := ((0 : (κ → Fv F v) × (κ → Fv F v)), y))
    filter_upwards [e1, e2, e3, e4, e5] with z h1 h2 h3 h4 h5
    simp only [Function.comp_apply, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, mul_zero, add_zero, sub_zero,
      AddChar.map_zero_eq_one] at h1 h2 h3 h4 h5
    exact ⟨⟨h1, h3.trans h5.symm⟩, ⟨h2, h4.trans h5.symm⟩⟩
  have h := hφc.eventually_forall_of_forall_eventually (x₀ := (0 : (κ → Fv F v) × (κ → Fv F v)))
    (P := fun (w : (κ → Fv F v) × (κ → Fv F v)) (y : κ → Fv F v) =>
      (ψ (y ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) = 1 ∧ φ (y + w.1) = φ y) ∧
      (ψ ((y - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) = 1 ∧ φ (y - w.1) = φ y)) key
  filter_upwards [h] with w hw
  funext x
  simp only [schr]
  by_cases hx : x ∈ tsupport φ
  · obtain ⟨⟨h1, h2⟩, -⟩ := hw x hx
    rw [h1, h2, one_mul]
  by_cases hx' : x + w.1 ∈ tsupport φ
  · obtain ⟨-, ⟨h1, h2⟩⟩ := hw _ hx'
    simp only [add_sub_cancel_right] at h1 h2
    rw [h1, ← h2, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx', image_eq_zero_of_notMem_tsupport hx, mul_zero]

end GlobalTheory.SchrSmall
