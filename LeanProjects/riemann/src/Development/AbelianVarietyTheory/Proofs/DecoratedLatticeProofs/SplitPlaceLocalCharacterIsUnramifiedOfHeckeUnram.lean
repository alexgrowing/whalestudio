import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSectionAddComplementMul

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinUnram

open GlobalTheory.SplitLinAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem off_idl (p : SplitPt D k) (a : kˣ) : (1 - p.e) * ((idl p a : (AE D)ˣ) : AE D) = 1 - p.e := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p (a : k)
  rw [idl_val]
  linear_combination (-1 : AE D) * ha + he

theorem e_mul_idl (p : SplitPt D k) (a : kˣ) : p.e * ((idl p a : (AE D)ˣ) : AE D) = p.sec a := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p (a : k)
  rw [idl_val]
  linear_combination ha - he

theorem map_e_eq_zero (p : SplitPt D k) {R : Type} [CommRing R] (f : AE D →+* R) (h : f (p.e + cA D p.e) = 0) :
    f p.e = 0 := by
  have h1 : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, p.split.1, p.split.2.1, add_zero]
  rw [h1, RingHom.map_mul, h, mul_zero]

theorem infPart_e (p : SplitPt D k) : infPart D p.e = 0 := by
  obtain ⟨ε, ⟨α, hε, -, -⟩, h⟩ := p.above
  refine map_e_eq_zero p _ ?_
  rw [h, hε]
  change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem compAt_e (p : SplitPt D k) {w : Pl D} (hw : w ≠ p.v) : compAt D w p.e = 0 := by
  obtain ⟨ε, ⟨α, hε, -, h0⟩, h⟩ := p.above
  refine map_e_eq_zero p _ ?_
  rw [h, hε]
  change evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  rw [h0 w hw]
  exact TensorProduct.zero_tmul _ _

theorem idl_int (p : SplitPt D k) {a : kˣ} (ha : (a : k) ∈ 𝒪[k]) :
    finPart D ((idl p a : (AE D)ˣ) : AE D) ∈ intAE D := by
  rw [idl_val, RingHom.map_add, RingHom.map_sub, RingHom.map_one]
  refine add_mem ((p.int_iff _).1 ha) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)) ?_)
  rw [← sec_one]
  exact (p.int_iff 1).1 (one_mem _)

theorem absFin_idl (p : SplitPt D k) {a : kˣ} (ha : (a : k) ∈ 𝒪[k]) (ha' : ((a⁻¹ : kˣ) : k) ∈ 𝒪[k]) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) = 1 := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart p.e p.split
  have key : ∀ b : kˣ, (b : k) ∈ 𝒪[k] →
      Valued.v ((Units.map π.toMonoidHom (idl p b) : (Fv D.host.F v)ˣ) : Fv D.host.F v) ≤ 1 := fun b hb =>
    GlobalTheory.SplitHecke.isInt_Ov.1 ((hπ.2.2.2 _).1 (by rw [e_mul_idl]; exact (p.int_iff _).1 hb))
  have a1 := key a ha
  have a2 := key _ ha'
  rw [GlobalTheory.SplitLinear.absFin_split D p.e v π p.split hπ _ (off_idl p a)]
  rw [MonoidHom.map_inv, MonoidHom.map_inv] at a2
  generalize Units.map π.toMonoidHom (idl p a) = y at a1 a2 ⊢
  have hne : Valued.v (y : Fv D.host.F v) ≠ 0 := by simp
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hne)] at a2
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, le_antisymm a1 a2]

theorem lam_unram : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ p.v → IsUnram (GlobalTheory.SplitLinAt.lam p χ r) := by
  intro D k _ _ _ _ p χ r hχ a ha
  have h1 : (a : k) ∈ 𝒪[k] := ha.le
  have h2 : ((a⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
    change valuation k ((a⁻¹ : kˣ) : k) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]
  have h3 : χ (idl p a) = 1 :=
    hχ _ (GlobalTheory.SplitLinear.off_norm'' _ (infPart_e p) (off_idl p a))
      (fun w hw => GlobalTheory.SplitLinear.off_norm'' (compAt D w) (compAt_e p hw) (off_idl p a)) (idl_int p h1)
      (by rw [← MonoidHom.map_inv]; exact idl_int p h2)
  refine Units.ext ?_
  rw [lam_val, h3, absFin_idl p h1 h2, Real.one_rpow]
  simp

end GlobalTheory.SplitLinUnram
end
