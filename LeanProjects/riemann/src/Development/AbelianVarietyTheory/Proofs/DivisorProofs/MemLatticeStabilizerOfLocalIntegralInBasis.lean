import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

namespace StabilizerBasis
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.StabBasis

theorem exists_bc_eq_of_entries {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (g : GL (Fin n) R)
    (h1 : ∀ i j, g.1 i j ∈ S) (h2 : ∀ i j, g⁻¹.1 i j ∈ S) :
    ∃ y : GL (Fin n) S, Formalism.UG.bc S.subtype y = g := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) S => A.map S.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem mem_St_of_inBasis_mem_KO : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)),
    (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  intro D n β x h
  have hent : ∀ (w : Pl D.host.E) (g : GL (Fin n) (Kw w)), g ∈ KO (Kw w) (Fin n) →
      ∀ i j, g.1 i j ∈ Formalism.UG.Ov D.host.E w := by
    intro w g hg i j
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hg
    obtain ⟨u, rfl⟩ := hg
    exact (u.1 i j).2
  have e2 : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  have a1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j =>
    (mem_OA_iff _).2 fun w => by
      have := hent w _ (h w) i j
      rwa [inBasis_apply] at this
  have a2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j =>
    (mem_OA_iff _).2 fun w => by
      have := hent w _ ((KO (Kw w) (Fin n)).inv_mem (h w)) i j
      rw [← map_inv, inBasis_apply] at this
      rwa [e2]
  obtain ⟨y, hy⟩ := exists_bc_eq_of_entries _ _ a1 a2
  refine ⟨y, ?_⟩
  have e : Formalism.L2.DIV.intGL D.host.F D.host.E n y = β⁻¹ * x * β := hy
  show β * Formalism.L2.DIV.intGL D.host.F D.host.E n y * β⁻¹ = x
  rw [e]; group

end GlobalTheory.CompanionTheory.StabBasis

end
end

end StabilizerBasis
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)), (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  first | exact @StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO | exact StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO | (intros; apply StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO <;> assumption)

end
end
