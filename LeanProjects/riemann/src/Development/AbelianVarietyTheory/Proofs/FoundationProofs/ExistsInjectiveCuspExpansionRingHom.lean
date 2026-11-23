import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionAtInfinityOfSomeLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

variable {Ω : Type} [Field Ω] (ε : Ω →+* ℂ)

theorem exists_isExp_of_mem_ring (a : ring ε.range) : ∃ h : HahnSeries ℚ Ω, IsExp ε a h :=
  GlobalTheory.T.exists_cuspExpansionAtInfinity_of_someLevel Ω ε a (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2)

def expan (a : ring ε.range) : HahnSeries ℚ Ω := Classical.choose (exists_isExp_of_mem_ring ε a)

theorem isExp_expan (a : ring ε.range) : IsExp ε a (expan ε a) :=
  Classical.choose_spec (exists_isExp_of_mem_ring ε a)

theorem expan_eq_of_isExp {a : ring ε.range} {h : HahnSeries ℚ Ω} (ha : IsExp ε a h) : expan ε a = h :=
  (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 _ _ _ (isExp_expan ε a) ha

def expanHom : ring ε.range →+* HahnSeries ℚ Ω where
  toFun := expan ε
  map_one' := by
    apply expan_eq_of_isExp
    have h := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.1 1
    have e1 : ((1 : ring ε.range) : ℍ → ℂ) = fun _ => ε 1 := by ext; simp
    rw [e1]; simpa using h
  map_mul' a b := by
    apply expan_eq_of_isExp
    have h := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.2
    simpa using h
  map_zero' := by
    apply expan_eq_of_isExp
    have h := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.1 0
    have e0 : ((0 : ring ε.range) : ℍ → ℂ) = fun _ => ε 0 := by ext; simp
    rw [e0]; simpa using h
  map_add' a b := by
    apply expan_eq_of_isExp
    have h := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).1
    simpa using h

theorem expanHom_injective : Function.Injective (expanHom ε) := by
  intro a b hab
  have hsub := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.1
  have h0 : expan ε a - expan ε b = 0 := sub_eq_zero.mpr hab
  rw [h0] at hsub
  have hmem : ((a - b : ring ε.range) : ℍ → ℂ) ∈ ring ε.range := (a - b).2
  have hin : InR ε.range ((a - b : ring ε.range) : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 hmem
  have hhol := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ε.range _ hin
  push_cast at hhol
  have := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.2.1 _ hhol hsub
  exact Subtype.ext (sub_eq_zero.mp this)

theorem expansion_injective_ringHom :
    ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω,
      Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) :=
  fun _ _ ε => ⟨expanHom ε, expanHom_injective ε, isExp_expan ε⟩

end GlobalTheory.FN
