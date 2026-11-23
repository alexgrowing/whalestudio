import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Mathlib.Topology.Algebra.ClopenNhdofOne

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.coset :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (V : Set Γ), IsOpen V → ∀ g ∈ V, ∃ H : Subgroup Γ, H.Normal ∧ IsOpen (H : Set Γ) ∧ ∀ h ∈ H, g * h ∈ V := by
  intro Γ _ _ _ _ _ V hV g hg
  have hU : IsOpen ((fun x : Γ => g * x) ⁻¹' V) := hV.preimage (continuous_const_mul g)
  have h1 : (1 : Γ) ∈ (fun x : Γ => g * x) ⁻¹' V := by simpa using hg
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  exact ⟨H.toSubgroup, H.isNormal', H.isOpen', fun h hh => hH hh⟩
