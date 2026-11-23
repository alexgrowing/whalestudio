import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import GroundTheory.AutomorphicForms.AffineBruhat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
import Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriGl
import Development.AutomorphicArithmetic.IwahoriCommensurability.AffineWeylSimpleReflectionCoset

set_option autoImplicit false

noncomputable section

open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

namespace UpperTheory.Gal.Spc.Iw

private def LI {G : Type} [Group G] (K : Subgroup G) (g : G) : Prop :=
  ∃ φ ∈ Hecke ℂ K, conv K φ (dosetInd ℂ K g) = dosetInd ℂ K 1

private theorem LI.congr {G : Type} [Group G] {K : Subgroup G} {g g' : G}
    (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) (hg : LI K g) : LI K g' := by
  have e : dosetInd ℂ K g' = dosetInd ℂ K g := by
    unfold dosetInd
    rw [DoubleCoset.doubleCoset_eq_of_mem h]
  unfold LI
  rw [e]
  exact hg

private theorem LI.one {G : Type} [Group G] (K : Subgroup G) : LI K (1 : G) :=
  ⟨_, Final.DosetIndMem G K ℂ 1, (Final.HeckeUnit G K ℂ _ (Final.DosetIndMem G K ℂ 1)).1⟩

private def Qr {G : Type} [Group G] (K : Subgroup G) (g : G) : Prop := ∀ h, LI K h → LI K (h * g)

private theorem Qr.one {G : Type} [Group G] (K : Subgroup G) : Qr K (1 : G) := fun h hh => by simpa using hh

private theorem Qr.mul {G : Type} [Group G] {K : Subgroup G} {g g' : G} (a : Qr K g) (b : Qr K g') : Qr K (g * g') :=
  fun h hh => by simpa [mul_assoc] using b _ (a h hh)

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)

private abbrev tau : GL (Fin (m + 1)) k :=
  diagPow k (m + 1) (Pi.mulSingle (Fin.last m) (Multiplicative.ofAdd 1)) * permGL k (finRotate (m + 1))⁻¹

private def goodDiag : Subgroup (Fin (m + 1) → Multiplicative ℤ) where
  carrier := {a | Qr (iwahori k (m + 1)) (diagPow k (m + 1) a) ∧ Qr (iwahori k (m + 1)) (diagPow k (m + 1) a⁻¹)}
  one_mem' := by simpa using Qr.one _
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simpa using ha.mul hb, ?_⟩
    rw [_root_.mul_inv_rev, map_mul]
    exact hb'.mul ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa using ha⟩

end Local

end UpperTheory.Gal.Spc.Iw
