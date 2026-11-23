import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedPullConstMorVPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfSumMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory

theorem eigen_components_mod_stable {k : Type} [Field k] {H : Type 1} [AddCommGroup H] [Module k H]
    {O : Type} [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H)
    (hF : ∀ c, ∀ x ∈ F, ρ c x ∈ F) {a : ℕ} (χ : Fin a → O → k)
    (hχ : ∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) (S : Finset (Fin a)) :
    ∀ u : Fin a → H, (∀ i ∈ S, ∀ c, ρ c (u i) - χ i c • u i ∈ F) →
      ∑ i ∈ S, u i ∈ F → ∀ i ∈ S, u i ∈ F := by
  first
  | exact @_root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem
  | exact _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem
  | (apply _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MembershipOfSum.mem_of_sum_mem ..)

theorem eigen_mod_stable : ∀ (k : Type) [Field k] (H : Type 1) [AddCommGroup H] [Module k H] (O : Type) [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H), (∀ c, ∀ x ∈ F, ρ c x ∈ F) → ∀ (a : ℕ) (χ : Fin a → O → k), (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → ∀ u : Fin a → H, (∀ i c, ρ c (u i) - χ i c • u i ∈ F) → ∑ i, u i ∈ F → ∀ i, u i ∈ F := by
  intro k _ H _ _ O _ ρ F hF a χ hχ u hu hs i
  exact eigen_components_mod_stable ρ F hF χ hχ Finset.univ u (fun i _ c => hu i c) hs i (Finset.mem_univ i)

end GlobalTheory
