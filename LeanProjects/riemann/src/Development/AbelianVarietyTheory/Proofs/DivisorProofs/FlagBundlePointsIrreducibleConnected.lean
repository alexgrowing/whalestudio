import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsConnectedIrreducibleBaseStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagConnect

theorem exists_irreducible_through : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → ∀ (L : Type) [Field L] (q₁ q₂ : Spec (CommRingCat.of L) ⟶ Y), q₁ ≫ π = q₂ ≫ π → ∃ (T : Scheme.{0}) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (f : T ⟶ Y), IrreducibleSpace T ∧ t₁ ≫ f = q₁ ∧ t₂ ≫ f = q₂ := by
  intro B Y π ι _ E r fl _ hF L _ q₁ q₂ hq
  obtain ⟨T, g, t₁, t₂, G, v₁, v₂, hT, h₁, h₂⟩ := GlobalTheory.T.flags_connected_irreducible_base L B (q₁ ≫ π) ι E r
    (carried π E r fl q₁ (q₁ ≫ π) rfl) (carried π E r fl q₂ (q₁ ≫ π) hq.symm)
  obtain ⟨f, ⟨wf, hf⟩, -⟩ := hF T g G
  have key : ∀ (q : Spec (CommRingCat.of L) ⟶ Y) (hq' : q ≫ π = q₁ ≫ π) (t : Spec (CommRingCat.of L) ⟶ T)
      (v : t ≫ g = q₁ ≫ π), Carries g E r G t (q₁ ≫ π) v (carried π E r fl q (q₁ ≫ π) hq') → t ≫ f = q := by
    intro q hq' t v ht
    obtain ⟨x, -, hx⟩ := hF _ (q₁ ≫ π) (carried π E r fl q (q₁ ≫ π) hq')
    have e₁ := hx q ⟨hq', carries_carried π E r fl q _ hq'⟩
    have e₂ := hx (t ≫ f) ⟨by rw [Category.assoc, wf, v], carries_comp π E r fl f g wf G t _ v _ _ hf ht⟩
    rw [e₁, e₂]
  exact ⟨T, t₁, t₂, f, hT, key q₁ rfl t₁ v₁ h₁, key q₂ hq.symm t₂ v₂ h₂⟩

end GlobalTheory.FlagConnect

end
