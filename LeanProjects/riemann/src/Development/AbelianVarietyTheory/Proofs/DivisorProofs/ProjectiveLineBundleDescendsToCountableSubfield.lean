import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfield
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ProjCountableDescent

open GlobalTheory.PolCountableDescent in

theorem projLB_descends_to_countable_subfield : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∀ (L : LB X), L.IsLB → ∃ (K₁ : Subfield K) (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (ψ : X ⟶ X₁) (L₁ : LB X₁), Countable K₁ ∧ IsProjOver p₁ ∧ IsPullback ψ p p₁ (spMap (algebraMap K₁ K)) ∧ L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  intro K _ X p hp L hL
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ X p hp
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ X p₀ p φ L hL sq
  let s : Finset K := s₀ ∪ s₂
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  have sq₁ : IsPullback (pullback.fst p₀ inc) (pullback.snd p₀ inc) p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : X ⟶ pullback p₀ inc := sq₁.lift φ (p ≫ spMap K₁.subtype)
    (by rw [Category.assoc, spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ pullback.fst p₀ inc = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd p₀ inc = p ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨L₁, hL₁, hI⟩ := H₂ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) _ _ _ ψ
    sq₁ hψ₁ hψ₂
  refine ⟨K₁, _, pullback.snd p₀ inc, ψ, L₁, countable_closure s,
    ProjSpace.isProjOver_pullback_snd _ hp₀, ?_, hL₁, hI⟩
  refine IsPullback.of_right (t := sq₁) ?_ hψ₂
  have e : spMap (algebraMap K₁ K) ≫ inc = spMap K₀.subtype := spMap_subtype_comp h
  rw [hψ₁, e]
  exact sq

end GlobalTheory.ProjCountableDescent
