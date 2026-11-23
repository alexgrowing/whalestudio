import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeCrystallineThickeningOneElementLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalProperties

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.FreeFin

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}

theorem isFree_id (n : ℕ) (T : Thick κ t) (hT : IsLev T.δ n) :
    IsFree n (𝟙 T) (Fin.elim0 : Fin 0 → T.B) := by
  refine ⟨hT, fun i ↦ i.elim0, fun S _ a c _ ↦ ⟨a, ⟨Category.id_comp a, fun i ↦ i.elim0⟩, ?_⟩⟩
  rintro g ⟨hg, -⟩
  rw [← hg, Category.id_comp]

theorem isFree_cons (n m : ℕ) {T F F' : Thick κ t} (u : T ⟶ F) (τ : Fin m → F.B) (hu : IsFree n u τ)
    (u' : F ⟶ F') (τ' : Unit → F'.B) (hu' : IsFree n u' τ') :
    IsFree n (u ≫ u') (Fin.cons (τ' ()) (fun i ↦ u'.φ (τ i)) : Fin (m + 1) → F'.B) := by
  obtain ⟨-, hτ, hU⟩ := hu
  obtain ⟨hF', hτ', hU'⟩ := hu'
  refine ⟨hF', fun i ↦ Fin.cases (hτ' ()) (fun j ↦ Thick.Hom.mem u' (hτ j)) i, ?_⟩
  intro S hS a c hc
  obtain ⟨g₁, ⟨hg₁a, hg₁c⟩, hg₁u⟩ := hU S hS a (fun j ↦ c j.succ) (fun j ↦ hc j.succ)
  obtain ⟨g, ⟨hga, hgc⟩, hgu⟩ := hU' S hS g₁ (fun _ ↦ c 0) (fun _ ↦ hc 0)
  refine ⟨g, ⟨?_, fun i ↦ ?_⟩, ?_⟩
  · rw [Category.assoc, hga, hg₁a]
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using hgc ()
    · simp only [Fin.cons_succ]
      rw [← Thick.comp_φ, hga, hg₁c]
  · rintro g' ⟨hg'a, hg'c⟩
    have h1 : u' ≫ g' = g₁ := by
      refine hg₁u _ ⟨by rw [← Category.assoc, hg'a], fun j ↦ ?_⟩
      have := hg'c j.succ
      simp only [Fin.cons_succ] at this
      rw [Thick.comp_φ, this]
    refine hgu _ ⟨h1, fun _ ↦ ?_⟩
    simpa using hg'c 0

theorem exists_free : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (n m : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) →
    ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Fin m → F.B), IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  intro R _ I κ X t n m T hT
  induction m with
  | zero => exact ⟨T, 𝟙 T, Fin.elim0, isFree_id _ T hT, QAtFormal.qAt_ident _ T⟩
  | succ m ih =>
    obtain ⟨F, u, τ, hu, hq⟩ := ih
    obtain ⟨F', u', τ', hu', hq'⟩ := GlobalTheory.T.exists_freeCrystallineThickening_oneElement_level R I κ X t n F hu.1
    exact ⟨F', u ≫ u', _, isFree_cons (n + 1) m u τ hu u' τ' hu', QAtFormal.qAt_comp _ u u' hq hq'⟩

end GlobalTheory.PDForm.FreeFin
