import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem spMap_id_complex : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
  simp [spMap]

theorem fineAt_of_isBC (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type)
    [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop)
    (F' : Fam ℂ O Λ g) (hBC : IsBC F' F σ) (hF : FineAt F σ ρ N C) : FineAt F' (RingHom.id ℂ) ρ N C := by
  obtain ⟨f, φ, pb, gp, hact, hL, heta⟩ := hBC
  have M := GlobalTheory.T.uniformisationAt_correspond_of_cartesian O bar g ρ R ℂ σ (RingHom.id ℂ) Λ F F' N f φ gp hact hL heta
  have base : ∀ y' : Sp ℂ ⟶ F'.X, y' ≫ F'.s = spMap (RingHom.id ℂ) → (y' ≫ f) ≫ F.s = spMap σ := by
    intro y' hy
    rw [Category.assoc, pb.w, ← Category.assoc, hy, spMap_id_complex, Category.id_comp]
  refine ⟨?_, ?_, ?_⟩
  · intro y' hy
    obtain ⟨D', t, P, e, hC, hU⟩ := hF.pts (y' ≫ f) (base y' hy)
    obtain ⟨e', hU', -⟩ := (M D' t P y' hy (base y' hy)).2 e hU
    exact ⟨D', t, P, e', hC, hU'⟩
  · intro D' t P hC hP
    obtain ⟨y, e, hU⟩ := hF.occ D' t P hC hP
    have w : y ≫ F.s = spMap (RingHom.id ℂ) ≫ spMap σ := by
      rw [hU.1, spMap_id_complex, Category.id_comp]
    obtain ⟨y', rfl, hy'⟩ : ∃ y', y' ≫ f = y ∧ y' ≫ F'.s = spMap (RingHom.id ℂ) :=
      ⟨pb.lift y _ w, pb.lift_fst _ _ w, pb.lift_snd _ _ w⟩
    obtain ⟨e', hU', -⟩ := (M D' t P y' hy' (base y' hy')).2 e hU
    exact ⟨y', e', hU'⟩
  · intro D' D'' t t' P P' y y' e e' hU hU' w h hw hP
    obtain ⟨e₁, hU₁, -⟩ := (M D' t P y hU.1 (base y hU.1)).1 e hU
    obtain ⟨e₂, hU₂, -⟩ := (M D'' t' P' y' hU'.1 (base y' hU'.1)).1 e' hU'
    have hf : y ≫ f = y' ≫ f := hF.sep D' D'' t t' P P' _ _ e₁ e₂ hU₁ hU₂ w h hw hP
    exact pb.hom_ext hf (hU.1.trans hU'.1.symm)

end GlobalTheory.PELU
