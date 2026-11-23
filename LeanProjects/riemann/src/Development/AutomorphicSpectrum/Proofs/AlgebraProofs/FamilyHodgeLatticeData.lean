import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyGivesConjugateLieData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Conj.Fam GlobalTheory.CompanionTheory.Ar.Crv.Inhab

theorem mem_imLat_iff_stdLat {K : Type} [Field K] (C : ACurve K) {d : ℕ} (i : C.I)
    (T : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K) × (Fin d → K)) (y : (Fin d → K) × (Fin d → K)) :
    y ∈ imLat C i T ↔ y ∈ stdLat (C.v i).valuationSubring.toSubring T := by
  have hs : ∀ w : (Fin d → K) × (Fin d → K), w ∈ stdH C d i ↔
      ∀ j, w.1 j ∈ (C.v i).valuationSubring.toSubring ∧ w.2 j ∈ (C.v i).valuationSubring.toSubring := by
    intro w
    rw [mem_stdH]
    exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hy
    exact Submodule.subset_span ⟨w, (hs w).1 hw, rfl⟩
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact (mem_imLat C).2 ⟨w, (hs w).2 hw, rfl⟩
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul a x _ hx =>
      obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hx
      refine (mem_imLat C).2 ⟨(a : K) • w, (hs _).2 fun j => ?_, ?_⟩
      · exact ⟨Subring.mul_mem _ a.2 ((hs w).1 hw j).1, Subring.mul_mem _ a.2 ((hs w).1 hw j).2⟩
      · rw [map_smul]
        rfl

theorem family_conj_H_eq : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I →
    ∃ D : ConjData C p O d, (∀ a, D.ρH a = rhoH F.B a) ∧
      ∀ i, D.H i = imLat C i (transH (F.φ i) (F.ψ i) (F.lam i)) := by
  intro K _ C p _ _ d O _ _ F hI
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.formal_group_action_ring_hom K d O F.B
  obtain ⟨⟨ρH, hρH⟩, -, -⟩ := GlobalTheory.T.formal_hermitian_action_pairing K d O F.B
  have iso := fun i => GlobalTheory.T.formal_isomorphism_transport K d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have h₁ := fun i => (iso i).1
  have h₂ := fun i => (iso i).2.1
  have hT := fun i => (iso i).2.2.1
  have hc := fun i => (iso i).2.2.2.2.1
  have good : ∀ i, (∀ a b, C.v i (lin (F.φ i) 1 a b) ≤ 1 ∧ C.v i (lin (F.ψ i) 1 a b) ≤ 1 ∧
      C.v i (bil (F.lam i) 1 1 a b) ≤ 1) → IntM C i (lin (F.φ i) 1) ∧ IntM C i (lin (F.ψ i) 1) ∧
        IntM C i (bil (F.lam i) 1 1) := fun i h =>
    ⟨fun a b => (h a b).1, fun a b => (h a b).2.1, fun a b => (h a b).2.2⟩
  have hiso := fun i => GlobalTheory.T.alpha_beta_isomorphism_transport K p d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  refine ⟨{ lie := fun i => colLat C i (lin (F.φ i) 1)
            H := fun i => imLat C i (transH (F.φ i) (F.ψ i) (F.lam i))
            lie_bun := isBun_colLat C _ _ h₁ h₂ (F.ae.subset fun i hi h => hi ?_)
            H_bun := isBun_imLat C _ hT (F.ae.subset fun i hi h => hi ?_)
            ρ := ρ
            ρH := ρH
            ρH_hom := fun a i x hx => ?_
            ρH_fst := fun a y => ?_
            ρH_inr := fun a φ => ?_
            hodge := hodge_family C _ _ _ h₁ h₂
            α := alpha F.B p
            β := beta F.B p
            conj := conj_family C p hI _ _ h₁ h₂ _ hT _ _ _ _ (fun i u => (hiso i).1 u)
              (fun i y => (hiso i).2 y) (fun i => locSplit C F i)
            α_act := fun a u => ?_
            β_act := fun a y => ?_ }, hρH, fun _ => rfl⟩
  · exact ⟨(good i h).1, (good i h).2.1⟩
  · obtain ⟨g₁, g₂, g₃⟩ := good i h
    exact imLat_transH_eq C (h₁ i) (h₂ i) g₁ g₂ g₃
  · obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hx
    rw [hρH]
    refine (mem_imLat C).2 ⟨rhoH (F.BK i) a w, rhoH_mem_stdH C i (F.Bi i) (F.BK i) (F.mapK i) a hw, ?_⟩
    exact (LinearMap.congr_fun (hc i a) w).symm
  · rw [hρH, rhoH_fst, hρ]
  · rw [hρH, rhoH_inr, hρ]
  · rw [hρ, hρH]
    exact GlobalTheory.T.alpha_equivariant_frobenius K p d O F.B a u
  · rw [hρ, hρH]
    exact GlobalTheory.T.beta_equivariant_frobenius K p d O F.B a y

theorem family_conj_H_lattices : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I → ∃ D : ConjData C p O d, (∀ a, D.ρH a = rhoH F.B a) ∧ ∀ i y, y ∈ D.H i ↔ y ∈ stdLat (C.v i).valuationSubring.toSubring (transH (F.φ i) (F.ψ i) (F.lam i)) := by
  intro K _ C p _ _ d O _ _ F hI
  obtain ⟨D, h₁, h₂⟩ := family_conj_H_eq K C p d O F hI
  refine ⟨D, h₁, fun i y => ?_⟩
  rw [h₂ i]
  exact mem_imLat_iff_stdLat C i _ y

end GlobalTheory.CompanionTheory.Ar.Flat
