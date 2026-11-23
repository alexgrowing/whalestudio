import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.UnifNorm

theorem norm_le_one_of_mem (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  have hv : ((Valued.v (x : ℂ_[p]) : NNReal) : ℝ) = ‖(x : ℂ_[p])‖ := by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  rw [← hv]
  have : Valued.v (x : ℂ_[p]) ≤ 1 := x.2
  exact_mod_cast this

theorem norm_eq_one_of_isUnit (p : ℕ) [Fact p.Prime] {x : 𝓞_ℂ_[p]} (hx : IsUnit x) :
    ‖(x : ℂ_[p])‖ = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h1 : (x : ℂ_[p]) * (y : ℂ_[p]) = 1 := by
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hy
    simpa using this
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  have ha := norm_le_one_of_mem p x
  have hb := norm_le_one_of_mem p y
  nlinarith [norm_nonneg (x : ℂ_[p]), norm_nonneg (y : ℂ_[p])]

theorem norm_pow_eq (p : ℕ) [Fact p.Prime] {V : Type} [CommRing V] {ϖ : V} {n : ℕ}
    (hn : Associated (p : V) (ϖ ^ n)) (φ : V →+* 𝓞_ℂ_[p]) :
    ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ n = ‖(p : ℂ_[p])‖ := by
  obtain ⟨u, hu⟩ := hn
  have h1 := congrArg (fun z : V => ‖((φ z : 𝓞_ℂ_[p]) : ℂ_[p])‖) hu
  have hu1 : ‖((φ (u : V) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 :=
    norm_eq_one_of_isUnit p ((u.isUnit).map φ)
  simp only [map_mul, map_pow, map_natCast] at h1
  simp [norm_mul, norm_pow, hu1] at h1
  exact h1.symm

end GlobalTheory.UnifNorm

theorem GlobalTheory.unif_norm_indep : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ ϖ : V, Irreducible ϖ → ∃ r : ℝ, ∀ φ : V →+* 𝓞_ℂ_[p], ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ = r := by
  intro F _ _ V _ p _ hp ϖ hϖ
  classical
  have hp0 : (p : V) ≠ 0 := by
    intro h
    have h' := congrArg (fun z : V => (z : F)) h
    simp only [ZeroMemClass.coe_zero] at h'
    push_cast at h'
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h'
  have hpnu : ¬ IsUnit (p : V) := by
    intro hu
    rw [ValuationSubring.mem_nonunits_iff] at hp
    rw [ValuationSubring.valuation_eq_one_iff] at hu
    have : V.valuation ((p : V) : F) < 1 := by simpa using hp
    exact (ne_of_lt this) hu
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hpnu (associated_one_iff_isUnit.mp hn)
  by_cases hne : Nonempty (V →+* 𝓞_ℂ_[p])
  · obtain ⟨φ₀⟩ := hne
    refine ⟨‖((φ₀ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖, fun φ => ?_⟩
    have e1 := GlobalTheory.UnifNorm.norm_pow_eq p hn φ
    have e0 := GlobalTheory.UnifNorm.norm_pow_eq p hn φ₀
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hn0).mp (e1.trans e0.symm)
  · exact ⟨0, fun φ => (hne ⟨φ⟩).elim⟩
