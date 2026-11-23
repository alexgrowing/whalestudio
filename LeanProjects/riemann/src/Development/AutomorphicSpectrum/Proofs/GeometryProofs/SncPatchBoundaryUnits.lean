import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem unitAt_finsetProd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {p : Cpt ξ}
    {I : Type} (s : Finset I) (f : I → Ω) (hf : ∀ i ∈ s, unitAt ξ p (f i)) :
    unitAt ξ p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one ξ p
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact unitAt_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem unitAt_of_finsetProd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {p : Cpt ξ}
    {I : Type} (s : Finset I) (f : I → Ω) (hf : ∀ i ∈ s, f i ∈ regAt ξ p)
    (hu : unitAt ξ p (∏ i ∈ s, f i)) {i : I} (hi : i ∈ s) : unitAt ξ p (f i) := by
  classical
  rw [← Finset.mul_prod_erase s f hi] at hu
  exact unitAt_of_mul_left hu (hf i hi)
    (prod_mem fun j hj => hf j (Finset.mem_of_mem_erase hj))

theorem exists_chartQ_unit_sep (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    (κ : Type) (x : κ → Ω) (c : κ) (B : Set (Cpt ξ)) (h : Ω) (e n : ℕ)
    (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (p : Cpt ξ) (_hξ : IsCptGen ξ)
    (hB : ∀ q ∈ B, Char0 ξ q) (hh : h ∈ Mdl.chartQ x c) (h0 : h ≠ 0)
    (hcl : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h →
      (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω)))
    (hp : Char0 ξ p) (hpc : InChart ξ x c p) (hph : unitAt ξ p h) (hpB : p ∉ B) :
    ∃ a ∈ Mdl.chartQ x c, unitAt ξ p a ∧ ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a := by
  classical
  set S : Finset (Fin e) := Finset.univ.filter fun i => (i : ℕ) < n with hS
  set f : Fin e → Ω := fun i => (z i : Ω) with hf
  set ζ : Ω := ∏ i ∈ S, f i with hζ
  have hζm : ζ ∈ Mdl.invAdj (Mdl.chartQ x c) h :=
    Subalgebra.prod_mem _ fun i _ => (z i).2
  obtain ⟨m, hm⟩ := exists_mul_pow_mem hh h0 hζm
  refine ⟨ζ * h ^ m * h, (Mdl.chartQ x c).mul_mem hm hh, ?_, ?_⟩
  · have hz : ∀ i ∈ S, unitAt ξ p (f i) := by
      intro i hi
      by_contra hni
      exact hpB ((hcl p hp hpc hph).2 ⟨i, (Finset.mem_filter.1 hi).2, hni⟩)
    exact unitAt_mul (unitAt_mul (unitAt_finsetProd S f hz) (unitAt_pow hph m)) hph
  · intro q hq hqc hua
    have hq0 := hB q hq
    have hA : ∀ s ∈ Mdl.chartQ x c, s ∈ regAt ξ q := fun s hs => chartQ_le hq0 hqc hs
    by_cases hqh : unitAt ξ q h
    · obtain ⟨i, hin, hni⟩ := (hcl q hq0 hqc hqh).1 hq
      have hreg : ∀ j ∈ S, f j ∈ regAt ξ q := fun j _ => invAdj_le hq0 hA hqh (z j).2
      have hζr : ζ ∈ regAt ξ q := prod_mem hreg
      have hhm : h ^ m * h ∈ regAt ξ q := (regAt ξ q).mul_mem (pow_mem (hA h hh) m) (hA h hh)
      have hua' : unitAt ξ q (ζ * (h ^ m * h)) := by rwa [← _root_.mul_assoc]
      have hζu : unitAt ξ q ζ := unitAt_of_mul_left hua' hζr hhm
      exact hni (unitAt_of_finsetProd S f hreg hζu (Finset.mem_filter.2 ⟨Finset.mem_univ i, hin⟩))
    · exact hqh (unitAt_of_mul_right hua (hA _ hm) (hA h hh))

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
