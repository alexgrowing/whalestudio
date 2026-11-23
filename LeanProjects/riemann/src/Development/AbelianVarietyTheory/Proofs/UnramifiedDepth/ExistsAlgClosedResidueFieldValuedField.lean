import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Interface
import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.ResField

variable {C : Type} [Field C] (V : VF C)

theorem nonneg (x : V.RR) : 0 ≤ V.v (x : C) := by
  have h : ((0 : ℝ) : WithTop ℝ) ≤ V.v (x : C) := x.2
  simpa using h

def mm : Ideal V.RR where
  carrier := {x | V.MM (x : C)}
  add_mem' := fun {x y} hx hy => V.v.map_lt_add hx hy
  zero_mem' := by simp [VF.MM]
  smul_mem' := fun c x hx => by
    show 0 < V.v ((c : C) * x)
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left (nonneg V c))

theorem mm_isMaximal : (mm V).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J x _ hx hxJ => ?_⟩
  · have h1 : 0 < V.v ((1 : V.RR) : C) := h
    simp at h1
  · have hx' : ¬ 0 < V.v (x : C) := hx
    have hx0 : V.v (x : C) = 0 := le_antisymm (not_lt.mp hx') (nonneg V x)
    have hne : (x : C) ≠ 0 := by
      intro h
      rw [h, AddValuation.map_zero] at hx0
      exact WithTop.top_ne_zero hx0
    have hinv : ((0 : ℝ) : WithTop ℝ) ≤ V.v ((x : C)⁻¹) := by
      rw [AddValuation.map_inv, hx0]
      simp
    let y : V.RR := ⟨(x : C)⁻¹, hinv⟩
    have hyx : y * x = 1 := Subtype.ext (by simp [y, hne])
    rw [← hyx]
    exact J.mul_mem_left y hxJ

theorem integers : (AddValuation.toValuation V.v).Integers V.RR where
  hom_inj := Subtype.val_injective
  map_le_one := fun r => by
    show 0 ≤ V.v (r : C)
    exact nonneg V r
  exists_of_le_one := fun {r} h => by
    have h' : 0 ≤ V.v r := h
    refine ⟨⟨r, ?_⟩, rfl⟩
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v r
    simpa using h'

theorem isAlgClosed_of_surjective [IsAlgClosed C] {Ω : Type} [Field Ω] (ρ : V.RR →+* Ω)
    (hρ : Function.Surjective ρ) : IsAlgClosed Ω := by
  refine IsAlgClosed.of_exists_root Ω fun p hp hirr => ?_
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective ρ hρ p)) hp
  have hdeg : (q.map (algebraMap V.RR C)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (integers V).hom_inj, hqdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  rw [Polynomial.IsRoot, Polynomial.eval_map] at hz
  have hint : IsIntegral V.RR z := ⟨q, hqmon, hz⟩
  obtain ⟨y, rfl⟩ := (integers V).exists_of_le_one ((integers V).mem_of_integral hint)
  rw [Polynomial.eval₂_at_apply] at hz
  have hy : q.eval y = 0 := (integers V).hom_inj (by rw [hz, map_zero])
  refine ⟨ρ y, ?_⟩
  rw [← hqmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

theorem exists_residueField : ∀ (C : Type) [Field C] (V : VF C), IsAlgClosed C → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω V.l) (ρ : V.RR →+* Ω), ∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C) := by
  intro C _ V _
  have := mm_isMaximal V
  let _ : Field (V.RR ⧸ mm V) := Ideal.Quotient.field (mm V)
  have hl : ((V.l : ℕ) : V.RR ⧸ mm V) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (mm V)), Ideal.Quotient.eq_zero_iff_mem]
    show 0 < V.v (((V.l : ℕ) : V.RR) : C)
    have hc : (((V.l : ℕ) : V.RR) : C) = ((V.l : ℕ) : C) := by simp
    rw [hc, V.v_l]
    exact zero_lt_one
  have : CharP (V.RR ⧸ mm V) V.l := (CharP.charP_iff_prime_eq_zero V.l_prime).2 hl
  exact ⟨V.RR ⧸ mm V, inferInstance, isAlgClosed_of_surjective V _ Ideal.Quotient.mk_surjective,
    inferInstance, Ideal.Quotient.mk (mm V), fun x => Ideal.Quotient.eq_zero_iff_mem⟩

end GlobalTheory.AlphaPair.ResField
