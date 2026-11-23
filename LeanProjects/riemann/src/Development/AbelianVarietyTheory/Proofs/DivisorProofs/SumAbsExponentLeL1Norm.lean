import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValVwProdLe

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.CovTop
attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.L1WeightExponents

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x; simp [conjEmb]

theorem conjEmb_injective : Function.Injective (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := by
  intro a b h
  rw [← conjEmb_conjEmb a, ← conjEmb_conjEmb b, h]

noncomputable def idx (Dw : Datum H) (s : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    Option (Psi H × Fin (Dw.p + Dw.q)) :=
  if h : s.1 (H.rt : E) = H.rt0 then
    (if hi : (s.2 : ℕ) < Dw.p then some (⟨s.1, h⟩, ⟨s.2, by omega⟩) else none)
  else if h' : conjEmb s.1 (H.rt : E) = H.rt0 then
    (if hi : (s.2 : ℕ) < Dw.q then
      some (⟨conjEmb s.1, h'⟩, ⟨Dw.p + (Dw.q - 1 - s.2), by omega⟩) else none)
  else none

theorem abs_exOf (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (s : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    |(exOf Dw u 0 (some s) : ℝ)| = (idx Dw s).elim 0 (fun t => |(u t.1 t.2 : ℝ)|) := by
  obtain ⟨τ, i⟩ := s
  simp only [exOf, exZ, wtOf, idx]
  split_ifs <;> simp

theorem idx_inj (Dw : Datum H) {s s' : Σ τ : E →+* ℂ, Fin (Dw.mult τ)} {t : Psi H × Fin (Dw.p + Dw.q)}
    (hs : idx Dw s = some t) (hs' : idx Dw s' = some t) : s = s' := by
  obtain ⟨τ, i⟩ := s
  obtain ⟨τ', i'⟩ := s'
  simp only [idx] at hs hs'
  split_ifs at hs hs' <;> (rw [← hs] at hs'; simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at hs'; obtain ⟨h1, h2⟩ := hs')
  · subst h1; exact Sigma.ext rfl (heq_of_eq (Fin.ext h2.symm))
  · omega
  · omega
  · have h3 := conjEmb_injective h1
    subst h3
    have h4 : (i : ℕ) = i' := by omega
    exact Sigma.ext rfl (heq_of_eq (Fin.ext h4))

theorem sum_abs_exponent_le_l1_norm (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) :
    ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |(exOf Dw u 0 (some s) : ℝ)| ≤ l1 u := by
  classical
  set G : Option (Psi H × Fin (Dw.p + Dw.q)) → ℝ := fun o => o.elim 0 (fun t => |(u t.1 t.2 : ℝ)|) with hG
  have hG0 : ∀ o, 0 ≤ G o := by
    intro o; cases o <;> simp [hG]
  calc ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |(exOf Dw u 0 (some s) : ℝ)|
      = ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), G (idx Dw s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_exOf]
    _ = ∑ s ∈ Finset.univ.filter (fun s => (idx Dw s).isSome), G (idx Dw s) := by
        refine (Finset.sum_filter_of_ne fun s _ hs => ?_).symm
        cases h : idx Dw s with
        | none => simp [h, hG] at hs
        | some t => simp
    _ = ∑ o ∈ (Finset.univ.filter (fun s => (idx Dw s).isSome)).image (idx Dw), G o := by
        refine (Finset.sum_image fun s hs s' hs' he => ?_).symm
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs hs'
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
        exact idx_inj Dw ht (he ▸ ht)
    _ ≤ ∑ o, G o := Finset.sum_le_univ_sum_of_nonneg hG0
    _ = l1 u := by
        rw [Fintype.sum_option]
        simp [hG, l1, Fintype.sum_prod_type]

end GlobalTheory.L1WeightExponents

theorem GlobalTheory.L1WeightExponents.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw), ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |(exOf Dw u 0 (some s) : ℝ)| ≤ l1 u :=
  fun _ _ _ _ _ Dw u => GlobalTheory.L1WeightExponents.sum_abs_exponent_le_l1_norm Dw u
