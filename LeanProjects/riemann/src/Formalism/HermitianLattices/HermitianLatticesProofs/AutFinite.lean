import Mathlib
import Formalism.HermitianLattices.GenusCovolBound
import Formalism.HermitianLattices.HermitianLatticesProofs.ThetaSummable

open Module Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section AutFiniteSec

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

lemma autFinite_short (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) [Submodule.IsLattice K L] (R : ℚ) :
    Set.Finite {v : V | v ∈ L ∧ Algebra.trace ℚ K (h v v) ≤ R} := by
  have hs := thetaSummable_main h hpos L 0 Complex.I (by simp)
  have hnorm : ∀ x : L, ‖Complex.exp (Real.pi * Complex.I * Complex.I *
      ((Algebra.trace ℚ K (h (0 + (x : V)) (0 + (x : V))) : ℚ) : ℂ))‖ =
        Real.exp (-Real.pi * ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ)) := by
    intro x
    rw [Complex.norm_exp, zero_add]
    congr 1
    have e : (Real.pi : ℂ) * Complex.I * Complex.I = -(Real.pi : ℂ) := by
      rw [mul_assoc, Complex.I_mul_I]
      ring
    rw [e]
    simp
  have hev := (tendsto_zero_iff_norm_tendsto_zero.1 hs.tendsto_cofinite_zero).eventually
    (gt_mem_nhds (Real.exp_pos (-Real.pi * (R : ℝ))))
  rw [Filter.eventually_cofinite] at hev
  refine (hev.image Subtype.val).subset ?_
  rintro v ⟨hvL, hvR⟩
  refine ⟨⟨v, hvL⟩, ?_, rfl⟩
  show ¬ (‖Complex.exp (Real.pi * Complex.I * Complex.I *
      ((Algebra.trace ℚ K (h (0 + v) (0 + v)) : ℚ) : ℂ))‖ < Real.exp (-Real.pi * (R : ℝ)))
  rw [not_lt, hnorm ⟨v, hvL⟩]
  apply Real.exp_le_exp.2
  have hR : ((Algebra.trace ℚ K (h v v) : ℚ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hvR
  nlinarith [Real.pi_pos]

end AutFiniteSec

theorem autFinite : AutFinite := by
  intro K V _ _ _ _ _ _ _ _ h _ hpos L hL
  obtain ⟨S, hS⟩ := Submodule.IsLattice.fg (A := K) (M := L)
  set R : ℚ := ∑ s ∈ S, Algebra.trace ℚ K (h s s) with hR
  have hSL : ∀ s ∈ S, s ∈ L := fun s hs => hS ▸ Submodule.subset_span hs
  have hsR : ∀ s ∈ S, Algebra.trace ℚ K (h s s) ≤ R := fun s hs =>
    Finset.single_le_sum (f := fun s => Algebra.trace ℚ K (h s s))
      (fun x _ => thetaSummable_nonneg h hpos x) hs
  have hT := autFinite_short h hpos L R
  have hspan : Submodule.span K (S : Set V) = ⊤ := by
    rw [eq_top_iff, ← Submodule.IsLattice.span_eq_top (A := K) (M := L), Submodule.span_le]
    intro x hx
    rw [← hS] at hx
    exact Submodule.span_le_restrictScalars (NumberField.RingOfIntegers K) K (S : Set V) hx
  let Φ : (V ≃ₗ[K] V) → (S → V) := fun g s => g s
  apply Set.Finite.of_finite_image (f := Φ)
  · refine (Set.Finite.pi (t := fun _ : S => {v : V | v ∈ L ∧ Algebra.trace ℚ K (h v v) ≤ R})
      (fun _ => hT)).subset ?_
    rintro _ ⟨g, ⟨hg, hgL⟩, rfl⟩ s _
    have hg' : ∀ x y, h (g x) (g y) = h x y := hg
    refine ⟨?_, ?_⟩
    · have hm : g s ∈ Formalism.HermitianLatticesTheory.gmap g L := Submodule.mem_map_of_mem (hSL s s.2)
      rwa [hgL] at hm
    · show Algebra.trace ℚ K (h (g s) (g s)) ≤ R
      rw [hg']
      exact hsR s s.2
  · intro g₁ _ g₂ _ hg
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hspan
    intro x hx
    exact congrFun hg ⟨x, hx⟩

end Formalism.HermitianLatticesTheory
