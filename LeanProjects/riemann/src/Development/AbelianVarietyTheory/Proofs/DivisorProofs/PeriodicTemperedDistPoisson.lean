import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantDistributionCharacters
open scoped Classical

namespace GlobalTheory.IntComb

noncomputable def dotForm (n : ℕ) : LinearMap.BilinForm ℝ (Fin n → ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, x i * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

theorem dotForm_apply (n : ℕ) (x y : Fin n → ℝ) : dotForm n x y = ∑ i, x i * y i := rfl

theorem dotForm_nondegenerate (n : ℕ) : (dotForm n).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have := hx (Pi.single i 1)
    simpa [dotForm_apply, Pi.single_apply] using this
  · intro y hy
    funext i
    have := hy (Pi.single i 1)
    simpa [dotForm_apply, Pi.single_apply] using this

abbrev intLat (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

theorem mem_intLat {n : ℕ} (x : Fin n → ℝ) :
    x ∈ intLat n ↔ ∃ k : Fin n → ℤ, x = fun i => (k i : ℝ) := by
  rw [intLat, (Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ x]
  simp only [Pi.basisFun_repr, Set.mem_range, eq_intCast]
  constructor
  · intro h
    choose k hk using h
    exact ⟨k, funext fun i => (hk i).symm⟩
  · rintro ⟨k, rfl⟩ i
    exact ⟨k i, rfl⟩

noncomputable def intLatEquiv (n : ℕ) : (Fin n → ℤ) ≃ intLat n :=
  Equiv.ofBijective (fun k => ⟨fun i => (k i : ℝ), (mem_intLat _).2 ⟨k, rfl⟩⟩)
    ⟨fun k k' h => by
      funext i
      have : ((k i : ℤ) : ℝ) = (k' i : ℝ) := congrFun (congrArg Subtype.val h) i
      exact_mod_cast this,
     fun l => by
      obtain ⟨k, hk⟩ := (mem_intLat l.1).1 l.2
      exact ⟨k, Subtype.ext hk.symm⟩⟩

theorem dirac_comb_unique : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ),
    (∀ k : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ, (∀ x, f' x = f (x + fun i => (k i : ℝ))) → T f' = T f) →
    (∀ m : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * f x) → T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = c * ∑' k : Fin n → ℤ, f (fun i => (k i : ℝ)) := by
  intro n T htr hmod
  obtain ⟨c, hc⟩ := GlobalTheory.LatticeComb.comb_unique (Fin n → ℝ) (dotForm n) (dotForm_nondegenerate n)
    (intLat n) 0 T
    (fun l hl f f' hf => by
      obtain ⟨k, rfl⟩ := (mem_intLat l).1 hl
      exact htr k f f' hf)
    (fun μ hμ f f' hf => by
      have hi : ∀ i, ∃ z : ℤ, μ i = z := by
        intro i
        obtain ⟨z, hz⟩ := hμ (Pi.single i 1) ((mem_intLat _).2 ⟨Pi.single i 1, by
          funext j; by_cases h : j = i <;> simp [Pi.single_apply, h]⟩)
        refine ⟨z, ?_⟩
        rw [← hz, dotForm_apply]
        simp [Pi.single_apply]
      choose m hm using hi
      have hμm : μ = fun i => (m i : ℝ) := funext hm
      subst hμm
      have h0 : dotForm n 0 (fun i => (m i : ℝ)) = 0 := by simp
      rw [h0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      refine hmod m f f' fun x => ?_
      rw [hf x, dotForm_apply]
      congr 3
      push_cast
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
  refine ⟨c, fun f => ?_⟩
  rw [hc f, ← (intLatEquiv n).tsum_eq]
  simp only [zero_add]
  rfl

end GlobalTheory.IntComb
