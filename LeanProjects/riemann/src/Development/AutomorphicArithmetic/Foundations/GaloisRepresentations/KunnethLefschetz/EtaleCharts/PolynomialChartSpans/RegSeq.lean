import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData

noncomputable section

namespace UpperTheory.Gal.KunnethLefschetz.G

private lemma mem_span_X_of_sum_eq_zero {A : Type} [CommRing A] {d : ℕ} (p : Fin d → MvPolynomial (Fin d) A)
    (h : ∑ m, MvPolynomial.X m * p m = 0) (l : Fin d) :
    p l ∈ Ideal.span (Set.range fun m : Fin d => (MvPolynomial.X m : MvPolynomial (Fin d) A)) := by
  have h0 : MvPolynomial.coeff 0 (p l) = 0 := by
    have h1 := congrArg (MvPolynomial.coeff (Finsupp.single l 1)) h
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single l] at h1
    · simpa [MvPolynomial.coeff_X_mul'] using h1
    · intro m _ hm
      rw [MvPolynomial.coeff_X_mul']
      simp [Finsupp.single_apply, hm.symm, hm]
    · simp
  have hs : (Set.range fun m : Fin d => (MvPolynomial.X m : MvPolynomial (Fin d) A)) =
      MvPolynomial.X '' (Set.univ : Set (Fin d)) := by
    ext x; simp
  rw [hs, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra hne
  push_neg at hne
  have : m = 0 := by
    ext i
    simpa using hne i (Set.mem_univ i)
  subst this
  exact (MvPolynomial.mem_support_iff.mp hm) h0

private lemma main {A C : Type} [CommRing A] [CommRing C] {d : ℕ} [Algebra (MvPolynomial (Fin d) A) C]
    [Module.Flat (MvPolynomial (Fin d) A) C] (v : Fin d → C)
    (hv : ∀ l, v l = algebraMap (MvPolynomial (Fin d) A) C (MvPolynomial.X l)) (a : Fin d → C)
    (ha : ∑ l, a l * v l ∈ Ideal.span (Set.range v) * Ideal.span (Set.range v)) (l : Fin d) :
    a l ∈ Ideal.span (Set.range v) := by
  classical
  obtain rfl : v = fun l => algebraMap (MvPolynomial (Fin d) A) C (MvPolynomial.X l) := funext hv
  obtain ⟨b, hbI, hb⟩ : ∃ b : Fin d → C,
      (∀ l, b l ∈ Ideal.span (Set.range fun l =>
        algebraMap (MvPolynomial (Fin d) A) C (MvPolynomial.X l))) ∧
      ∑ l, b l * algebraMap (MvPolynomial (Fin d) A) C (MvPolynomial.X l) =
        ∑ l, a l * algebraMap (MvPolynomial (Fin d) A) C (MvPolynomial.X l) := by
    change _ ∈ _ • Submodule.span C _ at ha
    rw [Submodule.mem_ideal_smul_span_iff_exists_sum] at ha
    obtain ⟨β, hβ, hsum⟩ := ha
    refine ⟨β, hβ, ?_⟩
    rw [← hsum, Finsupp.sum_fintype]
    · simp [smul_eq_mul]
    · simp
  have hmem : ∀ r ∈ Ideal.span (Set.range fun m : Fin d =>
      (MvPolynomial.X m : MvPolynomial (Fin d) A)),
      algebraMap (MvPolynomial (Fin d) A) C r ∈ Ideal.span (Set.range fun l =>
        algebraMap (MvPolynomial (Fin d) A) C (MvPolynomial.X l)) := by
    intro r hr
    have hm := Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin d) A) C) hr
    rw [Ideal.map_span, ← Set.range_comp] at hm
    exact hm
  have hc : ∑ l, (MvPolynomial.X l : MvPolynomial (Fin d) A) • (a l - b l) = 0 := by
    simp only [Algebra.smul_def, mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    simp only [mul_comm (algebraMap (MvPolynomial (Fin d) A) C _)]
    exact hb.symm
  obtain ⟨k, α, y, hxy, hrel⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := MvPolynomial (Fin d) A) (M := C) (f := fun l => MvPolynomial.X l)
    (x := fun l => a l - b l) hc
  have hcl : a l - b l ∈ Ideal.span (Set.range fun l =>
      algebraMap (MvPolynomial (Fin d) A) C (MvPolynomial.X l)) := by
    rw [show a l - b l = _ from hxy l]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (hmem _ (mem_span_X_of_sum_eq_zero (fun m => α m j) (hrel j) l))
  simpa using Ideal.add_mem _ hcl (hbI l)

theorem regSeq : RegSeq := by
  intro A C _ _ d φ hφ a ha l
  letI := φ.toAlgebra
  haveI : Module.Flat (MvPolynomial (Fin d) A) C := hφ
  rw [pow_two] at ha
  exact main (A := A) (fun l => φ (MvPolynomial.X l)) (fun _ => rfl) a ha l

end UpperTheory.Gal.KunnethLefschetz.G
