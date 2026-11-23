import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Mathlib.Combinatorics.HalesJewett
import Mathlib.LinearAlgebra.Vandermonde

theorem UpperTheory.V.Pr.expSums :
    UpperTheory.V.Pr.ExpSums := by
  intro κ ι σ _ _ _ α c hα hc
  classical
  by_contra hne
  push Not at hne
  choose C hC using hne
  obtain ⟨a, ha, b, s, hs⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range (Fintype.card ι)) C
  let e := (Fintype.equivFin ι).symm
  have hinj : Function.Injective fun j : Fin (Fintype.card ι) => ((α s (e j) : κˣ) : κ) ^ a := by
    intro i j hij
    by_contra h
    refine hα s (e i) (e j) (fun h' => h (e.injective h')) a ha ?_
    apply Units.ext
    simpa using hij
  have h0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (v := fun j => c s (e j) * ((α s (e j) : κˣ) : κ) ^ b) hinj (by
      intro i
      have h1 := hC (a • (i : ℕ) + b)
      rw [hs i (Finset.mem_range.2 i.2), ← e.sum_comp] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, pow_add, pow_mul]
      ring)
  obtain ⟨i, hi⟩ := hc s
  have h2 := congrFun h0 (e.symm i)
  simp only [Equiv.apply_symm_apply, Pi.zero_apply, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hi h2
  · exact pow_ne_zero _ (α s i).ne_zero h2
