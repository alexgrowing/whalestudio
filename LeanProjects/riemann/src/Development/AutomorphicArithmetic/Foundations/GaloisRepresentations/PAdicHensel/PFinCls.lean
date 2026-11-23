import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pFinCls :
    UnitCls → FinCongr → InfCongr → DefSign → RelOf → FinCls := by
  classical
  intro hU hF hI hD hR E _ _ _ A n p _ S
  obtain ⟨I, hI0, κ, hκ⟩ := hU p (A.tr ^ 2 - 4 * A.nm) (ne_of_lt A.disc_neg)
  have key : ∀ (B B' : DForm S.G) x t x' t', Triv S.G (AfP p) ↑B.β x t →
      Triv S.G (AfP p) ↑B'.β x' t' → κ t = κ t' → B.Rel B' := by
    intro B B' x t x' t' hT hT' hk
    obtain ⟨s, hs, hloc⟩ := hκ t t' hk
    obtain ⟨hM1, hM2, hM3⟩ := hD E A n p S B
    obtain ⟨hN1, hN2, hN3⟩ := hD E A n p S B'
    have hs0 : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
    have hsym : ∀ a b, (IsCMField.complexConj E) (((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) a b) =
        ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) b a := by
      intro a b
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_ratCast, hM1 a b]
    have hdet : ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)).det ≠ 0 := by
      rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hs0) hM2
    obtain ⟨P, hP, hPeq⟩ := GlobalTheory.HermGlobal.congr_of_local_complex (F := maximalRealSubfield E)
      (σ := IsCMField.complexConj E) (IsCMField.complexConj_ne_one E) hsym hN1 hdet hN2
      (fun w => hF E A n p S B B' x x' t t' hT hT' s hs hloc w)
      (by
        intro τ hτ
        have herm : ∀ N : Matrix (Fin n) (Fin n) E,
            (∀ a b, (IsCMField.complexConj E) (N a b) = N b a) → (N.map τ).IsHermitian := by
          intro N hN
          ext i j
          simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
          rw [← hN j i, hτ, starRingEnd_apply]
        have hsm : ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)).map τ =
            (s : ℂ) • (mat S ↑B.β * (A.H n)⁻¹).map τ := by
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ratCast]
        apply hI n _ _ (herm _ hsym) (herm _ hN1)
          (if InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ then 1 else -1)
        · intro v hv
          rw [hsm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
            Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero, mul_left_comm]
          exact mul_pos (by exact_mod_cast hs) (hM3 τ v hv)
        · intro v hv
          exact hN3 τ v hv)
    exact hR E A n p S B B' s hs P hP hPeq
  haveI := hI0
  let tOf : DForm S.G → (AfP p)ˣ := fun B => B.trivAf.choose_spec.choose
  have htOf : ∀ B : DForm S.G, Triv S.G (AfP p) ↑B.β B.trivAf.choose (tOf B) :=
    fun B => B.trivAf.choose_spec.choose_spec
  refine Finite.of_injective (fun q : DFCls S.G => κ (tOf (Quot.out (r := DForm.Rel) q))) ?_
  intro q q' h
  rw [← Quot.out_eq q, ← Quot.out_eq q']
  exact Quot.sound (key _ _ _ _ _ _ (htOf _) (htOf _) h)
