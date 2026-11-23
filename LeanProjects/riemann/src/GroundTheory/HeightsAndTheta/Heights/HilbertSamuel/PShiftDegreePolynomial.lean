import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftDegreePolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ShiftDegreePolynomial

def toMultilinear {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y)) :
    MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ where
  toFun := f
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact hadd m i x y
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact (AddMonoidHom.mk' (fun x => f (Function.update m i x)) (hadd m i)).map_zsmul c x

theorem expand {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (q : ℤ) (a b : K → ℤ) :
    f (fun _ => q • a + b) =
      ∑ s : Finset (Fin n), q ^ s.card * f (s.piecewise (fun _ => a) (fun _ => b)) := by
  have h1 := (toMultilinear f hadd).map_add_univ (fun _ => q • a) (fun _ => b)
  refine h1.trans (Finset.sum_congr rfl fun s _ => ?_)
  have h2 := (toMultilinear f hadd).map_piecewise_smul (fun _ => q)
    (s.piecewise (fun _ => a) (fun _ => b)) s
  have h3 : s.piecewise (fun i => q • s.piecewise (fun _ => a) (fun _ => b) i)
      (s.piecewise (fun _ => a) (fun _ => b)) = s.piecewise (fun _ => q • a) (fun _ => b) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [h3, Finset.prod_const, smul_eq_mul] at h2
  exact h2

theorem genericFibre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (P.map (MvPolynomial.map (Int.castRingHom ℚ))) ∧
      ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
        ((D + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : P.IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have h1 : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hchar
  have hq : ReciprocityTheory.AnForm.R.extQ P = P.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq _ _ ?_
    rw [hform]
    push_cast
    ring

theorem proof (h : MixedNumberPolynomial.Statement.{0}) : ShiftDegreePolynomial.Statement := by
  classical
  intro K _ ι _ P D a b hP
  obtain ⟨hprime, hdimq⟩ := genericFibre hP
  set Q := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hQ
  have hadd := (h ℚ K ι Q D hprime hdimq).2
  let f : (Fin D → K → ℤ) → ℤ := fun bs => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ Q bs
  let c : Finset (Fin D) → ℤ := fun s => f (s.piecewise (fun _ => a) (fun _ => b))
  refine ⟨∑ s : Finset (Fin D), Polynomial.C (c s : ℝ) * Polynomial.X ^ s.card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    simpa using Finset.card_le_univ s
  · rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single Finset.univ]
    · simp [c, f, genDeg, hQ]
    · intro s _ hs
      rw [if_neg]
      intro hD
      apply hs
      rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
      exact hD.symm
    · intro hu
      exact absurd (Finset.mem_univ _) hu
  · intro q
    have hexp := expand f hadd (q : ℤ) a b
    have hg : genDeg P D ((q : ℤ) • a + b) = f (fun _ => (q : ℤ) • a + b) := rfl
    rw [hg, hexp, Polynomial.eval_finsetSum]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [c, mul_comm]

end ShiftDegreePolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
