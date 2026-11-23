import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormEval
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem isHomogeneous_specRest {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e d : ℕ}
    {g : MvPolynomial (Fin (e + 1) × Fin n) R} (hg : IsMultiHomog d g) (y : Par e n → S) :
    (specRest φ g y).IsHomogeneous d := by
  classical
  rw [specRest, g.as_sum, eval₂_sum]
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  rw [eval₂_monomial, Finsupp.prod]
  have hdeg : ∀ ij : Fin (e + 1) × Fin n,
      (Fin.cases (motive := fun _ => MvPolynomial (Fin n) S) (X ij.2)
        (fun i => C (y (.inl (i, ij.2)))) ij.1 : MvPolynomial (Fin n) S).IsHomogeneous
        (groupWeight (e + 1) n ij 0) := by
    rintro ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [groupWeight] using isHomogeneous_X (R := S) j
    · have h0 : groupWeight (e + 1) n (i.succ, j) 0 = 0 := by simp [groupWeight]
      rw [h0]
      exact isHomogeneous_C _ _
  have hsum : ∑ ij ∈ m.support, groupWeight (e + 1) n ij 0 * m ij = d := by
    have hw := hg (mem_support_iff.mp hm)
    have h0 := congrFun hw 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have h := (isHomogeneous_C (σ := Fin n) (φ (coeff m g))).mul
    (IsHomogeneous.prod m.support _ _ fun ij _ => (hdeg ij).pow (m ij))
  rw [zero_add, hsum] at h
  exact h

theorem isHomogeneous_det_linear {R : Type*} [CommRing R] {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (MvPolynomial σ R)) (hN : ∀ i k, (N i k).IsHomogeneous 1) :
    N.det.IsHomogeneous (Fintype.card ι) := by
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun τ _ => ?_
  have hp := IsHomogeneous.prod Finset.univ (fun i => N (τ i) i) (fun _ => 1) fun i _ => hN (τ i) i
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hp
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R)]
  simpa using (isHomogeneous_C σ ((τ.sign : ℤ) : R)).mul hp

theorem ChowSecDegree.proof (h1 : ChowNormForm.Statement) (h2 : ChowFormHomog.Statement)
    (h3 : NormFormEval.Statement) : ChowSecDegree.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  classical
  obtain ⟨hfin, c, hc, heq⟩ := h1 k E n e Q g y hy hQ hg
  set QE := Q.map (MvPolynomial.map (algebraMap k E))
  have : Module.Finite E (SecAlg QE y) := hfin
  have : Module.Free E (SecAlg QE y) := Module.Free.of_divisionRing E (SecAlg QE y)
  let b : Module.Basis (Module.Free.ChooseBasisIndex E (SecAlg QE y)) E (SecAlg QE y) :=
    Module.Free.chooseBasis E (SecAlg QE y)
  have hN : (normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    rw [normForm_eq_det b, Module.finrank_eq_card_chooseBasisIndex]
    refine isHomogeneous_det_linear _ fun i k' => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X E j).mul (isHomogeneous_C (Fin n) _)
  have hone : (∑ j, algebraMap E (SecAlg QE y) (y (.inr j)) * secCoord QE y j) = 1 := by
    have hmem : chartForm y - 1 ∈ secIdeal QE y := Ideal.mem_sup_right (Ideal.subset_span rfl)
    have h := Ideal.Quotient.eq.mpr hmem
    rw [map_one] at h
    rw [← h]
    simp [chartForm, linForm, secCoord, map_sum, map_mul]
    rfl
  have hN0 : normForm (R := E) (SecAlg QE y) (secCoord QE y) ≠ 0 := by
    intro h0
    have hv := h3 E (SecAlg QE y) n (secCoord QE y) (fun j => y (.inr j))
    rw [h0, map_zero, hone, map_one] at hv
    exact zero_ne_one hv
  have hG : (specRest (algebraMap k E) g y).IsHomogeneous (chowDegree Q (e + 1)) :=
    isHomogeneous_specRest _ (h2 k n (e + 1) Q g hg) y
  rw [heq] at hG
  have hCN : (C c * normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    simpa using hN.C_mul c
  exact hCN.inj_right hG (mul_ne_zero (C_ne_zero.mpr hc) hN0)

end

end GroundTheory.Heights₂.Heights.Vertical
