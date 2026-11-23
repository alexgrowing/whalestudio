import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionKoszul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section ClassNumPairDiff

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_pairDiff_mul {n e : ℕ} {W : Ideal (MRing ι O)}
    (hadd : ∀ (a₁ a₂ : K → ℤ) (l : List (K → ℤ)), e ≤ l.length →
      vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l))
    (z z' : Fin n → K → ℤ) (j : Fin n) {H : MvPolynomial (Fin n ⊕ Fin n) ℤ} {t : ℕ}
    (hH : H.IsHomogeneous t) (Q : List (K → ℤ)) (ht : e ≤ t + Q.length) :
    classNum (Sum.elim z z') (pairDiff j * H) Q W =
      ∑ μ ∈ H.support,
        H.coeff μ * vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)) := by
  have hsub : classNum (Sum.elim z z') (pairDiff j * H) Q W =
      classNum (Sum.elim z z') (X (Sum.inl j) * H) Q W -
        classNum (Sum.elim z z') (X (Sum.inr j) * H) Q W := by
    rw [pairDiff, sub_mul]
    exact map_sub (classNumAddHom (Sum.elim z z') Q W) _ _
  rw [hsub, classNum_X_mul, classNum_X_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : e ≤ (classList (Sum.elim z z') μ ++ Q).length := by
    rw [List.length_append, classList_length_of_mem_support _ hH hμ]
    exact ht
  have h := hadd (z j - z' j) (z' j) _ hlen
  rw [sub_add_cancel] at h
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [h]
  ring

end ClassNumPairDiff

theorem cycEval_vNumL_comm (hC2 : VerticalDivisorsCommute.Statement.{0}) {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hP : IsModelOver P (l.length + 1)) {b b' : K → ℤ} {f g f' g' : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (hD' : IsVerticalDivisor P ϖ b' f' g') :
    cycEval (fun W => vNumL W (b' :: l)) (ratDiv P f g) =
      cycEval (fun W => vNumL W (b :: l)) (ratDiv P f' g') := by
  have h := hC2 O ϖ hϖ K ι P l.length hP b b' f g f' g' hD hD' l.get
  simp only [vNum_vecCons_eq, List.ofFn_get] at h
  exact h

theorem PairNumberExpansionIndependence.proof (hC2 : VerticalDivisorsCommute.Statement.{0}) :
    PairNumberExpansionIndependence.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP n z z' f g hD m A hA As Bs hAs hBs Q hQ
  have hrel : ∑ i, pairDiff i * (As - Bs) i = 0 := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, pairDiff, ← hAs.expansion,
      ← hBs.expansion, sub_self]
  obtain ⟨Kz, hKa, hKh, hK0, hKs⟩ := koszul_homogeneous (m := m) (As - Bs)
    (fun i => (hAs.homogeneous i).sub (hBs.homogeneous i)) hrel
  rw [← sub_eq_zero, ← pairNumHom_apply, ← pairNumHom_apply, ← map_sub]
  by_cases hm : m - 1 = 0
  · have h0 : As - Bs = 0 := funext fun i => by
      rw [hKs i]
      simp [hK0 hm]
    rw [h0, map_zero]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hlen : ∀ i j μ, μ ∈ (Kz i j).support → (classList (Sum.elim z z') μ ++ Q).length = e := by
    intro i j μ hμ
    rw [List.length_append, classList_length_of_mem_support _ (hKh i j) hμ]
    omega

  let V : Fin n → Fin n → (Fin n ⊕ Fin n →₀ ℕ) → ℤ := fun i j μ =>
    cycEval (fun W => vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)))
      (ratDiv P (f i) (g i))
  let F : Fin n → Fin n → ℤ := fun i j => ∑ μ ∈ (Kz i j).support, (Kz i j).coeff μ * V i j μ
  have hexp : pairNumHom P z z' f g Q (As - Bs) = ∑ i, ∑ j, F i j := by
    rw [pairNumHom_apply]
    unfold pairNum
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfin := ratDiv_finite_support P (f i) (g i)
    have hW : ∀ W ∈ hfin.toFinset, classNum (Sum.elim z z') ((As - Bs) i) Q W =
        ∑ j, ∑ μ ∈ (Kz i j).support,
          (Kz i j).coeff μ * vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)) := by
      intro W hWm
      rw [Set.Finite.mem_toFinset, Function.mem_support] at hWm
      rw [hKs i]
      have h := map_sum (classNumAddHom (Sum.elim z z') Q W) (fun j => pairDiff j * Kz i j)
        Finset.univ
      simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact classNum_pairDiff_mul (vNumL_add_of_ratDiv_ne_zero hϖ hP (hD i) hWm) z z' j (hKh i j) Q
        (by omega)
    simp only [F, V, cycEval_eq_sum hfin]
    rw [Finset.sum_congr rfl
      (fun W hW' => congrArg (ratDiv P (f i) (g i) W * ·) (hW W hW'))]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
    ring
  have hF : ∀ i j, F j i = -F i j := by
    intro i j
    simp only [F]
    rw [hKa j i, support_neg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hP' : IsModelOver P ((classList (Sum.elim z z') μ ++ Q).length + 1) := by
      rw [hlen i j μ hμ]
      exact hP
    have hc := cycEval_vNumL_comm hC2 hϖ _ hP' (hD i) (hD j)
    simp only [V, coeff_neg]
    rw [hc]
    ring
  rw [hexp]
  have hS : ∑ i, ∑ j, F i j = -∑ i, ∑ j, F i j := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hF i j
  linarith

end

end GroundTheory.Heights₂.Heights.NumbersDVR
