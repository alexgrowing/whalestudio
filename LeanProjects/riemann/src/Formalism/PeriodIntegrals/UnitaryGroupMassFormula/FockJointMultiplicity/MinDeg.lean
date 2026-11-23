import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.FockOperatorsKernel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KroneckerOneRightSwap

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJMF

def HwHarmDeg2 : Prop := ∀ p q r s : ℕ, ∀ (μ : Ix r s → ℚ) (e : ℕ) (v : Pol p q r s),
  v ∈ homog (Ix p q × Ix r s) e → IsHW (fockAct2 p q r s) μ v →
    (∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) v = 0) →
    (e : ℚ) = degW (cPair p q) μ

section Grade

variable {σ : Type*}

theorem hc_shift (L : Module.End ℂ (MvPolynomial σ ℂ)) (k : ℕ)
    (hL : ∀ (d : ℕ) (Q : MvPolynomial σ ℂ), Q ∈ homog σ d → L Q ∈ homog σ (d + k))
    (j : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent j (L P) = if k ≤ j then L (homogeneousComponent (j - k) P) else 0 := by
  have hP := sum_homogeneousComponent P
  conv_lhs => rw [← hP]
  rw [map_sum, map_sum]
  have hterm : ∀ d, homogeneousComponent j (L (homogeneousComponent d P)) =
      if j = d + k then L (homogeneousComponent d P) else 0 := by
    intro d
    exact homogeneousComponent_of_mem (hL d _ (homogeneousComponent_mem d P))
  simp only [hterm]
  split_ifs with hkj
  · rw [Finset.sum_eq_single (j - k)]
    · rw [if_pos (by omega)]
    · intro d _ hd
      rw [if_neg (by omega)]
    · intro hm
      rw [if_pos (by omega)]
      rw [Finset.mem_range] at hm
      rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]
  · exact Finset.sum_eq_zero fun d _ => if_neg (by omega)

theorem hc_X (l : σ) (j : ℕ) (Q : MvPolynomial σ ℂ) :
    homogeneousComponent j (X l * Q) = if 1 ≤ j then X l * homogeneousComponent (j - 1) Q else 0 := by
  have h := hc_shift (LinearMap.mulLeft ℂ (X l : MvPolynomial σ ℂ)) 1 (fun d Q' hQ' => by
    have h1 := (isHomogeneous_X ℂ l).mul hQ'
    rw [add_comm] at h1
    exact h1) j Q
  simpa using h

theorem supp_hc {e : ℕ} {P : MvPolynomial σ ℂ} {m : σ →₀ ℕ}
    (h : m ∈ (homogeneousComponent e P).support) : m ∈ P.support := by
  rw [mem_support_iff, coeff_homogeneousComponent] at h
  rw [mem_support_iff]
  split_ifs at h
  · exact h
  · exact absurd rfl h

theorem low_hc (L : Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) (h : L P = 0) (n : ℕ) : L (homogeneousComponent n P) = 0 := by
  have hz : ∀ e, homogeneousComponent e (L (homogeneousComponent n P)) = 0 := by
    intro e
    rw [hL e, homogeneousComponent_of_mem (homogeneousComponent_mem n P)]
    split_ifs with he
    · have h2 := hL e P
      rw [h, map_zero, he] at h2
      exact h2.symm
    · simp
  ext m
  have h3 := congrArg (coeff m) (hz (m.degree))
  rw [coeff_homogeneousComponent, if_pos rfl] at h3
  simpa using h3

theorem low_sum {ι : Type*} (t : Finset ι) (L : ι → Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ i (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L i P) = L i (homogeneousComponent (e + 2) P)) :
    ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e ((∑ i ∈ t, L i) P) = (∑ i ∈ t, L i) (homogeneousComponent (e + 2) P) := by
  intro e P
  simp only [LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => hL i e P

theorem exists_homog_of (P : MvPolynomial σ ℂ) (h0 : P ≠ 0) (D : ℚ)
    (h : ∀ e : ℕ, homogeneousComponent e P ≠ 0 → (e : ℚ) = D) :
    ∃ d : ℕ, (d : ℚ) = D ∧ P ∈ homog σ d := by
  have hex : ∃ e, homogeneousComponent e P ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h0
    rw [← sum_homogeneousComponent P]
    exact Finset.sum_eq_zero fun i _ => hall i
  obtain ⟨d, hd⟩ := hex
  refine ⟨d, h d hd, ?_⟩
  have hP : P = homogeneousComponent d P := by
    conv_lhs => rw [← sum_homogeneousComponent P]
    rw [Finset.sum_eq_single d]
    · intro i _ hi
      by_contra hne
      exact hi (by exact_mod_cast (h i hne).trans (h d hd).symm)
    · intro hdm
      exfalso
      apply hd
      apply homogeneousComponent_eq_zero
      rw [Finset.mem_range] at hdm
      omega
  rw [hP]
  exact homogeneousComponent_mem d P

end Grade

section Ops

variable {p q r s : ℕ}

theorem hc_raiLow (l l' : Ln p q r s) (h : linePos l = linePos l') (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e ((raiB l * lowB l') Q) = (raiB l * lowB l') (homogeneousComponent e Q) := by
  rw [Module.End.mul_apply, Module.End.mul_apply]
  cases hl : linePos l with
  | true =>
    have hl' : linePos l' = true := by rw [← h, hl]
    simp only [raiB, lowB, hl, hl', if_true, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [hc_X]
    cases e with
    | zero => simp
    | succ k => simp [PI.WFJM.hc_pderiv]
  | false =>
    have hl' : linePos l' = false := by rw [← h, hl]
    simp only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, LinearMap.neg_apply]
    rw [map_neg, PI.WFJM.hc_pderiv, hc_X, if_pos (by omega)]
    simp

theorem sameBlock_linePos_first {a b : Ix p q} (hab : sameBlock a b) (c : Ix r s) :
    linePos ((a, c) : Ln p q r s) = linePos ((b, c) : Ln p q r s) := by
  cases a <;> cases b <;> cases c <;> simp [sameBlock, linePos] at hab ⊢

theorem sameBlock_linePos_second {c d : Ix r s} (hcd : sameBlock c d) (a : Ix p q) :
    linePos ((a, c) : Ln p q r s) = linePos ((a, d) : Ln p q r s) := by
  cases c <;> cases d <;> cases a <;> simp [sameBlock, linePos] at hcd ⊢

theorem posC_sb {n m : ℕ} {a b : Ix n m} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> simp [posC, sameBlock] at h ⊢

theorem homogeneous_component_raise_first {a b : Ix p q} (hab : sameBlock a b) (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e (PI.FJM.rai1 (r := r) (s := s) a b Q) =
      PI.FJM.rai1 (r := r) (s := s) a b (homogeneousComponent e Q) := by
  simp only [PI.FJM.rai1, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => hc_raiLow _ _ (sameBlock_linePos_first hab c) e Q

theorem homogeneous_component_raise_second {c d : Ix r s} (hcd : sameBlock c d) (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e (PI.FJM.rai2 (p := p) (q := q) c d Q) =
      PI.FJM.rai2 (p := p) (q := q) c d (homogeneousComponent e Q) := by
  simp only [PI.FJM.rai2, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => hc_raiLow _ _ (sameBlock_linePos_second hcd a) e Q

theorem hc_mem_hwSub1 (μ : Ix p q → ℚ) (P : Pol p q r s) (hP : P ∈ hwSub (fockAct1 p q r s) μ) (e : ℕ) :
    homogeneousComponent e P ∈ hwSub (fockAct1 p q r s) μ := by
  rw [PI.WFJM.mem_hwSub1] at hP ⊢
  refine ⟨fun m hm a => hP.1 m (supp_hc hm) a, fun a b hab => ?_⟩
  rw [← homogeneous_component_raise_first (posC_sb hab), hP.2 a b hab, map_zero]

theorem hc_mem_hwSub2 (μ : Ix r s → ℚ) (P : Pol p q r s) (hP : P ∈ hwSub (fockAct2 p q r s) μ) (e : ℕ) :
    homogeneousComponent e P ∈ hwSub (fockAct2 p q r s) μ := by
  rw [PI.WFJM.mem_hwSub2] at hP ⊢
  refine ⟨fun m hm c => hP.1 m (supp_hc hm) c, fun c d hcd => ?_⟩
  rw [← homogeneous_component_raise_second (posC_sb hcd), hP.2 c d hcd, map_zero]

theorem span_jset (P : Pol p q r s) (hP : P ∈ Submodule.span ℂ (Jset p q r s)) : P ∈ Jset p q r s := by
  have key := PI.FJM.jointHarmonicsIffLaplacians p q r s
  induction hP using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact (key 0).2 ⟨fun i j => map_zero _, fun i j => map_zero _, fun k l => map_zero _,
      fun k l => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, a2, a3, a4⟩ := (key x).1 hx
    obtain ⟨b1, b2, b3, b4⟩ := (key y).1 hy
    exact (key (x + y)).2 ⟨fun i j => by rw [map_add, a1, b1, add_zero],
      fun i j => by rw [map_add, a2, b2, add_zero], fun k l => by rw [map_add, a3, b3, add_zero],
      fun k l => by rw [map_add, a4, b4, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨a1, a2, a3, a4⟩ := (key x).1 hx
    exact (key (c • x)).2 ⟨fun i j => by rw [map_smul, a1, smul_zero],
      fun i j => by rw [map_smul, a2, smul_zero], fun k l => by rw [map_smul, a3, smul_zero],
      fun k l => by rw [map_smul, a4, smul_zero]⟩

theorem jset_hc (P : Pol p q r s) (hP : P ∈ Jset p q r s) (e : ℕ) :
    homogeneousComponent e P ∈ Jset p q r s := by
  have key := PI.FJM.jointHarmonicsIffLaplacians p q r s
  obtain ⟨a1, a2, a3, a4⟩ := (key P).1 hP
  refine (key _).2 ⟨fun i j => ?_, fun i j => ?_, fun k l => ?_, fun k l => ?_⟩
  · exact low_hc _ (by unfold PI.FJM.lapA; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a1 i j) e
  · exact low_hc _ (by unfold PI.FJM.lapB; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a2 i j) e
  · exact low_hc _ (by unfold PI.FJM.lapC; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a3 k l) e
  · exact low_hc _ (by unfold PI.FJM.lapD; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a4 k l) e

end Ops

theorem minDegJ_of (hT1 : PI.FockOneDegW.HwHarmDeg) (hT2 : HwHarmDeg2) : PI.FJM.MinDegJ := by
  intro p q r s μ μ' P hP h0
  simp only [PI.FJM.JH, Submodule.mem_inf] at hP
  obtain ⟨⟨h1, h2⟩, hJ⟩ := hP
  have hJ' := span_jset P hJ
  refine ⟨exists_homog_of P h0 _ fun e he => ?_, exists_homog_of P h0 _ fun e he => ?_⟩
  · obtain ⟨j1, j2⟩ := jset_hc P hJ' e
    exact hT1 p q r s μ e _ (homogeneousComponent_mem e P) ⟨he, hc_mem_hwSub1 μ P h1 e⟩ j2
  · obtain ⟨j1, j2⟩ := jset_hc P hJ' e
    exact hT2 p q r s μ' e _ (homogeneousComponent_mem e P) ⟨he, hc_mem_hwSub2 μ' P h2 e⟩ j1

theorem minimal_degree_joint : PI.FJM.MinDegJ := minDegJ_of (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff)
  (fun p q r s μ e v hv hw hm => PI.FockOneDegW.Swap.hwHarmDeg2
    (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff) p q r s μ e v hv hw hm)

end PI.FJMF
