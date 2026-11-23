import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalRingCardinality.DataCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.DualWeyl GlobalTheory.CompactDS
open Formalism.GradedWeylDivisibility (rowAct rowDeg)
open scoped Matrix

noncomputable section

namespace GlobalTheory.NablaType

variable {n : ℕ}

theorem cdom_of_partial_sums (μ ν : Fin n → ℕ)
    (h : ∀ k : ℕ, (∑ a : Fin n with a.val < k, μ a) ≤ ∑ a : Fin n with a.val < k, ν a)
    (he : ∑ a, μ a = ∑ a, ν a) : CDom (allPos n) (fun a => (μ a : ℝ)) (fun a => (ν a : ℝ)) := by
  classical
  let D : ℕ → ℕ := fun k => (∑ a : Fin n with a.val < k, ν a) - ∑ a : Fin n with a.val < k, μ a
  have hD : ∀ k, (D k : ℝ) = ∑ a : Fin n, if a.val < k then ((ν a : ℝ) - μ a) else 0 := by
    intro k
    simp only [D]
    rw [Nat.cast_sub (h k), ← Finset.sum_filter, Finset.sum_sub_distrib]
    push_cast
    rfl
  have hstep : ∀ i : Fin n, (D (i.val + 1) : ℝ) - D i.val = (ν i : ℝ) - μ i := by
    intro i
    rw [hD, hD, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : b.val ≠ i.val := fun e => hb (Fin.ext e)
      by_cases h1 : b.val < i.val
      · rw [if_pos h1, if_pos (by omega), sub_self]
      · rw [if_neg h1, if_neg (by omega), sub_self]
    · simp
  have h0 : D 0 = 0 := by simp [D]
  have hn : D n = 0 := by simp [D, he]
  refine ⟨fun a b => if b.val = a.val + 1 then D b.val else 0, fun a b hab => ?_, ?_⟩
  · have : b.val = a.val + 1 := by by_contra h'; exact hab (if_neg h')
    exact ⟨Fin.lt_def.2 (by omega), rfl⟩
  · funext i
    have e1 : ∑ b : Fin n, ((if b.val = i.val + 1 then D b.val else 0 : ℕ) : ℝ) = D (i.val + 1) := by
      by_cases hi : i.val + 1 < n
      · rw [Finset.sum_eq_single ⟨i.val + 1, hi⟩]
        · simp
        · intro b _ hb
          rw [if_neg (fun e => hb (Fin.ext e)), Nat.cast_zero]
        · simp
      · rw [Finset.sum_eq_zero, show i.val + 1 = n by omega, hn, Nat.cast_zero]
        intro b _
        rw [if_neg (by omega), Nat.cast_zero]
    have e2 : ∑ a : Fin n, ((if i.val = a.val + 1 then D i.val else 0 : ℕ) : ℝ) = D i.val := by
      by_cases hi : 0 < i.val
      · rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
        · rw [if_pos (by simp only; omega)]
        · intro b _ hb
          rw [if_neg (fun e => hb (Fin.ext (by simp only; omega))), Nat.cast_zero]
        · simp
      · rw [Finset.sum_eq_zero, show i.val = 0 by omega, h0, Nat.cast_zero]
        intro b _
        rw [if_neg (by omega), Nat.cast_zero]
    rw [Pi.sub_apply, ← hstep, ← e1, ← e2]
    simp only [Finset.sum_apply, Pi.smul_apply, Formalism.REAL.root, Pi.sub_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero]
    congr 1
    · rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem cdom_of_coeff_ne_zero {la : Fin n → ℕ} {f : Pol n ℂ} (hf : f ∈ nabla la ℂ) (m : Fin n × Fin n →₀ ℕ)
    (hm : coeff m f ≠ 0) : CDom (allPos n) (fun a => (rowDeg m a : ℝ)) (fun a => (la a : ℝ)) := by
  unfold nabla at hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ n n la] at hf
  by_contra hc
  apply hm
  clear hm
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, rfl, rfl⟩ := hx
    by_contra h0
    obtain ⟨h1, h2⟩ := Formalism.GradedWeylDivisibility.bidetDominance ℂ n n K sz hsz I m (mem_support_iff.2 h0)
    exact hc (cdom_of_partial_sums _ _ h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [coeff_add, hx, hy, add_zero]
  | smul c x _ hx => rw [coeff_smul, hx, smul_zero]

def act (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) : Space lam.natW →L[ℂ] Space lam.natW :=
  LinearMap.toContinuousLinearMap
    ((g.det ^ lam.detShift) • ((toSpace lam.natW).conj (rho lam.natW ℂ g)))

def incl (lam : DomWeight n) : Space lam.natW →ₗ[ℂ] Pol n ℂ :=
  (nabla lam.natW ℂ).subtype ∘ₗ (toSpace lam.natW).symm.toLinearMap

theorem incl_injective (lam : DomWeight n) : Function.Injective (incl lam) :=
  (nabla lam.natW ℂ).injective_subtype.comp (toSpace lam.natW).symm.injective

theorem incl_mem (lam : DomWeight n) (x : Space lam.natW) : incl lam x ∈ nabla lam.natW ℂ :=
  ((toSpace lam.natW).symm x).2

theorem incl_act (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) (x : Space lam.natW) :
    incl lam (act lam g x) = (g.det ^ lam.detShift) • rowAct ℂ gᵀ (incl lam x) := rfl

theorem act_unitary (lam : DomWeight n) (u : UN n) (x : Space lam.natW) :
    act lam u.1 x = (u.1.det ^ lam.detShift) • rhoSpace lam.natW u x := rfl

theorem det_ne_zero {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ) : g.det ≠ 0 :=
  (Matrix.UnitaryGroup.det_isUnit ⟨g, hg⟩).ne_zero

theorem isURepOn_act (lam : DomWeight n) : IsURepOn (UJset (allPos n)) (act lam) := by
  rw [ujset_eq]
  refine ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · ext x
    apply incl_injective
    rw [incl_act, Matrix.transpose_one, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
    simp
  · ext x
    apply incl_injective
    rw [ContinuousLinearMap.comp_apply, incl_act, incl_act, incl_act, Matrix.transpose_mul,
      ← Formalism.GradedWeylDivisibility.rowActMul ℂ n n, Matrix.det_mul, mul_zpow, map_smul, smul_smul]
    rfl
  · have h1 : ‖g.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hg)
    rw [act_unitary lam ⟨g, hg⟩, norm_smul, norm_zpow, h1, one_zpow, one_mul, norm_rhoSpace]
  · rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun u : UN n => u.1.det ^ lam.detShift :=
      (continuous_subtype_val.matrix_det).zpow₀ _ fun u => Or.inl (det_ne_zero u.2)
    exact h1.smul (continuous_rhoSpace v)

theorem coeff_torus (lam : DomWeight n) (θ : Fin n → ℝ) (x : Space lam.natW) (m : Fin n × Fin n →₀ ℕ) :
    coeff m (incl lam (act lam (torus θ) x)) =
      chr (fun a => (rowDeg m a : ℝ) + lam.detShift) θ * coeff m (incl lam x) := by
  rw [incl_act, torus, Matrix.diagonal_transpose, coeff_smul, Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, Matrix.det_diagonal,
    smul_eq_mul, mul_left_comm, mul_comm]
  congr 1
  simp only [← Complex.exp_nat_mul]
  rw [chr, ← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem natW_add (lam : DomWeight n) (a : Fin n) : (lam.natW a : ℝ) + lam.detShift = lam.w a := by
  exact_mod_cast (factNatW n lam).2.1 a

theorem isKTypeOf_act (lam : DomWeight n) : IsKTypeOf (allPos n) (act lam) (fun a => (lam.w a : ℝ)) ⊤ := by
  have ha := (factNatW n lam).1
  refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => ?_, ?_, fun μ v _ hv hw => ?_⟩
  · by_cases h0 : S = ⊥
    · exact Or.inl h0
    right
    have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ S.map (incl lam), rowAct ℂ u f ∈ S.map (incl lam) := by
      rintro u hu _ ⟨f, hf, rfl⟩
      have hu' := transpose_mem_unitaryGroup hu
      have h1 : incl lam (act lam uᵀ f) ∈ S.map (incl lam) := ⟨_, hS _ (by rw [kset_eq]; exact hu') f hf, rfl⟩
      rw [incl_act, Matrix.transpose_transpose] at h1
      exact (Submodule.smul_mem_iff _ (zpow_ne_zero _ (det_ne_zero hu'))).1 h1
    have hcl := GlobalTheory.Branching.rowDivClosed_of_rowAct_stable _ (GlobalTheory.Branching.rowAct_mem_of_unitary_stable _ hU)
    have hne : S.map (incl lam) ≠ ⊥ := fun e => h0 (Submodule.map_injective_of_injective (incl_injective lam)
      (e.trans (Submodule.map_bot _).symm))
    have hle := GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl lam.natW ha _
      (by rintro _ ⟨f, -, rfl⟩; exact incl_mem lam f) hcl hne
    refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨g, hg, e⟩ := hle (incl_mem lam f)
    rwa [← incl_injective lam e]
  · refine ⟨toSpace _ ⟨_, extremal_mem ha⟩, trivial, fun h => ?_, fun θ _ => ?_⟩
    · exact extremal_ne_zero (congrArg (incl lam) h)
    · apply incl_injective
      ext m
      have h1 := coeff_torus lam θ (toSpace _ ⟨_, extremal_mem ha⟩) m
      refine h1.trans ?_
      rw [map_smul, coeff_smul, smul_eq_mul]
      by_cases hm : coeff m (incl lam (toSpace _ ⟨_, extremal_mem ha⟩)) = 0
      · rw [hm, mul_zero, mul_zero]
      have h2 := Formalism.GradedWeylDivisibility.hwRowWeight ℂ n n le_rfl lam.natW ha hm
      have h3 : (fun a => (rowDeg m a : ℝ) + lam.detShift) = fun a => (lam.w a : ℝ) := by
        funext a
        rw [← natW_add, ← Formalism.GradedWeylDivisibility.ldrow_weight_rowW, h2]
        simp [Formalism.GradedWeylDivisibility.rowNu]
      rw [h3]
      rfl
  · have h0 : incl lam v ≠ 0 := fun e => hv (incl_injective lam (e.trans (map_zero _).symm))
    obtain ⟨m, hm⟩ := ne_zero_iff.1 h0
    have h1 : μ = fun a => (rowDeg m a : ℝ) + lam.detShift := by
      refine chr_inj fun θ => ?_
      have h2 := coeff_torus lam θ v m
      have h3 : act lam (torus θ) v = chr μ θ • v := hw θ (by rw [kset_eq]; exact torus_mem θ)
      rw [h3, map_smul, coeff_smul, smul_eq_mul] at h2
      exact mul_right_cancel₀ hm h2
    have h4 := cdom_add (cdom_of_coeff_ne_zero (incl_mem lam v) m hm)
      (cdom_refl (allPos n) fun _ => (lam.detShift : ℝ))
    rw [h1]
    have h5 : (fun a => (lam.w a : ℝ)) = (fun a => (lam.natW a : ℝ)) + fun _ => (lam.detShift : ℝ) :=
      funext fun a => (natW_add lam a).symm
    rw [h5]
    exact h4

theorem exists_isHCTypeU_nablaSq : ∀ (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n), ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (e : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), Formalism.MainNotions.S.IsHCTypeU n (fun i => (lam.w i : ℝ) + ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ)) π ∧ Function.Injective e ∧ (∀ x, e x ∈ Formalism.BasicNotions.nablaSq ℂ n lam) ∧ ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ x, e (π (g : Matrix (Fin n) (Fin n) ℂ) x) = Formalism.BasicNotions.sqAct ℂ n lam g (e x) := by
  intro n lam
  have hK := isKTypeOf_act lam
  refine ⟨Space lam.natW, inferInstance, inferInstance, act lam, incl lam,
    ⟨?_, inferInstance, isURepOn_act lam, ?_⟩, incl_injective lam, incl_mem lam, fun g _ x => ?_⟩
  · obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
    exact ⟨v, 0, hv⟩
  · convert hK using 1
    funext a
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.lowK_const]
    simp [rhoVec]
  · rw [incl_act]
    simp [sqAct, detPow]

end GlobalTheory.NablaType
