import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.IndicatorRholMem
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SASingle
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Transfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OpEqExp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

noncomputable section

open Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def submoduleEvaluationFunctional {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H} (V : Submodule ℂ D)
    (w0 : V) : V →ₗ[ℂ] ℂ where
  toFun v := ⟪((w0 : D) : H), ((v : D) : H)⟫_ℂ
  map_add' x y := by simp [inner_add_right]
  map_smul' c x := by simp [inner_smul_right]

theorem lowestKType_vector_exists (ε : Fin n → Bool) (lam : Fin n → ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (T : KType ε (lowK ε lam)) (ι : V ≃ₗ[ℂ] T.V)
    (hιK : ∀ (k : KG ε) (v w : V), ((w : D) : H) = σ (toMK k) ((v : D) : H) → ι w = T.op k (ι v)) :
    IsKHWVec ε E (lowK ε lam) ((ι.symm T.w : V) : D) := by
  have := hV.1
  have hVK : ∀ (k : KG ε) (v : V), ∃ w : V, ((w : D) : H) = σ (toMK k) ((v : D) : H) := by
    intro k v
    obtain ⟨Z, hZ, he⟩ := HW.exists_log ε k
    have hs := KTypeIsomorphism.orbit_hasSum hσ hD hV.1 hV.2.1 hZ v
    let P : Submodule ℂ H := LinearMap.range (D.subtype ∘ₗ V.subtype)
    have hmem : σ (NormedSpace.exp Z) ((v : D) : H) ∈ P :=
      P.closed_of_finiteDimensional.mem_of_tendsto hs (Filter.Eventually.of_forall fun t =>
        P.sum_mem fun m _ => P.smul_mem _ ⟨_, rfl⟩)
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, by rw [he]; exact hw⟩
  let L : T.V →L[ℂ] H := LinearMap.toContinuousLinearMap (D.subtype ∘ₗ V.subtype ∘ₗ ι.symm.toLinearMap)
  have hK : ∀ X, inK ε X → ((actM E X ((ι.symm T.w : V) : D) : D) : H) = L (T.dτ X T.w) := by
    intro X hX
    obtain ⟨γ, hγ⟩ := HW.exists_curve ε hX
    have h1 := ((L.comp (ContinuousLinearMap.apply ℂ T.V T.w)).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (T.hasDeriv X hX γ hγ)
    refine (hD.deriv X hX.1 _).unique (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
    obtain ⟨w, hw⟩ := hVK (γ t) (ι.symm T.w)
    have h2 := hιK (γ t) _ w hw
    rw [ι.apply_symm_apply] at h2
    show σ _ _ = ((ι.symm (T.op (γ t) T.w) : D) : H)
    rw [← h2, ι.symm_apply_apply, hw, hγ]
  have hC : ∀ a b, ε a = ε b →
      ((E a b ((ι.symm T.w : V) : D) : D) : H) = L (T.dτ (Matrix.single a b 1) T.w) := by
    intro a b hab
    have hZ : (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
      ext i j
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
      split_ifs with h <;> simp_all
    have hJ : Jm ε * Jm ε = 1 := by
      rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp
    have hJh : (Jm ε).conjTranspose = Jm ε := by
      rw [Jm, Matrix.diagonal_conjTranspose]; congr 1; funext i
      simp only [Pi.star_apply]; split_ifs <;> simp
    have hZ' : Jm ε * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * Jm ε =
        Jm ε * (Jm ε * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε) := by
      have := congrArg Matrix.conjTranspose hZ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh] at this
      rw [Matrix.mul_assoc _ (Jm ε) (Jm ε), hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        hJ, Matrix.one_mul, this]
    have k1 : inK ε (cpart1 ε (Matrix.single a b 1)) := ⟨ta_inG_cpart1 ε _, by
      simp only [cpart1, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, hZ, hZ']⟩
    have k2 : inK ε (cpart2 ε (Matrix.single a b 1)) := ⟨ta_inG_cpart2 ε _, by
      simp only [cpart2, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hZ, hZ']⟩
    rw [← TRA.actM_single E a b, TRA.act_cpart (ε := ε), Submodule.coe_add, Submodule.coe_smul,
      hK _ k1, hK _ k2]
    conv_rhs => rw [← ta_cpart_sum ε (Matrix.single a b 1), map_add, map_smul, _root_.add_apply,
      _root_.smul_apply, map_add, map_smul]
  refine ⟨fun a => Subtype.ext ?_, fun a b hab he => Subtype.ext ?_⟩
  · rw [hC a a rfl, T.w_wt a, map_smul]; rfl
  · rw [hC a b he, T.w_hw a b hab he, map_zero]; rfl

theorem lowestKType_trace_integral (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (ι : V ≃ₗ[ℂ] T.V) (hμ : IsMu lam μ)
    (hcoef : ∀ g : Matrix (Fin n) (Fin n) ℂ, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', PsiM T μ g (ι v)⟫_ℂ)
    (W : Submodule ℂ (KS (n := n) V)) (hW : IsKStableSub ε (sA ε E V hV.2.1) W)
    (hθ : ∀ x ∈ W, sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) x = 0) :
    ∀ x ∈ W, sT E V x = 0 := by
  have := hV.1
  intro x hx
  funext c
  set w0 : H := (((ι.symm T.w : V) : D) : H) with hw0
  have hsT : sT E V x c = ∑ p ∈ x.support, if p.2 = c then wordE E p.1 (x p : D) else 0 := by
    conv_lhs => rw [← Finsupp.sum_single x, Finsupp.sum, map_sum, Finset.sum_apply]
    refine sum_congr rfl fun p _ => ?_
    rw [show p = (p.1, p.2) from rfl, sT_single, Pi.single_apply]
    simp only [eq_comm]
  have hword : ∀ w : List (Fin n × Fin n),
      ((w.map fun p => (Matrix.single p.1 p.2 1 : Matrix (Fin n) (Fin n) ℂ)).map (actM E)).prod =
        wordE E w := fun w => by
    rw [List.map_map, wordE]; congr 2; funext p; exact TRA.actM_single E p.1 p.2
  have h1J : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
    show (1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * 1 = Jm ε
    simp
  refine TRA.eq_zero_of_coef hσ hD (V := V) ?_ fun g hg v' => ?_
  · rw [hsT]
    refine Submodule.sum_mem _ fun p _ => ?_
    split_ifs
    · generalize p.1 = w
      induction w with
      | nil => exact Submodule.mem_sInf.mpr fun S hS => hS.1 (x p).2
      | cons q w ih => exact Submodule.mem_sInf.mpr fun S hS => hS.2 _ _ _ (Submodule.mem_sInf.mp ih S hS)
    · exact Submodule.zero_mem _
  let e := x.support.equivFin
  have hsum : ∀ F : List (Fin n × Fin n) × Fin n → ℂ, ∑ i, F (e.symm i) = ∑ p ∈ x.support, F p :=
    fun F => by rw [Equiv.sum_comp e.symm (fun p : x.support => F p), Finset.sum_coe_sort]
  have key := transfer n ε lam T μ ⟨hanti, hint⟩ hμ _
    (fun i => (e.symm i).1.1.map fun p => (Matrix.single p.1 p.2 1 : Matrix (Fin n) (Fin n) ℂ))
    (fun i => if (e.symm i).1.2 = c then ι (x (e.symm i)) else 0) ?_ g hg
  · have h2 := congrArg (fun u => ⟪ι v', u⟫_ℂ) key
    simp only [inner_sum, inner_zero_right] at h2
    rw [hsum fun p => ⟪ι v', rWord ε (p.1.map fun q =>
      (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ)) (PsiM T μ) g
        (if p.2 = c then ι (x p) else 0)⟫_ℂ] at h2
    rw [hsT, ← h2, Submodule.coe_sum, map_sum, inner_sum]
    refine sum_congr rfl fun p _ => ?_
    split_ifs
    · rw [TRA.rWord_coef hσ hD ι _ hcoef _ g hg, hword]
    · simp
  intro k z hz
  obtain ⟨X, hX, he⟩ := HW.exists_log ε k
  have he1 : NormedSpace.exp (((1 : ℝ) : ℂ) • X) = toMK k := by rw [he]; simp
  have hinv : toMK k * TRA.ei X 1 = 1 := by
    rw [← he1, TRA.ei, ← exp_add_smul]; simp
  have hki : toMK k⁻¹ = TRA.ei X 1 := by
    rw [← Matrix.mul_one (toMK k⁻¹), ← hinv, ← Matrix.mul_assoc, toMK_inv_mul', Matrix.one_mul]
  have hXi : ∀ c', TRA.Xi σ V w0 (eMM μ) (phiMM μ) (TRA.evZ μ z) c' X 1 x = 0 := fun c' =>
    TRA.Xi_vanish hσ hD hV.2.1 w0 _ _ _ c' hX W hW (fun y hy => by
      have h0 : ∀ y, TRA.Xi σ V w0 (eMM μ) (phiMM μ) (TRA.evZ μ z) c' X 0 y =
          TRA.evZ μ z (sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) y c') := by
        intro y
        induction y using Finsupp.induction_linear with
        | zero => simp
        | add y y' h h' => simp only [map_add, Pi.add_apply, h, h']
        | single p v =>
          have e0 : TRA.ei X 0 = 1 := by simp [TRA.ei]
          have e1 : TRA.wB (eMM μ) (phiMM μ) X 0 p.1 = wordE (eMM μ) p.1 (phiMM μ) := by
            simp [TRA.wB, TRA.cj, e0, TRA.actM_single, wordE]
          have e2 : TRA.aF σ V w0 1 v = submoduleEvaluationFunctional V (ι.symm T.w) v := by
            show ⟪w0, σ 1 _⟫_ℂ = _
            rw [hσ.1.1]; rfl
          rw [TRA.Xi_single, e0, e1, e2, show p = (p.1, p.2) from rfl, sθ_single, Pi.single_apply,
            Matrix.one_apply]
          split_ifs <;> simp [mul_comm]
      rw [h0, hθ y hy, Pi.zero_apply, map_zero]) 1 x hx
  let a : List (Fin n × Fin n) × Fin n → ℂ := fun p => ⟪T.op k T.w, ι (x p)⟫_ℂ *
    hWord (adW ε k (p.1.map fun q => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))) (PhiP μ) z
  have hXa : ∀ c', ∑ p ∈ x.support, TRA.ei X 1 c' p.2 * a p = 0 := fun c' => by
    rw [← hXi c']
    conv_rhs => rw [← Finsupp.sum_single x, Finsupp.sum, map_sum]
    refine sum_congr rfl fun p _ => ?_
    have e1 : TRA.evZ μ z (TRA.wB (eMM μ) (phiMM μ) X 1 p.1) = hWord (adW ε k (p.1.map fun q =>
        (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))) (PhiP μ) z := by
      rw [← TRA.evZ_word μ _ z hz, adW, List.map_map, List.map_map, hki, ← he1]; rfl
    have e2 : TRA.aF σ V w0 (TRA.ei X 1) (x p) = ⟪T.op k T.w, ι (x p)⟫_ℂ := by
      have hP : PsiM T μ (toMK k⁻¹) = T.op k⁻¹ := by
        have := psiM_equiv T μ k⁻¹ 1 h1J
        rwa [toMK_one', Matrix.mul_one, Matrix.mul_one, psiM_one, op_one', mul_one, mul_one] at this
      have h3 := hcoef (toMK k⁻¹) (k⁻¹).1.2 (x p) (ι.symm T.w)
      rw [ι.apply_symm_apply, hP] at h3
      rw [← hki]
      refine h3.trans ?_
      have hu : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).2
      have h4 : T.op k⁻¹ = star (T.op k) := by
        rw [← one_mul (T.op k⁻¹), ← hu, mul_assoc, ← op_mul', mul_inv_cancel, op_one', mul_one]
      rw [h4, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    rw [TRA.Xi_single, e1, e2]
    simp only [a]; ring
  rw [hsum fun p => ⟪T.op k T.w, if p.2 = c then ι (x p) else 0⟫_ℂ *
    hWord (adW ε k (p.1.map fun q => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))) (PhiP μ) z]
  calc _ = ∑ p ∈ x.support, (toMK k * TRA.ei X 1) c p.2 * a p := sum_congr rfl fun p _ => by
        rw [hinv, Matrix.one_apply]
        by_cases h : p.2 = c
        · simp [h, a]
        · simp [h, Ne.symm h]
    _ = ∑ c', toMK k c c' * ∑ p ∈ x.support, TRA.ei X 1 c' p.2 * a p := by
        simp only [Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]
        exact sum_comm
    _ = 0 := by simp [hXa]

theorem lowestKType_trace (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (hgap : GapLap ε lam h) (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε)
    (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (ι : V ≃ₗ[ℂ] T.V) (hμ : IsMu lam μ)
    (hιK : ∀ (k : KG ε) (v w : V), ((w : D) : H) = σ (toMK k) ((v : D) : H) → ι w = T.op k (ι v))
    (hcoef : ∀ g : Matrix (Fin n) (Fin n) ℂ, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', PsiM T μ g (ι v)⟫_ℂ)
    (W : Submodule ℂ (KS (n := n) V)) (hW : IsKStableSub ε (sA ε E V hV.2.1) W)
    (hθ : ∀ x ∈ W, sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) x = 0) :
    ∀ x ∈ W, sT E V x = 0 := by
  exact lowestKType_trace_integral ε lam H σ D E V hσ hD hV hint hanti T μ ι hμ hcoef W hW hθ

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
