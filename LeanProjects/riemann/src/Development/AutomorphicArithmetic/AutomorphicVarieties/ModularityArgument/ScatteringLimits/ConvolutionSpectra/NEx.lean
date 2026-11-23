import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResCob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobTail
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResTail
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nEx :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), Function.Surjective (1 - M.abelian₂ M.T₀ M.T₀ ∘L M.F.av wR ∘L M.abelian₂ M.T₀ M.T₀ : H →L[ℂ] H) → ∃ N : W →ₗ[ℂ] V, M.IsN N := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M hs
  obtain ⟨c0, cadd, csmul, -, csh, -, -, -⟩ := cobLaws M.F
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have hP' := (projLaws M.swap).2.2.2.2.1
  obtain ⟨o1, o2, l0, -, -, l1, l2, l3, l4⟩ := hL M.T₀ M.T₀ (by linarith)
  set T := M.T₀ with hT
  set Λ := M.abelian₂ T T with hΛ
  have mI : ∀ x : ℝ, MeasurableSet (Ioi x) := fun _ => measurableSet_Ioi
  have carry : ∀ p : L V, Tail p → M.F.Cob (M.J p - M.J (one V (∫ x, p x))) := fun p hp => by
    have := (cobLaws (shF V)).2.2.2.2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) (fun t h => (M.hJ t h).symm) _
      ((cobTail p).2 hp).2
    rwa [map_sub] at this
  have ex : ∀ w, ∃ n, M.F.Cob (M.J' (one W w) - M.J (one V n)) := by
    intro w
    set h := M.F.U (T - 1) (M.J' (one W w)) with hh
    have s0 : M.P' (Ioc 0 1) (M.J' (one W w)) = M.J' (one W w) := by
      show M.J' (cut W _ (M.J'.symm (M.J' _))) = _
      rw [M.J'.symm_apply_apply, ((cutLaws (Ioc 0 1) univ measurableSet_Ioc .univ).2.2.2.2.2.2.2.1 _).2]
      exact ((svSpec (V := W)).2 w).1.mono fun x hx hn => by rw [hx, indicator_of_notMem hn]
    have s1 : M.P' (Ioc (T - 1) T) h = h := by
      have := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) .univ).2.2.2.2 (T - 1)).2 (M.J' (one W w))
      have y : (fun x : ℝ => x - (T - 1)) ⁻¹' Ioc 0 1 = Ioc (T - 1) T := by
        ext x; simp only [mem_preimage, mem_Ioc]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
      rw [y] at this
      simp only [ContinuousLinearMap.comp_apply, s0] at this
      exact this.symm
    have s2 : M.P' (Ioi T) h = 0 := by
      have a : M.P' (Ioi T) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi T ∩ Ioc (T - 1) T) := (hP' _ _ (mI T) measurableSet_Ioc).1
      have b : Ioi T ∩ Ioc (T - 1) T = ∅ := eq_empty_of_forall_notMem fun x hx => absurd hx.1 (not_lt.2 hx.2.2)
      rw [b, show M.P' ∅ = 0 from (projLaws M.swap).2.2.2.2.2.1] at a
      rw [← s1]; exact DFunLike.congr_fun a h
    have s3 : M.P (Ioi (T + 1)) h = 0 := by
      have a : M.P' (Ioi (T - 1)) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi (T - 1) ∩ Ioc (T - 1) T) := (hP' _ _ (mI _) measurableSet_Ioc).1
      rw [inter_eq_right.2 Ioc_subset_Ioi_self] at a
      rw [← s1, ← a]
      exact DFunLike.congr_fun (hL (T + 1) (T - 1) (by linarith)).1 _
    obtain ⟨k, hk⟩ := hs (Λ h)
    set R := M.F.av wR with hR
    have hk' : k - Λ (R (Λ k)) = Λ h := hk
    have ΛΛ : ∀ x, Λ (Λ x) = Λ x := fun x => DFunLike.congr_fun l0 x
    have kΛ : Λ k = k := by
      have := congrArg Λ hk'
      rw [map_sub, ΛΛ, ΛΛ, ← hk'] at this
      exact sub_left_injective this
    rw [kΛ] at hk'
    have k1 : M.P (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l2 k
    have k2 : M.P' (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l4 k
    have r2 : M.P' (Ioi T) (R k) = 0 := by
      obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avSpec M.F).2.1).1 k
      rw [hR, e, ← (M.P' (Ioi T)).integral_comp_comm i]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ≤ 0
      · have a := DFunLike.congr_fun ((hP _ _ (mI (T - r)) .univ).2.2.2.2 r).2 k
        have y : (fun x : ℝ => x - r) ⁻¹' Ioi (T - r) = Ioi T := by ext x; simp
        have b : M.P' (Ioi (T - r)) ∘L M.P' (Ioi T) = M.P' (Ioi (T - r) ∩ Ioi T) := (hP' _ _ (mI _) (mI _)).1
        rw [inter_eq_left.2 (Ioi_subset_Ioi (by linarith))] at b
        rw [y, ← b] at a
        simp only [ContinuousLinearMap.comp_apply, k2, map_zero] at a
        simp [← a]
      · simp [wR, hr]
    have dec : h = (k - R k) + M.P (Ioi T) (R k) + M.P (Ioi T) h := by
      have a : Λ h = h - M.P (Ioi T) h - M.P' (Ioi T) h := rfl
      have b : Λ (R k) = R k - M.P (Ioi T) (R k) - M.P' (Ioi T) (R k) := rfl
      rw [a, b, s2, r2, sub_zero, sub_zero] at hk'
      linear_combination (norm := module) -hk'
    have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
    set u := M.J.symm k with hu
    have u1 : cut V (Iic T) u = u := by
      have a := (cl (Iic T) (Ioi T) measurableSet_Iic (mI T)).2.2.1 (Iic_disjoint_Ioi le_rfl)
      rw [Iic_union_Ioi, (cl _ _ .univ .univ).2.2.2.1] at a
      have b : u = cut V (Iic T) u + cut V (Ioi T) u := DFunLike.congr_fun a u
      have c : cut V (Ioi T) u = 0 := M.J.injective (by rw [map_zero]; exact k1)
      rw [c, add_zero] at b
      exact b.symm
    have e1 : M.P (Ioi T) (R k) = M.J (cut V (Ioi T) ((shF V).av wR u)) := by
      have := DFunLike.congr_fun (((avSpec (shF V)).2.2.2 _ (avSpec M.F).2.1).2.2.2.2 M.F
        (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) fun t h => (M.hJ t h).symm) u
      have a : M.J ((shF V).av wR u) = R (M.J u) := this
      rw [hu, M.J.apply_symm_apply] at a
      show M.J (cut V _ (M.J.symm (R k))) = _
      rw [← a, M.J.symm_apply_apply]
    set v := cut V (Ioi T) (M.J.symm h) with hv
    have e2 : M.P (Ioi T) h = M.J v := rfl
    have bv : Bdd v := by
      refine ⟨|T| + 1, ?_⟩
      have a := (cl (Ioc T (T + 1)) (Ioi (T + 1)) measurableSet_Ioc (mI _)).2.2.1 (Ioc_disjoint_Ioi le_rfl)
      rw [Ioc_union_Ioi_eq_Ioi (by linarith)] at a
      have c : cut V (Ioi (T + 1)) (M.J.symm h) = 0 := M.J.injective (by rw [map_zero]; exact s3)
      have b : v = cut V (Ioc T (T + 1)) (M.J.symm h) := by rw [hv, a, ContinuousLinearMap.add_apply, c, add_zero]
      have d := (cl (Icc (-(|T| + 1)) (|T| + 1)) (Ioc T (T + 1)) measurableSet_Icc measurableSet_Ioc).1
      have sub : Ioc T (T + 1) ⊆ Icc (-(|T| + 1)) (|T| + 1) := fun x hx =>
        ⟨by linarith [hx.1, neg_abs_le T], by linarith [hx.2, le_abs_self T]⟩
      rw [inter_eq_right.2 sub] at d
      rw [b]
      exact DFunLike.congr_fun d _
    have f1 := carry _ (resTail u T u1)
    have f2 := carry _ ((cobTail v).1 bv)
    have f3 := (cadd _ _ (cadd _ _ (cadd _ _ (csh (T - 1) (M.J' (one W w))) (resCob M.F k).1).1 f1).1 f2).1
    refine ⟨(∫ x, cut V (Ioi T) ((shF V).av wR u) x) + ∫ x, v x, ?_⟩
    convert f3 using 1
    rw [← e1, ← e2, map_add, map_add, ← hh, ← hR]
    linear_combination (norm := module) dec
  choose n hn using ex
  let b := Module.finBasis ℂ W
  refine ⟨b.constr ℂ fun i => n (b i), fun w => ?_⟩
  have e : M.J' (one W w) - M.J (one V (b.constr ℂ (fun i => n (b i)) w)) =
      ∑ i, b.repr w i • (M.J' (one W (b i)) - M.J (one V (n (b i)))) := by
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul, Module.Basis.constr_basis, smul_sub, Finset.sum_sub_distrib]
  rw [e]
  exact Finset.sum_induction _ _ (fun x y hx hy => (cadd x y hx hy).1) c0 fun i _ => csmul _ _ (hn _)
