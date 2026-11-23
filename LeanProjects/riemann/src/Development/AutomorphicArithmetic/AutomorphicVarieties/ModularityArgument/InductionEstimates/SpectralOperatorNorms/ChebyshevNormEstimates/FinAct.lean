import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.RepsRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeP

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.FinA

variable {K : Type} [Field K] [NumberField K]

local notation "pf" => MultiplicityOne.finProj K (2 + 2)
local notation "GF" => AdelicGLn.FiniteAdelicGL K (2 + 2)

theorem bf_fin {β : ℝ → ℂ} (hβ : HasCompactSupport β) (f : G1 K (2 + 2) → ℂ) (g : G1 K (2 + 2)) :
    (Function.support fun q : Cos K => bf β f ((q.out : G1 K (2 + 2)) * g)).Finite := by
  obtain ⟨R, hR⟩ := hβ.isCompact.bddBelow
  refine (locFin {g} R isCompact_singleton).subset fun q hq => ⟨g, rfl, hR (subset_tsupport _ fun h0 => hq ?_)⟩
  simp only [bf, h0, zero_mul]

theorem th_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → G1 K (2 + 2) → ℂ) (g : G1 K (2 + 2))
    (h : ∀ i ∈ s, (Function.support fun q : Cos K => F i ((q.out : G1 K (2 + 2)) * g)).Finite) :
    ∑ i ∈ s, c i * th (F i) g = th (fun x => ∑ i ∈ s, c i * F i x) g := by
  simp only [th]
  rw [finsum_sum_comm s _ fun i hi => (h i hi).subset fun q hq h0 => hq (by simp only [h0, mul_zero])]
  exact Finset.sum_congr rfl fun i hi => mul_finsum' _ _ (h i hi)

theorem regroup (s : Finset GF) (c : GF → ℂ) (T : Finset ℝ) (hT : ∀ h ∈ s, ∀ x, dl x h ∈ T) (w γ : ℝ → ℂ) (f : G1 K (2 + 2) → ℂ)
    (x : G1 K (2 + 2)) : ∑ t ∈ T, γ t * lin s c (fun r => if r = t then w r else 0) f x =
      ∑ h ∈ s, c h * (γ (dl x h) * w (dl x h) * f (x * pf h)) := by
  simp only [lin_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.sum_eq_single_of_mem _ (hT h hh x) fun t _ ht => by simp only [if_neg ht.symm, mul_zero, zero_mul], if_pos rfl]
  ring

theorem theta_id {β : ℝ → ℂ} (hβc : HasCompactSupport β) (s : Finset GF) (c : GF → ℂ) (T : Finset ℝ) (hT : ∀ h ∈ s, ∀ x, dl x h ∈ T)
    (f : G1 K (2 + 2) → ℂ) (fU : ℝ → G1 K (2 + 2) → ℂ)
    (hU : ∀ t, fU t = lin s c (fun r => if r = t then Complex.exp (2 * (r : ℂ)) else 0) f) :
    (fun y => ∑ h ∈ s, c h * theta β f (y * pf h)) = fun y => ∑ t ∈ T, 1 * theta (fun x => β (x + t)) (fU t) y := by
  funext y
  have hβt : ∀ t : ℝ, HasCompactSupport fun x => β (x + t) := fun t => hβc.comp_homeomorph (Homeomorph.addRight t)
  have e1 : ∀ h : GF, theta β f (y * pf h) = th (fun x => bf β f (x * pf h)) y := fun h => by
    simp only [theta_eq, th, mul_assoc]
  simp only [e1, theta_eq]
  rw [th_sum s c _ y fun h _ => by simpa only [mul_assoc] using bf_fin hβc f (y * pf h),
    th_sum T _ _ y fun t _ => bf_fin (hβt t) _ y]
  congr 1
  funext x
  have := regroup s c T hT (fun r => Complex.exp (2 * (r : ℂ)))
    (fun t => β (HP 2 2 x + t) * Complex.exp ((((2 + 2 : ℕ) : ℝ) / 2 * HP 2 2 x : ℝ) : ℂ)) f x
  have hH : ∀ (h : GF), HP 2 2 (x * pf h) = HP 2 2 x + dl x h := fun h => by rw [dl]; ring
  simp only [bf, hU, one_mul, hH]
  rw [this]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_assoc (β _) (Complex.exp _) (Complex.exp _), ← Complex.exp_add]
  congr 4
  push_cast
  ring

theorem flat_id (z : ℂ) (s : Finset GF) (c : GF → ℂ) (T : Finset ℝ) (hT : ∀ h ∈ s, ∀ x, dl x h ∈ T)
    (f : G1 K (2 + 2) → ℂ) (fU : ℝ → G1 K (2 + 2) → ℂ)
    (hU : ∀ t, fU t = lin s c (fun r => if r = t then Complex.exp (2 * (r : ℂ)) else 0) f) (x : G1 K (2 + 2)) :
    ∑ h ∈ s, c h • flat z f (x * pf h) = flat z (fun x => ∑ t ∈ T, Complex.exp (z * t) * fU t x) x := by
  have h2 := regroup s c T hT (fun r => Complex.exp (2 * (r : ℂ))) (fun t => Complex.exp (z * t)) f x
  have hH : ∀ (h : GF), HP 2 2 (x * pf h) = HP 2 2 x + dl x h := fun h => by rw [dl]; ring
  simp only [flat, hU, hH, smul_eq_mul]
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  have e : Complex.exp ((z + 2) * ((HP 2 2 x + dl x h : ℝ) : ℂ)) =
      Complex.exp ((z + 2) * (HP 2 2 x : ℂ)) * (Complex.exp (z * (dl x h : ℂ)) * Complex.exp (2 * (dl x h : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  ring

theorem act_of {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) (T : Finset ℝ) (U : ℝ → V →L[ℂ] V)
    (h : ∀ x, Y (J x) = ∑ t ∈ T, J ((U t).compLpL 2 volume (sh V t x))) : Act J Y fun z => ∑ t ∈ T, Complex.exp (z * t) • U t := by
  classical
  have h0 : ∀ y : L V, (0 : V →L[ℂ] V).compLpL 2 volume y = 0 := fun y => by
    refine Lp.ext ?_
    filter_upwards [(0 : V →L[ℂ] V).coeFn_compLpL (p := 2) (μ := volume) y, Lp.coeFn_zero V 2 (volume : Measure ℝ)] with x h1 h2
    rw [h1, h2]; rfl
  have hc : ∀ y : L V, conv (0 : ℝ → V →L[ℂ] V) y = 0 := fun y => by
    have := Classical.epsilon_spec (p := fun C : L V →L[ℂ] L V => ∀ u, ∀ᵐ x : ℝ, C u x = ∫ t : ℝ, (0 : ℝ → V →L[ℂ] V) t (u (x + t)))
      ⟨0, fun u => (Lp.coeFn_zero V 2 (volume : Measure ℝ)).mono fun x hx => by simpa using hx⟩ y
    refine Lp.ext ?_
    filter_upwards [this, Lp.coeFn_zero V 2 (volume : Measure ℝ)] with x h1 h2
    rw [h2]
    exact h1.trans (by simp)
  refine ⟨Finsupp.onFinset T (fun t => if t ∈ T then U t else 0) fun t ht => by_contra fun hn => ht (if_neg hn), 0,
    ⟨continuous_const, HasCompactSupport.zero⟩, fun x => ?_, fun z => ?_⟩
  · rw [Finsupp.onFinset_sum (g := fun (t : ℝ) (c : V →L[ℂ] V) => c.compLpL 2 volume (sh V t x)) _ fun t => h0 _, hc, add_zero, h, map_sum]
    exact Finset.sum_congr rfl fun t ht => by rw [if_pos ht]
  · rw [Finsupp.onFinset_sum (g := fun (t : ℝ) (c : V →L[ℂ] V) => Complex.exp (z * t) • c) _ fun t => smul_zero _]
    simp only [symb, Pi.zero_apply, smul_zero, integral_zero, add_zero]
    exact Finset.sum_congr rfl fun t ht => by rw [if_pos ht]

theorem ofin_apply {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
    (e : TF K n) (w : L2 μ) : Ofin μ m e w = ∫ h, e h • rightRegularRep (Gam K n) μ (MultiplicityOne.finProj K n h) w ∂m :=
  UnitaryRep.integrated_ccToL1_apply _ m e w

set_option maxHeartbeats 2000000 in
theorem actEx [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} (h₁ : CuspIrr μ₂ τ₁) (h₂ : CuspIrr μ₂ τ₂) {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d)
    {Kf : Subgroup GF} (hL : D.Level Kf) (hle : Kf ≤ AdelicGLn.integralFiniteGL K (2 + 2)) (m : Measure GF) [m.IsHaarMeasure]
    (e : TF K (2 + 2)) (he : ∀ k ∈ Kf, ∀ h, e (k * h) = e h ∧ e (h * k) = e h) :
    (∃ s, Act A.J (Ofin μ m e) s ∧ ∀ (z : ℂ) (v : Eu d) (x : G1 K (2 + 2)),
        ∫ h, e h * flat z (A.sec v) (x * pf h) ∂m = flat z (A.sec (s z v)) x) ∧ ∀ u, ∃ u', Ofin μ m e (A.J u) = A.J u' := by
  classical
  obtain ⟨s, c, hr⟩ := rule_ex hL hle m e fun k hk h => (he k hk h).2
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hU : ∀ ω : ℝ → ℂ, ∃ U : Eu d →L[ℂ] Eu d, ∀ v, A.sec (U v) = lin s c ω (A.sec v) := fun ω => by
    have hm : ∀ v, (lin s c ω ∘ₗ A.sec) v ∈ LinearMap.range A.sec := fun v => by
      have hf := lin_fix hL hle (fun k hk h => (he k hk h).1) hr ω (hsec v).1.cont (hsec v).2
      exact (A.onto _).2 ⟨lin_sec h₁ h₂ s c ω (hsec v).1 (hsec v).2 hf, hf⟩
    refine ⟨LinearMap.toContinuousLinearMap
      ((LinearEquiv.ofInjective A.sec A.inj).symm.toLinearMap ∘ₗ (lin s c ω ∘ₗ A.sec).codRestrict _ hm), fun v => ?_⟩
    exact congrArg Subtype.val ((LinearEquiv.ofInjective A.sec A.inj).apply_symm_apply ⟨_, hm v⟩)
  choose U hU using fun t : ℝ => hU fun r => if r = t then Complex.exp (2 * (r : ℂ)) else 0
  set T : Finset ℝ := s.biUnion fun h => (dl_fin h).toFinset with hTdef
  have hT : ∀ h ∈ s, ∀ x, dl x h ∈ T := fun h hh x => Finset.mem_biUnion.2 ⟨h, hh, (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩⟩
  have hH : ∀ (x : G1 K (2 + 2)) (h : GF), HP 2 2 (x * pf h) = HP 2 2 x + dl x h := fun x h => by rw [dl]; ring
  have hHk : ∀ (x : G1 K (2 + 2)), ∀ k ∈ Kf, HP 2 2 (x * pf k) = HP 2 2 x := fun x k hk => (hpSpec.2.1 _ (pf_mem (hle hk))).2 x
  have key : ∀ x, Ofin μ m e (A.J x) = ∑ t ∈ T, A.J ((U t).compLpL 2 volume (sh (Eu d) t x)) := by
    have : Ofin μ m e ∘L A.J.toContinuousLinearMap =
        ∑ t ∈ T, A.J.toContinuousLinearMap ∘L (U t).compLpL 2 volume ∘L sh (Eu d) t := by
      refine ContinuousLinearMap.ext_on (denseCc d).1 ?_
      rintro u ⟨β, v, hβ, hβc, hu⟩
      have hw := A.spec β v u hβ hβc hu
      have hinv : ∀ k ∈ Kf, rightRegularRep (Gam K (2 + 2)) μ (pf k) (A.J u) = A.J u := fun k hk => by
        refine reps_ext (reps_right hw _) ?_
        have : (fun y => theta β (A.sec v) (y * pf k)) = theta β (A.sec v) := by
          funext y
          simp only [theta, ← mul_assoc, hHk _ k hk, fix_inv hL hle (hsec v).2 _ hk]
        rw [this]
        exact hw
      have h1 : Ofin μ m e (A.J u) = ∑ h ∈ s, c h • rightRegularRep (Gam K (2 + 2)) μ (pf h) (A.J u) := by
        rw [ofin_apply]
        exact hr _ (fun h => rightRegularRep (Gam K (2 + 2)) μ (pf h) (A.J u)) fun h k hk => by
          rw [(pf).map_mul, UnitaryRep.map_mul_apply]
          exact congrArg (rightRegularRep (Gam K (2 + 2)) μ (pf h)) (hinv k hk)
      have hβt : ∀ t : ℝ, HasCompactSupport fun x => β (x + t) := fun t => hβc.comp_homeomorph (Homeomorph.addRight t)
      have h2 : ∀ t : ℝ, Reps μ (A.J ((U t).compLpL 2 volume (sh (Eu d) t u))) (theta (fun x => β (x + t)) (A.sec (U t v))) := fun t => by
        refine A.spec _ _ _ (hβ.comp (continuous_id.add continuous_const)) (hβt t) ?_
        filter_upwards [(U t).coeFn_compLpL (p := 2) (μ := volume) (sh (Eu d) t u), sh_ae (Eu d) t u,
          (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hu] with x a1 a2 a3
        exact (a1.trans (congrArg (U t) (a2.trans a3))).trans ((U t).map_smul _ _)
      have h3 := reps_sum T (fun _ => 1) fun t _ => h2 t
      have h4 := reps_sum s c fun h _ => reps_right hw (pf h)
      rw [theta_id hβc s c T hT (A.sec v) (fun t => A.sec (U t v)) (fun t => hU t v)] at h4
      have h5 : ∑ t ∈ T, A.J ((U t).compLpL 2 volume (sh (Eu d) t u)) = ∑ t ∈ T, (1 : ℂ) • A.J ((U t).compLpL 2 volume (sh (Eu d) t u)) :=
        Finset.sum_congr rfl fun _ _ => (one_smul ℂ _).symm
      refine (h1.trans (reps_ext h4 h3)).trans (h5.symm.trans ?_)
      symm
      exact ContinuousLinearMap.sum_apply _ _ _
    intro x
    exact (DFunLike.congr_fun this x).trans (ContinuousLinearMap.sum_apply _ _ _)
  refine ⟨⟨_, act_of A.J _ T U key, fun z v x => ?_⟩, fun u => ⟨_, (key u).trans (map_sum A.J _ _).symm⟩⟩
  have h1 := hr ℂ (fun h => flat z (A.sec v) (x * pf h)) fun h k hk => by
    simp only [flat, map_mul, ← mul_assoc, hHk _ k hk, fix_inv hL hle (hsec v).2 _ hk]
  have hs : A.sec ((∑ t ∈ T, Complex.exp (z * t) • U t) v) = fun x => ∑ t ∈ T, Complex.exp (z * t) * A.sec (U t v) x := by
    funext x
    rw [ContinuousLinearMap.sum_apply, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => by rw [ContinuousLinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  refine h1.trans ?_
  rw [flat, hs]
  exact flat_id z s c T hT (A.sec v) (fun t => A.sec (U t v)) (fun t => hU t v) x

theorem ofin_adj {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
    (e : TF K n) : ∃ e' : TF K n, (∀ h, e' h = starRingEnd ℂ (e h⁻¹)) ∧ ContinuousLinearMap.adjoint (Ofin μ m e) = Ofin μ m e' := by
  haveI := Whittaker.isMulRightInvariant_finite K n m
  haveI := isInvInvariant_of_isMulRightInvariant m
  let e' : TF K n := ⟨⟨fun h => starRingEnd ℂ (e h⁻¹), Complex.continuous_conj.comp (e.continuous.comp continuous_inv)⟩,
    (e.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)⟩
  refine ⟨e', fun _ => rfl, ?_⟩
  suffices hs : UnitaryRep.involution m (UnitaryRep.ccToL1 m e) = UnitaryRep.ccToL1 m e' from
    (UnitaryRep.adjoint_integrated ((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n)
      MultiplicityOne.continuous_finProj) m (UnitaryRep.ccToL1 m e)).trans (congrArg _ hs)
  have h1 : (UnitaryRep.ccToL1 m e : _ → ℂ) =ᵐ[m] e := MemLp.coeFn_toLp _
  have h2 : (UnitaryRep.ccToL1 m e' : _ → ℂ) =ᵐ[m] e' := MemLp.coeFn_toLp _
  refine Lp.ext ?_
  filter_upwards [h2, UnitaryRep.coeFn_involution m (UnitaryRep.ccToL1 m e),
    (Measure.measurePreserving_inv m).quasiMeasurePreserving.ae h1] with g ha hb hc
  rw [hb, hc, ha]
  rfl

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.FinA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.finAct :
    ForAllC fun K _ _ μ _ _ _ _ _ D d _ A A' => ∀ (Kf : Subgroup (AdelicGLn.FiniteAdelicGL K (2 + 2))), D.Level Kf → Kf ≤ AdelicGLn.integralFiniteGL K (2 + 2) →
      ∀ (m : Measure (AdelicGLn.FiniteAdelicGL K (2 + 2))) [m.IsHaarMeasure] (e : TF K (2 + 2)), (∀ k ∈ Kf, ∀ h, e (k * h) = e h ∧ e (h * k) = e h) →
      (∃ s, Act A.J (Ofin μ m e) s ∧ ∀ (z : ℂ) (v : Eu d) (x : G1 K (2 + 2)),
        ∫ h, e h * flat z (A.sec v) (x * MultiplicityOne.finProj K (2 + 2) h) ∂m = flat z (A.sec (s z v)) x) ∧
      ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P → Ofin μ m e ∘L P = P ∘L Ofin μ m e := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' Kf hL hle m _ e he
  refine ⟨(FinA.actEx μ hp.irr₁ hp.irr₂ A hL hle m e he).1, fun P hP => ?_⟩
  obtain ⟨e', he', hadj⟩ := FinA.ofin_adj μ m e
  have he2 : ∀ k ∈ Kf, ∀ h, e' (k * h) = e' h ∧ e' (h * k) = e' h := fun k hk h => by
    simp only [he', mul_inv_rev, he k⁻¹ (Kf.inv_mem hk) h⁻¹, and_self]
  refine (Hecke₃ K μ μ₂ τ₁ τ₂ hp D d d' A A' P hP).1 _ (FinA.actEx μ hp.irr₁ hp.irr₂ A hL hle m e he).2
    (FinA.actEx μ hp.irr₂ hp.irr₁ A' hL hle m e he).2 ?_ ?_
  · rw [hadj]; exact (FinA.actEx μ hp.irr₁ hp.irr₂ A hL hle m e' he2).2
  · rw [hadj]; exact (FinA.actEx μ hp.irr₂ hp.irr₁ A' hL hle m e' he2).2
