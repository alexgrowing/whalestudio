import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.KillsIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.PiLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.RepsRight
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LevelEx
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdmCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdmissibleCuspFormsFinite

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem proj_fix (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (A B : H →L[ℂ] H)
    (hAB : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ) (hA : ∀ y ∈ Y, A y ∈ Y) (hB : ∀ y ∈ Y, B y ∈ Y) (v : H) (hv : A v = v) :
    A (Y.starProjection v) = Y.starProjection v := by
  have hpY : Y.starProjection v ∈ Y := Submodule.starProjection_apply_mem Y v
  have hz : ∀ y ∈ Y, ⟪v - Y.starProjection v, y⟫_ℂ = 0 := fun y hy =>
    Submodule.inner_left_of_mem_orthogonal hy (Submodule.sub_starProjection_mem_orthogonal v)
  have hAz : ∀ y ∈ Y, ⟪A (v - Y.starProjection v), y⟫_ℂ = 0 := fun y hy => by
    rw [hAB]; exact hz _ (hB y hy)
  have e : A (Y.starProjection v) - Y.starProjection v =
      (v - Y.starProjection v) - A (v - Y.starProjection v) := by
    rw [map_sub, hv]; abel
  have h1 : A (Y.starProjection v) - Y.starProjection v ∈ Y := Y.sub_mem (hA _ hpY) hpY
  have h0 : ⟪A (Y.starProjection v) - Y.starProjection v, A (Y.starProjection v) - Y.starProjection v⟫_ℂ = 0 := by
    nth_rw 1 [e]
    rw [inner_sub_left, hz _ h1, hAz _ h1, sub_zero]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

private theorem integral_mem_fd (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] {α : Type*} [MeasurableSpace α] (m : Measure α)
    (f : α → H) (hf : ∀ a, f a ∈ Y) : ∫ a, f a ∂m ∈ Y := by
  by_cases hi : Integrable f m
  · have h := (Y.starProjection).integral_comp_comm hi
    have e : ∀ a, Y.starProjection (f a) = f a := fun a => Submodule.starProjection_eq_self_iff.2 (hf a)
    simp only [e] at h
    rw [h]
    exact Submodule.starProjection_apply_mem Y _
  · rw [integral_undef hi]
    exact Y.zero_mem

end Hilbert

section Forms

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

private theorem cls_tr {φ ψ : cuspForms K n} (x : G1 K n)
    (h : ∀ y : G1 K n, (ψ : AdelicGLn.AdelicGL K n → ℂ) y =
      (φ : AdelicGLn.AdelicGL K n → ℂ) ((y * x : G1 K n) : AdelicGLn.AdelicGL K n)) :
    Dp.clsL μ ψ = rightRegularRep (Gam K n) μ x (Dp.clsL μ φ) := by
  have h1 := isContRep_cuspToL2 μ ψ
  have h2 := (isContRep_cuspToL2 μ φ).translate x
  have e : (fun y : G1 K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) y) =
      fun y => (φ : AdelicGLn.AdelicGL K n → ℂ) ((y * x : G1 K n) : AdelicGLn.AdelicGL K n) := funext h
  rw [e] at h1
  exact Lp.ext (h1.ae_eq_quotFun.trans h2.ae_eq_quotFun.symm)

private theorem mem_fixF' (W : Subgroup (FA K n)) (x : LL μ) :
    x ∈ fixF μ W ↔ ∀ u ∈ W, rightRegularRep (Gam K n) μ (fin1 u) x = x := by
  simp [fixF, rhoF, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem lev_max (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw n w)) (hU : Lev U) (u : FA K n)
    (hu : u ∈ levOn S U) : finEmb K n u ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) := by
  refine finEmb_mem_maxCompact ((AdelicGLn.mem_integralFiniteGL_iff_forall ..).2 fun v => ?_)
  have h : finAt v (finEmb K n u) ∈ if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) n := hu v
  have h2 : finAt v (finEmb K n u) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    by_cases hv : v ∈ S
    · rw [if_pos hv] at h; exact (hU v).2 h
    · rwa [if_neg hv] at h
  have e : finAt v (finEmb K n u) = AdelicGLn.finiteRestrictedEquiv K n u v := by
    show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n u)).2) v = _
    rw [prodEquiv_finEmb]
  rw [e] at h2
  exact h2

end Forms

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.vecEx :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (LL μ)), CuspIrr μ τ → ∀ (n : ι → ℕ) (q : ι → ℤ), (∀ i, ∃ v ∈ τ, C.Pi μ i (n i) (q i) v ≠ 0) → ∀ S : Finset (Pl K), SphOff μ τ S →
      ∃ (U : ∀ w : Pl K, Subgroup (Gw 2 w)) (φ : G1 K 2 → ℂ), Lev U ∧ φ ≠ 0 ∧ Rd τ φ ∧ (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧
        FixA C.κ₂ (C.p n q) φ ∧ FixF (levOn S U) φ := by
  intro K _ _ _ ι _ C μ _ τ hτ n q hn S hS
  have hSum : IsSummand μ τ := ⟨hτ.le, hτ.closed, hτ.inv, hτ.ne, hτ.irr⟩
  obtain ⟨U, hU, hUne⟩ := UpperTheory.ConvolutionTheory.T.levelEx K 2 μ τ hSum S hS
  have hZne : τ ⊓ fixF μ (levOn S U) ≠ ⊥ := by
    rw [UpperTheory.ConvolutionTheory.C.fixLev K 2 μ S U, ← inf_assoc]
    exact hUne
  obtain ⟨hP, hPp, hPi, -⟩ := piLaws K ι C μ
  have hcomm : ∀ i a (u : FA K 2), Commute (fin1 u) (C.gl i a) := fun i a u =>
    MultiplicityOne.finProj_mul_archProj_comm u _
  obtain ⟨v, hvZ, hv0, hvP⟩ := occ K ι C μ τ hτ (τ ⊓ fixF μ (levOn S U)) Finset.univ n q inf_le_left hZne
    (fun i a x hx => ⟨hτ.inv _ _ hx.1, (mem_fixF' μ _ _).2 fun u hu => by
      rw [← UnitaryRep.map_mul_apply, (hcomm i a u).eq, UnitaryRep.map_mul_apply, (mem_fixF' μ _ _).1 hx.2 u hu]⟩)
    (fun i n' q' x hx => by
      obtain ⟨P, hPv, -, -, -, hc, hτP⟩ := hP i n' q'
      rw [← hPv]
      refine ⟨hτP τ hτ x hx.1, (mem_fixF' μ _ _).2 fun u hu => ?_⟩
      have h := DFunLike.congr_fun (hc (fin1 u) fun b => hcomm i b u).eq x
      simp only [ContinuousLinearMap.mul_apply] at h
      rw [← h, (mem_fixF' μ _ _).1 hx.2 u hu]) hn
  have hvτ : v ∈ τ := hvZ.1
  have hvF := (mem_fixF' μ _ _).1 hvZ.2
  have hforms := Dp.formsIrr K 2 μ τ hSum
  obtain ⟨Φ, hΦ, hne⟩ : ∃ Φ ∈ Dp.formsIn μ τ, ⟪Dp.clsL μ Φ, v⟫_ℂ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hcl : IsClosed {x : LL μ | ⟪x, v⟫_ℂ = 0} := isClosed_eq (by fun_prop) continuous_const
    have hsub : (((Dp.formsIn μ τ).map (Dp.clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) ⊆ {x : LL μ | ⟪x, v⟫_ℂ = 0} := by
      rintro _ ⟨φ, h, rfl⟩
      exact hcon φ h
    have hm : v ∈ closure (((Dp.formsIn μ τ).map (Dp.clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) := by
      rw [← Submodule.topologicalClosure_coe, hforms.2.2.2]
      exact hvτ
    exact hv0 (inner_self_eq_zero.1 (closure_minimal hsub hcl hm))
  let A : Submodule ℂ (AdelicGLn.AdelicGL K 2 → ℂ) := Submodule.span ℂ
    (Set.range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)) =>
      GroundTheory.Automorphic.rightTranslate (k : AdelicGLn.AdelicGL K 2) (Φ : AdelicGLn.AdelicGL K 2 → ℂ))
  haveI hAfd : FiniteDimensional ℂ A := Φ.2.1.isKFinite
  have hAst : ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)), ∀ f ∈ A, (fun g => f (g * k)) ∈ A := by
    intro k hk f hf
    have hle : A ≤ A.comap (LinearMap.funLeft ℂ ℂ fun g : AdelicGLn.AdelicGL K 2 => g * k) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨⟨k * k', mul_mem hk k'.2⟩, ?_⟩
      funext g
      simp [GroundTheory.Automorphic.rightTranslate, LinearMap.funLeft_apply, mul_assoc]
    exact hle hf
  let W : Submodule ℂ (cuspForms K 2) := Dp.formsIn μ τ ⊓ A.comap (cuspForms K 2).subtype
  haveI hWfd : FiniteDimensional ℂ W := by
    let f : W →ₗ[ℂ] A := ((cuspForms K 2).subtype ∘ₗ W.subtype).codRestrict A fun x => x.2.2
    exact FiniteDimensional.of_injective f fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : AdelicGLn.AdelicGL K 2 → ℂ)) h))
  let Y : Submodule ℂ (LL μ) := W.map (Dp.clsL μ)
  haveI hYfd : FiniteDimensional ℂ Y := inferInstance
  have hcen : ∀ ψ ∈ W, ψ ∈ centralCuspForms K 2 := fun ψ h => h.1.1
  have hYσ : ∀ (k : archCompact K 2), ∀ y ∈ Y, rightRegularRep (Gam K 2) μ (arc1 k) y ∈ Y := by
    rintro k _ ⟨ψ, hψ, rfl⟩
    refine ⟨(gkModuleCusp K 2).σ k ψ, ⟨hforms.1.σ k ψ hψ.1, hAst _ k.2 _ hψ.2⟩, ?_⟩
    exact cls_tr μ (arc1 k) fun y => apply_mul_infEmb_of_mem (hcen ψ hψ) y k
  have hYf : ∀ u ∈ levOn S U, ∀ y ∈ Y, rightRegularRep (Gam K 2) μ (fin1 u) y ∈ Y := by
    rintro u hu _ ⟨ψ, hψ, rfl⟩
    have hm := lev_max S U hU u hu
    refine ⟨finRepCusp K 2 u ψ, ⟨hforms.1.τ u ψ hψ.1, hAst _ hm _ hψ.2⟩, ?_⟩
    refine cls_tr μ (fin1 u) fun y => ?_
    have e : ((fin1 u : G1 K 2) : AdelicGLn.AdelicGL K 2) = finEmb K 2 u := by
      rw [fin1, MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL hm)]
    show (ψ : AdelicGLn.AdelicGL K 2 → ℂ) (y * finEmb K 2 u) = (ψ : AdelicGLn.AdelicGL K 2 → ℂ) (y * (fin1 u : G1 K 2))
    rw [e]
  have hYP : ∀ i n' q', ∀ y ∈ Y, C.Pi μ i n' q' y ∈ Y := fun i n' q' y hy =>
    integral_mem_fd Y μK _ fun m => Y.smul_mem _ (hYσ _ y hy)
  have hy₀P : ∀ i, C.Pi μ i (n i) (q i) (Y.starProjection v) = Y.starProjection v := by
    intro i
    obtain ⟨P, hPv, hsa, -⟩ := hP i (n i) (q i)
    have hst : ∀ y ∈ Y, P y ∈ Y := fun y hy => by rw [hPv]; exact hYP _ _ _ y hy
    rw [← hPv]
    exact proj_fix Y P P (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa) hst hst v
      (by rw [hPv]; exact hvP i (Finset.mem_univ i))
  have hy₀F : ∀ u ∈ levOn S U, rightRegularRep (Gam K 2) μ (fin1 u) (Y.starProjection v) = Y.starProjection v :=
    fun u hu => proj_fix Y _ (rightRegularRep (Gam K 2) μ (fin1 u)⁻¹)
      (UnitaryRep.inner_map_left _ _) (hYf u hu)
      (fun y hy => by rw [← map_inv]; exact hYf _ (inv_mem hu) y hy) v (hvF u hu)
  obtain ⟨Φ₀, hΦ₀, hcls⟩ : Y.starProjection v ∈ Y := Submodule.starProjection_apply_mem Y v
  have hrep : IsContRep μ (Y.starProjection v) fun m : G1 K 2 => (Φ₀ : AdelicGLn.AdelicGL K 2 → ℂ) m := by
    rw [← hcls]
    exact isContRep_cuspToL2 μ Φ₀
  have hy₀τ : Y.starProjection v ∈ τ := by
    rw [← hcls]
    exact hΦ₀.1.2
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K 2 => fun m : G1 K 2 =>
      (Φ₀ : AdelicGLn.AdelicGL K 2 → ℂ) ((m * k : G1 K 2) : AdelicGLn.AdelicGL K 2))) := by
    refine Submodule.finiteDimensional_of_le
      (S₂ := A.map (LinearMap.funLeft ℂ ℂ fun m : G1 K 2 => (m : AdelicGLn.AdelicGL K 2))) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hAst _ k.2 _ hΦ₀.2, rfl⟩
  have hRd := (cuspIrr_kFinite_rep_eq_centralCuspForm μ τ hτ _ hrep.1 ⟨_, hy₀τ, hrep.2.2⟩ hfin).1
  obtain ⟨B, hB⟩ := hRd.decay 0
  refine ⟨U, _, hU, ?_, hRd, ⟨B, fun x => by simpa using hB x⟩,
    ((ptPi K ι C μ _ _ hrep.1 hrep.2.2).2 C.κ₂ (C.p n q) (hPi n q)).1 ((hPp n q _).2 hy₀P), fun u hu g => ?_⟩
  · intro h0
    have hz : Y.starProjection v = 0 := by
      rw [h0] at hrep
      exact Lp.ext (hrep.ae_eq_quotFun.trans (isContRep_zero (μ := μ)).ae_eq_quotFun.symm)
    have hΦA : (Φ : AdelicGLn.AdelicGL K 2 → ℂ) ∈ A := Submodule.subset_span ⟨1, by
      funext x
      simp [GroundTheory.Automorphic.rightTranslate]⟩
    have hΦW : Φ ∈ W := ⟨hΦ, hΦA⟩
    have hΦY : Dp.clsL μ Φ ∈ Y := Submodule.mem_map_of_mem hΦW
    have hin : ⟪Dp.clsL μ Φ, v - Y.starProjection v⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hΦY (Submodule.sub_starProjection_mem_orthogonal v)
    rw [hz, sub_zero] at hin
    exact hne hin
  · have h2 := hrep.translate (fin1 u)
    rw [hy₀F u hu] at h2
    exact congrFun (h2.unique hrep) g
