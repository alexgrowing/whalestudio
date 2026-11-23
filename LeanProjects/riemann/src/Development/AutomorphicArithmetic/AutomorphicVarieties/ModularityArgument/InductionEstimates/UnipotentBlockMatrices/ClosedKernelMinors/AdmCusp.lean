import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosureOrbits.OrbitStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
import GroundTheory.AutomorphicForms.UnitaryAdmissible

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KF

private theorem kfin_class {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {v : L2 μ} {φ : G1 K n → ℂ} (hr : IsContRep μ v φ)
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K n => fun m => φ (m * k)))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => rk μ k v)) := by
  set T := Submodule.span ℂ (Set.range fun k : KG K n => fun m => φ (m * k)) with hT
  have huniq : ∀ {w w' : L2 μ} {f : G1 K n → ℂ}, IsContRep μ w f → IsContRep μ w' f → w = w' :=
    fun h h' => Lp.ext (h.ae_eq_quotFun.trans h'.ae_eq_quotFun.symm)
  have hex : ∀ f ∈ T, ∃ w : L2 μ, IsContRep μ w f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨_, hr.translate (k : G1 K n)⟩
    | zero => exact ⟨0, isContRep_zero⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, ha.add hb⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨c • a, ha.smul c⟩
  choose R hR using fun f : T => hex f f.2
  let L : T →ₗ[ℂ] L2 μ :=
    { toFun := R
      map_add' := fun a b => huniq (hR (a + b)) ((hR a).add (hR b))
      map_smul' := fun c a => huniq (hR (c • a)) ((hR a).smul c) }
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨_, Submodule.subset_span ⟨k, rfl⟩⟩, huniq (hR _) (hr.translate (k : G1 K n))⟩

private theorem contRep_of_reps {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {v : L2 μ} {φ : G1 K n → ℂ} (hc : Continuous φ) (hr : Reps μ v φ) : IsContRep μ v φ := by
  refine ⟨hc, fun γ hγ => ?_, hr⟩
  have h1 : ∀ᵐ y ∂μ, (v : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (γ * y)) = φ (γ * y) :=
    (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae hr
  have h2 : (fun y => φ (γ * y)) =ᵐ[μ] φ := by
    filter_upwards [h1, hr] with y a b
    have e : mk (Gam K n) (γ * y) = mk (Gam K n) y := Quotient.sound ⟨⟨γ, hγ⟩, rfl⟩
    rw [← a, e, b]
  exact congrFun ((Continuous.ae_eq_iff_eq μ (hc.comp (continuous_const.mul continuous_id)) hc).1 h2)

private theorem decay_of_form {K : Type} [Field K] [NumberField K] {n : ℕ} (Φ : cuspForms K n) (N : ℕ) :
    ∃ C : ℝ, ∀ m : G1 K n, ‖Φ.1 (m : AdelicGLn.AdelicGL K n)‖ * qht m ^ N ≤ C := by
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := K) n
  obtain ⟨C, hC⟩ := exists_norm_le_height_pow_neg_siegel Φ.2 hω hωB ht N
  refine ⟨C, fun m => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg m
  obtain ⟨b, hb, a, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hγ
  have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
  have hγx : AdelicGLn.diagonal K n γ * (m : AdelicGLn.AdelicGL K n) ∈ normOneGL K n := mul_mem hγ1 m.2
  have h := hC b hb ρ hρ hs kk hkk _ hγx hxe
  rw [Φ.2.1.isLeftInvariant γ (m : AdelicGLn.AdelicGL K n)] at h
  set x := AdelicGLn.diagonal K n γ * (m : AdelicGLn.AdelicGL K n) with hx
  have hpos : 0 < AutomorphicForm.height x := height_pos x
  have hbdd : BddBelow (Set.range fun γ : Gam K n =>
      AutomorphicForm.height (((γ : G1 K n) * m : G1 K n) : AdelicGLn.AdelicGL K n)) :=
    ⟨0, by rintro _ ⟨g, rfl⟩; exact (height_pos _).le⟩
  have hq : qht m ≤ AutomorphicForm.height x :=
    ciInf_le hbdd (⟨⟨_, hγ1⟩, ⟨γ, rfl⟩⟩ : Gam K n)
  have hq0 : 0 ≤ qht m := le_ciInf fun g => (height_pos _).le
  calc ‖Φ.1 (m : AdelicGLn.AdelicGL K n)‖ * qht m ^ N
      ≤ C * (AutomorphicForm.height x ^ N)⁻¹ * AutomorphicForm.height x ^ N :=
        mul_le_mul h (pow_le_pow_left₀ hq0 hq N) (pow_nonneg hq0 N) ((norm_nonneg _).trans h)
    _ = C := by rw [mul_assoc, inv_mul_cancel₀ (pow_pos hpos N).ne', mul_one]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cuspIrr_kFinite_rep_eq_centralCuspForm :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ : Submodule ℂ (L2 μ₂)), CuspIrr μ₂ τ → ∀ φ : G1 K 2 → ℂ, Continuous φ → (∃ v ∈ τ, Reps μ₂ v φ) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K 2 => fun m => φ (m * k))) →
      Rd τ φ ∧ ∃ Φ : cuspForms K 2, Φ ∈ centralCuspForms K 2 ∧ (∀ m : G1 K 2, Φ.1 (m : AdelicGLn.AdelicGL K 2) = φ m) ∧
        ((cuspToL2 μ₂ Φ : cuspidalL2 μ₂) : L2 μ₂) ∈ τ := by
  intro K _ _ _ μ₂ _ τ hτ φ hc hex hfd
  obtain ⟨v, hv, hr⟩ := hex
  have hsum : IsSummand μ₂ τ := ⟨hτ.le, hτ.closed, hτ.inv, hτ.ne, fun V' h1 h2 h3 => hτ.irr V' h1 h2 h3⟩
  have hcr := contRep_of_reps μ₂ hc hr
  obtain ⟨Φ, hΦ, rfl⟩ := kfin μ₂ hsum hv (kfin_class μ₂ hcr hfd)
  have hval : ∀ m : G1 K 2, Φ.1 (m : AdelicGLn.AdelicGL K 2) = φ m :=
    congrFun ((isContRep_cuspToL2 μ₂ Φ).unique hcr)
  refine ⟨⟨hc, ⟨_, hv, hr⟩, hcr.2.1, fun m => ?_, fun N => ?_⟩, Φ, hΦ.1, hval, hv⟩
  · have h := Φ.2.2 1 one_pos one_lt_two (m : AdelicGLn.AdelicGL K 2)
    unfold constantTerm at h
    rw [← h]
    exact setIntegral_congr_fun (measurableSet_unipFundamentalDomain (K := K) (n := 2) (r := 1))
      fun X _ => (hval _).symm
  · obtain ⟨C, hC⟩ := decay_of_form Φ N
    exact ⟨C, fun m => by rw [← hval]; exact hC m⟩
