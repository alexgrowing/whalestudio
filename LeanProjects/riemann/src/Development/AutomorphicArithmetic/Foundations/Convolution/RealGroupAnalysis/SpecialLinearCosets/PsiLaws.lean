import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.LocalFields.LocalZetaChar

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem sg_eq_incl {F : Type} [Field F] [NumberField F] (v : P F) (x : Kv v) :
    sg v x = finitePlaceIncl v x := by
  obtain ⟨-, -, h3, -, -, -, -, h8, -, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws F v
  refine Prod.ext ?_ ?_
  · rw [(h8 x).1, finitePlaceIncl_apply, finiteAdeleInr_fst]
  · rw [finitePlaceIncl_apply, finiteAdeleInr_snd]
    refine Subtype.ext (funext fun u => ?_)
    by_cases hu : u = v
    · subst hu
      exact (h3 x).trans (finiteAdeleSingleAdd_apply_self u x).symm
    · exact ((h8 x).2 u hu).trans (finiteAdeleSingleAdd_apply_of_ne hu x).symm

private theorem exists_char_ne {F : Type} [Field F] [NumberField F] (v : P F) :
    ∃ y, localAdelicChar F v y ≠ 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (FractionalIdeal.count F v ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) + 1))
  have h := (forall_localAdelicChar_mul_eq_one_iff v z).1 fun a _ => hc _
  rw [mem_localInvDifferent_iff_valued, hz, WithZero.exp_le_exp] at h
  omega

private theorem locConst_of_char {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (χ : AddChar G Circle) (H : AddSubgroup G)
    (hH : IsOpen (H : Set G)) (h1 : ∀ y ∈ H, χ y = 1) :
    IsLocallyConstant fun x => ((χ x : Circle) : ℂ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h0 := hH.mem_nhds (zero_mem H)
  have hcc : Continuous fun y : G => y - x := continuous_id.sub continuous_const
  have hc : Filter.Tendsto (fun y : G => y - x) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self] using hcc.tendsto x
  filter_upwards [hc h0] with y hy
  have e := AddChar.map_add_eq_mul χ (y - x) x
  rw [h1 _ hy, one_mul, sub_add_cancel] at e
  rw [e]

private theorem psi_locConst {F : Type} [Field F] [NumberField F] (v : P F) :
    IsLocallyConstant (ψl v) :=
  locConst_of_char (localAdelicChar F v) (localInvDifferent v) (isOpen_localInvDifferent v)
    fun _ hy => localAdelicChar_eq_one_of_mem hy

private theorem ab_idl_eq {F : Type} [Field F] [NumberField F] (v : P F) (t : (Kv v)ˣ) :
    ab (idl v t) = (GroundTheory.LocalField.modulus (t : Kv v) : ℝ) := by
  obtain ⟨-, -, -, -, -, h6, h7, -, -, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws F v
  let f0 : (Kv v)ˣ →* ℝ :=
    { toFun := fun t => ab (idl v t)
      map_one' := by simp [ab, idl]
      map_mul' := fun a b => by simp [ab, idl] }
  have hz : ∀ (x : (Kv v)ˣ) (n : ℤ), f0 (x ^ n) = f0 x ^ n := fun x n => by
    have := congrArg Units.val (map_zpow f0.toHomUnits x n)
    simpa using this
  set ϖ := GroundTheory.LocalField.unifUnit (Kv v) with hϖ
  have hϖ1 : GroundTheory.LocalField.ord (ϖ : Kv v) = 1 := by
    simpa using GroundTheory.LocalField.ord_unifUnit_zpow (K := Kv v) 1
  have hU : IsU ϖ := by
    show Valued.v (ϖ : Kv v) = _
    rw [valued_eq_exp_neg_ord ϖ.ne_zero, hϖ1]
    rfl
  have hu : f0 (ϖ ^ (-GroundTheory.LocalField.ord (t : Kv v)) * t) = 1 := h7 _ (by
    rw [valued_eq_one_iff_ord (Units.ne_zero _), GroundTheory.LocalField.ord_units_mul,
      GroundTheory.LocalField.ord_unifUnit_zpow]
    omega)
  have e : f0 t = f0 ϖ ^ GroundTheory.LocalField.ord (t : Kv v) := by
    conv_lhs => rw [GroundTheory.LocalField.eq_unifUnit_zpow_mul t]
    rw [map_mul, hz, hu, mul_one]
  show f0 t = _
  rw [e, show f0 ϖ = _ from h6 ϖ hU, GroundTheory.LocalField.modulus_of_ne_zero t.ne_zero,
    residueCard_adicCompletion]
  push_cast
  rw [_root_.inv_zpow, _root_.zpow_neg]

theorem UpperTheory.ConvolutionTheory.R2.I.psiLaws :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), localAdelicChar F v ≠ 1 ∧ (∀ x, ψ (sg v x) = ψl v x) ∧ (∀ x y, ψl v (x + y) = ψl v x * ψl v y) ∧
      IsLocallyConstant (ψl v) ∧ (∀ x : Kv v, x ≠ 0 → ∃ s, ψl v (s * x) ≠ 1) ∧
      ∀ t : (Kv v)ˣ, ab (idl v t) = (GroundTheory.LocalField.modulus (t : Kv v) : ℝ) := by
  intro F _ _ v
  refine ⟨fun h => ?_, fun x => ?_, fun x y => ?_, psi_locConst v, fun x hx => ?_, ab_idl_eq v⟩
  · obtain ⟨y, hy⟩ := exists_char_ne v
    exact hy (by rw [h]; rfl)
  · simp only [ψ, ψl, sg_eq_incl, localAdelicChar_apply]
  · simp only [ψl, AddChar.map_add_eq_mul, Circle.coe_mul]
  · obtain ⟨y, hy⟩ := exists_char_ne v
    refine ⟨y / x, fun h => hy ?_⟩
    rw [div_mul_cancel₀ y hx] at h
    exact Circle.coe_eq_one.1 h
