import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ClosedOneU

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap nonZeroDivisors Classical
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published NumberField.mixedEmbedding

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem finite_c {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) : {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 H.fin
  have ho := isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) hpow
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  apply hw
  exact Nat.le_zero.1 ((H.cond w).2 (show (0 : ℕ) ∈ _ from fun x hu _ => key w x hu fun h => absurd h hwS))

theorem finite_dd : {w : HeightOneSpectrum (𝓞 F) | dd w ≠ 0}.Finite := by
  have h0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simp only [Set.mem_ofPred_eq, dd, ordI, Nat.cast_ne_zero] at hw ⊢
  exact (Associates.count_ne_zero_iff_dvd h0 w.irreducible).1 hw

variable (F) in

def idealOf (e : HeightOneSpectrum (𝓞 F) → ℤ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := ∏ᶠ w, primeIdealUnit w ^ e w

def Jc (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := idealOf F fun w => (c w : ℤ)

def Jh (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := idealOf F fun w => -((c w : ℤ) + dd w)

private theorem count_Jc {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((Jc c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w := by
  refine count_finprod_primeIdealUnit_zpow (fun w => (c w : ℤ)) ?_ w
  exact Filter.eventually_cofinite.2 ((finite_c H).subset fun w hw => by simpa using hw)

private theorem count_Jh {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((Jh c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = -((c w : ℤ) + dd w) := by
  refine count_finprod_primeIdealUnit_zpow (fun w => -((c w : ℤ) + dd w)) ?_ w
  refine Filter.eventually_cofinite.2 (((finite_c H).union finite_dd).subset fun w hw => ?_)
  simp only [Set.mem_ofPred_eq] at hw
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  apply hw
  rw [h.1, h.2]
  simp

theorem phi_eq {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (y : Fin 2 → Ad F) :
    Phi c y = arch (UpperTheory.V.TR.pInf F (y 0)) (UpperTheory.V.TR.pInf F (y 1)) *
      if pFin F (y 0) ∈ idealFiniteAdeles (Jc c) ∧ pFin F (y 1) - 1 ∈ idealFiniteAdeles (Jc c) then 1 else 0 := by
  unfold Phi
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [mem_idealFiniteAdeles, count_Jc H]
  rw [← forall_and]
  exact Iff.rfl

theorem norm_phiH_le {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (y : Fin 2 → Ad F) :
    ‖PhiH c y‖ ≤ ‖arch (UpperTheory.V.TR.pInf F (y 0)) (UpperTheory.V.TR.pInf F (y 1))‖ *
      if pFin F (y 0) ∈ idealFiniteAdeles (Jh c) ∧ pFin F (y 1) ∈ idealFiniteAdeles (Jh c) then (1 : ℝ) else 0 := by
  unfold PhiH
  rw [norm_mul]
  split_ifs with h1 h2
  · rw [Circle.norm_coe]
  · exfalso
    apply h2
    simp only [mem_idealFiniteAdeles, count_Jh H, neg_neg]
    exact ⟨fun w => (h1 w).1, fun w => (h1 w).2⟩
  · rw [norm_zero, mul_zero]
    positivity
  · simp

private theorem pInf_coord_eq (x : Ad F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F x v = (homeomorphMixedSpace F x.1).1 ⟨v, IsTotallyReal.isReal v⟩ := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

private theorem continuous_pInf_coord (v : InfinitePlace F) :
    Continuous fun x : Ad F => UpperTheory.V.TR.pInf F x v := by
  have h : (fun x : Ad F => UpperTheory.V.TR.pInf F x v) =
      fun x => (homeomorphMixedSpace F x.1).1 ⟨v, IsTotallyReal.isReal v⟩ := funext fun x => pInf_coord_eq x v
  rw [h]
  exact (continuous_apply _).comp (continuous_fst.comp ((homeomorphMixedSpace F).continuous.comp continuous_fst))

private theorem continuous_arch_comp {X : Type*} [TopologicalSpace X] {a b : X → Ad F} (ha : Continuous a)
    (hb : Continuous b) : Continuous fun p => arch (UpperTheory.V.TR.pInf F (a p)) (UpperTheory.V.TR.pInf F (b p)) := by
  unfold arch
  refine continuous_finsetProd _ fun v _ => ?_
  have h1 : Continuous fun p => ((UpperTheory.V.TR.pInf F (a p) v : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_pInf_coord v).comp ha)
  have h2 : Continuous fun p => ((UpperTheory.V.TR.pInf F (b p) v : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_pInf_coord v).comp hb)
  exact (h1.add (continuous_const.mul h2)).mul
    (Complex.continuous_exp.comp (continuous_const.mul ((h1.pow 2).add (h2.pow 2))))

private theorem coe_scalar_mul (z : Ideles F) (g : GA F 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      Matrix.scalar (Fin 2) (z : Ad F) * (g : Matrix (Fin 2) (Fin 2) (Ad F)) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]

private theorem continuous_Y (g : GA F 2) (ξ : Fin 2 → F) :
    Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g :
        GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) := by
  have hz : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      ((moduleSection (w0 F) p.1 * (p.2 : Ideles F) : Ideles F) : Ad F) :=
    Units.continuous_val.comp (((continuous_moduleSection _).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  simp_rw [coe_scalar_mul, Matrix.scalar_apply]
  exact continuous_const.matrix_vecMul ((Continuous.matrix_diagonal (continuous_pi fun _ => hz)).matrix_mul
    continuous_const)

theorem measurable_eisInt {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (g : GA F 2) :
    Measurable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => eisInt ω (Phi c) g p.1 p.2) := by
  have hz : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      (moduleSection (w0 F) p.1 * (p.2 : Ideles F) : Ideles F) :=
    ((continuous_moduleSection _).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hterm : ∀ ξ : Fin 2 → F, Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      Phi c (rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g :
        GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) := by
    intro ξ
    have hY := continuous_Y g ξ
    have hY0 := (continuous_apply (0 : Fin 2)).comp hY
    have hY1 := (continuous_apply (1 : Fin 2)).comp hY
    have hf0 : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
        pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g :
          GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 0) := continuous_snd.comp hY0
    have hf1 : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
        pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g :
          GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 1) := continuous_snd.comp hY1
    have hO := ((isOpen_idealFiniteAdeles (Jc c)).preimage hf0).inter
      ((isOpen_idealFiniteAdeles (Jc c)).preimage (hf1.sub (continuous_const (y := (1 : Af F)))))
    simp_rw [phi_eq H]
    exact (continuous_arch_comp hY0 hY1).measurable.mul
      (Measurable.ite hO.measurableSet measurable_const measurable_const)
  have hθ : Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g) := by
    unfold thetaS
    exact Measurable.tsum fun ξ => hterm ξ.1
  have hω : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      ((ω.1 (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) : ℂˣ) : ℂ)⁻¹ :=
    (Units.continuous_val.comp (ω.2.1.comp hz)).inv₀ fun p => Units.ne_zero _
  have ht : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  unfold eisInt
  exact ((hθ.mul hω.measurable).mul ht.measurable).mul measurable_const

end UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability
