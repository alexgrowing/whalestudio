import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ContinuousMapGL
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LeftSm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.StepFin
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopLevel
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TsphComm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import Development.AutomorphicArithmetic.AdelicGluing.BaseChangeLevelIsOpenIsCompactContainsIwahori
import Development.AutomorphicArithmetic.AdelicGluing.ExistsIwahoriFactorizableFiniteVectorOfAverage
import Development.AutomorphicArithmetic.AdelicGluing.CuspidalProjectionCcStarTensIsLeftSmooth
import Development.AutomorphicArithmetic.AdelicGluing.CommuteHeckeOperatorFiniteConvolutionOfFreeIndic
import Development.AutomorphicArithmetic.AdelicGluing.GaloisTwistCompUOperatorEqUOperatorSmulPlace

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

theorem UpperTheory.ConvolutionTheory.GM.sideE :
    SideE := by
  intro F E _ _ _ _ _ _ _ _ σ hgen hprime n hn μ _ θ hθ q w₀ hsplit νE _ aE hA L ν
  obtain ⟨hsm, hlf, hpos, hnorm⟩ := hA
  obtain ⟨hFinS, hOpen, hCpt, hLe, hMax, hIw⟩ := UpperTheory.baseChangeLevel_isOpen_isCompact_contains_iwahori F E σ n hn q w₀ L
  obtain ⟨m, hm, hcompat⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx E n hn).2.1 μ νE
  haveI := hm
  obtain ⟨eU, heU, hOU⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix E n μ m (levE L.UE) hOpen hCpt
  obtain ⟨e, hg, hU', hfac⟩ := UpperTheory.exists_iwahori_factorizable_finite_vector_of_average F E σ n hn q w₀ L aE
  have hrr := UpperTheory.ConvolutionTheory.Tf.rrTens E n hn μ νE m hcompat
  have hIwOC : ∀ w : Pl E, IsOpen (GLnLocal.iwahori (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))) ∧
      IsCompact (GLnLocal.iwahori (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))) := fun w =>
    let h := UpperTheory.ConvolutionTheory.Tf.uiwPow E n μ w 0 0 (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
    ⟨h.2.2.1, h.2.2.2.1⟩

  have hOinf : ∀ (w : Pl E) (x : GL (Fin n) (w.adicCompletion E)), Commute (Oinf μ νE aE) (Hop μ w (GLnLocal.iwahori (w.adicCompletion E) n) x) := fun w x =>
    ((UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ w _ x (hIwOC w).1 (hIwOC w).2).2.2.2.2.1 _ fun g =>
      (UpperTheory.ConvolutionTheory.Tf.opAlg E n μ νE m).2.2.2.2.2.2.2.2 aE _)

  have hl : Fact (Module.finrank F E).Prime := ⟨hprime⟩
  have hσl : σ ^ Module.finrank F E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank F E]
    exact pow_card_eq_one'
  let pl : ZMod (Module.finrank F E) → PlacesOver E q := fun i => (σ ^ i.val) • w₀
  have hpl : ∀ i, pl (i + 1) = σ • pl i := by
    intro i
    haveI : Fact (1 < Module.finrank F E) := ⟨hprime.one_lt⟩
    have h1 : σ ^ (i + 1).val = σ ^ (i.val + 1) := by
      rw [ZMod.val_add, ZMod.val_one]
      conv_rhs => rw [← Nat.div_add_mod (i.val + 1) (Module.finrank F E), pow_add, pow_mul, hσl, one_pow, one_mul]
    show (σ ^ (i + 1).val) • w₀ = σ • (σ ^ i.val) • w₀
    rw [smul_smul, ← pow_succ', h1]
  have hRop : ∀ (w : PlacesOver E q) (x : GL (Fin n) (w.1.adicCompletion E)),
      Commute (Hop μ w.1 (GLnLocal.iwahori (w.1.adicCompletion E) n) x) (Rop μ (tens aE e)) := by
    intro w x
    obtain ⟨r, hr, hre⟩ := hfac w
    have c := UpperTheory.commute_heckeOperator_finiteConvolution_of_free_indicator E n hn μ m w.1 _ (hIwOC _).1 (hIwOC _).2 x r hr e hre
    show Commute _ (RR μ (tens aE e))
    rw [hrr]
    exact Commute.mul_right (hOinf _ _).symm c
  let amp : Amp μ :=
    { ν := νE, a₀ := aE, smooth := hsm, fin := hlf, S := {w : Pl E | w.under (𝓞 F) ∈ L.S ∨ w.under (𝓞 F) = q}, finS := hFinS,
      U := levE L.UE, le := hLe, isOpen := hOpen, max := hMax, pos := hpos, norm_le := hnorm }
  have hA : amp.A = Oinf μ νE aE ∘L prj (fixF μ (levE L.UE)) := rfl
  refine ⟨{ toAmp := amp, a := tens aE eU, a_op := ?_, a_smooth := ?_, g := tens aE e, g_smooth := UpperTheory.cuspidalProjection_ccStar_tens_isLeftSmooth E n hn aE e hsm hU',
            Uq := fun i => Uiw μ (pl i).1 ν, Uq_inner := ?_, Uq_comm := ?_, Uq_amp := ?_, Uq_perm := ?_ }, rfl, rfl, fun w => Iff.rfl, rfl, hg, ?_⟩
  · show RR μ (tens aE eU) = _
    rw [hrr, hOU]; rfl
  · refine ((UpperTheory.ConvolutionTheory.Tf.leftSm E n hn aE eU).1 hsm ⟨levE L.UE, hOpen, fun u hu h => ?_⟩)
    rw [heU, heU]
    have hiff : u * h ∈ (levE L.UE : Set (AdelicGLn.FiniteAdelicGL E n)) ↔ h ∈ (levE L.UE : Set (AdelicGLn.FiniteAdelicGL E n)) :=
      Subgroup.mul_mem_cancel_left _ hu
    by_cases hh : h ∈ (levE L.UE : Set (AdelicGLn.FiniteAdelicGL E n))
    · rw [Set.indicator_of_mem (hiff.2 hh), Set.indicator_of_mem hh]
    · rw [Set.indicator_of_notMem (mt hiff.1 hh), Set.indicator_of_notMem hh]
  · intro i V hV hinv
    exact (UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.2.2 (pl i).1 _ _ (hIwOC _).1 (hIwOC _).2 V hV hinv
  · intro i k
    by_cases h : (pl i).1 = (pl k).1
    · show Commute (Uiw μ (pl i).1 ν) (Uiw μ (pl k).1 ν)
      rw [h]
    · exact (UpperTheory.ConvolutionTheory.Tf.tsphComm E n μ (pl i).1 (pl k).1).2.1 h _ _ _ _ (hIwOC _).1 (hIwOC _).2 (hIwOC _).1 (hIwOC _).2
  · intro i
    have h1 := (UpperTheory.ConvolutionTheory.Tf.hopLevel E n μ m (pl i).1 _ (Cartan.diagPow ((pl i).1.adicCompletion E) n ν) (levE L.UE) (hIwOC _).1 (hIwOC _).2 hOpen hCpt
      (hIw (pl i)).1 (hIw (pl i)).2).1
    exact Commute.mul_right (hOinf _ _).symm h1
  · intro i
    have hc1 := UpperTheory.galoisTwist_comp_uOperator_eq_uOperator_smul_place F E σ n hn μ θ hθ (pl i).1 ν
    have h3 : Uiw μ (pl (i + 1)).1 ν = Uiw μ (σ • (pl i).1) ν := by rw [hpl]; rfl
    have h4 : Rop μ (tens aE e) ∘L Uiw μ (pl (i + 1)).1 ν = Uiw μ (pl (i + 1)).1 ν ∘L Rop μ (tens aE e) :=
      (hRop (pl (i + 1)) _).symm.eq
    show (Rop μ (tens aE e) ∘L θ.U) ∘L Uiw μ (pl i).1 ν = Uiw μ (pl (i + 1)).1 ν ∘L (Rop μ (tens aE e) ∘L θ.U)
    calc (Rop μ (tens aE e) ∘L θ.U) ∘L Uiw μ (pl i).1 ν = Rop μ (tens aE e) ∘L (θ.U ∘L Uiw μ (pl i).1 ν) := rfl
      _ = Rop μ (tens aE e) ∘L (Uiw μ (pl (i + 1)).1 ν ∘L θ.U) := by rw [hc1, h3]
      _ = (Rop μ (tens aE e) ∘L Uiw μ (pl (i + 1)).1 ν) ∘L θ.U := rfl
      _ = Uiw μ (pl (i + 1)).1 ν ∘L (Rop μ (tens aE e) ∘L θ.U) := by rw [h4]; rfl
  · show Uiw μ (pl 0).1 ν = Uiw μ w₀.1 ν
    simp [pl]
