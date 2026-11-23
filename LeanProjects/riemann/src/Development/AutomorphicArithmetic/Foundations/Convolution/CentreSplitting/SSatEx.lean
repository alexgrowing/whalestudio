import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FixedDense
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TsphVec
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.RhoLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.sSatEx :
    UpperTheory.ConvolutionTheory.Dp.SSatEx := by
  intro E _ _ _ n μ _ V hV w hne
  obtain ⟨π, h, -⟩ := exCusp E n μ V hV
  obtain ⟨J, hi, hd, -, hJ'⟩ := UpperTheory.ConvolutionTheory.Dp.locEmb E n μ π V h
  have hρ : ∀ g v, ‖locOn h.summand w g v‖ = ‖v‖ := fun g v => by
    change ‖RG μ (finGL E n (locGL E n w g)) (v : LL μ)‖ = ‖(v : LL μ)‖
    exact UnitaryRep.norm_map _ _ _
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  have hdense := UpperTheory.ConvolutionTheory.Dp.fixedDense _ _ _ (locOn h.summand w) (π.locRep w) J (GlobalTheory.LFun.KGL w n) hK hρ
    (π.isSmooth_locRep w) (hJ' w) hd
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hfix : ∀ u ∈ GlobalTheory.LFun.KGL w n, locOn h.summand w u ⟨v, hv.1⟩ = ⟨v, hv.1⟩ := fun u hu => by
    refine Subtype.ext ?_
    change localRepresentationL2 μ w u v = v
    rw [← rhoLoc E n μ w u v]
    have h2 := hv.2
    simp only [UpperTheory.ConvolutionTheory.fixL, UpperTheory.ConvolutionTheory.fixF, SetLike.mem_coe, Submodule.mem_iInf] at h2
    exact h2 _ ⟨u, by exact (PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.KGL_eq w n).le hu, rfl⟩
  have hs : GlobalTheory.LGrp.IsSpherical (π.locRep w) (GlobalTheory.LFun.KGL w n) := by
    refine (Submodule.ne_bot_iff _).2 ?_
    by_contra hno
    push_neg at hno
    have hsub : J '' {x | ∀ u ∈ GlobalTheory.LFun.KGL w n, π.locRep w u x = x} ⊆ {0} := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hno x (GlobalTheory.LGrp.mem_fixed.2 hx), map_zero]
      rfl
    exact h0 (congrArg Subtype.val (closure_minimal hsub isClosed_singleton (hdense _ hfix)))
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w hs
  exact ⟨_, (tsphVec E n μ w V hV B).1 ((satIff E n μ π V h w B).1 hB)⟩
