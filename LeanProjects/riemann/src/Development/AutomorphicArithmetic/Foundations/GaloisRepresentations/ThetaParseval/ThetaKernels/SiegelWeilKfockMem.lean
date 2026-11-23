import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockArch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockAlg

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem prodGen_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (S : InfinitePlace F → 𝓢(Fin d.m → Fin d.n → ℂ, ℂ))
    (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun X => (∏ w, S w (R.loc w X)) * g fun k => (d.crd X k).2) ∈ d.schM := by
  obtain ⟨T, hT⟩ := piProdSch (InfinitePlace F) (Fin d.m → Fin d.n → ℂ) S
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.schM, Submodule.mem_comap]
  refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L T, g, hg, ?_⟩
  funext c
  simp only [LinearMap.funLeft_apply, pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, hT, hL,
    _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
theorem fock_le_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ d.schM := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (fun w => (isSw_fP (P w)).choose) g hg
  have e : (fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w, (isSw_fP (P w)).choose (R.loc w X)) * g fun k => (d.crd X k).2 := by
    funext X
    congr 1
    exact Finset.prod_congr rfl fun w _ => by rw [(isSw_fP (P w)).choose_spec]
  change _ ∈ d.schM
  rw [e]
  exact h
theorem tens_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : R.tens w f Ψ ∈ d.schM := by
  obtain ⟨φ, hφ⟩ := hf
  have h : R.away w ≤ d.schM.comap (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensL_k R w f) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P, g, hg, rfl⟩
    have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (Function.update (fun w' => (isSw_fP (P w')).choose) w φ) g hg
    show R.tens w f _ ∈ d.schM
    convert h using 1
    funext X
    show f (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', (Function.update (fun w' => (isSw_fP (P w')).choose) w φ w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, hφ, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun w' hw' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw'), (isSw_fP (P w')).choose_spec]
  exact h hΨ
end PositivityTheory.SiegelWeilFormula.KFock
end
end
