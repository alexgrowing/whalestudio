import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Assemble
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictRelReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictPure
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictPlaces
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsFramesOfK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictFrames

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
def RelRealP_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf →
  ∀ (x : d.G) (t u : GL (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 →
  ∀ η : E, η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) (l : InfinitePlace F → ℝ) (εs : InfinitePlace F → Fin d.m → Bool)
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
    (∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)) ∧
    (∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star) ∧
    (∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1) ∧
    (∀ Y, Φg Y = d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ)) ∧
    (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf
theorem relReal_k : _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.RelRealP_k := by
  intro F E _ _ _ _ _ σ d R Φ P gf hP x t u _ η hη herm
  obtain ⟨Φf, Φv, hpf, hpr⟩ := _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.pure_prod_of'_k R Φ P gf hP u η (thW d.B) (thW_th' d.B) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη) (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w)
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη) (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_gc_k d u η hη w) (fun _ => -1) (fun _ => by norm_num)
  refine ⟨thW d.B, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη, fun _ => -1, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k R η, _, Φf, Φv, thW_th' d.B, fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w,
    fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_gc_k d u η hη w, fun _ => rfl, ⟨fun w => decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re), rfl⟩,
    _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isCharAF_of_good_k d.B d.ok.good, _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isPlaces_thW'_k d.B d.ok.good,
    _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.isFrames_of'_k R η hη d.ok.good.cm herm (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.eta_zeta'_k R hη herm) (thW d.B) (thW_th' d.B) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη)
      (fun w => _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_frc_k R η hη w), hpf, hpr⟩
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
