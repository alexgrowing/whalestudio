import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThMSymmApply
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitTheta

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def thM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) :=
  (Homeomorph.mk (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).toEquiv (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_cont_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_symm_cont_k d hη)).toMeasurableEquiv
def thE'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) : HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη g
theorem th_rat_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) :
    g ∈ ratU σ d.A.J ↔ _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := by
  rw [ratU, Subgroup.mem_subgroupOf, MonoidHom.mem_range, HeckeCharacterZeroLocus.SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf,
    HeckeCharacterZeroLocus.SiegelWeilU.HFin, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, hγ⟩
    have hg : (g.1 : GL (Fin d.m) (AE F E)) ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_mem_iff_k d hη g.1).1 g.2
    rw [← hγ] at hg
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (σ : E →+* E) (γ : Matrix (Fin d.m) (Fin d.m) E) * _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η * (γ : Matrix (Fin d.m) (Fin d.m) E) =
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η
    apply Matrix.map_injective (th_inclR_injective (F := F) (E := E))
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) ((γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F))) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) * (γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F)) =
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) at hg
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, th_cT_map]
    exact hg
  · rintro ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩
def thR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) ≃ ratU σ d.A.J where
  toFun h := ⟨(_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm h.1, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_rat_iff_k d hη _).2
    (by have e1 : _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm h.1) = h.1 := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).apply_symm_apply h.1
        rw [e1]; exact h.2)⟩
  invFun g := ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη g.1, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_rat_iff_k d hη _).1 g.2⟩
  left_inv h := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).apply_symm_apply h.1)
  right_inv g := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm_apply_apply g.1)
theorem th_haar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη)) := by
  have := d.ok.haar
  exact th_haar_map d.μ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_cont_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_symm_cont_k d hη)
theorem th_fd_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη)) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη '' d.D) := by
  refine d.ok.dom.image_of_equiv (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).toEquiv ⟨(_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).symm.measurable, ?_⟩ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thR_k d hη) ?_
  · change Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).symm (Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη) d.μ) ≪ d.μ
    rw [MeasurableEquiv.map_symm_map]
  · intro h x
    rfl
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
