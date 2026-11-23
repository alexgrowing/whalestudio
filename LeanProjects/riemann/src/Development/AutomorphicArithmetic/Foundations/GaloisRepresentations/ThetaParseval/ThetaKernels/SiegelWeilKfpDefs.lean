import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockArch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockIntSch

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
abbrev Yf_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := Fin d.m × Fin d.n × Fin 2 → Af F
abbrev Iw_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := InfinitePlace F × Fin d.m × Fin d.n × Bool
abbrev Vw_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := EuclideanSpace ℝ (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d)
def fin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d := fun k => (d.crd X k).2
def arc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d :=
  (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).symm fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im
def gau_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : ℂ := ∏ w, fP (1 : PX d.m d.n) (R.loc w X)
def vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ) (X : Mx F E d.m d.n) : ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k R X * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)
theorem vac_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) : _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g ∈ R.fock :=
  Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
theorem exists_lift_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) :
    ∃ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g :=
  (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.vac_mem_k R hg))
def zOf_k (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ) : InfinitePlace F → Fin d.m → Fin d.n → ℂ :=
  fun w a j => ⟨u (w, a, j, true), u (w, a, j, false)⟩
theorem arc_eq_iff_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X = u ↔ ∀ w, R.loc w X = _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ u) w := by
  constructor
  · rintro rfl w
    funext a j
    apply Complex.ext
    · simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k]
  · intro h
    apply (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).injective
    funext i
    obtain ⟨w, a, j, b⟩ := i
    have hw := congrFun (congrFun (h w) a) j
    cases b
    · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, ContinuousLinearEquiv.apply_symm_apply, Bool.false_eq_true, if_false]
      rw [hw]
      rfl
    · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, ContinuousLinearEquiv.apply_symm_apply, if_true]
      rw [hw]
      rfl
theorem exists_jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : ∃! X : Mx F E d.m d.n, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X = u ∧ _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X = y := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  set Z := _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ u) with hZ
  let cI := L.symm Z
  let c : Fin d.m × Fin d.n × Fin 2 → AF F := fun k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (cI k)) (y k) : AF F)
  have hc1 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) = cI := by
    funext k
    exact RingEquiv.apply_symm_apply _ _
  refine ⟨d.cmb c, ⟨?_, ?_⟩, ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k]
    intro w
    rw [← hL c w, hc1]
    show L (L.symm Z) w = Z w
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · funext k
    show (d.crd (d.cmb c) k).2 = y k
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k]
  · rintro X ⟨hX1, hX2⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k] at hX1
    have e1 : L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) = Z := by
      funext w
      rw [hL, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k]
      exact hX1 w
    have e2 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) = cI := by
      have h := congrArg L.symm e1
      rwa [ContinuousLinearEquiv.symm_apply_apply] at h
    have e3 : d.crd X = c := by
      funext k
      refine Prod.ext ?_ ?_
      · apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
        rw [congrFun e2 k]
        exact (congrFun hc1 k).symm
      · exact congrFun hX2 k
    rw [← e3, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k]
def jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).exists.choose
theorem arc_jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) = u := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).exists.choose_spec.1
theorem fin_jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) = y := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).exists.choose_spec.2
theorem jn_arc_fin_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) = X :=
  ((_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)).unique (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)).exists.choose_spec ⟨rfl, rfl⟩)
def hg_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) (f : Mx F E d.m d.n → ℂ) (g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ℂ :=
  ∫ y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (g y) ∂νf
def B_k (ν : Measure (Mx F E d.m d.n)) (Φ Ψ : d.Fn) : ℂ := ∫ X, d.T Φ X * star (d.T Ψ X) ∂ν
end PositivityTheory.SiegelWeilFormula.KFP
end
end
