import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.ContinuousLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockIntSch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockArch

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem continuous_loc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : Continuous (fun X : Mx F E d.m d.n => R.loc w X) := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w (p := Fin d.m) (q := Fin d.n)
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply]
  exact continuous_star.comp (continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp h)))
theorem continuous_arc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k
  refine (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  have h : Continuous fun X : Mx F E d.m d.n => R.loc i.1 X i.2.1 i.2.2.1 :=
    (continuous_apply _).comp ((continuous_apply _).comp (_root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_loc_k R i.1))
  split_ifs
  · exact Complex.continuous_re.comp h
  · exact Complex.continuous_im.comp h
theorem continuous_fin_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k
  exact continuous_pi fun k => continuous_snd.comp ((continuous_apply k).comp (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_crd_k d))
theorem continuous_zOf_k : Continuous (fun u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ => _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k u) := by
  refine continuous_pi fun w => continuous_pi fun a => continuous_pi fun j => ?_
  have : (fun u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ => _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k u w a j) =
      fun u => Complex.equivRealProdCLM.symm (u (w, a, j, true), u (w, a, j, false)) := by
    funext u
    rfl
  rw [this]
  exact Complex.equivRealProdCLM.symm.continuous.comp ((continuous_apply _).prodMk (continuous_apply _))
theorem zOf_add_k (u v : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ) : _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (u + v) = _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k u + _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k v := by
  funext w a j
  apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k]
theorem jn_eq_cmb_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ cF : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin d.m × Fin d.n × Fin 2 → AF F), Continuous cF ∧
      (∀ p q, cF (p + q) = cF p + cF q) ∧ ∀ p, _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2 = d.cmb (cF p) := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  let cF : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin d.m × Fin d.n × Fin 2 → AF F) := fun p k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) k))
      (p.2 k) : AF F)
  refine ⟨cF, ?_, fun p q => ?_, fun p => ?_⟩
  · refine continuous_pi fun k => ?_
    have e : (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => cF p k) = fun p =>
        (Prod.mk ((GroundTheory.Global.homeomorphMixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) k))
          (p.2 k) : AF F) := by
      funext p
      simp only [cF]
      rw [homeo_symm_eq]
    rw [e]
    exact Continuous.prodMk ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply k).comp
      (L.symm.continuous.comp (_root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_zOf_k.comp ((EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).continuous.comp continuous_fst)))))
      ((continuous_apply k).comp continuous_snd)
  · funext k
    refine Prod.ext ?_ ?_
    · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ (p + q).1)) k) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) k) +
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ q.1)) k)
      rw [← map_add, Prod.fst_add, map_add, _root_.PositivityTheory.SiegelWeilFormula.KFPB.zOf_add_k, map_add]
      rfl
    · rfl
  · refine (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R p.1 p.2).unique ⟨_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k R p.1 p.2, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R p.1 p.2⟩ ⟨?_, ?_⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k]
      intro w
      rw [← hL (cF p) w]
      have : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (cF p k).1) =
          L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) := by
        funext k
        exact RingEquiv.apply_symm_apply _ _
      rw [this, ContinuousLinearEquiv.apply_symm_apply]
    · funext k
      show (d.crd (d.cmb (cF p)) k).2 = p.2 k
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k]
def jnpE_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d ≃ₜ+ Mx F E d.m d.n where
  toFun p := _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2
  invFun X := (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)
  left_inv p := Prod.ext (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k R p.1 p.2) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R p.1 p.2)
  right_inv X := _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_arc_fin_k R X
  map_add' p q := by
    obtain ⟨cF, -, hadd, heq⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFPB.jn_eq_cmb_k R
    show _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R (p + q).1 (p + q).2 = _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2 + _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R q.1 q.2
    rw [heq, heq, heq, hadd, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_add_k]
  continuous_toFun := by
    obtain ⟨cF, hc, -, heq⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFPB.jn_eq_cmb_k R
    have : (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) = fun p => d.cmb (cF p) := funext heq
    show Continuous fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2
    rw [this]
    exact (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_cmb_k d).comp hc
  continuous_invFun := (_root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_arc_k R).prodMk _root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_fin_k
end PositivityTheory.SiegelWeilFormula.KFPB
end
end
