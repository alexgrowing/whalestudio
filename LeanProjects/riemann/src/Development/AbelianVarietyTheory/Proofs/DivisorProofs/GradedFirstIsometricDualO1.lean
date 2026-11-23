import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ProjSpace GlobalTheory.QCoh

namespace GlobalTheory.TautFlag

theorem resM_s_eq_ratioOn_smul (j j' : Fin 2) {V : (PSpace ℤ 1).Opens} (h : V ≤ chart ℤ 1 j) (h' : V ≤ chart ℤ 1 j') :
    resM K h' (s j') = ratioOn V j' h' j • resM K h (s j) := by
  have hm : Mono (kernel.ι quotMap) := equalizer.ι_mono
  refine injective_app_of_mono (kernel.ι quotMap) V ?_
  refine Eq.trans ?_ (kernel_ι_app_smul_resM_s j h _).symm
  rw [ratioOn_mul_ratioOn, ratioOn_mul_ratioOn]
  exact (app_resM _ _ _).trans ((congrArg (resM E h') (map_s j')).trans (resM_v j' h'))

theorem val_detUnit_rankOne_of_eq_smul {X : Scheme.{0}} {F : X.Modules} {U U' V : X.Opens} {a : Fin 1 → Γ(F, U)}
    {a' : Fin 1 → Γ(F, U')} (ha : IsFrame a) (ha' : IsFrame a') (h : V ≤ U) (h' : V ≤ U') (c : Γ(X, V))
    (hc : resM F h' (a' 0) = c • resM F h (a 0)) : (ha.detUnit ha' h h' : Γ(X, V)) = c := by
  rw [IsFrame.val_detUnit, Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply,
    hc, ← ha.basis_apply h, map_smul, Module.Basis.repr_self]
  simp

theorem det_g_adapt₀ (j j' : Fin 2) :
    (VB.det (flag.gr 0) 1).g (adapt₀ j).quot (adapt₀ j').quot = ((O1 ℤ 1).g j j')⁻¹ := by
  refine Units.ext (val_detUnit_rankOne_of_eq_smul _ _ _ _ _ ?_)
  refine (app_resM (VMetric.stepSeq flag 0).g inf_le_right (s j')).symm.trans ?_
  refine (congrArg ((VMetric.stepSeq flag 0).g.app _) (resM_s_eq_ratioOn_smul j j' inf_le_left inf_le_right)).trans ?_
  exact (Scheme.Modules.Hom.app_smul _ _ _).trans
    (congrArg (_ • ·) (app_resM (VMetric.stepSeq flag 0).g inf_le_left (s j)))

theorem grLB_zero_φ (σ : ℤ →+* ℂ) (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    ((VMetric.grLB flag 0 stdH.cInf).φ σ).φ (adapt₀ j).quot y = -Real.log (nsqV j y).re := by
  have e := Met.quot_G ((stdH.h.stepMet flag 0).met σ) (VMetric.stepSeq_shortExact flag 0)
    (flag.isVB (Fin.castSucc 0)) (flag.isVB_gr 0) (adapt₀ j) hy
  refine congrArg (fun z : ℂ => -Real.log z.re) ((congrArg Matrix.det e).trans ((Matrix.det_fin_one _).trans ?_))
  refine Eq.trans ?_ (gram_adapt₀ j hy 0 0)
  have key (H : Matrix (Fin 0 ⊕ Fin 1) (Fin 0 ⊕ Fin 1) ℂ) : quotGram H 0 0 = H (.inr 0) (.inr 0) := by
    simp [quotGram, toBlocks₂₂]
  exact key _

theorem fubini_study_weight_eq_log_norm (σ : ℤ →+* ℂ) (j : Fin 2) (y : CxPts (PSpace.str ℤ 1) σ) :
    ((hermitianTwistingSheaf ℤ 1).φ σ).φ j y = Real.log (nsqV j y).re := by
  change (ProjAn.fsO1 ℤ σ 1).φ j y = _
  refine (Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ ?_)
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine (Fin.sum_univ_two _).trans ?_
  simp only [nsqV, Complex.mul_conj, Complex.add_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rfl

theorem isometric_grLB_zero :
    (VMetric.grLB TautFlag.flag 0 TautFlag.stdH.cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1).dual :=
  HermLB.Isometric.symm (HermLB.isometric_of_chart (L := (hermitianTwistingSheaf ℤ 1).dual) (fun j => (adapt₀ j).quot)
    (fun _ => le_rfl) (fun x j j' _ _ => congrArg (gm (𝟙 _) x _) (det_g_adapt₀ j j').symm)
    fun σ j y hy => (grLB_zero_φ σ j hy).trans (congrArg (- ·) (fubini_study_weight_eq_log_norm σ j y).symm))

end GlobalTheory.TautFlag
