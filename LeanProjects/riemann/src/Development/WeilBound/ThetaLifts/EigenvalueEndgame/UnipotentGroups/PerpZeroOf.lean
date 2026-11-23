import Development.WeilBound.ThetaLifts.EigenvalueEndgame.TowerCodimensionTwo
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd

noncomputable section

namespace PositivityTheory.ThKEnd.Grp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG

theorem I_inv {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (hT : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    ∀ γ ∈ ratU σ W.J, ∀ h, M.I om Φ (γ * h) = M.I om Φ h := fun γ hγ h => by
  simp only [Model.I]
  congr 1
  funext g
  simpa using ((hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 1 (one_mem _) γ hγ g h

theorem iAut_of (hT : ThetaBasic) (hC : PositivityTheory.ThKF.ICont) (hS : PositivityTheory.ThKCT.SoStab) : IAut := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t
  exact ⟨fun Φ hΦ => ⟨(hC F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t)).1 (weilCondV t) Φ (polData_le t.geo.hM hΦ),
      I_inv hT (pairV t) (polData_le t.geo.hM hΦ)⟩,
    fun Φ hΦ => ⟨(hC F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)).2 (hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t)) Φ hΦ.2,
      I_inv hT (pairV' t) (polData_le t.geo.hM' hΦ.1)⟩⟩

theorem perpZero_of (hQ : SqInt) (hA : IAut) : PerpZero := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t f hf h1 h2
  have ha := sig_isAut hA t hf
  obtain ⟨Φ, hΦ, Φ', hΦ', e⟩ := hf
  obtain ⟨c, ⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ t.base.cm _ G.W.J (-1) (fun i j => by simpa using t.geo.hW.skew i j)
    (PositivityTheory.ThKG.Tow.Levi.det_ne_zero t.geo.hW)
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (UA σ G.W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  obtain ⟨q1, q2⟩ := hQ F E σ B a a' G X om om' t μ 𝓕 hμ h𝓕
  obtain ⟨a1, a2⟩ := hA F E σ B a a' G X om om' t
  have c1 := (a1 Φ hΦ).1
  have c2 := (a2 Φ' hΦ').1
  have f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ := by
    refine Integrable.mono' (((q1 Φ hΦ).add (q2 Φ' hΦ')).const_mul 2) (ha.1.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [e, Real.norm_of_nonneg (sq_nonneg _), Pi.sub_apply, Pi.add_apply]
    have := norm_sub_le (G.M.I om Φ x) (G.M'.I om' Φ' x)
    nlinarith [sq_nonneg (‖G.M.I om Φ x‖ - ‖G.M'.I om' Φ' x‖), norm_nonneg (G.M.I om Φ x - G.M'.I om' Φ' x)]
  refine PositivityTheory.ThKF.L2.eq_zero h𝓕 ha.1 ha.2 f2 ?_
  have p1 := h1 Φ hΦ μ 𝓕 hμ h𝓕
  have p2 := h2 Φ' hΦ' μ 𝓕 hμ h𝓕
  simp only [mul_comm _ (starRingEnd ℂ _)] at p1 p2
  have := integral_sub (PositivityTheory.ThKF.L2.integrableOn_mul ha.1 c1 f2 (q1 Φ hΦ)) (PositivityTheory.ThKF.L2.integrableOn_mul ha.1 c2 f2 (q2 Φ' hΦ'))
  rw [p1, p2, sub_zero] at this
  rw [← this]
  congr 1
  funext x
  rw [← mul_sub, ← Pi.sub_apply, ← e]

end PositivityTheory.ThKEnd.Grp

end
