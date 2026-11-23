import Development.WeilBound.ThetaLifts.EigenvalueEndgame.TowerCodimensionTwo
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Grp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG PositivityTheory.ThKF

variable {n d : ℕ} {X X₂ : Spc F E n} {W W₂ : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

variable (M X₂ W₂) in

def reM : Model σ (reS X X₂) (reS W W₂) := ⟨M.co, M.vac, M.μ, M.dom⟩

theorem so_re : M.So B.ψ B.τ₁ ≤ (reM X₂ W₂ M).So B.ψ B.τ₁ := Submodule.span_mono (by
  rintro _ ⟨f, φ, h1, h2, ⟨h3, ι, h4, h5⟩, rfl⟩
  exact ⟨f, φ, h1, h2, ⟨h3, ι, ⟨h4.bij, h4.trans, h4.mult⟩, h5⟩, rfl⟩)

theorem move (hA : ArchOp) (hM : CartanMove) (hp : IsPair B M χX χW om r s r' s') (hp₂ : IsPair B (reM X₂ W₂ M) χX χW om r s r' s')
    {h : UA σ W.J} (hh : h ∈ UAt σ W (evI F))
    (hθ : ∀ w, (mat h).map (piInf (B.emb w)) * W₂.θ w = W.θ w * (mat h).map (piInf (B.emb w))) :
    ∃ g : UA σ X.J, ∀ Φ ∈ PolData B M, om (g, h⁻¹) Φ ∈ PolData B (reM X₂ W₂ M) := by
  obtain ⟨g, hg, -, hT⟩ := hM F E σ B n d X W M χX χW om r s r' s' hp X₂ W₂ (reM X₂ W₂ M) rfl hp₂ h hh hθ
  obtain ⟨T, h1, -⟩ := hA F E σ B n d X W M χX χW om r s r' s' hp g hg h hh
  refine ⟨g⁻¹, fun Φ hΦ => (Submodule.span_le (p := (PolData B (reM X₂ W₂ M)).comap (om (g⁻¹, h⁻¹)))).2 ?_ hΦ⟩
  rintro _ ⟨f, hf, φ, h2, h3, rfl⟩
  rw [← hT T h1] at hf
  obtain ⟨f₂, h4, rfl⟩ := hf
  obtain ⟨ψ, h5, h6⟩ := pure_eq_pureA hp.good φ h2 h3
  refine Submodule.subset_span ⟨f₂, h4, φ, h2, h3, ?_⟩
  rw [h6, h6]
  change om _ (pureA F (T f₂) ψ) = _
  rw [← h1.1 f₂ ψ h5, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk, map_one,
    Module.End.one_apply]

theorem I_both (hI : PositivityTheory.ThKEst.IInv) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) (g : UA σ X.J)
    (h : UA σ W.J) : M.I om (om (g, h) Φ) = fun x => M.I om Φ (x * h) := by
  rw [← I_trans, ← (hI F E σ B n d X W M χX χW om r s r' s' hp _ (hp.weil.isUSplitting.pres (1, h) _ hΦ)).2.1 g,
    ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem sigRe_of (hA : ArchOp) (hM : CartanMove) (hC : CartanConj) (hI : PositivityTheory.ThKEst.IInv) (hS : PositivityTheory.ThKCT.SoStab) : SigRe := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t V V' W t₂
  obtain ⟨h, hh, hθ⟩ := hC F E σ B _ G.W W _ _ t.base t.geo.hW t₂.geo.hW
  obtain ⟨g, hg⟩ := move (X₂ := V) hA hM (pairV t) (pairV t₂) hh hθ
  obtain ⟨g', hg'⟩ := move (X₂ := V') hA hM (pairV' t) (pairV' t₂) hh hθ
  refine ⟨h⁻¹, ?_⟩
  rintro _ ⟨Φ, hΦ, Φ', hΦ', rfl⟩
  refine ⟨_, hg Φ hΦ, _, ⟨hg' Φ' hΦ'.1, so_re (hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) _ _ hΦ'.2)⟩, ?_⟩
  change _ = G.M.I om (om (g, h⁻¹) Φ) - G.M'.I om' (om' (g', h⁻¹) Φ')
  rw [I_both hI (pairV t) (polData_le t.geo.hM hΦ), I_both hI (pairV' t) (polData_le t.geo.hM' hΦ'.1)]
  rfl

end PositivityTheory.ThKEnd.Grp

end
