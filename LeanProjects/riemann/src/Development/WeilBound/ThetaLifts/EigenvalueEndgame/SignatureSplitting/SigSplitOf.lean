import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.SigSplit
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.TowerCodimensionTwo
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm

noncomputable section

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG

theorem sigMod_of (hW : WeilConv) (hD : KDecay) : SigMod := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' t _ ⟨Φ, hΦ, Φ', hΦ', rfl⟩
  obtain ⟨-, C, k, h1⟩ := (hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).1 Φ (polData_le t.geo.hM hΦ)
  obtain ⟨C', k', h2⟩ := ((hD F E σ B a a' G X om om' t).2 Φ' hΦ'.2).2.2
  refine ⟨max C 0 + max C' 0, max k k', fun h => ?_⟩
  have o : (1 : ℝ) ≤ ht h := by exact_mod_cast one_le_heightGL F h.1
  rw [add_mul]
  refine (norm_sub_le _ _).trans (add_le_add (((norm_integral_le_integral_norm _).trans (h1 h)).trans ?_) ((h2 h).trans ?_))
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ o (le_max_left _ _)) (by positivity) (le_max_right _ _)
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ o (le_max_right _ _)) (by positivity) (le_max_right _ _)

theorem split_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
    {a a' d₁ r s : ℕ} {W : Spc F E (a + a')} {W₁ : Spc F E d₁} {H : Plane E (a + a') d₁} {X : Chars F E} (hC : CTBasic)
    (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (p : IsPlane σ H W W₁) {f g fa fb ga gb : UA σ W.J → ℂ} (hf : IsAut f) (hg : IsAut g)
    (k1 : Split2 W₁ H X f fa fb) (k2 : Split2 W₁ H X g ga gb) (y : UA σ W.J) :
    ∃ A C, Split2 W₁ H X (fun x => (f - g) (x * y)) A C := by
  have k3 := isCT_right ((hC F E σ B _ _ _ _ H _ _ hB hW p).1 _ _ _ _ 1 hf hg k1.1 k2.1) y
  refine ⟨_, _, ?_, hasLaw_right (hasLaw_sub k1.2.1 k2.2.1 1) y, hasLaw_right (hasLaw_sub k1.2.2 k2.2.2 1) y⟩
  rw [one_smul, one_smul] at k3
  convert k3 using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, one_smul]
  ring

theorem sigSplit_of (hS : SplitEx) (hP : Tow.PlaneSkew) (hI : Iwa) (hC : CTBasic) (hA : IAut) (hR : SigRe) : SigSplit := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t hy
  have g := t.geo
  have := g.aBig
  have := g.lt
  obtain ⟨Y, W₁, H, h1, -, h2⟩ := hP F E σ B t.base (a + a') (a + a' - 2) (by omega) (by omega) G.W _ _ (by omega) hy g.hW 0 1
    one_pos (by omega)
  have t' : IsTriple B (reG G G.V G.V' Y) X om om' :=
    ⟨t.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, g.hV, g.hV', h1, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩, t.chars, t.weil, t.weil'⟩
  have p := (hI F E σ B _ _ _ _ H _ _ _ _ t.base h1 h2).1
  obtain ⟨h₀, hh⟩ := hR F E σ B a a' G X om om' t _ _ _ t'
  refine ⟨_, W₁, H, ⟨p.rank, p.xx, p.yy, p.xy, p.orth, p.gram, p.nondeg⟩, fun f hf => ?_⟩
  obtain ⟨Φ, hΦ, Φ', hΦ', e⟩ := hh f hf
  obtain ⟨s1, s2⟩ := hS F E σ B a a' (reG G G.V G.V' Y) X om om' t' _ W₁ H _ _ h2
  obtain ⟨⟨fa, fb⟩, k1, -⟩ := s1 Φ hΦ
  obtain ⟨⟨fa', fb'⟩, k2, -⟩ := s2 Φ' hΦ'
  obtain ⟨a1, a2⟩ := hA F E σ B a a' (reG G G.V G.V' Y) X om om' t'
  have k3 := split_sub (W := (reG G G.V G.V' Y).W) hC t.base h1 p (a1 Φ hΦ) (a2 Φ' hΦ') k1 k2 h₀⁻¹
  have e' : f = _ := funext fun y => (congrArg f (inv_mul_cancel_right y h₀).symm).trans (congrFun e (y * h₀⁻¹))
  rw [e']
  exact k3

end PositivityTheory.ThKEnd.Two

end
