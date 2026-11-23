import Development.WeilBound.ThetaLifts.CartanFactorisation.UpdSelf
import Development.WeilBound.ThetaLifts.CartanFactorisation.ActsComp
import Development.WeilBound.ThetaLifts.CartanFactorisation.RinfZero
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsMaximalCompactInfinite
import Development.WeilBound.ThetaLifts.LocalTheory.SplitInv

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem so_leK {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} (hM : M.IsGood B.ψ) : M.So B.ψ B.τ₁ ≤ schA F _ :=
  Submodule.span_le.2 (by
    rintro _ ⟨f, φ, h1, h2, -, rfl⟩
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hM φ h1 h2
    rw [e]
    exact PositivityTheory.ThKG.pureA_mem f hg)

theorem clsV (hW : WeilConv) (hC : ICont) (hS : SqInt) (t : IsTriple B G X om om') : Cls B G.M om (schA F _) :=
  have p := PositivityTheory.ThKG.pairV t
  have w := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p (PositivityTheory.ThKG.weilCondV t)
  ⟨le_rfl, fun Φ h => (w.1 Φ h).1, (hC F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 (PositivityTheory.ThKG.weilCondV t), fun ψ hψ _ => w.2 ψ hψ,
    fun μ 𝓕 h1 h2 Φ _ h => (hS F E σ B a a' G X om om' t μ 𝓕 h1 h2).1 Φ h⟩

theorem clsV' (hD : KDecay) (hK : KCoinv) (hc : SoCont) (hC : ICont) (hS : SqInt) (m : IsMatched B G X om om' R Rf) :
    Cls B G.M' om' (G.M'.So B.ψ B.τ₁) := by
  have p := PositivityTheory.ThKG.pairV' m.triple
  refine ⟨so_leK p.good, fun Φ h => ((hD F E σ B a a' G X om om' m.triple).2 Φ h).2.1,
    (hC F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).2 (hK F E σ B a a' G X om om' R Rf m).2, fun ψ hψ hf h => ?_,
    fun μ 𝓕 h1 h2 Φ h' h => (hS F E σ B a a' G X om om' m.triple μ 𝓕 h1 h2).2 Φ ⟨h, h'⟩⟩
  refine SeqContinuous.continuous fun u f hu => ?_
  have := hc F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p 1 (fun _ => ψ) (fun _ => f) (fun k _ => u k) (fun _ => ⟨hψ, hu⟩)
    (fun k => by simpa using hf (u k)) (by simpa using hf f) h
  simp only [Finset.univ_unique, Finset.sum_singleton] at this
  exact this

theorem pure_soK (m : IsTriple B G X om om') (f : SInf F _) {φ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = G.M'.vac u)
    {x} (hx : x ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁)) : pure f (upd φ B.v₁ x) ∈ G.M'.So B.ψ B.τ₁ := by
  obtain ⟨j, hj, -⟩ := intersection_update_fsHerm_neg_one pureAct (PositivityTheory.ThKG.pairV' m) f h1 h2 B.v₁
  rw [← hj]
  refine (Submodule.span_le (p := (G.M'.So B.ψ B.τ₁).comap j)).2 (fun y hy => ?_) hx
  show j y ∈ G.M'.So B.ψ B.τ₁
  rw [hj]
  exact Submodule.subset_span ⟨f, _, upd_sb h1 hy.1, upd_cof h2 _ _, by rwa [upd_self], rfl⟩

theorem kills0_of (hT : ThetaBasic) (hW : WeilConv) (hK : KCoinv) (h : Kills) : PositivityTheory.ThKG.Loc.Kills0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf m q0 f hf φ h1 h2 h3
  have p2 := PositivityTheory.ThKG.pairV' m.triple
  have cv := fun Φ hΦ => ((hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p2 (Or.inr (by simp [q0]))).1 Φ hΦ).1
  obtain ⟨-, k2, k3, -⟩ := (hK F E σ B a a' G X om om' R Rf m).1 _ m.triple.chars.good
  obtain ⟨x, hx, e⟩ := k3 B.τ₁ (Rf.p' _ (φ B.v₁))
  have ha : φ B.v₁ - x ∈ augAt om' B.v₁ := (k2 _ (sub_mem (h1 _) hx.1)).1 (by rw [map_sub, e, sub_self])
  obtain ⟨j, hj, hjS⟩ := intersection_update_fsHerm_neg_one pureAct p2 f h1 h2 B.v₁
  have js : ∀ y ∈ SB _, j y ∈ schA F _ := fun y hy => by
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA p2.good _ (upd_sb h1 hy) (upd_cof h2 B.v₁ y)
    rw [hj, e]
    exact PositivityTheory.ThKG.pureA_mem f hg
  have add : ∀ y ∈ SB _, ∀ z ∈ SB _, G.M'.I om' (j (y + z)) = G.M'.I om' (j y) + G.M'.I om' (j z) := fun y hy z hz =>
    funext fun g => by rw [map_add]; exact PositivityTheory.ThKG.I_add p2.weil cv (js y hy) (js z hz) g
  have key : ∀ z ∈ augAt om' B.v₁, G.M'.I om' (j z) = 0 := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨g, hg, x, hx, y, hy, hxy, rfl⟩ := h
      have e2 := add _ (sub_mem hy hx) _ hx
      rw [sub_add_cancel, ← hjS _ x hx y hxy, I_left unimodularity_holds hT p2 (js x hx)] at e2
      exact left_eq_add.1 (e2.trans (add_comm _ _))
    | zero => rw [map_zero]; exact PositivityTheory.ThKG.I_zero _ _
    | add a b ha hb iha ihb => rw [add a (augAt_le _ ha) b (augAt_le _ hb), iha, ihb, add_zero]
    | smul c a _ iha => funext h; rw [map_smul, PositivityTheory.ThKG.I_smul, iha]; simp
  have e3 := add _ (augAt_le _ ha) x hx.1
  rw [sub_add_cancel, key _ ha, zero_add, hj, hj, upd_eq] at e3
  rw [e3]
  refine (h F E σ B a a' G X om om' R Rf m).2 f hf _ (upd_sb h1 hx.1) (upd_cof h2 _ _)
    (by rw [upd_self]; exact Submodule.subset_span hx) (h3.imp id fun ⟨v, hv⟩ => ⟨v, ?_⟩)
  by_cases ev : v = B.v₁
  · subst ev; rw [upd_self, e, hv]
  · rwa [upd_ne _ _ _ ev]

end PositivityTheory.ThKF

end
