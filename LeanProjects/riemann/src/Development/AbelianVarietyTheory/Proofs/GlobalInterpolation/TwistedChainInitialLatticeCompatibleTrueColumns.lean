import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem valAt_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (φ : (I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ)
    (b : (I.stp u I.mu0 0).β) (b' : (I.stp u a 0).β) (p : (I.stp u I.mu0 0).D b) (p' : (I.stp u a 0).D b')
    (h : p.1.1.deco = p'.1.1.deco) :
    valAt (I.stp u a 0) B.fields.emb B.embLL (fun c => φ ((I.eCls0 l u a).symm c)) b' p' =
      valAt (I.stp u I.mu0 0) B.fields.emb B.embLL φ b p := by
  have hc : I.eCls0 l u a ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p')) = (I.stp u a 0).cl b' p' :=
    (I.eCls0 l u a).apply_symm_apply _
  have hdeco : ((I.stp u a 0).rep ((I.stp u a 0).cl b' p')).1.1.deco =
      ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p'))).1.1.deco := by
    conv_lhs => rw [← hc]
    exact stepZero_corresponding_representatives_same_deco hI u a _ _
  show (I.stp u a 0).tr B.fields.emb B.embLL b' ((I.stp u a 0).mv b' p')
      (φ ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p'))) = _
  generalize (I.eCls0 l u a).symm ((I.stp u a 0).cl b' p') = c at hdeco ⊢
  obtain ⟨b₁, q⟩ := c
  obtain rfl : b = b₁ := stepZero_chartIndex_subsingleton hI _ _ _
  have hm := (I.stp u a 0).mv_smul b' p'
  have hy : ∀ N, (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) 0).ys N = {∅} := fun N => by rw [ys0]; rfl
  obtain ⟨g, g1, g2, g3⟩ := GlobalTheory.LvT.StartTie.exists_lift (y' := ysAt B.R I.sel (I.tup a) (I.cst a) 0) hy
    ((levelTypePrimes_stepZero_eq_colLev hI I.mu0 b).trans (levelTypePrimes_stepZero_eq_colLev hI a b').symm) (chartIndexLevelTwistPrimes_stepZero_eq_top hI I.mu0 b) (chartIndexLevelTwistPrimes_stepZero_eq_top hI a b')
    ((I.stp u a 0).mv b' p') ((I.stp u I.mu0 0).rep ⟨b, q⟩) p ((I.stp u a 0).rep ((I.stp u a 0).cl b' p'))
    hdeco.symm (h.trans (congrArg (fun r : (I.stp u a 0).D b' => r.1.1.deco) hm).symm)
  have h1 := valAt_eq B.fields.emb B.embLL (l.lev u I.mu0).free0 φ ⟨b, q⟩ g
  refine Eq.trans ?_ (h1.symm.trans (congrArg _ g1))
  have h2 : (I.stp u a 0).tr B.fields.emb B.embLL b' ((I.stp u a 0).mv b' p') =
      (I.stp u I.mu0 0).tr B.fields.emb B.embLL b g :=
    congrArg₂ (trFr B.fields.emb B.embLL) (congrArg (Formalism.L2.Col.ufGL B.fields.E (B.R.N 0)) g2.symm) g3.symm
  exact congrFun (congrArg DFunLike.coe h2) _

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem rep_eCls0_symm (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c' : (I.stp u a 0).Cl) :
    ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm c')).1.1.deco = ((I.stp u a 0).rep c').1.1.deco := by
  conv_rhs => rw [← (I.eCls0 l u a).apply_symm_apply c']
  exact (stepZero_corresponding_representatives_same_deco hI u a _ _).symm

theorem nm_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Nm (tw (I.tw l l0 Z) u I.mu0) 0 v φ) = Nm (tw (I.tw l l0 Z) u a) 0 v ((I.cols l).e0Tw u a φ) := by
  unfold Nm
  erw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  funext c'
  refine (valAt_eCls0 hI l u a φ _ _ _ _ ?_).symm
  exact (dia_deco _ v a').trans ((congrArg (Formalism.L2.Col.DecoSet.dia1 v a') (rep_eCls0_symm hI l u a c')).trans
    (dia_deco _ v a').symm)

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem up_deco0 (l : I.Laws) (u : B.Word) (a : I.ι) (b : (I.stp u a 0).β) (p : (I.stp u a 0).D b)
    (P : (I.atIn u a).ST) (x : Formalism.L2.Col.Sp B.fields.E (B.R.N 0)) (hx : x ∈ p.1.1.deco.1.N) (hf : p.1.1.deco.1.f P x = 1) :
    (((I.atIn u a).A 0).up b p P x).1.1.deco = p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x := by
  change (p.mv (p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x)).1.1.deco = _
  by_cases hc : (p.1.1.deco.1.up P ((I.atIn u a).T : 𝓞 B.fields.E) x).Ok
  · apply mv_deco
    have h1 := congrArg Formalism.L2.Col.Deco.N (((l.lev u a).tied 0).up_deco b p P x hx hf)
    refine Eq.trans h1 ?_
    unfold Formalism.L2.Col.DecoSet.up
    rw [dif_pos hc]
    rfl
  · have h1 : p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x = p.1.1.deco := dif_neg hc
    rw [h1]
    exact congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => q.1.1.deco) (dif_pos ⟨p.1.1.2, p.2⟩ : p.mv p.1.1.deco = _)

def onesAt {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v : Y.A.vT) (c : Y.C.cls 0) : Finset (Y.fm.lv 0 v c) :=
  Finset.univ.filter (fun x : Y.fm.lv 0 v c => Y.fm.fv 0 v c x = 1)

theorem mem_onesAt {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v : Y.A.vT) (c : Y.C.cls 0) (x : Y.fm.lv 0 v c) :
    x ∈ onesAt Y v c ↔ Y.fm.fv 0 v c x = 1 := by
  simp [onesAt]

theorem uop_apply {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v) (φ : Fn Y 0) :
    Uop Y 0 v φ = fun c => ∑ x ∈ onesAt Y v c, Y.fm.upT 0 v c x (φ (Y.fm.up 0 v c x)) := by
  funext c
  simp [Uop, LinearMap.sum_apply, onesAt]

theorem uop_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ) = Uop (tw (I.tw l l0 Z) u a) 0 v ((I.cols l).e0Tw u a φ) := by
  funext c'
  have hd := rep_eCls0_symm hI l u a c'
  have hN := congrArg (fun d : Formalism.L2.Col.DecoSet B.fields.E (B.R.N 0) _ _ => d.1.N) hd
  have hF := congrArg (fun d : Formalism.L2.Col.DecoSet B.fields.E (B.R.N 0) _ _ => d.1.f v) hd
  refine (show (I.cols l).e0Tw u a (Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ) c' =
    Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ ((I.eCls0 l u a).symm c') from rfl).trans ?_
  refine (congrFun (uop_apply (tw (I.tw l l0 Z) u I.mu0) v φ) _).trans
    (Eq.trans ?_ (congrFun (uop_apply (tw (I.tw l l0 Z) u a) v ((I.cols l).e0Tw u a φ)) c').symm)
  revert hd hN hF
  generalize (I.eCls0 l u a).symm c' = c
  intro hd hN hF
  refine Eq.trans ?e1 (up_match B.fields.emb B.embLL (l.lev u I.mu0).free0 ((l.lev u I.mu0).lev 0) ((l.lev u I.mu0).tied 0)
    ((l.lev u a).lev 0) ((l.lev u a).tied 0) v (onesAt (tw (I.tw l l0 Z) u I.mu0) v) ?hs c' _ ?hs' φ ((I.cols l).e0Tw u a φ) c.1 ((I.stp u I.mu0 0).rep c)
    hN hF ?hup)
  case e1 =>
    exact (valAt_rep B.fields.emb B.embLL (l.lev u I.mu0).free0 (fun c => ∑ x ∈ onesAt (tw (I.tw l l0 Z) u I.mu0) v c,
      valAt (I.stp u I.mu0 0) B.fields.emb B.embLL φ c.1 (((I.atIn u I.mu0).A 0).upPt v c x)) c).symm
  case hs => exact fun c x => mem_onesAt (tw (I.tw l l0 Z) u I.mu0) v c x
  case hs' => exact fun x => mem_onesAt (tw (I.tw l l0 Z) u a) v c' x
  case hup =>
    intro x hx h1
    refine valAt_eCls0 hI l u a φ _ _ _ _ ?_
    refine (up_deco0 l u I.mu0 _ _ v x hx h1).trans ((congrArg (fun d : Formalism.L2.Col.DecoSet B.fields.E (B.R.N 0) _ _ =>
      d.up v ((I.atIn u a).T : 𝓞 B.fields.E) x) hd).trans
        (up_deco0 l u a _ _ v x (hN ▸ hx) (by rw [← congrFun hF x]; exact h1)).symm)

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem uop_mem (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) {φ : Fn (tw (I.tw l l0 Z) u a) 0} (hφ : φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0) :
    Uop (tw (I.tw l l0 Z) u a) 0 v φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0 := by
  erw [uop_apply]
  exact DiaStab.mem_Fi _ B.fields.emb B.embLL _ (l.lev u a).free0 _ fun _ => Submodule.sum_mem _ fun _ _ =>
    DiaStab.tr_mem _ B.fields.emb B.embLL _ _ _ (hφ _).1

theorem ulist_mem (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (ls : List (tw (I.tw l l0 Z) u a).A.vT) {φ : Fn (tw (I.tw l l0 Z) u a) 0} (hφ : φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0) :
    Ulist (tw (I.tw l l0 Z) u a) ls φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0 := by
  induction ls with
  | nil => exact hφ
  | cons v ls ih => exact uop_mem l l0 Z u a v ih

theorem ulist_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (ls : List (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Ulist (tw (I.tw l l0 Z) u I.mu0) ls φ) = Ulist (tw (I.tw l l0 Z) u a) ls ((I.cols l).e0Tw u a φ) := by
  induction ls with
  | nil => rfl
  | cons v ls ih => exact (uop_eCls0 hI l l0 Z u a v _).trans (congrArg (Uop (tw (I.tw l l0 Z) u a) 0 v) ih)

theorem step0Tie_trueCols : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), Step0Tie (I.tw l l0 Z) u a := by
  intro B X I hI l l0 Z u a w _
  refine ⟨rfl, fun x hx => ?_⟩
  refine nlam_map (X := tw (I.tw l l0 Z) u I.mu0) (Y := tw (I.tw l l0 Z) u a)
    (e := (I.cols l).e0Tw u a) (eL := (I.tw l l0 Z).e0 u a) w rfl ((I.tw l l0 Z).embed_mul_block_embedding u a)
    (fun x hx => ((I.tw l l0 Z).twist_preserves_base_lattice u a x).1 hx) (fun v => ⟨v, fun φ _ => nm_eCls0 hI l l0 Z u a v φ⟩) rfl
    (fun φ hφ => ulist_mem l l0 Z u I.mu0 _ hφ) (fun φ _ => ulist_eCls0 hI l l0 Z u a _ φ) hx

end GlobalTheory.LvT.TrueStep0
