import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.TrueGeo GlobalTheory.TrueCx
open scoped ContDiff

def cutoff (y : ℝ) : ℝ := Real.smoothTransition (3 - y) ^ 2

theorem cutoff_mem (y : ℝ) : cutoff y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sq_nonneg _, pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)⟩

theorem cutoff_of_le {y : ℝ} (h : y ≤ 2) : cutoff y = 1 := by
  rw [cutoff, Real.smoothTransition.one_of_one_le (by linarith), one_pow]

theorem cutoff_of_ge {y : ℝ} (h : 3 ≤ y) : cutoff y = 0 := by
  rw [cutoff, Real.smoothTransition.zero_of_nonpos (by linarith), zero_pow two_ne_zero]

theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff ∧ ContDiff ℝ ∞ fun y => √(cutoff y) := by
  have h : ContDiff ℝ ∞ fun y : ℝ => Real.smoothTransition (3 - y) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  exact ⟨h.pow 2, by simpa only [cutoff, Real.sqrt_sq (Real.smoothTransition.nonneg _)] using h⟩

def cutWt (κ R r : ℝ) : ℝ := cutoff (Real.log r / Real.log R) / (1 + (r / R) ^ κ)

theorem cutWt_mem (κ : ℝ) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) : cutWt κ R r ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Real.rpow_nonneg (div_nonneg hr hR) κ
  exact ⟨div_nonneg (cutoff_mem _).1 (by linarith), (div_le_one (by linarith)).2 ((cutoff_mem _).2.trans (by linarith))⟩

theorem cutWt_of_ge (κ : ℝ) {R r : ℝ} (hR : 2 ≤ R) (h : R ^ 3 ≤ r) : cutWt κ R r = 0 := by
  have h1 := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at h1
  rw [cutWt, cutoff_of_ge ((le_div_iff₀ (Real.log_pos (by linarith))).2 (by exact_mod_cast h1)), zero_div]

theorem cutWt_of_le (κ : ℝ) {R r : ℝ} (hR : 2 ≤ R) (hr : 0 < r) (h : r ≤ R ^ 2) : cutWt κ R r = 1 / (1 + (r / R) ^ κ) := by
  have h1 := Real.log_le_log hr h
  rw [Real.log_pow] at h1
  rw [cutWt, cutoff_of_le ((div_le_iff₀ (Real.log_pos (by linarith))).2 (by exact_mod_cast h1))]

example (κ : ℝ) {R : ℝ} (hR : 2 ≤ R) : cutWt κ R R = 1 / 2 := by
  rw [cutWt_of_le κ hR (by linarith) (by nlinarith), div_self (by linarith), Real.one_rpow, one_add_one_eq_two]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (σ : c.F →+* ℂ)

def OddPrimesWithRootsOfUnity.eigMet : EigMet Z σ := .ofForm (x.met σ) (x.met_smooth σ).1

theorem OddPrimesWithRootsOfUnity.eigMet_gram : (x.eigMet σ).gram = x.gram := rfl

theorem OddPrimesWithRootsOfUnity.smoothOn_eigMet : (x.eigMet σ).SmoothOn (manifold Z σ) Set.univ := fun V _ F τ a b _ =>
  have ⟨g, h1, h2, h3⟩ := x.gram_smooth (σ := σ) V F τ a b
  ⟨g, h1.mono Set.inter_subset_right, h2.mono Set.inter_subset_right, fun y _ hy f hf => h3 y hy f (hf τ)⟩

theorem OddPrimesWithRootsOfUnity.exp_le_r (y : CxPts (genStr Z) σ) : Real.exp 1 ≤ x.r σ y :=
  le_sub_self_iff _ |>.2 (Real.log_nonpos (sq_nonneg _) (pow_le_one₀
    (Finset.prod_nonneg fun i _ => ((x.nrm_div σ i).1 y).1)
    (Finset.prod_le_one (fun i _ => ((x.nrm_div σ i).1 y).1) fun i _ => ((x.nrm_div σ i).1 y).2)))

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem xiR_pos (D : D7) : 0 < xiR D :=
  norm_embedding_xi_zero D D.host.φ₀ ▸ norm_pos_iff.2 ((map_ne_zero _).2 (cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D))

variable (s) in

theorem FinalTheorems.im_neg_xi (σ : κ.c.F →+* ℂ) (k : (s.U σ).Comp) (τ : ((s.U σ).X k).Ψ) :
    (τ.1 (-((s.U σ).X k).ξ0)).im = xiR D := by
  by_cases h : Formalism.L2.PjFree.GoodEmb κ.c σ
  · have h1 := A.im_neg_xi_neg τ.1 ((((s.unf σ h).1.2.1 k).2 _).1 τ.2)
    have h2 := s.xiAbs σ k τ.1
    rw [← s.xi_eq σ k] at h1
    rw [← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.2 (GlobalTheory.FrameNormLie.re_xi _ _)] at h2
    rw [← h2, abs_of_pos (by simpa using h1)]
  · exact ((s.unif.isEmpty_comp h).false k).elim

namespace ToroidalCompactificationData

variable (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ)

def hodge : EigMet s.T.Z σ :=
  .hodge s.U (2 * Real.pi * xiR D) (mul_pos Real.two_pi_pos (xiR_pos D)) (x.eigMet σ)

variable {σ} {y : CxPts (genStr s.T.Z) σ}

theorem _root_.GlobalTheory.ShFam.FinalTheorems.exists_isHodgeFrame_iff : (∃ f, IsHodgeFrame s.U y f) ↔ ¬ LiesIn y (genBd s.T.Z) :=
  ⟨fun ⟨_, h⟩ => h.not_liesIn, exists_isHodgeFrame fun σ h => (s.unf σ h).1⟩

theorem hodge_gram {f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)} (hf : IsHodgeFrame s.U y f)
    (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    (x.hodge σ).gram y g τ = ((2 * Real.pi * xiR D : ℝ) : ℂ) • ((f.co g τ)ᴴ * f.co g τ) :=
  hf.gram_eq (fun σ h => (s.unf σ h).1) (xiR_pos D) s.im_neg_xi g τ

theorem hodge_gram_of_liesIn (h : LiesIn y (genBd s.T.Z)) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    (x.hodge σ).gram y g τ = x.gram y g τ := dif_neg fun h' => FinalTheorems.exists_isHodgeFrame_iff.1 h' h

theorem hodge_gram_riemann (hσ : Formalism.L2.PjFree.GoodEmb κ.c σ) (W : UnfWit (s.U σ)) {i : Fin W.F.n}
    {P : (W.F.Di i).La →+ (Fin W.g → ℂ)} (hP : IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab κ.c σ (W.e j).1) P)
    {Hm : Matrix (Fin W.g) (Fin W.g) ℂ} (hH : IsRiem W.F i P Hm) {q : FrPt s.Xo κ.c (CAt σ)}
    {z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Fin W.g → ℂ)} (hq : AnLie W.F i P q z) (τ : D.host.E →+* ℂ) :
    (x.hodge σ).gram (cxPt s.T.Z q) (cxFrame s.T.Z q) τ = (Real.pi : ℂ) • of fun b b' => hermForm Hm (z τ b') (z τ b) :=
  hodge_gram_eq_riemann (fun σ h => (s.unf σ h).1) (xiR_pos D) s.im_neg_xi hσ W hP hH hq τ _

theorem hodge_gram_lieFrame (L : CmList A) (k : s.Comp) {f : (s.fd k).dom} (hf : IsOrth (s.fd k) f.1) (t : D.what₂.Tau)
    (τ : D.host.E →+* ℂ) : (x.hodge κ.σ₀).gram (s.framePt k f) (s.lieFrame k f) τ =
      (hodgeC (s.fd k) (s.lab L k) t : ℂ) • 1 := by
  rw [x.hodge_gram (f := s.lieFrame k f) (isHodgeFrame_cxFrame κ.good_σ₀ hf), EigFrame.co_self, conjTranspose_one,
    Matrix.mul_one, hodgeC, Data.c, s.xiAbs, mul_left_comm, _root_.mul_assoc]

def IsMuExp (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ), ¬ LiesIn y (genBd s.T.Z) →
    ∀ (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (v : Fin (S.Dw.mult τ) → ℂ),
      x.r σ y ^ (-C) * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re ≤ (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ∧
        (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ≤ x.r σ y ^ C * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re

example (h : ∀ σ, x.eigMet σ = x.hodge σ) : x.IsMuExp 0 :=
  ⟨le_rfl, fun σ y _ g τ v => by simp [← h, x.eigMet_gram]⟩

def muExp : ℝ := Classical.epsilon x.IsMuExp

theorem isMuExp_muExp (h : ∃ C, x.IsMuExp C) : x.IsMuExp x.muExp := Classical.epsilon_spec h

def kap : ℝ := 2 * x.muExp + 3

theorem lt_kap : 2 * x.muExp + 2 < x.kap := by rw [kap]; linarith

open Classical in
variable (σ) in

def wt (R : ℝ) (y : CxPts (genStr s.T.Z) σ) : ℝ :=
  if LiesIn y (genBd s.T.Z) then 0 else cutWt x.kap (max R 2) (x.r σ y)

theorem wt_mem (R : ℝ) (y : CxPts (genStr s.T.Z) σ) : x.wt σ R y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold wt
  split_ifs
  exacts [⟨le_rfl, zero_le_one⟩, cutWt_mem _ (le_max_of_le_right zero_le_two) ((Real.exp_pos 1).le.trans (x.exp_le_r σ y))]

theorem wt_eq {R : ℝ} (hR : 2 ≤ R) (h : ¬ LiesIn y (genBd s.T.Z)) : x.wt σ R y = cutWt x.kap R (x.r σ y) := by
  rw [wt, if_neg h, max_eq_left hR]

theorem wt_eq_zero {R : ℝ} (hR : 2 ≤ R) (h : LiesIn y (genBd s.T.Z) ∨ R ^ 3 ≤ x.r σ y) : x.wt σ R y = 0 := by
  by_cases h' : LiesIn y (genBd s.T.Z)
  · exact if_pos h'
  · rw [x.wt_eq hR h', cutWt_of_ge _ hR (h.resolve_left h')]

variable (σ) in

def eigMetAt : Option ℝ → EigMet s.T.Z σ
  | none => x.hodge σ
  | some R => .interp (x.wt σ R) (x.wt_mem R) (x.eigMet σ) (x.hodge σ)

end ToroidalCompactificationData

variable (x : ToroidalCompactificationData s) (Φ : s.Flag)

def metsOf : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL) := fun k R σ n => (Φ.C k).met (x.eigMetAt (embOf κ.e σ) R) n

def refMet : ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n) :=
  fun k σ n => (Φ.C k).met (x.eigMet (embOf κ.e σ)) n

def rFlag : ∀ k σ, Pts (Φ.C k).Y σ → ℝ := fun k σ p => x.r (embOf κ.e σ) ((Φ.C k).down p)

variable (k : s.Comp) (R : Option ℝ) (σ : D.what₂.LL →+* ℂ) (n n' : Letter S.Dw → ℤ)

theorem posSet_metsOf : Met.posSet (metsOf x Φ k R σ n) = Set.univ := FlagCpt.posSet_met _ _

theorem posSet_refMet : Met.posSet (refMet x Φ k σ n) = Set.univ := FlagCpt.posSet_met _ _

theorem pn_metsOf_add : (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k R σ (n + n')) =
    (cxSt D.what₂.LL).pn _ σ _ ((cxSt D.what₂.LL).mAdd _ σ _ _ (metsOf x Φ k R σ n) (metsOf x Φ k R σ n')) :=
  FlagCpt.pn_met_add _ _ _

theorem pn_refMet_add : (cxSt D.what₂.LL).pn _ σ _ (refMet x Φ k σ (n + n')) =
    (cxSt D.what₂.LL).pn _ σ _ ((cxSt D.what₂.LL).mAdd _ σ _ _ (refMet x Φ k σ n) (refMet x Φ k σ n')) :=
  FlagCpt.pn_met_add _ _ _

variable {x Φ k σ n} {p : Pts (Φ.C k).Y σ}

theorem pn_metsOf {g : (Φ.C k).FrameAt p} {f : (Φ.C k).Y.Fn} {a : ℂ} (h : IsCoord (Φ.C k) p.1 g n f a) :
    (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k R σ n) ((cxSt D.what₂.LL).cx _ σ f) p =
      ‖a‖ ^ 2 * ∏ z : Letter S.Dw, grSq ((x.eigMetAt _ R).gram _ g z.1) z.2 ^ n z := FlagCpt.pn_met _ _ h

theorem pn_metsOf_none {g : (Φ.C k).FrameAt p} (hg : IsHodgeFrame s.U _ g) {f : (Φ.C k).Y.Fn} {a : ℂ}
    (h : IsCoord (Φ.C k) p.1 g n f a) :
    (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k none σ n) ((cxSt D.what₂.LL).cx _ σ f) p =
      ‖a‖ ^ 2 * ∏ z : Letter S.Dw, (2 * Real.pi * xiR D) ^ n z := by
  rw [pn_metsOf none h]
  refine congrArg _ (Finset.prod_congr rfl fun z _ => congrArg (· ^ n z) ?_)
  rw [ToroidalCompactificationData.eigMetAt, x.hodge_gram hg, EigFrame.co_self, conjTranspose_one, Matrix.mul_one, smul_one_eq_diagonal,
    grSq_diagonal fun _ => (mul_pos Real.two_pi_pos (xiR_pos D)).ne']

theorem metsOf_some_eq {R : ℝ} (hR : 2 ≤ R) (h : (Φ.C k).π (base p) ∈ genBd s.T.Z ∨ R ^ 3 ≤ rFlag x Φ k σ p)
    (a : (Φ.C k).Y.Fnˣ) : Met.h (metsOf x Φ k (some R) σ n) a p = Met.h (refMet x Φ k σ n) a p :=
  FlagCpt.met_congr (x.eigMetAt _ (some R)) n (G' := x.eigMet _)
    (fun g _ => EigMet.interp_gram_zero (hs := x.wt_mem R) g (x.wt_eq_zero hR h)) a

theorem exp_le_rFlag : Real.exp 1 ≤ rFlag x Φ k σ p := x.exp_le_r _ _

end GlobalTheory.ShFam
