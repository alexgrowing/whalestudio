import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOfIsOrtho
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FjNormMulExpLeSupFlow
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfLePolyExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealFlowPeriodsSpanEqTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOrthogonality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos

noncomputable section

namespace GlobalTheory.CuspUnif

section Decay

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mem_SS_of_decay (X : Data E r) (hr : 0 < r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    {C c : ℝ} (hc : 0 < c) (h : ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ C * Real.exp (-c / X.firstMinimumSq x)) : P ∈ X.SS la := by
  have := GlobalTheory.ModeDecay.nonempty_cmType X
  set f : ℝ := (Fintype.card X.Ψ : ℝ) with hf
  have hf0 : 0 < f := Nat.cast_pos.2 Fintype.card_pos
  have hπ := Real.pi_pos
  refine ⟨hP, fun ξ hξ x hx => GlobalTheory.ModeDecay.fj_eq_zero_of_decay GlobalTheory.fj_norm_mul_exp_le_sup_flow
    ReciprocityTheory.ChartRestriction.G.AR.Inst.la1GGStatement_firstMinimum r X la P (c / (8 * Real.pi * f)) hP.1
    ⟨Real.sqrt |C|, 0, le_rfl, fun y hy η hη h2 => ?_⟩ ξ hξ 0 (by simpa using by positivity) x hx⟩
  set t := ⨅ τ, X.tt η y τ with ht
  have ht2 : 2 ≤ t := le_ciInf h2
  have ht' : 0 < t := by linarith
  have hpos : ∀ v : Fin r → E, v ≠ 0 → ∀ τ, 0 < X.c τ * X.maj y τ (Data.emb τ.1 v) := fun v hv τ =>
    mul_pos (TwoSidedBoostBounds.c_pos X τ) (X.maj_pos hy τ (emb_ne_zero τ.1 hv))
  have hle : ∀ τ, X.c τ * X.maj y τ (Data.emb τ.1 η) ≤ 1 / t := fun τ =>
    (le_one_div ht' (hpos η hη.2.2 τ)).1 (ciInf_le (f := fun τ => X.tt η y τ) (Finite.bddBelow_range _) τ)
  have hla : X.firstMinimumSq y ≤ f / t :=
    calc X.firstMinimumSq y ≤ ∑ τ, X.c τ * X.maj y τ (Data.emb τ.1 η) := by
          refine csInf_le ⟨0, ?_⟩ ⟨η, hη.1, hη.2.2, rfl⟩
          rintro _ ⟨v, -, hv, rfl⟩
          exact Finset.sum_nonneg fun τ _ => (hpos v hv τ).le
      _ ≤ ∑ _τ : X.Ψ, 1 / t := Finset.sum_le_sum fun τ _ => hle τ
      _ = f / t := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  have hla0 : 0 < X.firstMinimumSq y := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom X hr hy)
  have hexp : Real.exp (-c / X.firstMinimumSq y) ≤ Real.exp (-4 * Real.pi * (c / (8 * Real.pi * f)) * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have : c / (f / t) ≤ c / X.firstMinimumSq y := div_le_div_of_nonneg_left hc.le hla0 hla
    have e1 : ((2 : ℕ) : ℝ) * (-4 * Real.pi * (c / (8 * Real.pi * f)) * t) = -(c / (f / t)) := by
      push_cast
      field_simp
      norm_num
    rw [e1, neg_div]
    linarith
  rw [Real.rpow_zero, mul_one]
  refine (Real.le_sqrt_of_sq_le ((h y hy).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left hexp (abs_nonneg C))))).trans_eq ?_
  rw [Real.sqrt_mul (abs_nonneg C), Real.sqrt_sq (Real.exp_pos _).le]

end Decay

section Unif

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.OrthoMetric GlobalTheory.SupFull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem norm_hermC_col (X : FD.Data E r) {x : FD.Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ)
    (v : Fin r → ℂ) (b : Fin r) :
    ‖FD.hermC τ.1 X.Gm (FD.col (FD.mat x τ) b) v‖ = ‖((FD.mat x τ)⁻¹.mulVec v) b‖ := by
  set w := (FD.mat x τ)⁻¹.mulVec v with hw
  have hv : (FD.mat x τ).mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hx τ).1), Matrix.one_mulVec]
  have hg : ∀ i, FD.hermC τ.1 X.Gm (FD.col (FD.mat x τ) b) (FD.col (FD.mat x τ) i) =
      if b = i then ((FD.sgn X.p0 (b : ℕ) : ℝ) : ℂ) else 0 := fun i => by
    have := congrFun (congrFun (ho τ) b) i
    simpa [FD.gram, Matrix.diagonal_apply] using this
  have e : FD.hermC τ.1 X.Gm (FD.col (FD.mat x τ) b) v =
      ∑ i, starRingEnd ℂ (w i) * FD.hermC τ.1 X.Gm (FD.col (FD.mat x τ) b) (FD.col (FD.mat x τ) i) := by
    rw [← hv]
    simp only [FD.hermC, FD.col, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  simp only [hg, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, norm_mul, Complex.norm_conj]
  unfold FD.sgn
  split_ifs <;> simp

theorem hermForm_period {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) {k : U.Comp} {x : (U.X k).dom}
    (W : PullbackSections.UnfAt U k x) (Wu : PullbackSections.UnitAt W) (hx : (U.X k).IsOrtho x.1) (a : (W.F.Di (W.ik k)).La) :
    (hermForm Wu.Hm (W.Pm a) (W.Pm a)).re =
      ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (FD.Data.emb τ.1 (W.φ k a : Fin r → E)) := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  have hper : ∀ (v : Fin r → E) j, ‖perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2‖ =
      ‖((FD.mat x.1 ((W.e.trans f) j).1)⁻¹.mulVec (FD.Data.emb ((W.e.trans f) j).1.1 v)) ((W.e.trans f) j).2‖ := by
    intro v j
    have h := hf (W.e j)
    rw [Equiv.trans_apply]
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    generalize ((W.e j).2 : ℕ) = i at h ⊢
    dsimp only at h ⊢
    rw [← hp0] at h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · unfold perFr
      rw [dif_pos a, dif_pos hn]
    · unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      exact norm_hermC_col (U.X k) x.2 hx ⟨_, hτ⟩ _ _
  have hn : ∀ j, ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖((W.e.trans f) j).1.1 (U.X k).ξ0‖ := fun j => by
    rcases hf (W.e j) with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · rw [Equiv.trans_apply, h]
    · rw [Equiv.trans_apply, h]
      exact (Complex.norm_conj _).symm
  simp only [FD.MajorantOrthogonality.maj_ortho _ x.2 hx, ReciprocityTheory.MultiplicativeHeights.normSq, Finset.mul_sum]
  rw [← Fintype.sum_prod_type', hm_eq_diagonal E H Dw l Xo c σ r U hσ hU k x W Wu hx, hermForm, dotProduct,
    Complex.re_sum]
  refine Fintype.sum_equiv (W.e.trans f) _ _ fun j => ?_
  rw [Matrix.mulVec_diagonal, Pi.star_apply, mul_left_comm, Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq, W.pm_eq, hper, hn]
  rfl

def firstMin {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) : ℝ :=
  sInf {t | ∃ z ∈ Λ, z ≠ 0 ∧ t = (hermForm Hm z z).re}

theorem exists_unif_la1sq {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) {k : U.Comp} {x : (U.X k).dom}
    (hx : (U.X k).IsOrtho x.1) {y : Sp ℂ ⟶ Xo.X} (hy : y = (U.un k x).x) (Φ₀ : FibKey Xo ℂ y) :
    ∃ (g : ℕ) (_ : g = Φ₀.key.P.g) (u : HolUnif Φ₀.key.P.A Φ₀.key.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ ∧ (U.X k).firstMinimumSq x.1 = firstMin u.Λ Hm := by
  subst hy
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (secNZ_of_secGen lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, hΛ, hA, -, -, hg, -⟩ := exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2 Wu.c3 Wu.c4
    Wu.c5 Wu.c6 Wu.c7
  refine ⟨W.g, hg, u, Wu.Hm, χ, hA, congrArg sInf (Set.ext fun t => ?_)⟩
  have hm : ∀ z, z ∈ u.Λ ↔ ∃ a, W.Pm a = z := fun z => by rw [hΛ]; rfl
  constructor
  · rintro ⟨v, hv, hv0, rfl⟩
    obtain ⟨a, ha⟩ := (W.φ k).surjective ⟨v, hv⟩
    have e := hermForm_period hσ hU W Wu hx a
    rw [ha] at e
    refine ⟨W.Pm a, (hm _).2 ⟨a, rfl⟩, fun h0 => ?_, e.symm⟩
    have := GlobalTheory.ModeDecay.nonempty_cmType (U.X k)
    have hp : 0 < ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (FD.Data.emb τ.1 v) :=
      Finset.sum_pos (fun τ _ => mul_pos (FD.TwoSidedBoostBounds.c_pos _ τ) ((U.X k).maj_pos x.2 τ (FD.emb_ne_zero τ.1 hv0)))
        Finset.univ_nonempty
    rw [← e, h0] at hp
    simp [hermForm] at hp
  · rintro ⟨z, hz, hz0, rfl⟩
    obtain ⟨a, rfl⟩ := (hm z).1 hz
    refine ⟨W.φ k a, (W.φ k a).2, fun h0 => hz0 ?_, hermForm_period hσ hU W Wu hx a⟩
    rw [(W.φ k).map_eq_zero_iff.1 (Subtype.ext h0), map_zero]

theorem la1sq_eq_of_un_x_eq {U U' : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) (hU' : IsUnf U') (hpq : 1 ≤ Dw.p + Dw.q)
    {k : U.Comp} {x : (U.X k).dom} (hx : (U.X k).IsOrtho x.1) {k' : U'.Comp} {x' : (U'.X k').dom}
    (hx' : (U'.X k').IsOrtho x'.1) (e : (U'.un k' x').x = (U.un k x).x) :
    (U.X k).firstMinimumSq x.1 = (U'.X k').firstMinimumSq x'.1 := by
  obtain ⟨Φ⟩ := nonempty_fibKey E H Dw l Xo ℂ (U'.un k' x').x hpq
  obtain ⟨_, rfl, u, Hm, χ, hA, h⟩ := exists_unif_la1sq hσ hU hx e Φ
  obtain ⟨_, rfl, u', Hm', χ', hA', h'⟩ := exists_unif_la1sq hσ hU' hx' rfl Φ
  obtain ⟨-, t1', t2'⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all Φ.key.P Φ.key.rig Φ.key.rig_gen u' Hm' χ' hA'
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo Φ.key.P.A Φ.key.P.isAb Φ.key.P.L Φ.key.P.g Φ.key.P.g u'
    t1' t2' u.ex u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  have hi := UnifCompare.injective u u' F hF
  have hs := LinearMap.injective_iff_surjective.1 hi
  rw [h, h']
  refine congrArg sInf (Set.ext fun t => ⟨?_, ?_⟩)
  · rintro ⟨z, hz, hz0, rfl⟩
    exact ⟨F z, (UnifCompare.mem_iff u u' F hF z).2 hz, fun h0 => hz0 (hi (h0.trans (map_zero F).symm)),
      by rw [UnifCompare.hermForm_eq Φ.key.P.isLB u u' hA hA' F hF]⟩
  · rintro ⟨z, hz, hz0, rfl⟩
    obtain ⟨z, rfl⟩ := hs z
    exact ⟨z, (UnifCompare.mem_iff u u' F hF z).1 hz, fun h0 => hz0 (by rw [h0, map_zero]),
      by rw [UnifCompare.hermForm_eq Φ.key.P.isLB u u' hA hA' F hF]⟩

end Unif

end GlobalTheory.CuspUnif
