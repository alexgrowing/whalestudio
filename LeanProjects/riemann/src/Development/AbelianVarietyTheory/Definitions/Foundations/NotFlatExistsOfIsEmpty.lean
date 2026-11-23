import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

noncomputable section

namespace GlobalTheory.FlatLine.Model

open NumberField IsDedekindDomain Module AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_vAdd_two_ne (K : Type) [Field K] [NumberField K] :
    ∃ w : HeightOneSpectrum (𝓞 K), vAdd w (2 : K) ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := sum_vAdd_nat (K := K) (n := 2) two_ne_zero
  simp only [Nat.cast_ofNat, h, Int.cast_zero, zero_mul, finsum_zero] at h1
  exact (Real.log_pos one_lt_two).ne h1

theorem exists_constSec (h1 : N1c) (h2 : GlobalTheory.Published.HasseNormSt) (Xo : Moduli Dw l) (c : Coeff l)
    (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (x : ℝ) :
    ∃ U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q), (∀ σ, GoodEmb c σ → IsUnf (U σ)) ∧ Nonempty (Comp Xo c) ∧
      ∀ Z : Comp Xo c, ∃ s : ConstSec U x Z 0 0, (∀ σ, s.cInf σ = 2) ∧ (∃ w, s.rho_vw w ≠ 0) ∧ s.deg = 0 := by
  classical
  have hex : ∀ σ : c.F →+* ℂ, ∃ U : Unf Xo c σ (Dw.p + Dw.q), GoodEmb c σ → IsUnf U := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, hU⟩ := GlobalTheory.IsUnfEx.exists_isUnf h1 h2 GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
        GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c σ hpq hσ
      exact ⟨⟨U.Comp, U.X, U.un⟩, fun _ => hU⟩
    · exact ⟨⟨Empty, fun k => k.elim, fun k => k.elim⟩, fun h => absurd h hσ⟩
  choose U hU using hex
  refine ⟨U, hU, (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l Xo c hpq).1, fun Z => ?_⟩
  have h := hasPts U hpq hg hU Z
  obtain ⟨w, hw⟩ := exists_vAdd_two_ne c.F
  refine ⟨(ConstSec.one x h).smul 2 two_ne_zero, fun σ => ?_, ⟨w, ?_⟩,
    (ConstSec.deg_smul _ _ _).trans (ConstSec.deg_one h)⟩
  · show ‖σ 2‖ * 1 = 2
    rw [map_ofNat]; simp
  · show (vAdd w (2 : c.F) : ℝ) + 0 ≠ 0
    simpa using hw

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem nonempty_psi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Nonempty (Psi H) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ (H.rt : E) = H.rt0
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨_, conj_mem h⟩⟩

theorem not_flatExists_of_isEmpty (hpq : 1 ≤ Dw.p + Dw.q) (h : ∀ σ, IsEmpty (U σ).Comp) : ¬ FlatExists U x := by
  intro hF
  obtain ⟨Z⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l Xo c hpq).1
  obtain ⟨τ⟩ := nonempty_psi H
  obtain ⟨s⟩ := hF.nonempty Z τ
  obtain ⟨z, -⟩ := (s.hasPts.1 c.F.val.toRingHom).1
  exact (h _).false z.1

theorem flatExistsAt_unique (hpq : 1 ≤ Dw.p + Dw.q) {a b : ℝ} (ha : FlatExistsAt U x a) (hb : FlatExistsAt U x b) :
    a = b := by
  have hne := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l Xo c hpq).1
  obtain ⟨τ⟩ := nonempty_psi H
  rw [← ha.c1_eq hne τ, hb.c1_eq hne τ]

theorem pnorm_modelFlat (X : Data E r) (τ : X.Ψ) (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    X.pnorm (modelFlat r τ) P y = ‖P y‖ * (‖(mat y τ).det‖ * Real.sqrt ‖τ.1 X.Gm.det‖) := by
  have h := pnorm_horizGen X τ hy
  have hx : ‖(mat y τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hy τ).1
  simp only [Data.pnorm, horizGen, norm_inv] at h ⊢
  rw [← h]; field_simp

theorem norm_rdU_sig (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {Z : Comp Xo c} {τ : Psi H} (s : FlatSec U x Z τ)
    (σ : c.F →+* ℂ) (k : (U (goodOf c σ)).Comp) :
    ∃ (hτ : relab c (goodOf c σ) τ.1 ∈ ((U (goodOf c σ)).X k).Ψ) (a : ℝ), 0 < a ∧ ∀ y,
      (⟨k, y⟩ : Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) ∈ framesOn (U (goodOf c σ)) Z →
        ‖rdU (U (goodOf c σ)) s.sig k y‖ = a * ‖horizGen ⟨_, hτ⟩ y‖ := by
  have hσ := goodEmb_goodOf c σ
  have hτ : relab c (goodOf c σ) τ.1 ∈ ((U (goodOf c σ)).X k).Ψ := by
    refine (((hU _ hσ).2.1 k).2 _).2 ?_
    have hσ0 : goodOf c σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg (goodOf c σ) (Subtype.ext τ.2)).trans hσ0
  have hG : 0 < Real.sqrt ‖relab c (goodOf c σ) τ.1 ((U (goodOf c σ)).X k).Gm.det‖ :=
    Real.sqrt_pos.2 (norm_pos_iff.2 ((map_ne_zero _).2 ((U (goodOf c σ)).X k).Gm_det))
  have hl := lieFacZ_pos (Dw := Dw) x (wtOf Dw (flatWt Dw τ) 0)
  refine ⟨hτ, s.cInf σ / (lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) *
    Real.sqrt ‖relab c (goodOf c σ) τ.1 ((U (goodOf c σ)).X k).Gm.det‖), div_pos (s.cInf_pos σ) (mul_pos hl hG),
    fun y hy => ?_⟩
  have h := s.homN_eq hy
  rw [homN, ptN, modelWt_flatWt _ hσ (hU _ hσ) τ k hτ, pnorm_modelFlat _ _ _ hy.1] at h
  have hx : ‖(mat y ⟨_, hτ⟩).det‖ ≠ 0 := norm_ne_zero_iff.2 (hy.1 _).1
  rw [← h, horizGen, norm_inv]
  field_simp

def twoFr (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r := fun _ => ((2 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) :)

theorem mat_double {Ψ : Finset (E →+* ℂ)} (y : Frame Ψ r) (τ : Ψ) :
    mat (rmul (lact 1 y) (twoFr Ψ r)) τ = (2 : ℂ) • mat y τ := by
  show ((1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ) * ((2 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) = _
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  simp

theorem double_mem {X : Data E r} {y : Frame X.Ψ r} (hy : y ∈ X.dom) : rmul (lact 1 y) (twoFr X.Ψ r) ∈ X.dom := by
  intro τ
  refine ⟨by rw [mat_double, Matrix.det_smul]; exact mul_ne_zero (by simp) (hy τ).1, fun i => ?_⟩
  have hg : gram τ.1 X.Gm ((2 : ℂ) • mat y τ) = (4 : ℂ) • gram τ.1 X.Gm (mat y τ) := by
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
      map_ofNat]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have : dmin X.Gm (rmul (lact 1 y) (twoFr X.Ψ r)) τ i = (((4 : ℝ) ^ (i : ℕ) : ℝ) : ℂ) * dmin X.Gm y τ i := by
    rw [dmin, mat_double, hg, dmin, lminor, lminor, Matrix.submatrix_smul]
    simp [Matrix.det_smul]
  rw [this, Complex.re_ofReal_mul, mul_left_comm]
  exact mul_pos (by positivity) ((hy τ).2 i)

theorem flatSec_ne_const (hpq : 1 ≤ Dw.p + Dw.q) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {Z : Comp Xo c} {τ : Psi H}
    (s : FlatSec U x Z τ) (a : c.F) : s.sig ≠ a • idem Z := by
  intro hs
  let σ : c.F →+* ℂ := c.F.val.toRingHom
  have hI := hU _ (goodEmb_goodOf c σ)
  obtain ⟨⟨k, y⟩, hy⟩ := (s.hasPts.1 σ).1
  obtain ⟨hτ, b, hb, h⟩ := norm_rdU_sig hU s σ k
  have hd := double_mem hy.1
  have hy' : (⟨k, rmul (lact 1 y) (twoFr _ r)⟩ : Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) ∈
      framesOn (U (goodOf c σ)) Z := by
    obtain ⟨t, ht⟩ := (hI.2.2.2.1 k k ⟨y, hy.1⟩ ⟨_, hd⟩).2 ⟨1, one_mem _, twoFr _ r, fun τ' =>
      ⟨by
        show ((2 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).det ≠ 0
        simp,
       fun a c h => by simp [twoFr, Matrix.one_apply_ne h.ne']⟩, rfl⟩
    refine ⟨hd, fun p => ?_⟩
    have e : ptF ((U (goodOf c σ)).un k ⟨_, hd⟩) = ptF ((U (goodOf c σ)).un k ⟨y, hy.1⟩) := by
      simp only [ptF, ht.1]
    rw [e]; exact hy.2 p
  have hv : ∀ z ∈ framesOn (U (goodOf c σ)) Z, ‖rdU (U (goodOf c σ)) s.sig z.1 z.2‖ = ‖goodOf c σ a‖ := fun z hz => by
    rw [← homN_zero _ x, hs, homN_smul, homN_idem _ x hz.1 hz.2 ((s.hasPts.1 σ).2 z hz _), mul_one]
  have e := (h _ hy').symm.trans ((hv _ hy').trans ((hv _ hy).symm.trans (h _ hy)))
  have hx : ‖(mat y ⟨_, hτ⟩).det‖ ≠ 0 := norm_ne_zero_iff.2 (hy.1 _).1
  rw [mul_right_inj' hb.ne', horizGen, horizGen, mat_double, Matrix.det_smul, norm_inv, norm_inv, inv_inj, norm_mul,
    mul_left_eq_self₀] at e
  have e2 := e.resolve_right hx
  have hr : r ≠ 0 := by have := hI.1; omega
  simp only [Fintype.card_fin, norm_pow, Complex.norm_ofNat] at e2
  exact (one_lt_pow₀ one_lt_two hr).ne' e2

def rescale {Z : Comp Xo c} {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ) (x' : ℝ) :
    ConstSec U x' Z la δ :=
  { s with
    cInf := (fun _ => lieFacZ Dw x' (wtOf Dw la 0) / lieFacZ Dw x (wtOf Dw la 0)) * s.cInf
    cInf_pos := fun σ => mul_pos (div_pos (lieFacZ_pos _ _) (lieFacZ_pos _ _)) (s.cInf_pos σ)
    norm_inf := fun σ => image_eq_singleton_iff.2 ⟨(s.hasPts.1 σ).1, fun z hz => by
      have := (lieFacZ_pos (Dw := Dw) x (wtOf Dw la 0)).ne'
      rw [Pi.mul_apply, ← s.homN_eq hz, homN, homN]; field_simp⟩ }

theorem sum_flatWt (τ : Psi H) :
    ∑ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) = Dw.q - Dw.p := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have key : ∀ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) =
      (if ρ = conjEmb τ.1 then (Dw.q : ℝ) else 0) - if ρ = τ.1 then (Dw.p : ℝ) else 0 := fun ρ => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hm : Dw.mult ρ = Dw.p := by simp [Datum.mult, h]
      have h1 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = τ.1 then -1 else 0 :=
        fun i => by
          have := wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i (hm ▸ i.2)
          rw [this]
          simp [flatWt, parWt, Subtype.ext_iff]
      simp only [h2]
      split_ifs <;> simp_all
    · have hm : Dw.mult ρ = Dw.q := by simp [Datum.mult, h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = conjEmb τ.1 then 1 else 0 :=
        fun i => by
          have := wtOf_small (flatWt Dw τ) 0 ⟨_, conj_mem h⟩ i (hm ▸ i.2)
          simp only [conjEmb_conjEmb] at this
          rw [this]
          by_cases e : ρ = conjEmb τ.1
          · simp [flatWt, parWt, Subtype.ext_iff, e, conjEmb_conjEmb]
          · have : conjEmb ρ ≠ τ.1 := fun e' => e (by rw [← e', conjEmb_conjEmb])
            simp [flatWt, parWt, Subtype.ext_iff, e, this]
      simp only [h2]
      split_ifs <;> simp_all
  simp [key]

theorem deg_rescale {Z : Comp Xo c} {τ : Psi H} (s : FlatSec U x Z τ) (x' : ℝ) :
    (rescale s x').deg = s.deg - ((Dw.p : ℝ) - Dw.q) / 2 * (Real.log (2 * Real.pi * x') - Real.log (2 * Real.pi * x)) := by
  have h := lineDeg_mul (r := fun _ => lieFacZ Dw x' (wtOf Dw (flatWt Dw τ) 0) / lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0))
    (ρ := 0) (fun _ => div_pos (lieFacZ_pos _ _) (lieFacZ_pos _ _)) s.cInf_pos (by simp) s.finite_rho
  rw [zero_add] at h
  refine h.trans ?_
  have hK : (finrank ℚ c.F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  simp only [lineDeg, ConstSec.deg, lieFacZ, ← Real.exp_sub, Real.log_exp, sum_flatWt, Pi.zero_apply, zero_mul,
    finsum_zero, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
  field_simp
  ring

theorem flatExistsAt_rescale {a : ℝ} (h : FlatExistsAt U x a) (x' : ℝ) : FlatExistsAt U x'
    (a + ((Dw.p : ℝ) - Dw.q) / 2 * (Real.log (2 * Real.pi * x') - Real.log (2 * Real.pi * x))) := fun Z τ =>
  ⟨(h Z τ).1.map fun s => rescale s x', fun s => by
    have h1 := deg_rescale s x
    rw [(h Z τ).2] at h1
    linarith⟩

theorem flDefect_vp_cyclotomic (h2 : finrank ℚ E = 12) (hd : (discr E).natAbs = 3 ^ 6 * 7 ^ 10) (h7 : H.d = 7) :
    flDefect_vp Dw 3 = Dw.q / 2 ∧ flDefect_vp Dw 7 = -(Dw.q / 6) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have a3 : padicValNat 3 (3 ^ 6 * 7 ^ 10) = 6 := by
    rw [padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have a7 : padicValNat 7 (3 ^ 6 * 7 ^ 10) = 10 := by
    rw [padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  simp only [flDefect_vp, different_vp, h2, hd, h7, a3, a7]
  constructor <;> norm_num <;> ring

end GlobalTheory.FlatLine.Model
