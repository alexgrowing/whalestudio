import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcNilpotent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermFormSumSmul

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix

namespace GlobalTheory.ArcLieBound

theorem inv_form_le {g : ℕ} {Y₀ Y G₀ G : Matrix (Fin g) (Fin g) ℝ} (h₀ : Y₀.PosDef) (hG₀ : G₀ * Y₀ = 1)
    (hG : G * Y = 1) (hle : ∀ x, x ⬝ᵥ Y₀ *ᵥ x ≤ x ⬝ᵥ Y *ᵥ x) (a : Fin g → ℝ) : a ⬝ᵥ G *ᵥ a ≤ a ⬝ᵥ G₀ *ᵥ a := by
  have e : Y *ᵥ (G *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hG, Matrix.one_mulVec]
  have e₀ : Y₀ *ᵥ (G₀ *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hG₀, Matrix.one_mulVec]
  set x := G *ᵥ a
  set x₀ := G₀ *ᵥ a
  have hs : Y₀ᵀ = Y₀ := by simpa using h₀.1.eq
  have h1 := h₀.posSemidef.dotProduct_mulVec_nonneg (x₀ - x)
  have h2 : x₀ ⬝ᵥ Y₀ *ᵥ x = x ⬝ᵥ a := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, e₀, dotProduct_comm]
  have h3 := hle x
  rw [e] at h3
  rw [star_trivial, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, h2, e₀] at h1
  rw [dotProduct_comm a, dotProduct_comm a]
  linarith

theorem re_hermForm_sum {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (p : Fin g → Fin g → ℂ)
    (h1 : ∀ k l, (hermForm Hm (p k) (p l)).im = 0) (u : Fin g → ℂ) :
    (hermForm Hm (∑ j, u j • p j) (∑ j, u j • p j)).re =
      (fun j => (u j).re) ⬝ᵥ (Matrix.of fun k l => (hermForm Hm (p k) (p l)).re) *ᵥ (fun j => (u j).re) +
      (fun j => (u j).im) ⬝ᵥ (Matrix.of fun k l => (hermForm Hm (p k) (p l)).re) *ᵥ (fun j => (u j).im) := by
  have e : ∀ z, hermForm Hm (∑ j, u j • p j) z = ∑ j, u j * hermForm Hm (p j) z := fun z => by
    simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [e, Complex.re_sum, dotProduct, dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LatticeCovolumeL2.hermForm_sum_smul]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, h1, Complex.conj_re, Complex.conj_im]
  ring

theorem eq_sum {g : ℕ} (h : Matrix (Fin g) (Fin g) ℂ) (p : Fin g → Fin g → ℂ)
    (hp : ∀ k, h *ᵥ (p k) = Pi.single k 1) (v : Fin g → ℂ) : v = ∑ j, (h *ᵥ v) j • p j := by
  have hs : Function.Surjective (Matrix.toLin' h) := fun v =>
    ⟨∑ j, v j • p j, by
      simp only [Matrix.toLin'_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hp]
      ext i
      simp [Pi.single_apply]⟩
  apply LinearMap.injective_iff_surjective.2 hs
  simp only [Matrix.toLin'_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hp]
  ext i
  simp [Pi.single_apply]

theorem diag_le {g : ℕ} (d : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z, z ≠ 0 → 0 < (hermForm (Matrix.diagonal fun j => (d j : ℂ)) (M *ᵥ z) (M *ᵥ z)).re)
    (z : Fin g → ℂ) (a : Fin g) :
    0 < d a ∧ d a * ‖(M *ᵥ z) a‖ ^ 2 ≤ (hermForm (Matrix.diagonal fun j => (d j : ℂ)) (M *ᵥ z) (M *ᵥ z)).re := by
  have e : ∀ v : Fin g → ℂ, (hermForm (Matrix.diagonal fun j => (d j : ℂ)) v v).re = ∑ j, d j * ‖v j‖ ^ 2 := by
    intro v
    rw [hermForm, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def, mul_left_comm, Complex.mul_conj,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hinj : Function.Injective (Matrix.toLin' M) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra h0
    have := hpos v h0
    rw [Matrix.toLin'_apply] at hv
    simp [hv, hermForm] at this
  have hd : ∀ j, 0 < d j := fun j => by
    obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj (Pi.single j 1)
    rw [Matrix.toLin'_apply] at hv
    have := hpos v (by
      rintro rfl
      simpa using congrFun hv j)
    rw [hv, e, Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      simp [hb]
    · simp
  refine ⟨hd a, ?_⟩
  rw [e]
  exact Finset.single_le_sum (f := fun j => d j * ‖(M *ᵥ z) j‖ ^ 2)
    (fun k _ => mul_nonneg (hd k).le (sq_nonneg _)) (Finset.mem_univ a)

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} [Algebra (FractionRing ℂ) ℂ]
  [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {a : ArcIn Dw l β ℂ (σ.comp β)}
  {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty} {Ha : HolArc Y σ a χ W Fu}
  {th : a.D₀.P.L.Sec} (Θ : ThetaDat Ha th)

theorem exists_im_tau : ∃ A N : Matrix (Fin g) (Fin g) ℝ, ∀ w : ℂ, (Θ.τ w).map Complex.im = A + w.im • N := by
  obtain ⟨nn, h1, h2, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  have hreal : ∀ v j, ((Θ.h *ᵥ Ha.N v) j).im = 0 := by
    intro v j
    obtain ⟨u, hu⟩ := Θ.bas.surjective (nn v)
    have hu0 := ((Θ.orth u).1 fun v' hv' => by
      have := h2 v v'
      rwa [hv', map_zero, neg_eq_zero, ← hu] at this).1
    have hs : u = ∑ k, u (.inl k) • Pi.single (.inl k) 1 := by
      ext (i | i)
      · simp [Pi.single_apply]
      · simp [hu0]
    have hp : ∀ k, Θ.h *ᵥ Ha.P₀ (Θ.bas (Pi.single (.inl k) 1)) = Pi.single k 1 := fun k => by
      have := (Θ.per 0 k).1
      rwa [Ha.Pw_eq, zero_smul, add_zero] at this
    rw [h1, ← hu, hs]
    simp only [map_sum, map_zsmul, Matrix.mulVec_sum, Matrix.mulVec_smul, hp]
    simp [Pi.single_apply]
  refine ⟨Matrix.of fun j k => ((Θ.h *ᵥ Ha.P₀ (Θ.bas (Pi.single (.inr k) 1))) j).im,
    Matrix.of fun j k => ((Θ.h *ᵥ Ha.N (Θ.bas (Pi.single (.inr k) 1))) j).re, fun w => ?_⟩
  ext j k
  have := congrFun (Θ.per w k).2 j
  rw [Ha.Pw_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [show Θ.τ w j k = _ from this.symm]
  simp [hreal]

theorem im_tau_mono {w₀ w : ℂ} (hw : w₀.im ≤ w.im) (x : Fin g → ℝ) :
    x ⬝ᵥ (Θ.τ w₀).map Complex.im *ᵥ x ≤ x ⬝ᵥ (Θ.τ w).map Complex.im *ᵥ x := by
  obtain ⟨A, N, h⟩ := exists_im_tau Θ
  have e : ∀ w : ℂ, x ⬝ᵥ (Θ.τ w).map Complex.im *ᵥ x = x ⬝ᵥ A *ᵥ x + w.im * x ⬝ᵥ N *ᵥ x := fun w => by
    rw [h, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hN : 0 ≤ x ⬝ᵥ N *ᵥ x := by
    by_contra hn
    have hn' : 0 < -(x ⬝ᵥ N *ᵥ x) := by linarith
    set s : ℝ := max (Ha.T + 1) ((x ⬝ᵥ A *ᵥ x + 1) / -(x ⬝ᵥ N *ᵥ x))
    have h1 := (Θ.pos (s * Complex.I) (by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
        add_zero]
      exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _))).2.posSemidef.dotProduct_mulVec_nonneg x
    rw [star_trivial, e] at h1
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
      add_zero] at h1
    have h2 : x ⬝ᵥ A *ᵥ x + 1 ≤ s * -(x ⬝ᵥ N *ᵥ x) := (div_le_iff₀ hn').1 (le_max_right _ _)
    linarith
  rw [e, e]
  have := mul_le_mul_of_nonneg_right hw hN
  linarith

omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem exists_riem_inv {w : ℂ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hR : IsRiem Fu Ha.i (Ha.Pw w) Hm) :
    ∃ G : Matrix (Fin g) (Fin g) ℝ, G * (Θ.τ w).map Complex.im = 1 ∧ ∀ v, (hermForm Hm v v).re =
      (fun j => ((Θ.h *ᵥ v) j).re) ⬝ᵥ G *ᵥ (fun j => ((Θ.h *ᵥ v) j).re) +
      (fun j => ((Θ.h *ᵥ v) j).im) ⬝ᵥ G *ᵥ (fun j => ((Θ.h *ᵥ v) j).im) := by
  let p : Fin g → Fin g → ℂ := fun j => Ha.Pw w (Θ.bas (Pi.single (.inl j) 1))
  let q : Fin g → Fin g → ℂ := fun j => Ha.Pw w (Θ.bas (Pi.single (.inr j) 1))
  have h1 : ∀ i j, (hermForm Hm (p i) (p j)).im = 0 := fun i j => by simp [p, hR.2.2, Θ.sympl, omegaStd]
  refine ⟨_, LatticeCovolumeL2.riem_inv Hm (Θ.τ w) p q
    (LatticeCovolumeL2.cols Θ.h (Θ.τ w) _ _ (fun i => (Θ.per w i).1) (fun i => (Θ.per w i).2)) h1 (fun i j => by
      simp only [p, q, hR.2.2, Θ.sympl, omegaStd]
      by_cases hij : i = j <;> simp [Pi.single_apply, hij, eq_comm]), fun v => ?_⟩
  rw [← re_hermForm_sum Hm p h1, ← eq_sum Θ.h p (fun i => (Θ.per w i).1)]

include Θ in

theorem riem_anti {w₀ w : ℂ} (h₀ : Ha.T < w₀.im) (hw : w₀.im ≤ w.im) {H₀ Hm : Matrix (Fin g) (Fin g) ℂ}
    (hR₀ : IsRiem Fu Ha.i (Ha.Pw w₀) H₀) (hR : IsRiem Fu Ha.i (Ha.Pw w) Hm) (v : Fin g → ℂ) :
    (hermForm Hm v v).re ≤ (hermForm H₀ v v).re := by
  obtain ⟨G₀, a₀, b₀⟩ := exists_riem_inv Θ hR₀
  obtain ⟨G, a₁, b₁⟩ := exists_riem_inv Θ hR
  rw [b₀, b₁]
  exact add_le_add (inv_form_le (Θ.pos w₀ h₀).2 a₀ a₁ (im_tau_mono Θ hw) _)
    (inv_form_le (Θ.pos w₀ h₀).2 a₀ a₁ (im_tau_mono Θ hw) _)

end ThetaShiftProofs

open GlobalTheory.FrameNormLie GlobalTheory.FrameNorm in
set_option maxHeartbeats 1000000 in

theorem point_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}
    {U : Formalism.L2.PjFree.Unf Xo c σ r} (Uw : UnfWit U) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (x : (U.X k).dom) (hx : IsUnitFr (U.X k) x.1) (i₀ : Fin Uw.F.n)
    (P' : (Uw.F.Di i₀).La →+ (Fin Uw.g → ℂ))
    (p' : IsPeriod (Uw.F.Di i₀) (fun j => Formalism.L2.PjFree.relab c σ (Uw.e j).1) P') (y : FrPt Xo c (CAt σ))
    (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (hy : AnLie Uw.F i₀ P' y z) (t : Ix Dw → (CAt σ)ˣ)
    (hB : FrBor t (U.un k x) y) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ) (hR : IsRiem Uw.F i₀ P' Hm)
    (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    ∃ ρ : E →+* ℂ, 0 < 2 * (ρ (-(U.X k).ξ0)).im ∧
      2 * (ρ (-(U.X k).ξ0)).im * ‖Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ)‖ ^ 2 ≤
        (hermForm Hm (z τ i) (z τ i)).re := by
  classical
  obtain ⟨g, e, F, ik, φ, hEF, Pm, hPm, hper0, hlie, hnorm⟩ := Uw
  dsimp only at *
  have hr := hU.1
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  have hP := hPm k x
  have p := hper0 k x
  obtain ⟨hPx, hv⟩ := hlie k x
  set P := Pm k x
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hr
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (U.X k).Ψ × Fin r, ∀ j,
      (Formalism.L2.PjFree.relab c σ (e j).1 ∈ (U.X k).Ψ ∧ (idx j).1.1 = Formalism.L2.PjFree.relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (Formalism.L2.PjFree.relab c σ (e j).1 ∉ (U.X k).Ψ ∧
        (idx j).1.1 = ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  have hper : ∀ (x : Frame (U.X k).Ψ r) v j, Formalism.L2.PjFree.perFr (U.X k) x v (Formalism.L2.PjFree.relab c σ (e j).1)
      (e j).2 = perVec (U.X k) idx x v j := by
    intro x v j
    unfold perVec
    have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold Formalism.L2.PjFree.perFr
      rw [dif_neg a, dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ b ∈ Bor (U.X k).Ψ r, Supp (fun j => (e j).1) (fun j => ((e j).2 : ℕ))
      (PerBor.moveMat (U.X k).p0 idx b) := by
    intro b hb j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · rw [if_neg (by omega)] at h2
      exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by simp only; omega⟩
    · rw [if_neg (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      exact ⟨hbij.1 (by rw [← hcc (Formalism.L2.PjFree.relab c σ (e j).1), ← b1, ← h1, b2, hcc]), by simp only; omega⟩
  obtain ⟨T, hT, hT1, hTf⟩ := exists_tri_unit (U.X k) idx hinj hs x.1 x.2 hx
  have hPv : ∀ a, P a = perVec (U.X k) idx x.1 (φ k a : Fin r → E) := fun a => funext fun j =>
    (hP a j).trans (hper _ _ _)
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ g _ F i₀ (ik k) P' P p' p
    (by rw [← hPx, ← hy.1, hB.1])
  set A := LinearMap.toMatrix' h.toLinearMap with hAdef
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hAdef, LinearMap.toMatrix'_mulVec]; rfl
  obtain ⟨cf, hcf1, hcf2, hcf3⟩ := hB.2.1 τ i
  have hcol : A *ᵥ z τ i = (∑ j, (show ℂ from cf j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k x).u τ) _ (hv τ) cf
      (y.u τ i)).1 (hPx ▸ hcf3)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F _ P' p' _ P h.toLinearMap p hex _ _).1 (hy.2 τ i)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ p'.2.2.2.1
    ((T * A)ᵀ * (Matrix.diagonal (diagXi (U.X k) idx) * (T * A).map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [← UnitDet.hermForm_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hAv, hAv, ← hh, ← hh, hPv, hPv, hTf, ← hEF, hiso, hR.2.2]
      simp)
  have hval : ((T * A) *ᵥ z τ i) (e.symm ⟨τ, i⟩) =
      T (e.symm ⟨τ, i⟩) (e.symm ⟨τ, i⟩) * Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ) := by
    rw [← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [Matrix.mulVec_smul, Matrix.mulVec_single_one, hcf1, mul_comm]
      rfl
    · intro j _ hj
      rw [Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul, mul_eq_zero]
      rcases lt_or_gt_of_ne hj with hlt | hlt
      · right
        by_contra hne
        have := (hT _ _ hne).2
        beta_reduce at this
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
        exact absurd hlt (not_lt.2 this)
      · exact Or.inl (hcf2 j hlt)
    · simp
  obtain ⟨h1, h2⟩ := diag_le (fun j => 2 * ((idx j).1.1 (-(U.X k).ξ0)).im) (T * A) (fun v hv => by
    rw [UnitDet.hermForm_mulVec]
    exact lt_of_lt_of_eq (hR.2.1 v hv) (by rw [← key]; rfl)) (z τ i) (e.symm ⟨τ, i⟩)
  rw [hval, norm_mul, hT1, one_mul, UnitDet.hermForm_mulVec] at h2
  exact ⟨_, h1, h2.trans (le_of_eq (by rw [← key]; rfl))⟩

theorem norm_diag_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ∀ j, ‖Formalism.L2.PjFree.toC (t (some j) : CAt σ)‖ ≤ B := by
  intro E _ _ _ H Dw l Xo c r σ U Uw _ _ O _ β Y a χ W Ha th Θ z hσ hU _
  set w₀ : ℂ := ((Ha.T + 1 : ℝ) : ℂ) * Complex.I with hw₀
  have e₀ : w₀.im = Ha.T + 1 := by simp [hw₀]
  have h₀ : Ha.T < w₀.im := by rw [e₀]; exact lt_add_one _
  obtain ⟨H₀, hR₀⟩ := (Ha.period w₀ h₀).2.2.2.2
  obtain ⟨B, hB⟩ := (Set.finite_range fun s : U.Comp × (E →+* ℂ) × (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
    (hermForm H₀ (z s.2.2.1 s.2.2.2) (z s.2.2.1 s.2.2.2)).re / (2 * (s.2.1 (-(U.X s.1).ξ0)).im)).bddAbove
  refine ⟨Ha.T + 1, Real.sqrt B, fun w hw yw hy k x t hx hb j => ?_⟩
  have hw' : Ha.T < w.im := by linarith
  obtain ⟨Hm, hR⟩ := (Ha.period w hw').2.2.2.2
  obtain ⟨τ, i⟩ := j
  obtain ⟨ρ, h1, h2⟩ := point_bound Uw hσ hU k x hx Ha.i _ (Ha.period w hw') yw z hy.1 t hb Hm hR τ i
  refine Real.le_sqrt_of_sq_le (le_trans ?_ (hB ⟨(k, ρ, ⟨τ, i⟩), rfl⟩))
  rw [le_div_iff₀' h1]
  exact h2.trans (riem_anti Θ h₀ (by rw [e₀]; exact hw.le) hR₀ hR _)

end GlobalTheory.ArcLieBound
