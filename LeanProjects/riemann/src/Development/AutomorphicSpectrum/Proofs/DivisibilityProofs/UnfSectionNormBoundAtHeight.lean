import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Foundations.NotFlatExistsOfIsEmpty
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectors
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LeadMinorSmulOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.FlatNorm

open ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT Formalism.L2.LamCM
open scoped Matrix ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

theorem exists_test (f : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    ∃ (p : TRing c.F) (ψ : p.R →ₐ[c.F] S) (y₀ : FrPt Xo c p.R), FrMap ψ y₀ y ∧ evR Xo c f y = ψ (f p y₀) := by
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose, h.choose_spec.choose_spec.choose_spec, ?_⟩
  unfold evR evalAt
  rw [dif_pos h]

theorem exists_gram_det (hσ : GoodEmb c σ) (hU : IsUnf U) {k : U.Comp} (x : (U.X k).dom)
    (hx : (U.X k).IsOrtho x.1) (y : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ) (ht : FrBor t (U.un k x) y)
    (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n) (z : Sp ℂ ⟶ Xo.X) (hz : z = y.x)
    (v : Fin n → (GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ Xo.univ.t.G)) (hv : ∀ i, (v i).left = y.u τ (Fin.cast hn.symm i)) :
    ∃ Γ : Matrix (Fin n) (Fin n) ℂ, IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L z v Γ ∧
      ‖Γ.det‖ = (Real.pi * (2 * ‖relab c σ τ (U.X k).ξ0‖)) ^ n *
        (∏ i : Fin n, ‖toC (t (some ⟨τ, Fin.cast hn.symm i⟩) : CAt σ)‖) ^ 2 := by
  classical
  subst hn
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := PositivityTheory.UnitarySelfGeneration.GF.hm_diag hσ hU W Wu hx
  choose cf h1 h2 h3 using ht.2.1 τ
  let Y : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := fun j i => toC (cf i j)
  let Dv : Fin (Dw.mult τ) → Fin W.g → ℂ := fun i => ∑ j, Y j i • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)
  have hd : ∀ i, IsDerivAt0 (fun z => (W.F.ex (W.ik k) W.Pm z).left) (Dv i) (v i).left := fun i => by
    rw [hv]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm W.per _ ((U.un k x).u τ)
      (fun i => Pi.single (W.e.symm ⟨τ, i⟩) 1) (W.der τ) (fun j => Y j i) _).1 ?_
    have := h3 i
    rw [W.pt] at this
    exact this
  set κ : ℝ := Real.pi * (2 * ‖relab c σ τ (U.X k).ξ0‖) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  let Γ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := Matrix.of fun a b => Real.pi * hermForm Wu.Hm (Dv a) (Dv b)
  refine ⟨Γ, (hodgeGram_iff_period E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm Wu.Hm W.per Wu.herm Wu.c1 z
    (hz.trans (ht.1.trans W.pt)) _ v Dv Γ hd).2 fun a b => rfl, ?_⟩
  have hG : Γᵀ = Yᴴ * ((κ : ℂ) • (1 : Matrix _ _ ℂ)) * Y := by
    ext p q
    show (Real.pi : ℂ) * hermForm Wu.Hm (Dv q) (Dv p) = _
    rw [MetricChange.hermForm_sum]
    have hf : ∀ a b : Fin (Dw.mult τ), hermForm Wu.Hm (Pi.single (W.e.symm ⟨τ, a⟩) 1) (Pi.single (W.e.symm ⟨τ, b⟩) 1) =
        if a = b then ((2 * ‖relab c σ τ (U.X k).ξ0‖ : ℝ) : ℂ) else 0 := by
      intro a b
      rw [hH, hermForm, single_dotProduct, Matrix.mulVec_diagonal, _root_.one_mul, Equiv.apply_symm_apply, Pi.star_apply]
      split_ifs with hab
      · subst hab
        simp
      · rw [Pi.single_eq_of_ne (fun hh => hab (eq_of_heq (Sigma.mk.inj (W.e.symm.injective hh)).2))]
        simp
    simp only [hf, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      smul_eq_mul, Finset.mul_sum, hκ]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hdet : Y.det = ∏ i, toC (t (some ⟨τ, i⟩) : CAt σ) := by
    have hb : Y.BlockTriangular id := fun a b h => h2 b a h
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_congr rfl fun i _ => h1 i
  rw [← Matrix.det_transpose, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_smul,
    Matrix.det_one, hdet]
  simp only [Fintype.card_fin, _root_.mul_one, norm_mul, norm_star, norm_pow, Complex.norm_real, norm_prod, Fin.cast_eq_self,
    Real.norm_eq_abs, abs_of_nonneg hκ0]
  ring

theorem pnorm_flat (X : Data E r) (τ : X.Ψ) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    X.pnorm (GlobalTheory.FlatLine.modelFlat r τ) P y =
      ‖P y‖ * ∏ i : Fin r, Real.sqrt ‖dmin X.Gm y τ i.succ / dmin X.Gm y τ i.castSucc‖ := by
  classical
  unfold Data.pnorm
  congr 1
  rw [Fintype.prod_eq_single τ]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [GlobalTheory.FlatLine.modelFlat, Real.sqrt_eq_rpow]
  · intro τ' h
    simp [GlobalTheory.FlatLine.modelFlat, h]

theorem prod_split {p q r : ℕ} (hr : r = p + q) (f : Fin r → ℝ) :
    ∏ a, f a = (∏ i : Fin p, f ⟨q + i, by omega⟩) * ∏ j : Fin q, f ⟨q - 1 - j, by omega⟩ := by
  subst hr
  have e : ∏ a, f a = ∏ a : Fin (q + p), f (Fin.cast (by omega) a) :=
    (Fintype.prod_equiv (finCongr (by omega)) _ _ fun a => by simp).symm
  rw [e, Fin.prod_univ_add, mul_comm]
  congr 1
  rw [← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ext
  simp [Fin.val_rev]
  omega

end GlobalTheory.CompanionTheory.Ar.Br.FlatNorm

namespace GlobalTheory.CompanionTheory.Ar.Br

open GlobalTheory.CompanionTheory.Ar.Br.FlatNorm ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj in

theorem homN_eq_exp_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ) (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (t : ℝ), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf U → (∀ k (τ' : E →+* ℂ), ‖τ' (U.X k).ξ0‖ = x) → s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) → IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ t → ∀ z ∈ GlobalTheory.AllWt.framesOn U Z, (∀ hz : z.2 ∈ (U.X z.1).dom, GlobalTheory.FlatLine.Tested (U.un z.1 ⟨z.2, hz⟩)) → GlobalTheory.AllWt.homN U x (GlobalTheory.AllWt.wtOf D (GlobalTheory.FlatLine.flatWt D τ) 0) s z = Real.exp t := by
  intro E _ _ _ H D l Xo c r σ U x Z τ s φ t hσ hU hx hs hline hread hinf z hz htest
  classical
  obtain ⟨k, y⟩ := z
  obtain ⟨hy, hlies⟩ := hz
  have ht := htest hy
  dsimp only at hy hlies ht
  obtain ⟨p, ψ, z₀, hmap, hval⟩ := exists_test s (U.un k ⟨y, hy⟩) ht
  have hp : D.mult τ.1 = D.p := by simp [Datum.mult, τ.2]
  have hq : D.mult (ComplexEmbedding.conjugate τ.1) = D.q := by
    have h := GlobalTheory.AllWt.conj_not_mem τ
    have h' : ¬ (ComplexEmbedding.conjugate τ.1) (H.rt : E) = H.rt0 := h
    unfold Datum.mult
    rw [if_neg h']
  let ψ' : p.R →+* ℂ := (ψ : p.R →+* CAt σ)
  let yF : Sp ℂ ⟶ Xo.XF c := GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k ⟨y, hy⟩)
  have hβ : ψ'.comp (algebraMap c.F p.R) = σ := RingHom.ext fun a => ψ.commutes a
  have hu : under yF = spMap ψ' ≫ z₀.x := by
    show GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k ⟨y, hy⟩) ≫ pullback.fst _ _ = _
    rw [GlobalTheory.AllWt.ptF, pullback.lift_fst]
    exact hmap.1
  have hsn : yF ≫ pullback.snd _ _ = spMap (ψ'.comp (algebraMap c.F p.R)) := by
    show GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k ⟨y, hy⟩) ≫ pullback.snd _ _ = _
    rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, hβ]
    rfl
  have hrange : Set.range yF ⊆ (Z : Set (Xo.XF c)) := by
    rintro _ ⟨s', rfl⟩
    exact hlies s'
  obtain ⟨v, w, hv, hw, hfr⟩ := GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt E H D l Xo c τ.1 p.R z₀ ℂ ψ' yF hp hq hu hsn
  have hfZ := hfr _ hrange
  have hread' := hread p z₀ ℂ ψ' yF hu hsn hrange v w hp hq hv hw
  rw [hβ] at hfZ
  obtain ⟨x₀, tt, ho, hb, hnorm⟩ := PositivityTheory.UnitarySelfGeneration.GF.move hσ hU ⟨y, hy⟩
  have hz' : under yF = (U.un k ⟨y, hy⟩).x := by
    rw [hu]; exact hmap.1.symm
  have hv' : ∀ i, (v i).left = (U.un k ⟨y, hy⟩).u τ.1 (Fin.cast hp.symm i) := fun i => by
    rw [hv i]; exact (hmap.2.1 _ _).symm
  have hw' : ∀ j, (w j).left = (U.un k ⟨y, hy⟩).u (ComplexEmbedding.conjugate τ.1) (Fin.cast hq.symm j) := fun j => by
    rw [hw j]; exact (hmap.2.1 _ _).symm
  obtain ⟨Γ, hΓ, dΓ⟩ := exists_gram_det hσ hU x₀ ho _ tt hb τ.1 D.p hp (under yF) hz' v hv'
  obtain ⟨Δ, hΔ, dΔ⟩ := exists_gram_det hσ hU x₀ ho _ tt hb (ComplexEmbedding.conjugate τ.1) D.q hq (under yF) hz' w hw'
  have hI := hinf yF v w Γ Δ hfZ hΓ hΔ
  have hφ : φ ℂ yF v w ≠ 0 := hline.ne ℂ σ yF v w hfZ
  obtain ⟨-, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  have hτ : relab c σ τ.1 ∈ (U.X k).Ψ := (hty _).2 ((hrt τ.1).2 τ.2)
  have hx1 : ‖relab c σ τ.1 (U.X k).ξ0‖ = x := hx k _
  have hx2 : ‖relab c σ (ComplexEmbedding.conjugate τ.1) (U.X k).ξ0‖ = x := hx k _
  have hx0 : 0 < x := hx1 ▸ norm_pos_iff.2 ((map_ne_zero _).2 (U.X k).ξ0_ne)
  rw [hx1] at dΓ
  rw [hx2] at dΔ
  set A : ℝ := ∏ i : Fin D.p, ‖toC (tt (some ⟨τ.1, Fin.cast hp.symm i⟩) : CAt σ)‖ with hA
  set B : ℝ := ∏ j : Fin D.q, ‖toC (tt (some ⟨ComplexEmbedding.conjugate τ.1, Fin.cast hq.symm j⟩) : CAt σ)‖ with hB
  have hA0 : 0 < A := Finset.prod_pos fun i _ => norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) (tt _))
  have hB0 : 0 < B := Finset.prod_pos fun i _ => norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) (tt _))
  have hprod : ∏ a : Fin r, Real.sqrt ‖dmin (U.X k).Gm y ⟨_, hτ⟩ a.succ / dmin (U.X k).Gm y ⟨_, hτ⟩ a.castSucc‖ =
      A * B⁻¹ := by
    rw [prod_split (p := D.p) (q := D.q) hU.1, hA, hB, ← Finset.prod_inv_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have h := (hnorm ⟨τ.1, Fin.cast hp.symm i⟩ ⟨_, hτ⟩ ⟨D.q + i, by have := hU.1; omega⟩).1 rfl
        (by show D.q + (i : ℕ) = (U.X k).p0 + (i : ℕ); rw [hp0])
      rw [← h, Real.sqrt_sq (norm_nonneg _)]
    · refine Finset.prod_congr rfl fun j _ => ?_
      have hj := j.2
      have h := (hnorm ⟨ComplexEmbedding.conjugate τ.1, Fin.cast hq.symm j⟩ ⟨_, hτ⟩
        ⟨D.q - 1 - j, by have := hU.1; omega⟩).2 (GlobalTheory.AllWt.relab_conj σ τ.1).symm
        (by show D.q - 1 - (j : ℕ) + (j : ℕ) + 1 = (U.X k).p0; rw [hp0]; omega)
      rw [← inv_eq_iff_eq_inv.2 h, Real.sqrt_inv, Real.sqrt_sq (norm_nonneg _)]
  have hrd : rdU U s k y = φ ℂ yF v w := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hy, dif_pos]
    rw [hval]
    exact hread'
  have hL : GlobalTheory.AllWt.lieFacZ D x (GlobalTheory.AllWt.wtOf D (GlobalTheory.FlatLine.flatWt D τ) 0) =
      Real.exp (-(((D.q : ℝ) - D.p) / 2) * Real.log (2 * Real.pi * x)) := by
    rw [GlobalTheory.AllWt.lieFacZ, GlobalTheory.FlatLine.Model.sum_flatWt]
  rw [GlobalTheory.AllWt.homN, GlobalTheory.AllWt.ptN]
  dsimp only
  rw [GlobalTheory.FlatLine.modelWt_flatWt U hσ hU τ k hτ, pnorm_flat, hrd, hprod, hL, ← hI, dΓ, dΔ]
  have hκ : Real.pi * (2 * x) = 2 * Real.pi * x := by ring
  have hκ0 : 0 < 2 * Real.pi * x := by positivity
  have hP : 0 < ‖φ ℂ yF v w‖ := norm_pos_iff.2 hφ
  rw [hκ, Real.log_mul (pow_pos hκ0 _).ne' (pow_pos hA0 _).ne', Real.log_mul (pow_pos hκ0 _).ne' (pow_pos hB0 _).ne',
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  conv_lhs => rw [← Real.exp_log hP, ← Real.exp_log hA0, ← Real.exp_log (inv_pos.2 hB0), Real.log_inv]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Br
