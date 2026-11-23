import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSection

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

open GlobalTheory.Dict.Extend GlobalTheory.Dict.Pull

namespace GlobalTheory.LargeCover

section Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def PrincUpTo (X : Data E r) (M : ℕ) (la : Wt X.Ψ r) : Prop :=
  ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
    (∀ v ∈ X.Λ, ∃ u ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • u) →
      ∃ gb ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, bchar la b = 1 ∧ ∀ x, lact gb x = lact ga (rmul x b)

theorem conj_stab {X X' : Data E r} (hG : X'.Gm = X.Gm) {a g : GL (Fin r) E} {M : ℕ} (ha : IsUn X a) (hg : IsUn X g)
    (hfix : mapL g (mapL a X'.Λ) = mapL a X'.Λ)
    (hM : ∀ u ∈ mapL a X'.Λ, ∃ u' ∈ mapL a X'.Λ, (g : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') :
    IsUStab X'.Gm X'.Λ (a⁻¹ * g * a) ∧
      ∀ v ∈ X'.Λ, ∃ u ∈ X'.Λ, ((a⁻¹ * g * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • u := by
  have hc : mapL (a⁻¹ * g * a) X'.Λ = X'.Λ := by
    rw [mapL_mul, mapL_mul, hfix, ← mapL_mul, inv_mul_cancel, mapL_one]
  refine ⟨⟨?_, fun x => ?_⟩, fun v hv => ?_⟩
  · rw [hG]
    exact isUn_mul (isUn_mul (isUn_inv ha) hg) ha
  · rw [← mem_mapL (a := a⁻¹ * g * a), hc]
  · obtain ⟨u', ⟨w, hw, e⟩, hu⟩ := hM _ (mem_mapL.2 hv)
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = u' := e
    refine ⟨w, hw, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, ← e',
      Matrix.mulVec_add, Matrix.mulVec_smul, inv_mulVec, inv_mulVec]

theorem exists_pow_root_eq_one (K : Type) [Field K] [NumberField K] :
    ∃ w : ℕ, 0 < w ∧ ∀ (u : K) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1 := by
  refine ⟨NumberField.Units.torsionOrder K, NumberField.Units.torsionOrder_pos K, fun u n hn hu => ?_⟩
  have hi : IsIntegral ℤ u := IsIntegral.of_pow hn (hu ▸ isIntegral_one)
  have h1 : (⟨u, hi⟩ : 𝓞 K) ^ n = 1 := Subtype.ext hu
  let v : (𝓞 K)ˣ := Units.ofPowEqOne _ n h1 hn.ne'
  have hv : v ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Units.pow_ofPowEqOne h1 hn.ne'⟩)
  have h2 : (⟨v, hv⟩ : NumberField.Units.torsion K) ^ NumberField.Units.torsionOrder K = 1 := by
    unfold NumberField.Units.torsionOrder
    first | exact pow_card_eq_one | exact pow_card_eq_one'
  have h3 : v ^ NumberField.Units.torsionOrder K = 1 := congrArg Subtype.val h2
  exact congrArg (fun x : (𝓞 K)ˣ => ((x : 𝓞 K) : K)) h3

theorem princUpTo_of_root (X : Data E r) (M w : ℕ) (hw : ∀ (u : E) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1)
    (la : Wt X.Ψ r) (hla : ∀ τ i, (w : ℤ) ∣ la τ i)
    (h : ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
      (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (M : E) • y) →
      ∃ gb ∈ X.Γ, ∃ (u : E) (n : ℕ), 0 < n ∧ u ^ n = 1 ∧
        (gb : Matrix (Fin r) (Fin r) E) = u • (ga : Matrix (Fin r) (Fin r) E)) : PrincUpTo X M la := by
  intro ga hga hc
  obtain ⟨gb, hgb, u, n, hn, hu, he⟩ := h ga hga fun x hx => by
    obtain ⟨y, hy, e⟩ := hc x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hu; exact zero_ne_one hu
  let b : Frame X.Ψ r := fun τ => (Matrix.diagonal fun _ => τ.1 u : Matrix (Fin r) (Fin r) ℂ)
  have hb : ∀ τ, mat b τ = τ.1 u • (1 : Matrix (Fin r) (Fin r) ℂ) := fun τ => by
    rw [Matrix.smul_one_eq_diagonal]; rfl
  refine ⟨gb, hgb, b, fun τ => ⟨?_, fun a c hac => Matrix.diagonal_apply_ne _ hac.ne'⟩, ?_, fun x => ?_⟩
  · rw [hb, Matrix.det_smul, Matrix.det_one, _root_.mul_one]
    exact pow_ne_zero _ ((map_ne_zero τ.1).2 hu0)
  · refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
    obtain ⟨k, hk⟩ := hla τ i
    have : b τ i i = τ.1 u := Matrix.diagonal_apply_eq _ i
    rw [this, hk, _root_.zpow_mul, zpow_natCast, ← map_pow, hw u n hn hu, map_one, _root_.one_zpow]
  · funext τ
    show (gb : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
      (ga : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)
    have : (u • (ga : Matrix (Fin r) (Fin r) E)).map τ.1 = τ.1 u • (ga : Matrix (Fin r) (Fin r) E).map τ.1 := by
      ext a c; simp
    rw [he, this, hb, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]

end Pull

theorem isStabForm_pull_upto (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ) (hga : IsUn X ga) (hl : ∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) (hΔ : ∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) (hP : PrincUpTo X' M la') (hχ : ChiOne X' la') (hb : X'.IsBddSec la' P) : IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x := by
  obtain ⟨⟨hd, hbor, hinv⟩, C, hC⟩ := hb
  have m1 : ∀ x ∈ X.dom, castFr h.psi.symm (lact ga⁻¹ x) ∈ X'.dom := fun x hx =>
    cast_GG h.psi.symm h.gm.symm h.p0.symm (lact_mem (isUn_inv hga) hx)
  have m2 : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    lact_mem hga (cast_GG h.psi h.gm h.p0 hx)
  refine ⟨⟨?_, ?_, ?_, C, ?_⟩, fun x hx => ⟨m2 x hx, ?_⟩⟩
  · exact hd.comp ((cast_diff h.psi.symm).comp (differentiable_lact ga⁻¹)).differentiableOn m1
  · intro x hx b hb
    rw [lact_rmul, cast_rmul, hbor _ (m1 x hx) _ (cast_bor h.psi.symm hb), ← cast_bchar h.psi hl]
    rfl
  · intro g hg hfix x hx
    obtain ⟨s1, s2⟩ := conj_stab h.gm hga (hΔ g hg).1 hfix ((hΔ g hg).2 hfix)
    obtain ⟨gb, hgb, b, hb, hb1, hgbb⟩ := hP _ s1 s2
    have e : lact ga⁻¹ (lact g x) = lact (ga⁻¹ * g * ga) (lact ga⁻¹ x) := by
      rw [lact_lact, lact_lact, mul_inv_cancel_right]
    show P (castFr h.psi.symm (lact ga⁻¹ (lact g x))) = _
    have e2 := hinv _ hgb _ (m1 x hx)
    rw [hχ _ hgb, _root_.one_mul, hgbb, lact_rmul, hbor _ (lact_mem s1.1 (m1 x hx)) _ hb, hb1, _root_.one_mul] at e2
    rw [e, cast_lact, e2]
  · intro x hx
    refine le_of_eq_of_le ?_ (hC _ (m1 x hx))
    unfold Data.pnorm
    rw [cast_wt h.psi h.gm hl]
    simp only [dmin_lact (isUn_inv hga)]
  · rw [lact_lact, inv_mul_cancel, lact_one, cast_symm]

set_option maxHeartbeats 800000 in

theorem holSub0_le_span_shortGen_upto : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, PrincUpTo (U.X k) l.M (Formalism.L2.PjFree.laU U a n k)) → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → holSub0 U.X (Formalism.L2.PjFree.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  intro hci E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hA hG hlev hnab huc h3 hpin nab bad nV a hbad hdom hbig
    hpr hchi htot P hP
  obtain ⟨hP1, hP0⟩ := hP
  rcases isEmpty_or_nonempty U.Comp with hemp | ⟨⟨k₀⟩⟩
  · have : P = 0 := funext fun k => (hemp.false k).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨W⟩ := nonempty_uw hU
  have hrpq : r = Dw.p + Dw.q := hU.1
  have hn : r ≤ n := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    nlinarith
  have hev : Even n := by
    unfold Formalism.L2.Pj.Dom at hdom
    tauto
  have huw := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k k₀).1,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k k₀).2, by rw [(huw k).1, (huw k₀).1, (hG k k₀).2]⟩
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin (hrpq ▸ hn)
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.T.exists_letterRowWeightDictionary E H Dw l c σ r W.g n (U.X k₀) a W.e hσ hrpq (hU.2.1 k₀).1 (hU.2.1 k₀).2
    (huw k₀).2.1 hdom
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_classicalLevelData_coverSelfDual E H Dw l Xo c n d σ r (U.X k₀) hn hrpq (huw k₀).2.1 hlev h3 ph ψ x₀ hph
  obtain ⟨v₀, mu, hv₀, hmu⟩ := GlobalTheory.SW.exists_vacua_and_multipliers E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D
  obtain ⟨x0, ga, δ, hadm, hset, hsep⟩ := GlobalTheory.T.exists_components_lattices_moved_to_level_family E H Dw l Xo c n d σ r U hσ hU hr1 hA hlev W k₀ hsame ph D hn hD
  obtain ⟨u, hu, hread⟩ := GlobalTheory.T.short_series_readings_eq_classical_thetaSeries hci E H Dw l Xo c n d σ r U hσ hU hr1 hlev hnab huc ph ψ x₀ hph W (U.X k₀) a
    hdom Dc D hn hDe hD v₀ hv₀ x0
  choose C hC hrd using fun k => hread k (hsame k) (ga k) (δ k) (hset k).1 (hset k).2.1 (hset k).2.2.1
    (hset k).2.2.2.1 (hset k).2.2.2.2
  have hmu1 := GlobalTheory.T.vacuum_multiplier_eq_one_on_stabiliser E H Dw l Xo c n d σ r W.g (U.X k₀) Dc.bas Dc.idx D hn ph Dc.sympl hev hD
    (W.F.Di (W.ik k₀)) (W.emb k₀) (huw k₀).2.2.2.1 (huw k₀).2.2.2.2.1 (huw k₀).2.2.2.2.2.1 (huw k₀).2.2.2.2.2.2
    v₀ hv₀ mu hmu
  have hgrp := (GlobalTheory.SW.level_laws E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D hn).2.2.1
  have hpull := fun k => isStabForm_pull_upto E r (U.X k) (U.X k₀) (hsame k) (ga k) (Formalism.L2.PjFree.laU U a n k)
    (wtOf (U.X k₀) Dc.hr Dc.k Dc.k' n) D.grp l.M ((C k)⁻¹ • P k) (hset k).1
    (fun τ i => by
      rw [Dc.wt_eq]
      simp only [wtX, Formalism.L2.PjFree.laU, (hsame k).p0])
    (fun g' hg' => ⟨((hgrp g').1 hg').1, fun hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).2⟩)
    (hpr k) (hchi k) (isBddSec_of_mem_holSub U.X _ P hP1 k _)
  have hM2 : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hMm : ((2 * bad * d.l₂.M : ℕ) : 𝓞 E) ∈ D.𝔪 := by
    rw [hD.m, Nat.cast_mul]
    refine Ideal.mul_mem_left _ _ ?_
    have h1 : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [d.l₂.prod]
      exact Ideal.mem_span_singleton_self _
    unfold Mfr
    exact (Submodule.mem_inf.1 (Ideal.mul_le_inf h1)).2
  obtain ⟨m, Λ, Pj, hΛ, hQ⟩ := GlobalTheory.T.stableForms_eq_sum_thetaSeries_freeLowerRows E r (U.X k₀) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev hbig D hn
    (2 * bad * d.l₂.M) (Mfr l) (Jd d) (by positivity) hMm hD.prod hD.cop v₀ hv₀ mu hmu Dc.k Dc.k' U.Comp
    (fun k => mapL (ga k) (U.X k).Λ) _ (fun k => (hset k).2.1) hsep
    (fun k g' hg' hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).1) (fun k => (hpull k).1)
  have hgl := fun j => GlobalTheory.Dict.GenLatCmp.genLat_vset E n (Λ j)
  have hg1 := fun j => (hgl j).1 bad d.l₂.M hbad d.l₂.odd (hΛ j).1
  choose N hN using fun j => (hg1 j).2.2.2
  have hV : ∀ j, Λ j ∈ Vset E n d.l₂.M := fun j => (hgl j).2.2.1 _ _ (Dvd.intro_left _ rfl) (hΛ j).1
  choose mj t R hR hPj using fun j => GlobalTheory.T.harmonicRowHighest_eq_span_integral_harmonic E H Dw l c σ r W.g Dw.p n (U.X k₀) a Dc (Λ j) (N j)
    (hN j).1.pos ((hN j).2.2.trans inf_le_left) (Pj j) (hΛ j).2
  choose f hf hfr using fun j i => (htot ⟨Λ j⟩ (N j) x0 (R j i) (hg1 j).1 (hg1 j).2.1 (hg1 j).2.2.1 (hN j)
    (hadm _) (hR j i)).2
  have hPe : P = ∑ j, ∑ i, (t j i * (u (Λ j) (N j))⁻¹) • Formalism.L2.PjFree.rdU U (f j i) := by
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ (U.X k).dom
    · obtain ⟨hx1, hx2⟩ := (hpull k).2 x hx
      have e1 := hQ k _ hx1
      rw [hx2, Pi.smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ (hC k)] at e1
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hPj j, theta_sum_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrd k (Λ j) (hV j) (N j) (hN j) (R j i) (hR j i).1 (f j i) (hf j i) (hfr j i) x hx]
      have := hu (Λ j) (hV j) (N j) (hN j)
      field_simp
    · rw [hP0 k x hx]
      refine (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_).symm
      have : Formalism.L2.PjFree.rdU U (f j i) k x = 0 := dif_neg hx
      rw [this, mul_zero]
  rw [hPe]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨f j i, ⟨hf j i, ⟨Λ j⟩, N j, x0, R j i, (hg1 j).1, (hg1 j).2.1, (hg1 j).2.2.1, hN j,
    hadm _, hR j i, hfr j i⟩, rfl⟩

end GlobalTheory.LargeCover
