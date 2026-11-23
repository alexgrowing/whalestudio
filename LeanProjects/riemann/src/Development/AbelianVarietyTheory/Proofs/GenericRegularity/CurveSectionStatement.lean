import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
import Formalism.LocalToGlobal.ProjectiveLattices.CurveSec
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FinitePtsOfCurve
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericSectionPointsInequivalentValuations

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped WithZero

namespace GlobalTheory.ValZeroSection

theorem approx_family {P C : Type} [Finite P] (Ω : C → Type) [∀ Z, Field (Ω Z)] (Zc : P → C)
    (v : ∀ ζ, Valuation (Ω (Zc ζ)) ℤᵐ⁰)
    (hgen : ∀ ζ, ∃ x, v ζ x = WithZero.exp (1 : ℤ))
    (hsep : ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' →
      ∃ r : ∀ Z, Ω Z, v ζ (r (Zc ζ)) < 1 ∧ v ζ' (r (Zc ζ')) = 1)
    (n : P → ℤ) : ∃ a : ∀ Z, Ω Z, ∀ ζ, v ζ (a (Zc ζ)) = WithZero.exp (n ζ) := by
  classical
  have key : ∀ Z, ∃ x : Ω Z, ∀ (ζ : P) (hζ : Zc ζ = Z), v ζ (cast (congrArg Ω hζ.symm) x) = WithZero.exp (n ζ) := by
    intro Z
    have : Fintype {ζ : P // Zc ζ = Z} := Fintype.ofFinite _
    have hV : ∀ ζ : {ζ : P // Zc ζ = Z}, ∃ V : Valuation (Ω Z) ℤᵐ⁰,
        (∀ x : Ω Z, V x = v ζ.1 (cast (congrArg Ω ζ.2.symm) x)) ∧ (∀ r : ∀ Z, Ω Z, V (r Z) = v ζ.1 (r (Zc ζ.1))) ∧
        ∃ x, V x = WithZero.exp (1 : ℤ) := by
      rintro ⟨ζ, rfl⟩
      exact ⟨v ζ, fun _ => rfl, fun _ => rfl, hgen ζ⟩
    choose V hV1 hV2 hV3 using hV
    obtain ⟨x, hx⟩ := ReciprocityTheory.ChartRestriction.G.Lift.exists_val_eq V hV3 (fun i i' hne he => by
      obtain ⟨r, h1, h2⟩ := hsep i.1 i'.1 (fun e => hne (Subtype.ext e)) (i.2.trans i'.2.symm)
      rw [← hV2 i r] at h1
      rw [← hV2 i' r] at h2
      exact h1.ne (he.eq_one_iff_eq_one.2 h2)) (fun i => n i.1)
    exact ⟨x, fun ζ hζ => (hV1 ⟨ζ, hζ⟩ x).symm.trans (hx ⟨ζ, hζ⟩)⟩
  choose a ha using key
  exact ⟨a, fun ζ => ha (Zc ζ) ζ rfl⟩

theorem glue_ratios {R C : Type} [CommRing R] (Ω : C → Type) [∀ Z, Field (Ω Z)] (e : ∀ Z, R →+* Ω Z)
    (M : ℕ → AddSubgroup R) (S : Finset C) (a : ∀ Z, Ω Z)
    (hmul : ∀ k f g, f ∈ M k → g ∈ M 1 → f * g ∈ M (k + 1))
    (hu : ∀ Z ∈ S, ∃ u ∈ M 1, e Z u ≠ 0)
    (hsplit : ∀ Z k, ∀ g ∈ M k, ∃ g' ∈ M k, e Z g' = e Z g ∧ ∀ Z', Z' ≠ Z → e Z' g' = 0)
    (hbir : ∀ Z ∈ S, ∃ k, ∃ p ∈ M k, ∃ q ∈ M k, e Z q ≠ 0 ∧ e Z p = a Z * e Z q) :
    ∃ k, ∃ p ∈ M (k + 1), ∃ q ∈ M (k + 1), ∀ Z ∈ S, e Z q ≠ 0 ∧ e Z p = a Z * e Z q := by
  classical
  have hup : ∀ Z ∈ S, ∀ k m, (∃ p ∈ M k, ∃ q ∈ M k, e Z q ≠ 0 ∧ e Z p = a Z * e Z q) →
      ∃ p ∈ M (k + m), ∃ q ∈ M (k + m), e Z q ≠ 0 ∧ e Z p = a Z * e Z q := by
    intro Z hZ k m hk
    obtain ⟨u, hu1, hu2⟩ := hu Z hZ
    induction m with
    | zero => exact hk
    | succ m ih =>
      obtain ⟨p, hp, q, hq, h1, h2⟩ := ih
      refine ⟨p * u, hmul _ _ _ hp hu1, q * u, hmul _ _ _ hq hu1, ?_, ?_⟩
      · rw [map_mul]; exact mul_ne_zero h1 hu2
      · rw [map_mul, map_mul, h2, mul_assoc]
  choose! k hk using hbir
  set K := S.sup k with hK
  have hK' : ∀ Z ∈ S, ∃ p ∈ M (K + 1), ∃ q ∈ M (K + 1), (e Z q ≠ 0 ∧ e Z p = a Z * e Z q) ∧
      ∀ Z', Z' ≠ Z → e Z' p = 0 ∧ e Z' q = 0 := by
    intro Z hZ
    have hle : k Z ≤ K := Finset.le_sup hZ
    have := hup Z hZ (k Z) (K + 1 - k Z) (hk Z hZ)
    rw [show k Z + (K + 1 - k Z) = K + 1 by omega] at this
    obtain ⟨p, hp, q, hq, h1, h2⟩ := this
    obtain ⟨p', hp', h3, h4⟩ := hsplit Z _ p hp
    obtain ⟨q', hq', h5, h6⟩ := hsplit Z _ q hq
    exact ⟨p', hp', q', hq', ⟨by rwa [h5], by rw [h3, h5, h2]⟩, fun Z' hZ' => ⟨h4 Z' hZ', h6 Z' hZ'⟩⟩
  choose! p hp q hq h1 h2 using hK'
  refine ⟨K, ∑ Z ∈ S, p Z, sum_mem hp, ∑ Z ∈ S, q Z, sum_mem hq, fun Z hZ => ?_⟩
  have ep : e Z (∑ Z ∈ S, p Z) = e Z (p Z) := by
    rw [map_sum]
    exact Finset.sum_eq_single_of_mem Z hZ fun b hb hne => (h2 b hb Z hne.symm).1
  have eq : e Z (∑ Z ∈ S, q Z) = e Z (q Z) := by
    rw [map_sum]
    exact Finset.sum_eq_single_of_mem Z hZ fun b hb hne => (h2 b hb Z hne.symm).2
  rw [ep, eq]
  exact h1 Z hZ

theorem valV_lt_of_nval_lt {T : CDVR} {x y : T.Fr} (hx : x ≠ 0) (h : nval T.V 1 x < nval T.V 1 y) :
    valV T.V y < valV T.V x := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero]
    exact zero_lt_iff.2 (valV_ne_zero hx)
  rw [nval_of_ne hx, nval_of_ne hy, EReal.coe_lt_coe_iff, Nat.cast_one, div_one, div_one, Int.cast_lt] at h
  refine (WithZero.log_lt_log (valV_ne_zero hy) (valV_ne_zero hx)).1 ?_
  simp only [vV] at h
  omega

theorem exists_forms_val {P C Wt : Type} [Finite P] (Ω : C → Type) [∀ Z, Field (Ω Z)] (Zc : P → C) (Tt : P → CDVR)
    (ι : ∀ ζ, Ω (Zc ζ) →+* (Tt ζ).Fr) (M : Wt → Type) (e : ∀ Z w, M w → Ω Z) (ev : ∀ ζ w, M w → (Tt ζ).Fr)
    (h1 : ∀ ζ, ∃ a, vV (Tt ζ).V (ι ζ a) = 1)
    (h2 : ∀ ζ w F, e (Zc ζ) w F = 0 → ev ζ w F = 0)
    (h3 : ∀ ζ w F F', ι ζ (e (Zc ζ) w F) * ev ζ w F' = ι ζ (e (Zc ζ) w F') * ev ζ w F)
    (h4 : ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' → ∃ w F F', ev ζ w F' ≠ 0 ∧ ev ζ' w F' ≠ 0 ∧
      nval (Tt ζ).V 1 (ev ζ w F') < nval (Tt ζ).V 1 (ev ζ w F) ∧
      nval (Tt ζ').V 1 (ev ζ' w F') < nval (Tt ζ').V 1 (ev ζ' w F - ev ζ' w F'))
    (L : ℕ → Wt) (hL : ∀ ζ k, ∃ u : M (L k), ev ζ _ u ≠ 0)
    (hR : ∀ a : ∀ Z, Ω Z, ∃ k, ∃ p q : M (L k), ∀ ζ, e (Zc ζ) _ q ≠ 0 ∧ e (Zc ζ) _ p = a (Zc ζ) * e (Zc ζ) _ q)
    (n : P → ℤ) :
    ∃ k, ∃ p q : M (L k), ∀ ζ, ev ζ _ p ≠ 0 ∧ ev ζ _ q ≠ 0 ∧
      vV (Tt ζ).V (ev ζ _ p) + n ζ = vV (Tt ζ).V (ev ζ _ q) := by
  have hratio : ∀ ζ w F F', ev ζ w F' ≠ 0 → ι ζ (e (Zc ζ) w F / e (Zc ζ) w F') = ev ζ w F / ev ζ w F' := by
    intro ζ w F F' hF'
    have h0 : ι ζ (e (Zc ζ) w F') ≠ 0 := (map_ne_zero _).2 fun h => hF' (h2 ζ w F' h)
    rw [map_div₀, div_eq_div_iff h0 hF', h3, mul_comm]
  obtain ⟨a, ha⟩ := approx_family Ω Zc (fun ζ => (valV (Tt ζ).V).comap (ι ζ))
    (fun ζ => by
      obtain ⟨a, ha⟩ := h1 ζ
      have h0 : ι ζ a ≠ 0 := by
        intro h
        rw [h] at ha
        simp [vV] at ha
      refine ⟨a⁻¹, ?_⟩
      rw [Valuation.comap_apply, map_inv₀, map_inv₀, ← WithZero.exp_log (valV_ne_zero (V := (Tt ζ).V) h0),
        ← WithZero.exp_neg]
      exact congrArg _ ha)
    (fun ζ ζ' hne hZ => by
      obtain ⟨w, F, F', a1, a2, a3, a4⟩ := h4 ζ ζ' hne hZ
      refine ⟨fun Z => e Z w F / e Z w F', ?_, ?_⟩
      · rw [Valuation.comap_apply, hratio ζ w F F' a1, map_div₀]
        exact (div_lt_one₀ (zero_lt_iff.2 (valV_ne_zero a1))).2 (valV_lt_of_nval_lt a1 a3)
      · rw [Valuation.comap_apply, hratio ζ' w F F' a2, map_div₀]
        have := Valuation.map_add_eq_of_lt_left _ (valV_lt_of_nval_lt a2 a4)
        rw [add_sub_cancel] at this
        rw [this, div_self (valV_ne_zero a2)]) (fun ζ => n ζ)
  obtain ⟨k, p, q, hpq⟩ := hR a
  refine ⟨k, p, q, fun ζ => ?_⟩
  obtain ⟨hq0, hp⟩ := hpq ζ
  have ha' : valV (Tt ζ).V (ι ζ (a (Zc ζ))) = WithZero.exp (n ζ) := ha ζ
  have ha0 : ι ζ (a (Zc ζ)) ≠ 0 := by
    intro h
    rw [h, map_zero] at ha'
    exact WithZero.exp_ne_zero ha'.symm
  obtain ⟨u, hu⟩ := hL ζ k
  have hq : ev ζ _ q ≠ 0 := by
    intro h
    have := h3 ζ _ q u
    rw [h, mul_zero] at this
    exact mul_ne_zero ((map_ne_zero _).2 hq0) hu this
  have hr := hratio ζ _ p q hq
  rw [hp, mul_div_cancel_right₀ _ hq0, eq_div_iff hq] at hr
  refine ⟨hr ▸ mul_ne_zero ha0 hq, hq, ?_⟩
  rw [← hr, vV_mul ha0 hq]
  have : vV (Tt ζ).V (ι ζ (a (Zc ζ))) = - n ζ := by rw [vV, ha', WithZero.log_exp]
  omega

theorem exists_gen_ne_zero {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF}
    {la : HeightOneSpectrum (𝓞 B.KO)} {ζ : PtsG G la} {y : E.Pt' la} (hs : SecPt ζ y) :
    ∃ i, hs.ev (emb (xplus X E hM) la G.N (X.inc wL (G.w i))) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply hs.s0.ne_zero
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Algebra.smul_def, map_mul]
  exact mul_eq_zero_of_right _ (hc k)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_ratio {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (hC : CompSplitSt h j hG) (hB : BIRSt h j hj hG G) (S : Finset (Comp (T.Q.Xo j) T.Q.c))
    (hS : ∀ Z ∈ S, ∃ i, evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0)
    (a : ∀ Z : Comp (T.Q.Xo j) T.Q.c, Om Z) :
    ∃ k, ∃ p q : (recB h.toLawsCore).Cusp j (addL (wt0 D j) wL (k + 1)), ∀ Z ∈ S,
      evC hG Z ((q : (recB h.toLawsCore).Cusp j _) : T.R j) ≠ 0 ∧
      evC hG Z ((p : (recB h.toLawsCore).Cusp j _) : T.R j) =
        a Z * evC hG Z ((q : (recB h.toLawsCore).Cusp j _) : T.R j) := by
  have hw1 : ∀ i, ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j) ∈ cutR T.C j (addL (wt0 D j) wL 1) := by
    intro i
    rw [add_zero_weight_one_eq]
    exact (G.w i).2
  obtain ⟨k, p, hp, q, hq, hpq⟩ := glue_ratios (R := T.R j) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => (evCAlg hG hT Z).toRingHom) (fun k => (cutR T.C j (addL (wt0 D j) wL k)).toAddSubgroup) S a
    (fun k f g hf hg => esec_mem_mulL h hj hf hg)
    (fun Z hZ => by
      obtain ⟨i, hi⟩ := hS Z hZ
      exact ⟨_, hw1 i, fun h0 => hi ((evCAlg_apply hG hT Z _).symm.trans h0)⟩)
    (fun Z k g hg => by
      obtain ⟨g', h1, h2⟩ := hC Z (addL (wt0 D j) wL k) ⟨g, hg⟩
      refine ⟨(g' : T.R j), g'.2, ?_, fun Z' hZ' => ?_⟩
      · exact (evCAlg_apply hG hT Z _).trans (h1.trans (evCAlg_apply hG hT Z _).symm)
      · exact (evCAlg_apply hG hT Z' _).trans (h2 Z' hZ'))
    (fun Z hZ => by
      obtain ⟨i, hi⟩ := hS Z hZ
      obtain ⟨k, g, Pw, hP, hne, he⟩ := hB Z (a Z)
      have hg : (g : T.R j) ∈ cutR T.C j (addL (wt0 D j) wL k) := by
        rw [addL, zero_weight_add]
        exact g.2
      have hq := esec_hom_mem h hj (fun i => ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j))
        (fun i => (G.w i).2) (Pw * MvPolynomial.X i) (hP.mul (MvPolynomial.isHomogeneous_X _ i))
      have hv := (evCAlg_apply hG hT Z _).trans (esec_evC_aeval h hj hG hT Z
        (fun i => ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) (Pw * MvPolynomial.X i))
      rw [map_mul (MvPolynomial.aeval fun i => evC hG Z _), MvPolynomial.aeval_X] at hv
      refine ⟨k + 1, _, esec_mem_mulL h hj hg (hw1 i), _, hq, ?_, ?_⟩
      · exact fun h0 => mul_ne_zero hne hi (hv.symm.trans h0)
      · refine Eq.trans ?_ (congrArg (fun t => a Z * t) hv).symm
        refine (map_mul (evCAlg hG hT Z) _ _).trans ?_
        rw [evCAlg_apply, evCAlg_apply, ← mul_assoc, he])
  refine ⟨k, ⟨p, hp⟩, ⟨q, hq⟩, fun Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := hpq Z hZ
  refine ⟨fun h0 => h1 ((evCAlg_apply hG hT Z _).trans h0), ?_⟩
  refine (evCAlg_apply hG hT Z _).symm.trans (h2.trans ?_)
  exact congrArg (fun t => a Z * t) (evCAlg_apply hG hT Z _)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem eSec_of_valSep {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hC : CompSplitSt h j hG) (hB : BIRSt h j hj hG G) (hV : ValSepSt h j hj hG G la) :
    ESecSt (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la := by
  classical
  intro y hw g0 hM hg0
  have hfin : Finite (PtsG G la) := (finite_pts_of_curve _
    (inCurveSec (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la y (fun ζ => (hw ζ).toSecPt) g0 hM hg0)).1
  have := Fintype.ofFinite (PtsG G la)
  obtain ⟨Zc, ι, h1, h2, h3, h4⟩ := hV y hw
  have hgen := fun ζ => exists_gen_ne_zero (hw ζ).toSecPt
  obtain ⟨k, p, q, hpq⟩ := exists_forms_val (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z) Zc (fun ζ => (hw ζ).T) ι
    (fun w => (recB h.toLawsCore).Cusp j w)
    (fun Z w F => evC hG Z ((F : (recB h.toLawsCore).Cusp j w) : T.R j))
    (fun ζ w F => (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)))
    h1 h2 h3 h4 (fun k => addL (wt0 D j) wL (k + 1))
    (fun ζ k => by
      obtain ⟨i, hi⟩ := hgen ζ
      rw [← esecW_eq]
      refine ⟨esecPow h hj (G.w i) k, ?_⟩
      rw [esec_inc_pow]
      exact fun h0 => pow_ne_zero (k + 1) hi
        (((map_pow ((hw ζ).ev.comp (emb (recPlus h j hj) la G.N)) _ _).symm).trans h0))
    (fun a => by
      obtain ⟨k, p, q, hpq⟩ := exists_ratio h hj hG hT G hC hB (Finset.univ.image Zc)
        (fun Z hZ => by
          obtain ⟨ζ, -, rfl⟩ := Finset.mem_image.1 hZ
          obtain ⟨i, hi⟩ := hgen ζ
          exact ⟨i, fun h0 => hi (h2 ζ wL (G.w i) h0)⟩) a
      exact ⟨k, p, q, fun ζ => hpq (Zc ζ) (Finset.mem_image_of_mem Zc (Finset.mem_univ ζ))⟩)
    (fun ζ => vV (hw ζ).T.V ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc wF g0))))
  exact ⟨k + 1, emb (recPlus h j hj) la G.N ((recPJ h j hj).inc _ p),
    emb (recPlus h j hj) la G.N ((recPJ h j hj).inc _ q),
    emb_mem_Vw (recPlus h j hj) la G.N _ p, emb_mem_Vw (recPlus h j hj) la G.N _ q,
    fun β hβ => hasseRp_emb (recPlus h j hj) la hβ _, fun β hβ => hasseRp_emb (recPlus h j hj) la hβ _, hpq⟩

end GlobalTheory.ValZeroSection

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.eSec_of_curveHyp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ESecSt (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la :=
  fun D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB =>
    GlobalTheory.ValZeroSection.eSec_of_valSep h hj hG hT G la hC hB
      (GlobalTheory.GenSep.valSep_of_curveHyp D T h j hj hG hT ka wL wF G S g0 la hH hV hC hB)
