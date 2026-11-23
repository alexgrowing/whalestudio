import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqMulOfContinuousOnQuotient
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfForallAlgHom

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecDivision

open NumberField Topology Filter
open scoped Matrix

theorem dvd_of_locally_bounded {K A : Type} [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.Smooth K A] (σ : K →+* ℂ) {a b : A} (ha : a ≠ 0)
    (H : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)), IsOpen B →
      (∀ z ∈ B, (φ z).comp (algebraMap K A) = σ) → (∀ u : A, DifferentiableOn ℂ (fun z => φ z u) B) →
      ∀ z₀ ∈ B, ∃ n : ℕ, n ≠ 0 ∧ ∃ M : ℝ, ∀ᶠ z in 𝓝 z₀, ‖φ z b‖ ^ n ≤ M * ‖φ z a‖ ^ n) : a ∣ b := by
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_smooth K A
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  by_contra hn
  obtain ⟨p, hp, s, r, hs, hr, h⟩ := GlobalTheory.ContinuousQuotient.exists_prime_of_not_dvd ha hn
  letI : Algebra K ℂ := σ.toAlgebra
  have h0 : Ideal.Quotient.mkₐ K p s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨e, he⟩ := not_forall.mp fun h => h0 (GlobalTheory.FiniteOrderRule.eq_zero_of_forall_algHom (K := K) (Ω := ℂ) _ h)
  obtain ⟨ι, -, m, B, φ, hB, hφσ, hd, hcov, hne⟩ := GlobalTheory.T.exists_countable_holomorphic_families_smooth K A σ
  let ψ : A →ₐ[K] ℂ := e.comp (Ideal.Quotient.mkₐ K p)
  obtain ⟨i, z₀, hz₀, hψ⟩ := hcov ψ.toRingHom (RingHom.ext fun k => ψ.commutes k)
  obtain ⟨n, hn0, M, hM⟩ := H _ _ _ (hB i) (hφσ i) (hd i) z₀ hz₀
  have hc : ∀ u, ContinuousAt (fun z => φ i z u) z₀ := fun u =>
    (hd i u).continuousOn.continuousAt ((hB i).mem_nhds hz₀)
  have hr0 : φ i z₀ r = 0 := by
    rw [hψ]
    change e (Ideal.Quotient.mk p r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  have hs0 : φ i z₀ s ≠ 0 := by rw [hψ]; exact he
  have hlt : ∀ᶠ z in 𝓝 z₀, M * ‖φ i z r‖ ^ n < ‖φ i z s‖ ^ n := by
    refine ContinuousAt.eventually_lt (continuousAt_const.mul ((hc r).norm.pow n)) ((hc s).norm.pow n) ?_
    simp only [hr0, norm_zero, zero_pow hn0, mul_zero]
    exact pow_pos (norm_pos_iff.2 hs0) n
  obtain ⟨z, hz, h1, h2⟩ := ((hne i z₀ hz₀ a ha).and_eventually (hM.and hlt)).exists
  have h3 : ‖φ i z a‖ ^ n * ‖φ i z s‖ ^ n = ‖φ i z b‖ ^ n * ‖φ i z r‖ ^ n := by
    rw [← mul_pow, ← mul_pow, ← norm_mul, ← norm_mul, ← map_mul, ← map_mul, h]
  have h4 : 0 < ‖φ i z a‖ ^ n := pow_pos (norm_pos_iff.2 hz) n
  have h5 := mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg (φ i z r)) n)
  have h6 := mul_lt_mul_of_pos_left h2 h4
  nlinarith

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.GenericFrames GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.CompHt GlobalTheory.FlagTan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_near_frames (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) {A : Type} [CommRing A]
    [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ} {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ))
    (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (hB : IsOpen B) (hφ : ∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B)
    (hy : ∀ b ∈ B, FrMap (φ b) yA (y b)) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (k : U.Comp) (x₀ : (U.X k).dom), (∃ t, FrBor t (U.un k x₀) (y b₀)) ∧ ∀ V ∈ 𝓝 x₀.1, ∀ᶠ b in 𝓝 b₀,
      ∃ x : (U.X k).dom, x.1 ∈ V ∧ ∃ t, FrBor t (U.un k x) (y b) ∧ ∀ i, t (some i) = 1 := by
  obtain ⟨hr, hty, hsur, -, -, g, e, F, ik, ψ, hef, hun⟩ := hU
  obtain ⟨B', k', P, hB', hb', hs, hP, hyP⟩ :=
    GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨k, ⟨x₁, hx₁⟩, t₁, ht₁⟩ := hsur (y b₀)
  obtain ⟨P₁, hP₁, hP₁', hu₁, -⟩ := hun k ⟨x₁, hx₁⟩
  obtain rfl : ik k = k' := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb') (hu₁.symm.trans (ht₁.1.symm.trans (hyP b₀ hb').1))
  obtain ⟨idx, hper, -, honto⟩ := dictionary c σ e _ (U.X k) (ψ k) hσ (F.sig _).1 (F.sig _).2 hr
    (hty k).1 (hty k).2 (hef k) (GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k) (ψ k) hσ hr
      (hty k).1 (hty k).2 (hef k) x₁ hx₁ P₁ hP₁ hP₁')
  have hbor : ∀ x (hx : x ∈ (U.X k).dom), ∀ b ∈ B',
      (∀ a j, pc (U.X k) x (ψ k a : Fin r → E) (idx j).1 (idx j).2 = P b a j) →
      ∃ t, FrBor t (U.un k ⟨x, hx⟩) (y b) ∧ ∀ i, t (some i) = 1 := by
    intro x hx b hb hh
    obtain ⟨P₀, hP₀, hP₀', hux, hud, -⟩ := hun k ⟨x, hx⟩
    have hPS : ∀ v, P₀ v = (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ P b v := fun v => funext fun j => by
      rw [Matrix.one_mulVec]
      exact (hP₀ v j).trans ((hper _ _ j).trans (hh v j))
    obtain ⟨t, ht, ht1⟩ := GlobalTheory.FrameNorm.frBor_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ 1 (y b)
      (U.un k ⟨x, hx⟩) (hP.1 b hb) hP₀' hPS (fun j j' hj => by
        obtain rfl : j = j' := by
          by_contra hjj
          exact hj (Matrix.one_apply_ne hjj)
        exact ⟨rfl, le_rfl⟩) (hyP b hb).1 hux (hyP b hb).2 hud
    refine ⟨t, ht, fun i => Units.ext ?_⟩
    have := ht1 (e.symm i)
    rw [Equiv.apply_symm_apply, Matrix.one_apply_eq] at this
    exact this
  choose! x₂ hx₂ hr₂ using fun b (hb : b ∈ B') => honto (P b) (hP.1 b hb)
  have hBn : ∀ᶠ b in 𝓝 b₀, b ∈ B' := hB'.mem_nhds hb'
  refine ⟨k, ⟨x₂ b₀, hx₂ b₀ hb'⟩, (hbor _ _ b₀ hb' (hr₂ b₀ hb')).imp fun _ h => h.1, fun V hV => ?_⟩
  have key := GlobalTheory.T.period_coordinates_frames_lift_tendsto E r (U.X k) _ (𝓝 b₀) (x₂ b₀) x₂ (hx₂ b₀ hb') (hBn.mono hx₂) (fun v hv τ i => by
    obtain ⟨a, rfl⟩ : ∃ a, (ψ k a : Fin r → E) = v := ⟨(ψ k).symm ⟨v, hv⟩, by simp⟩
    obtain ⟨j, hj⟩ := idx.surjective (τ, i)
    obtain ⟨rfl, rfl⟩ : τ = (idx j).1 ∧ i = (idx j).2 := by rw [hj]; exact ⟨rfl, rfl⟩
    change Tendsto (fun b => pc (U.X k) (x₂ b) (ψ k a) _ _) _ (𝓝 (pc (U.X k) (x₂ b₀) (ψ k a) _ _))
    rw [hr₂ b₀ hb']
    have hc : ContinuousAt (fun b => P b a j) b₀ :=
      (continuous_apply j).continuousAt.comp ((hP.2 a).continuousOn.continuousAt hBn)
    exact hc.tendsto.congr' (hBn.mono fun b hb => (hr₂ b hb a j).symm)) _
    (inter_mem hV ((FourierCoefficientDomain.isOpen_dom _).mem_nhds (hx₂ b₀ hb')))
  filter_upwards [hBn, key] with b hb ⟨x, ⟨hxV, hx⟩, hxx⟩
  exact ⟨⟨x, hx⟩, hxV, hbor x hx b hb fun a j => (hxx _ _ _).trans (hr₂ b hb a j)⟩

theorem toC_evR_frBor {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) {t : Ix Dw → (CAt σ)ˣ}
    {y y' : FrPt Xo c (CAt σ)} (h : FrBor t y y') (ht : ∀ i, t (some i) = 1) :
    toC (evR Xo c f y') = toC (t none : CAt σ) ^ e none * toC (evR Xo c f y) := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  rw [evR_frBor hf h, Finset.prod_eq_single none (fun i _ hi => by
    obtain ⟨j, rfl⟩ := Option.ne_none_iff_exists'.1 hi
    rw [ht, one_zpow]) (fun h => absurd (Finset.mem_univ _) h), Units.val_zpow_eq_zpow_val]
  rfl

theorem rdU_apply (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) (x : (U.X k).dom) :
    rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2

theorem chart_dvd (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) {h : GenFrEx Xo c} (C : FChart h)
    {e e' : Ix Dw → ℤ} {f g : Rul Xo c} (hf : f ∈ secZ Xo c e) (hg : g ∈ secZ Xo c e') (q : FDSec U.X)
    (hq : ∀ k, ContinuousOn (q k) (U.X k).dom)
    (hfg : ∀ z ∈ framesOn U C.Z, rdU U g z.1 z.2 = q z.1 z.2 * rdU U f z.1 z.2) {a b : C.R} (ha0 : a ≠ 0)
    (ha : ∀ (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)), FrMap ψ C.y z → evR Xo c f z = ψ a)
    (hb : ∀ (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)), FrMap ψ C.y z → evR Xo c g z = ψ b) : a ∣ b := by
  classical
  haveI := C.sm
  refine dvd_of_locally_bounded σ ha0 fun m B φ hB hφσ hd z₀ hz₀ => ?_
  let mk : ∀ z ∈ B, C.R →ₐ[c.F] CAt σ := fun z hz =>
    { (show C.R →+* CAt σ from φ z) with commutes' := fun a => RingHom.congr_fun (hφσ z hz) a }
  let φ' : (Fin m → ℂ) → (C.R →ₐ[c.F] CAt σ) := fun z => if hz : z ∈ B then mk z hz else mk z₀ hz₀
  have hφ' : ∀ z ∈ B, ∀ u, toC (φ' z u) = φ z u := by
    intro z hz u
    simp only [φ', dif_pos hz]
    rfl
  choose y hy using fun z => exists_frMap (φ' z) C.y
  obtain ⟨k, x₀, ⟨t₀, ht₀⟩, hnear⟩ := exists_near_frames U hσ hU C.y φ' y hB
    (fun u => (hd u).congr fun z hz => hφ' z hz u) (fun z _ => hy z) hz₀
  obtain ⟨n, hn, hev, η, hη, hη0⟩ := exists_even_sec_evR_ne_zero E H Dw l Xo c σ (y z₀)
  have hηc : ContinuousOn (rdU U η k) (U.X k).dom :=
    (hU.2.2.2.2.1 0 n ⟨fun _ _ _ _ => le_rfl, hev⟩ η hη k).1.continuousOn
  rw [← secZ_nat] at hη
  obtain ⟨w, -, hw⟩ := GlobalTheory.DegCmp.fChart_exists_val C hη
  have hBn : ∀ᶠ z in 𝓝 z₀, z ∈ B := hB.mem_nhds hz₀
  have hdn : (U.X k).dom ∈ 𝓝 x₀.1 := (FourierCoefficientDomain.isOpen_dom _).mem_nhds x₀.2
  have hw0 : φ z₀ w ≠ 0 := by
    rw [← hφ' z₀ hz₀, ← hw _ _ _ (hy z₀)]; exact hη0
  have hx0 : rdU U η k x₀.1 ≠ 0 := by
    letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
    rw [rdU_apply]
    intro h0
    apply hη0
    rw [evR_frBor hη ht₀, show evR Xo c η (U.un k x₀) = 0 from h0, mul_zero]
  let G : (Fin m → ℂ) × Frame (U.X k).Ψ r → ℝ := fun p =>
    ‖(φ p.1 w / rdU U η k p.2) ^ (e' none - e none) * q k p.2 ^ n‖
  have hG : ContinuousAt G (z₀, x₀.1) := by
    have c1 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => φ p.1 w) (z₀, x₀.1) :=
      ContinuousAt.comp (g := fun z => φ z w) ((hd w).continuousOn.continuousAt hBn) continuousAt_fst
    have c2 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => rdU U η k p.2) (z₀, x₀.1) :=
      ContinuousAt.comp (g := rdU U η k) (hηc.continuousAt hdn) continuousAt_snd
    have c3 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => q k p.2) (z₀, x₀.1) :=
      ContinuousAt.comp (g := q k) ((hq k).continuousAt hdn) continuousAt_snd
    exact (((c1.div c2 hx0).zpow₀ _ (Or.inl (div_ne_zero hw0 hx0))).mul (c3.pow n)).norm
  have hlt : ∀ᶠ p in 𝓝 (z₀, x₀.1), G p < G (z₀, x₀.1) + 1 := hG.eventually_lt continuousAt_const (lt_add_one _)
  rw [nhds_prod_eq, eventually_prod_iff] at hlt
  obtain ⟨pa, hpa, pb, hpb, hlt⟩ := hlt
  have hV : ∀ᶠ x in 𝓝 x₀.1, pb x ∧ rdU U η k x ≠ 0 := hpb.and ((hηc.continuousAt hdn).eventually_ne hx0)
  refine ⟨n, hn.ne', G (z₀, x₀.1) + 1, ?_⟩
  filter_upwards [hBn, hpa, hnear _ hV] with z hz hza ⟨x, ⟨hx1, hx2⟩, t, ht, ht1⟩
  have hon : LiesOn C.Z (U.un k x) := fun s => by
    rw [← GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap (hy z), AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact GlobalTheory.UnifComp.liesOn_chart C _
  have e0 : rdU U g k x.1 = q k x.1 * rdU U f k x.1 := hfg ⟨k, x.1⟩ ⟨x.2, hon⟩
  have e1 := toC_evR_frBor hf ht ht1
  have e2 := toC_evR_frBor hg ht ht1
  have e3 := toC_evR_frBor hη ht ht1
  rw [ha _ _ (hy z), hφ' z hz, ← rdU_apply] at e1
  rw [hb _ _ (hy z), hφ' z hz, ← rdU_apply] at e2
  rw [hw _ _ _ (hy z), hφ' z hz, ← rdU_apply] at e3
  have hT : toC (t none : CAt σ) ≠ 0 := (show ℂˣ from t none).ne_zero
  generalize toC (t none : CAt σ) = T at e1 e2 e3 hT
  have e4 : φ z w / rdU U η k x.1 = T ^ n := by
    rw [div_eq_iff hx2, e3, ← zpow_natCast]; rfl
  have e5 : φ z b = T ^ (e' none - e none) * q k x.1 * φ z a := by
    rw [e1, e2, e0, zpow_sub₀ hT]
    field_simp
  have e6 : ‖φ z b‖ ^ n = G (z, x.1) * ‖φ z a‖ ^ n := by
    simp only [G]
    rw [e4, e5, ← norm_pow, ← norm_pow, ← norm_mul, mul_pow, mul_pow, ← zpow_natCast T, ← zpow_mul,
      ← zpow_natCast (T ^ _), ← zpow_mul, mul_comm (n : ℤ)]
  rw [e6]
  exact mul_le_mul_of_nonneg_right (hlt hza hx1).le (pow_nonneg (norm_nonneg _) _)

open IsDedekindDomain Module Formalism.BasicNotions GlobalTheory.FlatCore in

theorem exists_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (e e' : Ix Dw → ℤ) (f g : Rul Xo c), f ∈ secZ Xo c e → f ∈ suppOn Z → g ∈ secZ Xo c e' → g ∈ suppOn Z → f ≠ 0 → ∀ σ, GoodEmb c σ → ∀ q : FDSec (U σ).X, (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) g z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∃ s ∈ secZ Xo c (e' - e), idem Z * s = s ∧ s * f = g := by
  intro E _ _ _ H Dw l Xo c r U x hL Z e e' f g hf hfZ hg hgZ hf0 σ hσ q hq hfg
  obtain ⟨-, -, h, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have off : ∀ {u : Rul Xo c}, u ∈ suppOn Z → ∀ Z', Z' ≠ Z → genVal Z' u = 0 := fun hu Z' hZ => by
    rw [genVal_apply h]; exact evC_eq_zero h hZ hu
  have hfz : genVal Z f ≠ 0 := fun h0 => hf0 (secZ_eq_zero_of_genVal hf fun Z' => by
    by_cases hZ : Z' = Z
    · rw [hZ, h0]
    · exact off hfZ Z' hZ)
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (e' - e)
    (fun Z' => genVal Z' g / genVal Z' f) fun C => by
      by_cases hZ : C.Z = Z
      swap
      · rw [off hgZ _ hZ, zero_div, mul_zero]; exact zero_mem _
      subst hZ
      obtain ⟨a, ha1, ha2⟩ := GlobalTheory.DegCmp.fChart_exists_val C hf
      obtain ⟨b, hb1, hb2⟩ := GlobalTheory.DegCmp.fChart_exists_val C hg
      have ha0 : (a : Om C.Z) ≠ 0 := by rw [ha1]; exact mul_ne_zero (Units.ne_zero _) hfz
      obtain ⟨u, hu⟩ := chart_dvd (U σ) hσ (hL.unf σ hσ) C hf hg q hq hfg (fun h0 => ha0 (by rw [h0]; rfl))
        (ha2 _) (hb2 _)
      have hu' : (b : Om C.Z) = a * u := by rw [hu]; rfl
      have hp : (∏ i, C.t i ^ e' i) = (∏ i, C.t i ^ (e' - e) i) * ∏ i, C.t i ^ e i := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by rw [← zpow_add, Pi.sub_apply, sub_add_cancel]
      have : ((∏ i, C.t i ^ (e' - e) i : (Om C.Z)ˣ) : Om C.Z) * (genVal C.Z g / genVal C.Z f) = u := by
        refine mul_left_cancel₀ ha0 ?_
        rw [← hu', ha1, hb1, hp, Units.val_mul]
        field_simp
      rw [this]
      exact u.2
  have hsv' : ∀ Z' : Comp Xo c, genVal Z' s = genVal Z' g / genVal Z' f := fun Z' => (genVal_apply h Z' s).trans (hsv Z')
  refine ⟨s, hs, sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (idem_mul_mem Z hs).1 hs) fun Z' => ?_),
    sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (sub_add_cancel e' e ▸ mul_mem_secZ hs hf) hg) fun Z' => ?_)⟩
  · rw [map_sub, map_mul]
    by_cases hZ : Z' = Z
    · rw [hZ, GlobalTheory.DegCmp.genVal_idem_self, one_mul, sub_self]
    · rw [hsv', off hgZ _ hZ, zero_div, mul_zero, sub_self]
  · rw [map_sub, map_mul, hsv']
    by_cases hZ : Z' = Z
    · rw [hZ, div_mul_cancel₀ _ hfz, sub_self]
    · rw [off hgZ _ hZ, zero_div, zero_mul, sub_self]

end GlobalTheory.SecDivision
