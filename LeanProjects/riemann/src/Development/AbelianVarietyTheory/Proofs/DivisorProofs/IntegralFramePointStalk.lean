import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTwistedSectionComponent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyValZero

section Key

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_lift_ringHom {O : Type} [CommRing O] (T : CDVR) (f : O →+* T.Fr)
    (hf : ∀ a, f a ∈ (algebraMap T.V T.Fr).range) : ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = f := by
  have inj := IsFractionRing.injective T.V T.Fr
  choose b hb using hf
  refine ⟨⟨⟨⟨b, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, RingHom.ext hb⟩ <;> simp [hb]

theorem key_unit_eqChar {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    {T : CDVR} {io : c.F →+* T.Fr} (ho : ∀ a, io a ∈ (algebraMap T.V T.Fr).range)
    {x : Sp T.Fr ⟶ Xo.X} (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) {n : ℕ} {w : Fin n → (epsR T.V ⟶ G.G)} (hw : IsLieBasis w)
    {θ : G.PP.L.Sec} (hθ : Generates (X := G.G) θ) (k : KeyIn T.Fr)
    (hk : IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr)) :
    ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 c.F)
  let la : HeightOneSpectrum (𝓞 c.F) := ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField _)⟩
  obtain ⟨W, p, Y, -, hp, h2, h3, h4, h5⟩ := exists_model Xo c hpq hg la
  obtain ⟨b, hb⟩ := exists_lift_ringHom T (io.comp (c.V W).subtype) fun a => ho _
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, -⟩ := extPt Y T b z hx
  obtain ⟨tP, ⟨mP'⟩⟩ : ∃ t : SAB H (Sp T.V), Nonempty (SABMap t Y.t yt) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP t' yt (Out.jK T.V) mP' (PullbackSections.sabMapCast mJ hj)
  have hprop : IsProper t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G tP t' hprop m2 mK
  obtain ⟨n', -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP G yt (𝟙 _) mP' ψ
  exact (((GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels κ hκ E H Dw l Xo c _ _ Y p hpq (isBaseRing_local c W) hp h2 h3 h4 h5).1 T.V T.Fr z yt h1 G
    (PullbackSections.sabMapCast n' (Category.id_comp yt)) n w hw θ k hk).1 hθ).1

theorem vV_unit (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    unfold valV
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    refine (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 ?_
    show (u : T.V) ∉ IsLocalRing.maximalIdeal T.V
    exact fun h => h u.isUnit
  simp [vV, h1]

theorem mem_range_iff (T : CDVR) (x : T.Fr) : x ∈ (algebraMap T.V T.Fr).range ↔ 0 ≤ vV T.V x := by
  by_cases h : x = 0
  · subst h; simp [vV]
  have e : 0 ≤ vV T.V x ↔ valV T.V x ≤ 1 := by
    rw [← WithZero.log_le_log (valV_ne_zero (V := T.V) h) one_ne_zero, WithZero.log_one, vV]
    omega
  rw [e]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a,
    fun h => IsDiscreteValuationRing.exists_lift_of_le_one h⟩

theorem exists_tied_unit {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {T : CDVR} {io : c.F →+* T.Fr} (ho : ∀ a, io a ∈ (algebraMap T.V T.Fr).range)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (hy : Integral T io y) :
    letI := io.toAlgebra
    ∃ (Φ : FibKey Xo T.Fr y.x), Tied e y.s y.u Φ ∧ vV T.V (κ T.Fr Φ.key : T.Fr) = 0 := by
  classical
  letI := io.toAlgebra
  choose τ' hτ using fun τ : E →+* ℂ => exists_lift_ringHom T (io.comp (embK c τ)) fun a => ho _
  replace hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a) := fun τ a => DFunLike.congr_fun (hτ τ) a
  obtain ⟨G, t', m1, m2, ⟨ub, u1, u2, u3, u4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, hp, hs⟩ := hy
  obtain ⟨U₀, hU₀, hg₀⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨⟨P, rfl, hPg⟩, -⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U₀ t' (hU₀ ▸ m1)
  obtain ⟨Ψ, -, hΨ, -⟩ := exists_tied E H Dw l Xo c g e T.Fr y hpq
  have hgp : 1 ≤ g := hΨ ▸ Ψ.g_pos
  obtain rfl : P.g = g := hPg.trans (hg₀.trans (card_frame_index Dw e))
  have ht : SecTie m1 σ y.s := ⟨w1, s1, r1, i1, hs⟩
  have hne := ((SecTieEx.secTie_exists_unique E H Dw l Xo T.Fr y.x P.t m1).2.2 σ _ ht).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo T.Fr _ _ y.gen)
  have hB := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c T.Fr y.x y.u P.g e y.tan y.eig).1 y.basis
  obtain ⟨-, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo T.Fr y.x P.t.G m1.φ m1.cart
  choose u' hu₁ hu₂ using u4
  have hov : ∀ τ i, u' τ i ≫ P.t.G.hom = (epsR T.Fr).hom := fun τ i => by
    have : IsPreimmersion (spMap (algebraMap T.V T.Fr)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu₂,
      Category.assoc, Over.w]
    exact (GlobalTheory.EtaVal.spMap_comp_spMap _ _).trans ((congrArg spMap (RingHom.ext fun a => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (GlobalTheory.EtaVal.spMap_comp_spMap _ _).symm)
  let v : Fin P.g → (epsR T.Fr ⟶ P.t.G) := fun j => Over.homMk (u' (e j).1 (e j).2) (hov _ _)
  have hv : IsLieBasis v := (hb _ v).2 (by
    rw [show (fun j => (v j).left ≫ m1.φ) = fun j => y.u (e j).1 (e j).2 from funext fun j => hu₁ _ _]
    exact hB)
  obtain ⟨n, w, hw⟩ := Chart.exists_isLieBasis G.G G.semi.smooth
  obtain ⟨w', hw', hww⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ _ G.G P.t.G m2.φ m2.cart G.semi.smooth n w hw
  obtain rfl : P.g = n := by
    simpa using Fintype.card_congr ((GlobalTheory.Serre.Lie.basis P.t.act hv).indexEquiv (GlobalTheory.Serre.Lie.basis P.t.act hw'))
  have inj := IsFractionRing.injective T.V T.Fr
  obtain ⟨A, U, a1, a2, a3⟩ := exists_lie_matrices G.act hw τ' (m := Dw.mult) ub
    (fun τ k => (isTan_iff_isTangent _).1 (u1 τ k)) (fun τ k a => u2 τ k a _ (hτ τ a))
    (fun τ x hx he => (u3 τ x ((isTan_iff_isTangent _).2 hx) fun a z hz => by
      rw [inj (hz.trans (hτ τ a).symm)]
      exact he a).exists)
  obtain ⟨u, hu⟩ := key_unit_eqChar hκ hpq hg ho y.x_over m1 m2 hw hθ _
    (isFibreOf_of_sabMap _ P m2 hgp hne r2 i2 hp hw' hww)
  refine ⟨⟨P, m1, hgp, σ, hne, v, hv⟩, ⟨ht, rfl, fun j => hu₁ _ _⟩, ?_⟩
  have hinj : Function.Injective τ' := fun τ₁ τ₂ h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a =>
      congrArg Subtype.val (io.injective ((hτ τ₁ a).symm.trans ((h ▸ rfl : _ = _).trans (hτ τ₂ a)))))
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
  have hD := GlobalTheory.ColengthDifferent.colength_dvd E T.Fr T.V (E →+* ℂ) τ' Dw.mult _ e A U hinj (Embeddings.card E ℂ)
    inferInstance a1 a2 (fun _ => δ) (fun _ => hδ)
  have hδu : ∀ τ, IsUnit (τ' τ δ) := fun τ => by
    have h0 : embK c τ δ ≠ 0 := (map_ne_zero (embF c τ)).2 (RingOfIntegers.coe_ne_zero_iff.2 hδ0)
    obtain ⟨b, hb⟩ := ho (embK c τ δ)⁻¹
    exact IsUnit.of_mul_eq_one b (inj (by rw [map_mul, hτ, hb, ← map_mul, mul_inv_cancel₀ h0, map_one, map_one]))
  obtain ⟨d, hd⟩ : IsUnit (Matrix.of fun j k => U (e j).1 (e j).2 k).det :=
    isUnit_of_dvd_unit hD (IsUnit.prod_iff.2 fun τ _ => (hδu τ).pow _)
  suffices h : (κ T.Fr (FibKey.key ⟨P, m1, hgp, σ, hne, v, hv⟩) : T.Fr) =
      algebraMap T.V T.Fr ((Matrix.of fun j k => U (e j).1 (e j).2 k).det ^ 4 * (u : T.V)) by
    rw [h, ← hd, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    exact vV_unit T _
  have h := hκ.1 T.Fr P.pol hgp P.t.PP.rig P.t.PP.rigGen σ hne w' hw' σ hne v hv 1
    ((Matrix.of fun j k => U (e j).1 (e j).2 k).map (algebraMap T.V T.Fr)) (fun i => by simp [constFn])
    (fun j => Chart.comb_baseChange _ m2.cart (a3 (e j).1 (e j).2) hww (hu₂ _ _))
  rw [one_pow, one_mul, hu] at h
  rw [map_mul, map_pow, RingHom.map_det]
  exact h

theorem val_inv_root {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io)
    (ho : ∀ a, io a ∈ (algebraMap T.V T.Fr).range) {ε : Rul Xo c} (hε : ε * ε = ε) (hZ : evI y ε ≠ 0)
    (ρ K : (Rul Xo c)ˣ) {a : c.F} (ha : a ≠ 0) (haK : ε * (ρ : Rul Xo c) ^ 4 = a • (ε * (K : Rul Xo c)))
    (hK : vV T.V (evI y (K : Rul Xo c)) = 0) : vV T.V (evI y (ε * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c))) = 0 := by
  have hid : evI y ε = 1 := mul_left_cancel₀ hZ (by rw [← evI_mul, hε, mul_one])
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hu : ∀ u : (Rul Xo c)ˣ, ev u ≠ 0 := fun u => (u.isUnit.map ev).ne_zero
  have ha' : io a ≠ 0 := (map_ne_zero io).2 ha
  have hio : vV T.V (io a) = 0 := by
    have h1 := (mem_range_iff T _).1 (ho a)
    have h2 := (mem_range_iff T _).1 (ho a⁻¹)
    have h3 := vV_mul (V := T.V) ha' ((map_ne_zero io).2 (inv_ne_zero ha))
    rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    omega
  have h1 : ev ρ ^ 4 = io a * ev K := by
    have h := congrArg (evI y) haK
    rw [evI_smul, evI_mul, evI_mul, hid, one_mul, one_mul] at h
    exact (map_pow ev _ 4).symm.trans h
  have h2 := congrArg (vV T.V) h1
  rw [vV_mul ha' (hu K), hio, show vV T.V (ev K) = 0 from hK,
    show vV T.V (ev ρ ^ 4) = 4 * vV T.V (ev ρ) by simp [vV]] at h2
  have h3 := vV_mul (V := T.V) (hu ρ) (hu ρ⁻¹)
  rw [← map_mul, Units.mul_inv, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
  rw [evI_mul, hid, one_mul]
  change vV T.V (ev _) = 0
  omega

end Key

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.KeyRootTw in

theorem twSec_keyRoot_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) →
    FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) →
    ∀ Z : Comp Xo c, ∃ t : TwSec U x Z (wtOf Dw 0 1), ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
      (∀ a, io a ∈ (algebraMap T.V T.Fr).range) → evI y (idem Z) ≠ 0 → vV T.V (evI y t.sig) = 0 := by
  intro E _ _ _ H Dw l Xo c r U x hU hx hF hpq hg
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨⟨ρ, hρmem⟩, hρ⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := GlobalTheory.T.theta_key_section_valuation_bounds_different κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨⟨ρ, hρmem⟩⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) := by
    simp [Fintype.card_sigma]
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 1) = -keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  have hadd : wtOf Dw 0 1 + wtOf Dw 0 (-1) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  intro Z
  obtain ⟨a, ha, haK⟩ := hρ Z
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  set s : Rul Xo c := idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * (ρ : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 1)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hρmem)
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-1))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hρmem
    have h2 : exZ Dw (wtOf Dw 0 (-1)) = keyEx Dw := by
      have h3 := exZ_add_eq (Dw := Dw) (wtOf Dw 0 1) (wtOf Dw 0 (-1))
      rw [hadd, hex] at h3
      have h4 : exZ Dw (0 : WTZ E) = 0 := by funext i; cases i <;> rfl
      rw [h4] at h3
      exact (neg_add_eq_zero.1 h3.symm).symm
    rwa [zero_add, ← h2] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hnorm := fun σ : c.F →+* ℂ => fun z (hz : z ∈ framesOn (U (goodOf c σ)) Z) =>
    homN_root E H Dw l Xo c (goodOf c σ) r (U (goodOf c σ)) x Z ρ K a (C σ) ha (hCpos σ) haK (hCeq σ) z hz
      ((hP.1 σ).2 z hz)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 1) s z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-1)) s' z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ ((1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hbnd := fun w (v : Rul Xo c → EReal) (hv : v ∈ valOn Z w) =>
    val_root E H Dw l Xo c Z w v hv ρ K a (B w) ha haK (hval w v (valOn_subset Z w hv)).1
      (hval w v (valOn_subset Z w hv)).2
  let t : TwSec U x Z (wtOf Dw 0 1) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by
        have h5 := exZ_neg_eq (Dw := Dw) (wtOf Dw 0 1)
        have h6 : -wtOf Dw 0 1 = wtOf Dw 0 (-1) := neg_eq_of_add_eq_zero_right hadd
        rw [← h5, h6]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, idem_mul_idem]
      idem_inv := by rw [hs', ← mul_assoc, idem_mul_idem]
      mul_inv := by rw [hs, hs', mul_mul_mul_comm, idem_mul_idem, Units.inv_mul, mul_one]
      cInf := fun σ => (‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)
      cInf_pos := fun σ => Real.rpow_pos_of_pos (mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) (hCpos σ)) _
      norm_inf := fun σ z hz => by
        rw [(hnorm σ z hz).1, norm_goodOf]
      cusp_sig := fun G hG f hf =>
        GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 1) s ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono 1) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 (-1)) s' ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono (-1))
          hsm' hsupp' hbd' (G + wtOf Dw 0 1) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun w => -(vAdd w a : ℝ) / 4 - B w
      hi := fun w => -(vAdd w a : ℝ) / 4
      lo_le := fun w v hv => (hbnd w v hv).1
      le_hi := fun w v hv => (hbnd w v hv).2
      finite_lo := by
        refine ((finite_vAdd ha).union (Set.finite_iUnion fun τ => finite_ord (embF c τ))).subset fun w hw => ?_
        by_contra hn
        simp only [Set.mem_union, Function.mem_support, Set.mem_iUnion, not_or, not_exists, not_not] at hn
        apply hw
        simp [B, hn.1, hn.2]
      finite_hi := by
        refine (finite_vAdd ha).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, not_not] at hn
        apply hw
        simp [hn]
      pts := hP }
  refine ⟨t, fun T io y ho hZ => ?_⟩
  letI := io.toAlgebra
  obtain ⟨Φ, hΦ, hK0⟩ := exists_tied_unit hkr hpq hg e ho y.1 y.2.2
  rw [← hKval T.Fr y.1 Φ hΦ] at hK0
  exact val_inv_root y ho (idem_mul_idem Z) hZ ρ K ha haK hK0

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in

theorem key_val_zero : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) 0 1), vV T.V (evI y' t.sig) = 0 := by
  intro _ h2 _ _
  refine h2.imp fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, -⟩ := h
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY Z TF y T io y' g _ hpt hZ => ?_⟩
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  obtain ⟨t, ht⟩ := twSec_keyRoot_val _ _ _ _ _ _ _ Y.U (xiR (Fm.D x ι)) hY.1.unf hY.1.xiAbs hY.1.geo hL.pos hL.good Z
  refine ⟨t, ht T io y' (fun a => ?_) hZ⟩
  letI := io.toAlgebra
  have h1 := ptY_str TF.X y'.1
  rw [hpt, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc] at h1
  obtain ⟨b, hb⟩ := Spec.map_surjective
    (Spec.map (CommRingCat.ofHom g) ≫ ((Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ≫ flagStr TF.X)
  rw [← hb, ← Spec.map_comp] at h1
  exact ⟨b.hom a, congrArg (fun q => CommRingCat.Hom.hom q a) (Spec.map_injective h1)⟩

end GlobalTheory.KeyValZero
