import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFour
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulPhiLeValuationProductForm
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionIntegralFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSteep

section Tau

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open GlobalTheory.ThetaConst
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in

theorem phiC_le_valuation (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [hcpl : IsAdicComplete (maximalIdeal V) V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V))
    (G : SAB H (Sp V)) (S : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G) (ϖ : V) (hϖ : Irreducible ϖ)
    (Q : P.D.toPre.X → ℤ) (hQ : QForm.IsQ P.D.toPre ϖ Q) (hQ0 : ∀ a, 0 ≤ Q a) (cj : E → E)
    (hcj : ∀ a, cj a = IsCMField.complexConj E a) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X)
    (hβ : ∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) (R : ℕ) (hR : Odd R) (hR1 : 1 < R) (J : Type) [Fintype J] (n : ℕ)
    (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (val : FractionRing V) (hsp : GlobalTheory.EtaAn.Spans xs)
    (hval : TauValAt Xo c R cf xs y val) (hne : val ≠ 0) :
    Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (R : ℝ) ^ 4 ≤ (vV V val : ℝ) := by
  obtain ⟨hLL, h2, h3, h4, h5⟩ := GlobalTheory.lawsAndExpansions
  have hL : Laws := hLL.1
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have htors := GlobalTheory.UT.torsionIso_of_pelUnif hLL h2 h3 h4 h5 E H V _ hA G P
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.T.exists_valuation_algebraicClosure_extending_vV V ϖ hϖ
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra c.F F := ((algebraMap (FractionRing V) F).comp (algebraMap c.F (FractionRing V))).toAlgebra
  let ψ : FractionRing V →ₐ[c.F] F := { algebraMap (FractionRing V) F with commutes' := fun _ => rfl }
  have hψ : ψ.toRingHom = algebraMap (FractionRing V) F := rfl
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c _ F ψ y
  have hzx : z.x = spMap (algebraMap (FractionRing V) F) ≫ y.x := hz.1
  have hR0 : 0 < R := by omega
  have e4 : (R ^ 2) ^ 2 = R ^ 4 := by rw [← pow_mul]
  have hR2 : Odd (R ^ 2) := hR.pow
  obtain ⟨-, hbc, hloc, -⟩ := GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (pow_pos hR0 4)
  obtain ⟨ev, hev'⟩ := exists_isLevOf_geometric Xo c hval.dvd z.x
  have hev : IsFullLev Xo (R ^ 4) z.x ev := hev'.2.1
  have hevt : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := by
    rw [e4]
    exact (hbc F F (RingHom.id F) z.x z.x (𝟙 _) (by simp [spMap]) ev hev).2
  have hevs : ∀ p : ptO Xo z.x ⟶ Xo.univ.t.G, p ^ ((R ^ 2) ^ 2) = 1 → ∃ q, ev q = p := by
    rw [e4]
    exact (hloc F z.x ev hev).1
  have hw := fun q => ((GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR2).1 F z (ev q) (hevt q)).exists
  choose w hw using hw
  have hvalF : algebraMap (FractionRing V) F val = tauExpr cf xs w :=
    TauValAt.map_eq hR ψ hz hval (tauValAt_self hev' hw)
  obtain ⟨Φ, w₀, hN, hact, hint⟩ := GlobalTheory.T.exists_fib_normW_of_intSec E H Dw l Xo c V y G S P
  obtain ⟨th, hth⟩ := GlobalTheory.T.exists_abelianSection_of_universalFibreSection E H Dw l Xo V y.x P.A Φ F z.x hzx z.s
  obtain ⟨ϑ, hϑ, hν⟩ := GlobalTheory.T.exists_expandsF_nuGe_zero_of_intTh V hcpl ϖ hϖ P.D Q hQ F v hv P.A G.G G.semi P.U w₀ hN.1 th
    (hint F ψ z th hψ hz hth)
  obtain ⟨tr, htr, htra⟩ := GlobalTheory.T.exists_mulEquiv_ptO_hom_of_eq_spMap_comp E H Dw l Xo V y.x P.A Φ F z.x hzx
  obtain ⟨pt, hpt, hspan⟩ := GlobalTheory.T.exists_heisenbergLifts_span_latticeClasses E H V G P htors F ((R ^ 2) ^ 2) (pow_pos (pow_pos hR0 2) 2)
    (LatMod Dw (R ^ 4)) (fun a => tr (ev a)) (fun a b => by rw [hev.1, map_mul])
    (fun o a => by rw [hev.2.1]; exact htra _ _ (hact o) _)
    (fun a => by rw [← map_pow, hevt, map_one])
    (fun u hu => by
      obtain ⟨a, ha⟩ := hevs (tr.symm u) (by rw [← map_pow, hu, map_one])
      exact ⟨a, by rw [ha, MulEquiv.apply_symm_apply]⟩)
  have hb : ∀ a (q : ℚ), (∀ χ, q ≤ (Q ((R ^ 2) • χ + (pt a).y) : ℚ) / ((R ^ 2) ^ 2 : ℕ)) →
      (q : WithTop ℚ) ≤ v (w a) := by
    intro a q hq
    obtain ⟨t, ht⟩ := GlobalTheory.T.normalisedThetaConstant_of_universal_origin_value E H Dw l Xo c V y.x P.A Φ F z hzx th hth (R ^ 2) hR2 (ev a) (tr (ev a)) (w a)
      (hevt a) (htr _) (hw a)
    exact GlobalTheory.T.le_valuation_oddLevel_thetaConstant_integralExpansion V hcpl ϖ hϖ P.D Q hQ F v hv P.A G.G G.semi P.U w₀ Φ.ρ hN th ϑ hϑ hν (R ^ 2) hR2 (pt a)
      (tr (ev a)) t (w a) (hpt a) ht q hq
  haveI : Module.Finite ℤ P.D.toPre.X := P.D.toPre.finX
  have hcj1 : ∀ a : 𝓞 E, ∃ a' : 𝓞 E, (a' : E) = cj a := fun a => ⟨H.bar a, by rw [H.bar_eq, hcj]⟩
  have hcj2 : (H.w0 : E) + cj H.w0 = 1 := by
    rw [hcj, ← H.bar_eq, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]; simp
  have key : ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (R : ℝ) ^ 4 → ((1 : ℕ) : ℚ) * q ≤ ((vV V val : ℤ) : ℚ) := by
    intro q hq
    have h := RatBound.le_addVal_prod_sum v (G := Unit) cf (fun _ j b => w (xs j b)) q (fun _ j => by
      refine GlobalTheory.T.le_sum_of_le_phiC_div_sq E cj hcj1 H.w0 hcj2 P.D.toPre.X Q β hβ hQ0 (R ^ 2) (by nlinarith) n
        (fun b => (pt (xs j b)).y) (hspan n (fun b => xs j b) (hsp j)) (fun b => v (w (xs j b)))
        (fun b => hb _) q ?_
      rw [Nat.cast_pow, ← pow_mul]; exact hq)
    rw [Fintype.prod_unique, Fintype.card_unique] at h
    change _ ≤ v (tauExpr cf xs w) at h
    rw [← hvalF, hvv val hne] at h
    exact_mod_cast h
  simpa using mul_le_of_forall_rat_le 1 one_pos _ _ key

theorem tau_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) {φ : ℝ}
    (hφ : GlobalTheory.SlopeRec.HasPhi y φ) {R : ℕ} (hR : Odd R) (hR1 : 1 < R) {J : Type} [Fintype J] {n : ℕ}
    {cf : J → ℤ} {xs : J → Fin n → LatMod Dw (R ^ 4)} (hsp : GlobalTheory.EtaAn.Spans xs) {f : Rul Xo c}
    (hf : IsTauRule Xo c R cf xs f) (hne : evI y f ≠ 0) : φ / (R : ℝ) ^ 4 ≤ (vV T.V (evI y f) : ℝ) := by
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩ := hφ
  obtain ⟨G₀, ⟨I⟩⟩ := (intSec_exists_and_baseChange E H Dw l Xo c).1 T io y
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t I.t' t' y.1.x (𝟙 _) I.m1
    (PullbackSections.sabMapCast m1 (Category.id_comp _).symm)
  obtain ⟨mK, -⟩ := sabComp pullCubComp E H _ _ _ G₀ I.t' t' _ (𝟙 _) I.m2 mF
  have hprop : IsProper t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G G₀ t' hprop m2
    (PullbackSections.sabMapCast mK (Category.id_comp _))
  obtain ⟨S⟩ := intSec_baseChange (RingHom.id T.V) (AlgHom.id c.F T.Fr) y.1 y.1 G₀ G
    (PullbackSections.sabMapCast ψ (Spec.map_id _).symm) I (fun _ => rfl) (FramedBaseChange.refl y.1)
  exact phiC_le_valuation E H Dw l Xo c T.V y.1 G S P ϖ hϖ Q hQ h0 _ (fun _ => rfl) β hβ R hR hR1 J n cf xs _ hsp
    (hf.tauValAt_evR hR y.2.1) hne

end Tau

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

theorem exists_tied_integral {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {T : CDVR} {io : c.F →+* T.Fr} (ho : ∀ a, io a ∈ (algebraMap T.V T.Fr).range)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (hy : Integral T io y) :
    letI := io.toAlgebra
    ∃ (Φ : FibKey Xo T.Fr y.x), Tied e y.s y.u Φ ∧ (κ T.Fr Φ.key : T.Fr) ∈ (algebraMap T.V T.Fr).range := by
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
  refine ⟨⟨P, m1, hgp, σ, hne, v, hv⟩, ⟨ht, rfl, fun j => hu₁ _ _⟩,
    (Matrix.of fun j k => U (e j).1 (e j).2 k).det ^ 4 * (u : T.V), Eq.symm ?_⟩
  have h := hκ.1 T.Fr P.pol hgp P.t.PP.rig P.t.PP.rigGen σ hne w' hw' σ hne v hv 1
    ((Matrix.of fun j k => U (e j).1 (e j).2 k).map (algebraMap T.V T.Fr)) (fun i => by simp [constFn])
    (fun j => Chart.comb_baseChange _ m2.cart (a3 (e j).1 (e j).2) hww (hu₂ _ _))
  rw [one_pow, one_mul, hu] at h
  rw [map_mul, map_pow, RingHom.map_det]
  exact h

variable (Xo c) in

theorem exists_key (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) :
    ∃ K : (Rul Xo c)ˣ, (K : Rul Xo c) ∈ AllWt.secZ Xo c ((4 : ℤ) • keyEx Dw) ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), (∀ a, io a ∈ (algebraMap T.V T.Fr).range) →
        evI y (K : Rul Xo c) ∈ (algebraMap T.V T.Fr).range := by
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := exists_unit_secZ_keyRule κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hkr : IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  refine ⟨K, hKmem, fun T io y ho => ?_⟩
  letI := io.toAlgebra
  obtain ⟨Φ, hΦ, h⟩ := exists_tied_integral hkr hpq hg e ho y.1 y.2.2
  rw [← hKval T.Fr y.1 Φ hΦ] at h
  exact h

end Key

section Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.HSApp

theorem top_le_stalkPt {Y : Scheme.{0}} (y : Y) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (U : Y.Opens)
    (hy : y ∈ U) : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ U := by
  intro s _
  show (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ U
  have h : (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ Set.range (Y.fromSpecStalk y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact h.mem_open U.isOpen hy

theorem evalPt_stalkPt {Y : Scheme.{0}} (y : Y) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (V : Y.Opens)
    (hV : y ∈ V) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ V) (a : Γ(Y, V)) :
    GlobalTheory.TangentOrigin.evalPt (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) V h a = ψ (ger y hV a) := by
  have h1 : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ V := by
    intro s _
    have : Y.fromSpecStalk y s ∈ Set.range (Y.fromSpecStalk y) := ⟨s, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open V.isOpen hV
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp ψ (Y.fromSpecStalk y) _ h1]
  congr 1
  have : (Y.fromSpecStalk y).appLE _ ⊤ h1 ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom =
      Y.presheaf.germ _ y hV := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hV]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk y)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q _) this

theorem val_stalkPt {Y : Scheme.{0}} {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (y : Y) (i : B.ι)
    (hy : y ∈ O) (hi : y ∈ B.U i) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (f : H0 p B O)
    (hO : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ O)
    (hj : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ B.U i) :
    H0.val (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) i hO hj f = ψ (H0.germ i y hy hi f) := by
  rw [H0.val_apply, H0.germ_apply]
  exact evalPt_stalkPt y ψ _ _ _ _

theorem val_congr_pt {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O : T'.Opens} {R : Type}
    [CommRing R] {x x' : Sp R ⟶ T'} (e : x = x') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x' ⁻¹ᵁ O)
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst e; rfl

theorem val_restr_pt {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O O' : T'.Opens}
    (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ T') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O')
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi)
    (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

theorem exists_extension {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] (hN : Geo.Tor.IsNormalScheme Y)
    {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} (hB : B.IsLB) {O : Y.Opens} (hO : (O : Set Y).Nonempty)
    (m : H0 p B O)
    (h : ∀ y : Y, y ∉ O → IsDiscreteValuationRing (Y.presheaf.stalk y) → ∀ (i : B.ι), y ∈ B.U i →
      ∃ (T : CDVR) (g : Y.presheaf.stalk y →+* T.V), IsLocalHom g ∧ Function.Injective g ∧
        ∀ hO hi, H0.val (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ Y.fromSpecStalk y) i hO hi m ∈
          (algebraMap T.V T.Fr).range) :
    ∃ s : H0 p B ⊤, H0.restr le_top s = m := by
  haveI := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : Nonempty O := hO.to_subtype
  obtain ⟨t, ht⟩ := (GlobalTheory.exists_sec_res_eq_iff hB (W := O) (LB.coord_mem m)).2 fun y hy hyO => by
    haveI := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hy
    obtain ⟨i, hi⟩ := exists_chart hB y
    obtain ⟨T, g, hg, hinj, hv⟩ := h y hyO inferInstance i hi
    have hη : ∀ V : Y.Opens, (V : Set Y).Nonempty → genericPoint Y ∈ V := fun V hV =>
      ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
    have hηO := hη O hO
    have hηi := hη (B.U i) ⟨y, hi⟩
    haveI hne : Nonempty (O ⊓ B.U i : Y.Opens) := ⟨⟨genericPoint Y, hηO, hηi⟩⟩
    refine ⟨i, hne, hi, ?_⟩
    have hinj' : Function.Injective ((algebraMap T.V T.Fr).comp g) := (IsFractionRing.injective T.V T.Fr).comp hinj
    let ψ : Y.functionField →+* T.Fr := IsFractionRing.lift hinj'
    have hψ : ∀ a, ψ (algebraMap (Y.presheaf.stalk y) Y.functionField a) = algebraMap T.V T.Fr (g a) :=
      fun a => IsFractionRing.lift_algebraMap hinj' a
    have e : Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ Y.fromSpecStalk y =
        Spec.map (CommRingCat.ofHom (R := Y.presheaf.stalk (genericPoint Y)) ψ) ≫ Y.fromSpecStalk (genericPoint Y) := by
      rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y), ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      exact (hψ a).symm
    have a1 := top_le_stalkPt (genericPoint Y) ψ O hηO
    have a2 := top_le_stalkPt (genericPoint Y) ψ (B.U i) hηi
    have hv' := hv (e ▸ a1) (e ▸ a2)
    rw [val_congr_pt e i _ a1 _ a2, val_stalkPt _ i hηO hηi] at hv'
    change ψ (Y.germToFunctionField (O ⊓ B.U i) (LB.coord m i)) ∈ _ at hv'
    generalize Y.germToFunctionField (O ⊓ B.U i) (LB.coord m i) = q at hv' ⊢
    obtain ⟨b, hb⟩ := hv'
    rcases ValuationRing.isInteger_or_isInteger (Y.presheaf.stalk y) q with hq | ⟨a, ha⟩
    · exact hq
    by_cases hq0 : q = 0
    · exact hq0 ▸ zero_mem _
    have h1 : b * g a = 1 := IsFractionRing.injective T.V T.Fr (by
      rw [map_mul, hb, ← hψ, ha, ← map_mul, mul_inv_cancel₀ hq0, map_one, map_one])
    obtain ⟨u, rfl⟩ : IsUnit a := hg.1 a (IsUnit.of_mul_eq_one_right _ h1)
    exact ⟨(u⁻¹ : _ˣ), by rw [map_units_inv, ha, inv_inv]⟩
  refine ⟨H0.ofSec p ⊤ t, (H0.restr_ofSec _ _).trans (H0.ext_germ fun y hy => ?_)⟩
  obtain ⟨i, hi⟩ := exists_chart hB y
  refine ⟨i, hi, ?_⟩
  rw [H0.germ_ofSec, H0.germ_apply]
  exact (ger_resG _ _ _ _).symm.trans (congrArg _ (ht i))

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

theorem local_injective_of_centred {Y : Scheme.{0}} {y : Y}
    {ν : Valuation (Y.presheaf.stalk y) (WithZero (Multiplicative ℤ))}
    (hν : Centred y ν) (T : CDVR) (g : Y.presheaf.stalk y →+* T.V) (ρ : ℝ) (hρ : 0 < ρ)
    (hval : ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)) :
    IsLocalHom g ∧ Function.Injective g := by
  have key : ∀ a, a ≠ 0 → vV T.V (algebraMap T.V T.Fr (g a)) = 0 → IsUnit a := fun a ha0 ha => by
    by_contra hna
    have h0 : ν a ≠ 0 := fun h => ha0 (hν.2.2 a h)
    have hlog : WithZero.log (ν a) < 0 := by
      simpa using (WithZero.log_lt_log h0 one_ne_zero).2 (hν.2.1 a hna)
    have hv := hval a h0
    rw [ha, Int.cast_zero, mul_zero, neg_eq_zero, Int.cast_eq_zero] at hv
    omega
  refine ⟨⟨fun a ha => key a (fun h => ?_) ?_⟩, (injective_iff_map_eq_zero g).2 fun a ha => ?_⟩
  · rw [h, map_zero] at ha; exact not_isUnit_zero ha
  · obtain ⟨u, hu⟩ := ha
    rw [← hu, vV_unit]
  · by_contra h0
    have := (key a h0 (by simp [ha, vV])).map g
    rw [ha] at this
    exact not_isUnit_zero this

theorem exists_centred {Y : Scheme.{0}} (y : Y) [IsDomain (Y.presheaf.stalk y)]
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] : ∃ ν, Centred y ν :=
  ⟨(IsDiscreteValuationRing.maximalIdeal (Y.presheaf.stalk y)).intValuation,
    fun a => IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ a,
    fun a ha => (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem _ a).2 ha,
    fun a ha => by_contra fun h => IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero _ a h ha⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

open GlobalTheory.ThetaConst GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.AllWt in

theorem exists_rule (hP : Hypotheses2) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (hM : 5 ^ 4 ∣ l.M)
    (Z : Comp Xo c) (s : ∀ τ, FlatSec U x Z τ) :
    ∃ f : secZ Xo c (exOf Dw ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt Dw) 0), f.1 ∈ suppOn Z ∧ f ≠ 0 ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), (∀ a, io a ∈ (algebraMap T.V T.Fr).range) →
        (letI := io.toAlgebra; LiesOn Z y.1) → GlobalTheory.SlopeRec.HasPhi y φ → evI y f.1 ≠ 0 →
          8 * φ / 625 ≤ (vV T.V (evI y f.1) : ℝ) := by
  obtain ⟨K, hK, hKv⟩ := exists_key Xo c hL.pos hL.good
  have h : HasPts U Z := hasPts U hL.pos hL.good hL.unf Z
  have h5 : Odd 5 := by decide
  obtain ⟨x₀, hx₀⟩ := exists_isAdm Dw (R := 5) (by norm_num)
  obtain ⟨u, f, hf, hfZ⟩ := exists_isGenRule_nonzeroOn (Xo := Xo) (c := c) h5 (by norm_num) hM x₀ Z
  refine ⟨⟨thetaOn h s K f, thetaOn_mem_secZ h s hK (IsTauRule.mem_sec h5 hf)⟩, thetaOn_mem_suppOn h s K f,
    fun h0 => ((nonzeroOn_thetaOn_iff h s K f).2 hfZ).ne_zero (congrArg Subtype.val h0), fun T io y φ hio hZ hφ hne => ?_⟩
  letI := io.toAlgebra
  have hid : evI y (idem Z) = 1 := evR_idem hZ y.2.1
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hio0 : ∀ a, a ≠ 0 → vV T.V (io a) = 0 := fun a ha => by
    have h1 := (mem_range_iff T _).1 (hio a)
    have h2 := (mem_range_iff T _).1 (hio a⁻¹)
    have h3 := vV_mul (V := T.V) ((map_ne_zero io).2 ha) ((map_ne_zero io).2 (inv_ne_zero ha))
    rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    omega
  have hs : ∀ τ, ev (s τ).sig ∈ (algebraMap T.V T.Fr).range := fun τ => by
    have h1 := GlobalTheory.T.archimedean_section_integral_frame hP hP.q2 hP.q3 E H Dw l Xo c r U x hL Z τ (ArchSec.ofConst (s τ)) T io y hio0 hZ
    change nval T.V 1 (ev (s τ).sig) = 0 at h1
    by_cases h0 : ev (s τ).sig = 0
    · exact h0 ▸ zero_mem _
    rw [nval_of_ne h0, Nat.cast_one, div_one, EReal.coe_eq_zero, Int.cast_eq_zero] at h1
    exact (mem_range_iff T _).2 h1.ge
  have e : evI y (thetaOn h s K f) = evI y f ^ 8 * (ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q))) := by
    change ev _ = ev f ^ 8 * _
    rw [thetaOn, shift_sig]
    simp only [map_mul, map_pow, map_prod]
    rw [show ev (idem Z) = 1 from hid, one_mul, mul_assoc]
  have hB : ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q)) ∈ (algebraMap T.V T.Fr).range :=
    mul_mem (pow_mem (hKv T io y hio) _) (prod_mem fun τ _ => pow_mem (hs τ) _)
  change evI y (thetaOn h s K f) ≠ 0 at hne
  change _ ≤ (vV T.V (evI y (thetaOn h s K f)) : ℝ)
  rw [e] at hne ⊢
  have hf0 : evI y f ≠ 0 := fun h0 => hne (by rw [h0]; simp)
  have b1 := tau_bound y hφ h5 (by norm_num) (fun _ => hx₀.spans (by norm_num) u) hf hf0
  have b2 : (0 : ℝ) ≤ vV T.V (ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q))) := by
    exact_mod_cast (mem_range_iff T _).1 hB
  rw [vV_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne),
    show vV T.V (evI y f ^ 8) = 8 * vV T.V (evI y f) by simp [vV]]
  push_cast at b1 ⊢
  linarith

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

set_option maxHeartbeats 1000000 in

theorem through_point (y : Y₀ X Z) (T : CDVR) (io : c.F →+* T.Fr) (y' : IntFr Xo c T io)
    (g : (Y₀ X Z).presheaf.stalk y →+* T.V)
    (hpt : letI := io.toAlgebra; X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) :
    (∀ a, io a ∈ (algebraMap T.V T.Fr).range) ∧ (letI := io.toAlgebra; AllWt.LiesOn Z y'.1) ∧
    ⊤ ≤ (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ X Z).fromSpecStalk y) ⁻¹ᵁ U₀ X Z ∧
    ∀ (la : AllWt.Weight Dw) (f : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (j : (L₀ X Z la).ι), y ∈ (L₀ X Z la).U j →
      ∀ hO hj, ∃ u : T.Vˣ, H0.val (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
        (Y₀ X Z).fromSpecStalk y) j hO hj (sec₀ X Z _ f) = algebraMap T.V T.Fr (u : T.V) * evI y' f.1 := by
  letI := io.toAlgebra
  have he : Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) =
      Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hx₀ : X.ptY y'.1 = (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y) ≫ inc₀ X Z := by rw [Category.assoc]; exact hpt
  have hpt' : X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
      (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) := by
    rw [hpt, he, Category.assoc]
  have hOf : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ flagOpen X :=
    GlobalTheory.FlagMod.le_preimage_map (z := X.pt y'.1) X.inc (top_le_inc X) le_top
  have hx' := (X.pt_inc _).trans hx₀
  have hU₀ : ⊤ ≤ (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ X Z).fromSpecStalk y) ⁻¹ᵁ U₀ X Z := by
    have h1 := hOf
    rw [hx', Scheme.Hom.comp_preimage] at h1
    exact h1
  refine ⟨fun a => ?_, ?_, hU₀, fun la f j hj' hO hj => ?_⟩
  · have h1 := ptY_str X y'.1
    rw [hpt', Category.assoc] at h1
    obtain ⟨b, hb⟩ := Spec.map_surjective ((Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ≫ flagStr X)
    rw [← hb, ← Spec.map_comp] at h1
    exact ⟨b.hom a, congrArg (fun q => CommRingCat.Hom.hom q a) (Spec.map_injective h1)⟩
  · rw [← ptY_le_iff X Z, hx₀, Scheme.Hom.comp_preimage]
    intro s _
    exact Subtype.prop ((Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ X Z).fromSpecStalk y) s)
  have hk : inc₀ X Z y ∈ X.F.U (j PUnit.unit) := mem_pull.1 hj'
  have hzV : ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ⁻¹ᵁ
      X.F.U (j PUnit.unit) := by
    have := top_le_stalkPt y g (inc₀ X Z ⁻¹ᵁ X.F.U (j PUnit.unit)) hk
    rw [← Category.assoc, Scheme.Hom.comp_preimage]
    exact this
  have hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j PUnit.unit) := by
    rw [X.pt_inc, hpt']
    exact FlagMod.le_preimage_comp _ hzV
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor y'.1 (j PUnit.unit) hz
  have e2 : evI y' f.1 = (∏ ix, t ix ^ AllWt.exOf Dw la 0 ix).val * H0.val (Spec.map (CommRingCat.ofHom
      ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ X Z).fromSpecStalk y) j hO hj (sec₀ X Z _ f) := by
    refine (evR_eq_val_secOf f hOf hQ ht).trans (congrArg (_ * ·) ?_)
    rw [val_congr_pt hx' _ hOf (hx' ▸ hOf) hz (hx' ▸ hz)]
    exact (H0.val_pull (inc₀ X Z) (le_refl (U₀ X Z)) _ j hO hj _ _ (secOf X _ f)).symm
  have hu := GlobalTheory.T.chartFrame_change_diagonal_units_integral_frame X T io y' _ hpt' (j PUnit.unit) hzV hz Q t hQ ht
  have ex : ∀ ix, ∃ u : T.Vˣ, Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) u = t ix ^ AllWt.exOf Dw la 0 ix := by
    intro ix
    rcases ix with _ | ⟨σ, i⟩
    · exact ⟨1, by rw [FlagMod.exOf_none, zpow_zero, map_one]⟩
    · obtain ⟨u, hu⟩ := hu σ i
      exact ⟨u ^ AllWt.exOf Dw la 0 (some ⟨σ, i⟩), by rw [map_zpow]; congr 1; exact Units.ext hu⟩
  choose uf huf using ex
  have hP : Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) (∏ ix, uf ix) = ∏ ix, t ix ^ AllWt.exOf Dw la 0 ix := by
    rw [map_prod]; exact Finset.prod_congr rfl fun ix _ => huf ix
  refine ⟨(∏ ix, uf ix)⁻¹, ?_⟩
  rw [e2, ← hP, Units.coe_map, ← mul_assoc, MonoidHom.coe_coe, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem mul_mem_vanBd {a b s : AllWt.Weight Dw} (h : a + b = s) (θ : H0 (str₀ X Z) (L₀ X Z a) ⊤)
    {f : H0 (str₀ X Z) (L₀ X Z b) ⊤} (hf : f ∈ vanBd X Z b) : ((common₀ X Z).addChart h).mul θ f ∈ vanBd X Z s := by
  intro y hy i hi
  obtain ⟨t, ha, hb, hc⟩ := ((common₀ X Z).addChart h).cover y
  rw [H0.germ_change i _ y _ hi hc, ProdChart.germ_mul _ _ _ t y _ ha hb hc]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hf y hy _ hb))

variable {X} in
set_option maxHeartbeats 1000000 in

theorem exists_section (hP : Hypotheses2) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : FlatCore.Laws U x)
    (hM : 5 ^ 4 ∣ l.M) (TF : TorFlag Xo c) (s : ∀ τ, FlatLine.FlatSec U x Z τ)
    (hdeg : ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ) :
    ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt Dw)) ⊤, θ ≠ 0 ∧
      ∀ (y : Y₀ TF.X Z) ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ j hj (m : ℤ),
        ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          8 * φ / 625 ≤ (m : ℝ) := by
  obtain ⟨f, hfZ, hf0, hf⟩ := exists_rule hP hL hM Z s
  obtain ⟨hs, -, hc⟩ := GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hL.geo
  haveI := hs
  haveI := hc
  haveI : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (FlagTan.dimFlag Dw) _
  haveI := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  haveI : IsLocallyNoetherian (Y₀ TF.X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ TF.X Z)
  have hN : Geo.Tor.IsNormalScheme (Y₀ TF.X Z) := fun y => by
    obtain ⟨_, _⟩ := TF.X.normal (inc₀ TF.X Z y)
    let e := (asIso ((inc₀ TF.X Z).stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  obtain ⟨θ, hθ⟩ := exists_extension hN (isLB_L₀ TF.X Z _) (dense_U₀ TF.X Z).nonempty (sec₀ TF.X Z _ f)
    fun y hy _ j hj => by
      obtain ⟨ν, hν⟩ := exists_centred y
      obtain ⟨_, -, T, io, y', g, ρ, φT, hρ, hφT, -, hpt, hval⟩ := hdeg y hy ν hν
      obtain ⟨g1, g2⟩ := local_injective_of_centred hν T g ρ hρ hval
      refine ⟨T, g, g1, g2, fun hO hi => ?_⟩
      obtain ⟨a1, a2, -, a4⟩ := through_point TF.X Z y T io y' g hpt
      obtain ⟨u, hu⟩ := a4 _ f j hj hO hi
      rw [hu]
      refine mul_mem ⟨_, rfl⟩ ?_
      by_cases h0 : evI y' f.1 = 0
      · exact h0 ▸ zero_mem _
      have b1 := hf T io y' φT a1 a2 hφT h0
      have b2 := hφT.nonneg
      refine (mem_range_iff T _).2 ?_
      have : (0 : ℝ) ≤ vV T.V (evI y' f.1) := by linarith
      exact_mod_cast this
  refine ⟨θ, fun h0 => hf0 (eq_zero_of_sec₀ TF.X Z hfZ (by rw [← hθ, h0, map_zero])), fun y ν hν φ hφ j hj m hm => ?_⟩
  obtain ⟨T, io, y', g, ρ, φT, hρ, hφT, rfl, hpt, hval⟩ := hφ
  obtain ⟨-, g2⟩ := local_injective_of_centred hν T g ρ hρ hval
  obtain ⟨a1, a2, a3, a4⟩ := through_point TF.X Z y T io y' g hpt
  have hi := top_le_stalkPt y ((algebraMap T.V T.Fr).comp g) _ hj
  obtain ⟨u, hu⟩ := a4 _ f j hj a3 hi
  rw [← hθ, val_restr_pt le_top _ j (top_le_stalkPt y _ ⊤ (memTop y)), val_stalkPt y j (memTop y) hj,
    RingHom.comp_apply] at hu
  have hne : ν (H0.germ j y (memTop y) hj θ) ≠ 0 := hm ▸ WithZero.coe_ne_zero
  have hg0 : algebraMap T.V T.Fr (g (H0.germ j y (memTop y) hj θ)) ≠ 0 := fun h => hne (by
    rw [(injective_iff_map_eq_zero _).1 g2 _ ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective T.V T.Fr) _ h),
      map_zero])
  have hv := hval _ hne
  rw [hu] at hg0 hv
  rw [hm, vV_mul (left_ne_zero_of_mul hg0) (right_ne_zero_of_mul hg0), vV_unit, zero_add,
    show WithZero.log ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = -m from rfl] at hv
  have b1 := mul_le_mul_of_nonneg_left (hf T io y' φT a1 a2 hφT (right_ne_zero_of_mul hg0)) hρ.le
  push_cast at hv
  linarith

end Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem four_le_expL {L : ℝ} (hL : 10 ≤ L) : 4 ≤ expL L := by
  refine le_expL ?_
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  push_cast
  linarith

set_option maxHeartbeats 2000000 in

theorem exists_theta_section : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))) ⊤, θ ≠ 0 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ f ∈ space TF.X Z Y.U (la - ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))), ((common₀ TF.X Z).addChart (add_sub_cancel ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i)) la)).mul θ f ∈ space TF.X Z Y.U la) ∧ ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ (j : (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).ι) (hj : y ∈ (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).U j) (m : ℤ), ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → 8 * φ / 625 ≤ (m : ℝ) := by
  intro h1 h2 h3 h4
  refine (((GlobalTheory.T.centred_point_phi_positive h1 h2 h3 h4).and h4).and (GlobalTheory.CovTop.Sizes.hostN 0)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C, hC, x0, hx0⟩, ⟨C₁, -, x1, hx1⟩⟩, ⟨C₂, -, x2, hx2⟩⟩ := h
  refine ⟨C, hC, max x0 (max x1 x2), fun x hx hle ι p hp i hi Y hY Z TF => ?_⟩
  have l0 : x0 ≤ x := (le_max_left _ _).trans hle
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hdeg := hx0 x hx l0 ι p hp i hi Y hY Z TF
  have hfl := hx1 x hx l1 ι p hp i hi Y hY
  have hnum := hx2 x hx l2 ι p hp i
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  have hM : 5 ^ 4 ∣ Y.d.l₂.M := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    exact Dvd.dvd.mul_left ((pow_dvd_pow_of_dvd (by norm_num) 4).trans (pow_dvd_pow 15 (four_le_expL hnum.big.2.1))) _
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have := hnum.f8
    have := hnum.deg
    omega
  obtain ⟨θ, hθ, hb⟩ := exists_section Z h1 hL hM TF (fun τ => (hfl Z τ).1.some) hdeg
  exact ⟨θ, hθ, fun la _ f hf' => vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF la
    (mul_mem_vanBd TF.X Z _ θ ((GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _).space_le hf')),
    fun y _ ν hν φ hφ j hj m hm => hb y ν hν φ hφ j hj m hm⟩

end GlobalTheory.ThetaSteep
