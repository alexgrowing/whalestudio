import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleIsUnitAtBadLevelPlaceStatement

noncomputable section

namespace GlobalTheory.KeyValAny

section Model

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_model_at (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q)
    (la : HeightOneSpectrum (𝓞 c.F)) {p : ℕ} (hp : p.Prime) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hgp : l.GoodAt p) :
    ∃ (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype),
      c.V W = (la.valuation c.F).valuationSubring ∧ Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := by
  classical
  obtain ⟨W, hWe, hWn⟩ := GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom
    (la.valuation c.F).valuationSubring
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]
    have := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl
    simpa using this
  have hW : (p : ℂ) ∈ W.nonunits := by simpa using hWn _ hpU
  have key : ∀ X : ∀ l : Level H, Moduli Dw l, ∃ Y : Model (X l) c (c.V W).subtype,
      Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := fun X => by
    obtain ⟨Y, hY, -⟩ := GlobalTheory.partI_closed.2 E H Dw hpq X
    obtain ⟨h1, h2⟩ := hY p W hp hW
    obtain ⟨h3, h4, h5⟩ := h2 ⟨l, c, hgp⟩
    exact ⟨_, h1.1 ⟨l, c, hgp⟩, h4, h5, h3⟩
  have h := key (Function.update (fun l' => Classical.choice (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l' hpq)) l Xo)
  rw [Function.update_self] at h
  obtain ⟨Y, hY⟩ := h
  exact ⟨W, Y, hWe, hY⟩

theorem key_unit_at {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q)
    {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} (hp : p.Prime) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hgp : l.GoodAt p)
    {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    {x : Sp T.Fr ⟶ Xo.X} (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) {n : ℕ} {w : Fin n → (epsR T.V ⟶ G.G)} (hw : IsLieBasis w)
    {θ : G.PP.L.Sec} (hθ : Generates (X := G.G) θ) (k : KeyIn T.Fr)
    (hk : IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr)) :
    ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  obtain ⟨W, Y, hW, h2, h3, h4, h5⟩ := exists_model_at Xo c hpq la hp hpl hgp
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (β := (c.V W).subtype)
    (fun a => (Valuation.mem_valuationSubring_iff _ _).1 (hW ▸ a.2)) T io e ho
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

end Model

end GlobalTheory.KeyValAny

noncomputable section

namespace GlobalTheory.KeyValAny

section Any

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem key_unit_any {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q)
    {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    {x : Sp T.Fr ⟶ Xo.X} (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) {n : ℕ} {w : Fin n → (epsR T.V ⟶ G.G)} (hw : IsLieBasis w)
    {θ : G.PP.L.Sec} (hθ : Generates (X := G.G) θ) (k : KeyIn T.Fr)
    (hk : IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr)) :
    ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  obtain ⟨p, hp, hpl⟩ := GlobalTheory.Reg.exists_prime_natCast_mem la
  by_cases hgp : l.GoodAt p
  · exact key_unit_at hκ hpq hp hpl hgp ho hxs m1 m2 hw hθ k hk
  · exact GlobalTheory.T.thetaKeyRule_isUnit_at_bad_level_place E H Dw l Xo c κ hκ hpq la p hp hpl hgp T io e ho x hxs G t' m1 m2 n w hw θ hθ k hk

theorem exists_tied_det_any {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q)
    {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {r : ℕ} (ho : OverLa la T.V io r)
    (τ' : (E →+* ℂ) → (𝓞 E →+* T.V)) (hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a))
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (hy : Integral T io y) :
    letI := io.toAlgebra
    ∃ (Φ : FibKey Xo T.Fr y.x) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T.V)
      (U : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin g → T.V) (u : T.Vˣ), Tied e y.s y.u Φ ∧
      (∀ τ (x : Fin g → T.V), (∀ a, (A a).mulVec x = τ' τ a • x) →
        ∃ cf : Fin (Dw.mult τ) → T.V, x = ∑ k, cf k • U τ k) ∧
      (∀ τ k a, (A a).mulVec (U τ k) = τ' τ a • U τ k) ∧
      (κ T.Fr Φ.key : T.Fr) =
        algebraMap T.V T.Fr ((Matrix.of fun j k => U (e j).1 (e j).2 k).det ^ 4 * (u : T.V)) := by
  letI := io.toAlgebra
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
  obtain ⟨u, hu⟩ := key_unit_any hκ hpq ho y.x_over m1 m2 hw hθ _
    (isFibreOf_of_sabMap _ P m2 hgp hne r2 i2 hp hw' hww)
  refine ⟨⟨P, m1, hgp, σ, hne, v, hv⟩, A, U, u, ⟨ht, rfl, fun j => hu₁ _ _⟩, a1, a2, ?_⟩
  have h := hκ.1 T.Fr P.pol hgp P.t.PP.rig P.t.PP.rigGen σ hne w' hw' σ hne v hv 1
    ((Matrix.of fun j k => U (e j).1 (e j).2 k).map (algebraMap T.V T.Fr)) (fun i => by simp [constFn])
    (fun j => Chart.comb_baseChange _ m2.cart (a3 (e j).1 (e j).2) hww (hu₂ _ _))
  rw [one_pow, one_mul, hu] at h
  rw [map_mul, map_pow, RingHom.map_det]
  exact h

end Any

section Main

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open GlobalTheory.KeyIntegralVal

theorem key_valuation_nonneg : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : (Rul Xo c)ˣ), 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ GlobalTheory.AllWt.secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) := by
  intro κ hκ E _ _ _ H Dw l Xo c g e K hpq _ hK w v hv
  classical
  obtain ⟨⟨_, T, io, r, ho, y, -, η, -, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  choose τ' hτ using fun τ : E →+* ℂ => GlobalTheory.EtaVal.exists_base_map_of_overLa (β := embK c τ)
    (fun a => w.valuation_le_one (K := c.F) (RingOfIntegers.mapRingHom (embF c τ) a)) T io r ho
  replace hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a) := fun τ a => DFunLike.congr_fun (hτ τ) a
  have hinj : Function.Injective τ' := fun τ₁ τ₂ h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a =>
      congrArg Subtype.val (io.injective ((hτ τ₁ a).symm.trans ((h ▸ rfl : _ = _).trans (hτ τ₂ a)))))
  obtain ⟨Φ, A, U, u, hΦ, a1, a2, hu⟩ := exists_tied_det_any hκ hpq e ho τ' hτ y.1 y.2.2
  choose δ hδ hδ0 hδv using fun τ : E →+* ℂ => exists_mem_different_vLa (embF c τ) w
  have hD := GlobalTheory.ColengthDifferent.colength_dvd E T.Fr T.V (E →+* ℂ) τ' Dw.mult g e A U hinj (Embeddings.card E ℂ) inferInstance a1 a2 δ hδ
  have hb := nval_bounds ho (fun τ => embF c τ (δ τ)) (fun τ => τ' τ (δ τ)) Dw.mult _ u
    (fun τ => (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 (hδ0 τ))) (fun τ => hτ τ (δ τ)) hD
  rw [← hu, ← hK T.Fr y.1 Φ hΦ] at hb
  exact hb.1

end Main

end GlobalTheory.KeyValAny
