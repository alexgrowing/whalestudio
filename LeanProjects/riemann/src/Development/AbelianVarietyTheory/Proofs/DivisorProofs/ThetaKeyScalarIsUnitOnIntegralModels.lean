import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeyInputAtChartPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPoleOfBounded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalAtOfUnif
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendOfIntegralAtDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfUnitBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFlatValuationSubringBaseRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcPropertyLocalisationBaseChangeOfModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitFibresLocalisedModelBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitThetaKeyRuleOpenModelChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitThetaKeyScalarGoodReductionChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFibrePowerAndExternalTensorSectionNonzeroCloStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineSectionsExternalTensorPowerFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRigidifiedSectionOfScalarMultiplStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfArcsAndGoodReductionPointsStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyUnitModels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

open GlobalTheory.FlagMod (ev_res ev_spMap le_preimage_mono)

theorem norm_bounds {κ : KeyRule} (hκ : IsKeyRule κ) (x : KeyIn ℂ) {τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c₀ : ℂ} (hab : GlobalTheory.KeyPow.charHalf _ a b) (hc : c₀ ≠ 0)
    (hN : GlobalTheory.KeyPow.NormalAt x τ Mx a b c₀) {C : ℝ} (hC : 0 < C) (h₁ : C⁻¹ ≤ ‖Mx.det‖ / ‖c₀‖ ^ 2)
    (h₂ : ‖Mx.det‖ / ‖c₀‖ ^ 2 ≤ C) : ‖(κ ℂ x : ℂ)‖ ≤ C ^ 4 ∧ ‖(κ ℂ x : ℂ)⁻¹‖ ≤ C ^ 4 := by
  have hr : 0 < ‖Mx.det‖ / ‖c₀‖ ^ 2 := (inv_pos.2 hC).trans_le h₁
  have hM : Mx.det ≠ 0 := fun h0 => by simp [h0] at hr
  obtain ⟨P, hg, rig, hrig, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN₀, e₁, hMv⟩ := GlobalTheory.KeyConst.exists_rescale P hg rig hrig th hth v hv τ Mx _ _ c₀ hc hM hN
  obtain ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩ := (GlobalTheory.KeyPow.normalAt_one_iff _ _ _ _).1 hN₀
  have e := hκ.1 ℂ P hg rig hrig _ hth₀ v₀ hv₀ th hth v hv c₀ Mx e₁ hMv
  rw [hκ.2.2.2.1 ⟨P, hg, rig, hrig, th₀, hth₀, v₀, hv₀⟩ u τ a b k₁ k₂ hab.1 hab.2 k₃ k₄ k₅ k₆, Units.val_one,
    _root_.mul_one] at e
  have q : 0 < ‖c₀‖ := norm_pos_iff.2 hc
  have e' : ‖(κ ℂ ⟨P, hg, rig, hrig, th, hth, v, hv⟩ : ℂ)‖ = (‖Mx.det‖ / ‖c₀‖ ^ 2) ^ 4 := by
    have := congrArg (‖·‖) e
    simp only [norm_mul, norm_pow] at this
    rw [div_pow, ← pow_mul, eq_div_iff (by positivity), ← this, _root_.mul_comm]
  constructor
  · rw [e']
    gcongr
  · rw [norm_inv, e', ← inv_pow]
    gcongr
    exact inv_le_of_inv_le₀ hC h₁

theorem countable_sections {X : Scheme.{0}} {O : Type} [CommRing O] [Countable O] (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {U : X.Opens} (hU : IsAffineOpen U) : Countable Γ(X, U) := by
  have hf : (s.appLE ⊤ _ le_top).hom.FiniteType :=
    (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨_, hU⟩ le_top)
  letI := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp O, ⊤) Γ(X, U) := hf
  have hc : Countable Γ(Sp O, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.symm.injective.countable
  obtain ⟨n, f, hfs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  have : Countable (MvPolynomial (Fin n) Γ(Sp O, ⊤)) :=
    (MvPolynomial.basisMonomials (Fin n) Γ(Sp O, ⊤)).repr.injective.countable
  exact hfs.countable

theorem exists_chart_unit {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (M : GChart Y) : ∃ u : Γ(Y.X, M.U), IsUnit u ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X)
      (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), Set.range z ⊆ Set.range Y.j → KeyAt M z hz x → (κ K x : K) = ev z M.U hz u := by
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, hopen⟩ := GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W
  have := Y.jQ_open
  have hj : IsOpenImmersion Y.j := by unfold Model.j; infer_instance
  obtain ⟨-, -, -, -, -, hdom, -⟩ := GlobalTheory.genericPart_dense_proOpen W c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have hdense : Dense (Set.range Y.j) := hdom.denseRange
  obtain ⟨W₀, f₀, hW, hf⟩ := GlobalTheory.T.exists_unit_thetaKeyRule_open_model_chart E H D l Xo c _ _ Y inferInstance hj hpq κ hκ M
  have hcF : Countable c.F := by
    have := c.fin
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F
    rw [← Cardinal.mk_le_aleph0_iff]
    simpa [Cardinal.mkRat] using this
  have : Countable W := Subtype.val_injective.countable
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := M.dom
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ := IsTotallyComplex.finrank E
    have h₂ : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact Nat.mul_pos (by omega) hpq
  have hWU : W₀ ≤ M.U := fun x hx => ((hW x).1 hx).1
  have hWj : ∀ {K : Type} [Field K] {z : Sp K ⟶ Y.X}, ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := fun hz => by
    rintro _ ⟨q, rfl⟩; exact ((hW _).1 (hz (Set.mem_univ q))).2
  have hne : ∃ x, x ∈ W₀ := by
    obtain ⟨q⟩ : Nonempty (Sp Γ(Y.X, M.U)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
    obtain ⟨x, hx, hx'⟩ := hdense.exists_mem_open M.U.isOpen ⟨_, tau_le M.hU le_rfl (Set.mem_univ q)⟩
    exact ⟨x, (hW x).2 ⟨hx', hx⟩⟩
  obtain ⟨hinj, hext⟩ := GlobalTheory.GenExt.extend_of_integral_at_dvr _ _ W₀ hWU M.hU M.dom
    (IsLocallyNoetherian.component_noetherian ⟨_, M.hU⟩) (GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen M.hU)
    (countable_sections Y.s M.hU) hne
  have key : ∀ u : Γ(Y.X, W₀), (u = f₀.val ∨ u = (f₀⁻¹).val) → ∃ f, resG _ hWU f = u := by
    intro u hu
    refine hext u fun R K _ _ _ _ _ _ z hR hz h => ?_
    let y := IsOpenImmersion.lift Y.j (spMap (algebraMap R K) ≫ z) (hWj h)
    have : CharZero K := charZero_of_injective_ringHom (Spec.preimage (y ≫ pullback.snd _ _)).hom.injective
    refine GlobalTheory.T.integral_of_arcs_and_goodReduction_points E H D l Xo c W Y h3 h4 hs hj M.U W₀ u (fun x hx hx' => (hW x).2 ⟨hx, hx'⟩)
      (fun a χ hA hover hgen hχ => ?_) (fun R K _ _ _ _ _ _ _ z y hz hy hab h => ?_) R K z y hR hz
      (IsOpenImmersion.lift_fac _ _ _) h
    · obtain ⟨y, hy, T, C', hC', hT⟩ := GlobalTheory.ArcNormal.arc_normal_form _ _ _ _ _ _ _ Y hpq hP a χ hA hover hgen M hχ
      refine GlobalTheory.ArcReg.not_pole_of_bounded _ M.U W₀ u χ y M.hU hWU hχ hy ⟨T, C' ^ 4, fun w hw hyw => ?_⟩
      obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (y w) (le_preimage_mono hWU hyw) (hWj hyw) hpos
      obtain ⟨τ, Mx, a', b', c₀, k₁, k₂, k₃, k₄, k₅⟩ := hT w hw _ x hk
      obtain ⟨b₁, b₂⟩ := norm_bounds hκ x k₁ k₂ k₃ hC' k₄ k₅
      have e := hf ℂ (y w) hyw _ x hk
      rcases hu with rfl | rfl
      · rwa [e]
      · rwa [map_units_inv, e]
    · obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M _ (le_preimage_comp _ hz) (hWj h) hpos
      obtain ⟨v, hv⟩ := GlobalTheory.T.isUnit_thetaKeyScalar_goodReduction_chart E H D l Xo c _ _ Y κ hκ M R K z hz y hy hab x hk
      have e := hf K _ h _ x hk
      rcases hu with rfl | rfl
      · exact ⟨v, by rw [e, hv]⟩
      · exact ⟨(v⁻¹ : Rˣ), by rw [map_units_inv, map_units_inv, e, hv]⟩
  obtain ⟨f, hf₁⟩ := key _ (Or.inl rfl)
  obtain ⟨f', hf₂⟩ := key _ (Or.inr rfl)
  refine ⟨f, IsUnit.of_mul_eq_one f' (hinj ?_), fun K _ _ z hz x hr hk => ?_⟩
  · exact ((RingHom.map_mul _ f f').trans ((congrArg₂ (· * ·) hf₁ hf₂).trans f₀.mul_inv)).trans (RingHom.map_one _).symm
  · have hz₀ : ⊤ ≤ z ⁻¹ᵁ W₀ := fun q hq => (hW _).2 ⟨hz hq, hr ⟨q, rfl⟩⟩
    rw [← hf K z hz₀ _ x hk, ← hf₁, ev_res z hWU hz₀ hz]

theorem lieComb_one {K : Type} [Field K] (x : KeyIn K) (i : Fin x.P.g) :
    IsLieComb ((1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i) x.v (x.v i) := by
  have : (1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i = Pi.single i 1 := by
    ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this]
  have := x.P.isAb.comm
  exact (GlobalTheory.LieComb.lieComb_algebra _ _ _ x.v x.basis.1).2.2.2.1 i

theorem unitAt_local {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] :
    UnitAt κ Y V K := by
  intro y yt hyt t m n w hw θ x hx
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, -⟩ := GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W
  obtain ⟨M, hM⟩ := GlobalTheory.FlagMod.exists_gChart hP (yt (IsLocalRing.closedPoint V))
  have hz : ⊤ ≤ yt ⁻¹ᵁ M.U := ((IsLocalRing.closed_point_mem_iff (U := yt ⁻¹ᵁ M.U)).1 hM).ge
  obtain ⟨u, hu, hval⟩ := exists_chart_unit Y hpq hP h3 h4 hs hκ M
  have := t.semi.smooth
  obtain ⟨θ₀, h₀⟩ : ∃ θ₀ : t.PP.L.Sec, NonzeroClosed (X := t.G) θ₀ := by
    obtain ⟨-, θ₀, -, -, hne⟩ := GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne
    obtain ⟨g, i, h₁, h₂⟩ := hne (IsLocalRing.closedPoint V)
    exact ⟨θ₀, g, h₁, TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  have hC : ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) →
      Generates (X := t.G) θ → ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := fun θ x hx hθ => by
    obtain ⟨x', a, d, hk, e⟩ := GlobalTheory.T.exists_generatingFrame_unit_change_to_chart E H D l Xo c _ _ Y M V K yt hz t m n w hw θ x hx hθ
    have e₁ := e κ hκ
    rw [hval K _ _ x' (by
      rw [hyt]; rintro _ ⟨q, rfl⟩; exact ⟨y q, (Scheme.Hom.comp_apply _ _ _).symm⟩) hk,
      ev_spMap (algebraMap V K) yt M.U hz, RingHom.comp_apply] at e₁
    refine ⟨(d ^ 4)⁻¹ * (a ^ 8 * (hu.map (ev yt M.U hz)).unit), ?_⟩
    have hd : algebraMap V K d ≠ 0 := (d.isUnit.map _).ne_zero
    rw [Units.val_mul, map_mul, map_units_inv, Units.val_mul, map_mul, IsUnit.unit_spec, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, map_pow, map_pow, e₁, inv_mul_cancel_left₀ (pow_ne_zero _ hd)]
  have hB : ∀ (θ : t.PP.L.Sec), Generates (X := t.G) θ → ∀ N : ℕ, Generates (X := pow t.G N) (boxSec t.G θ N) :=
    fun θ' hθ N => by
      obtain ⟨a, ha, -⟩ := hθ θ₀
      obtain ⟨hfl, g, hg, hnz⟩ := GlobalTheory.T.flat_fibrePower_and_externalTensorSection_nonzero_closedFibre V t.G t.PP.L θ' (NonzeroClosed.of_isMul ha h₀).2 N
      obtain ⟨X', p', φ, L', b, k₁, k₂, k₃, k₄⟩ := GlobalTheory.T.exists_line_sections_externalTensorPower_fibre V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx N
      exact generates_of_generic_line (pow t.G N).hom k₁ (LB.isLB_linComb t.PP.isLB _ _) k₂ k₃ b k₄ _ hg hnz
  refine ⟨fun hθ => ⟨hC θ x hx hθ, fun N _ => hB θ hθ N⟩, ?_⟩
  intro N hN σ a hσ hmul
  have hg₀ := generates_of_isFibreOf t.PP.isLB hx h₀
  obtain ⟨b, hθb, -⟩ := hg₀ θ
  obtain ⟨th₀, hth₀, hth, hx₀⟩ := GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx θ₀ b hθb
  obtain ⟨u₀, hu₀⟩ := hC θ₀ _ hx₀ hg₀
  have hbox₀ := hB θ₀ hg₀ N
  have hom := hκ.1 K x.P x.g_pos x.rig x.rig_gen th₀ hth₀ x.v x.basis x.th x.th_ne x.v x.basis (algebraMap V K b) 1
    hth (lieComb_one x)
  rw [Matrix.det_one, one_pow, _root_.one_mul] at hom
  obtain ⟨c', hc', -⟩ := hσ (boxSec t.G θ₀ N)
  have hcu : IsUnit c' := Generates.isUnit hσ hbox₀ hc'
  have ha : a = b ^ N * c' := (hσ (boxSec t.G θ N)).unique hmul (IsMul.trans (isMul_boxSec hθb N) hc')
  obtain ⟨k, rfl⟩ := hN
  refine ⟨hcu.unit * u₀ ^ k, ?_⟩
  rw [ha, Nat.mul_div_cancel_left k (by norm_num : 0 < 8)]
  simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [← hu₀, ← hom, pow_mul]
  ring

theorem unitAt_valuation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (hpq : 1 ≤ D.p + D.q)
    (hβ : IsBaseRing β) (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule}
    (hκ : IsKeyRule κ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] : UnitAt κ Y V K := by
  intro y yt hyt t m
  have hinj := IsFractionRing.injective V K
  have sp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B),
      spMap f ≫ spMap g = spMap (f.comp g) := fun _ _ => (Spec.map_comp _ _).symm
  obtain ⟨io, hio⟩ : ∃ io : c.F →+* K, spMap io = y ≫ pullback.snd _ _ := ⟨_, Spec.map_preimage _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : O →+* V, spMap b₀ = yt ≫ Y.s := ⟨_, Spec.map_preimage _⟩
  have hc : (algebraMap V K).comp b₀ = io.comp β := by
    have e : spMap ((algebraMap V K).comp b₀) = spMap (io.comp β) := by
      rw [← sp, ← sp, hb₀, hio, ← Category.assoc, hyt, Model.j, Category.assoc, Category.assoc, Category.assoc,
        pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let W : ValuationSubring c.F :=
    { (algebraMap V K).range.comap io with
      mem_or_inv_mem' := fun a => by
        have := ValuationRing.isInteger_or_isInteger V (io a)
        rw [← map_inv₀] at this
        exact this }
  let b : O →+* W := β.codRestrict W.toSubring fun a => ⟨b₀ a, RingHom.congr_fun hc a⟩
  have hb : W.subtype.comp b = β := rfl
  let e := RingEquiv.ofBijective (algebraMap V K).rangeRestrict
    ⟨fun a a' h => hinj (congrArg Subtype.val h), (algebraMap V K).rangeRestrict_surjective⟩
  let b' : W →+* V := e.symm.toRingHom.comp ((io.comp W.subtype).codRestrict (algebraMap V K).range fun a => a.2)
  have hb' : b'.comp b = b₀ := RingHom.ext fun a => by
    apply e.injective
    exact (e.apply_symm_apply _).trans (Subtype.ext (RingHom.congr_fun hc a).symm)
  obtain ⟨_, _⟩ := GlobalTheory.T.isPreimmersion_flat_valuationSubring_baseRing E H l c O β hβ W b hb
  let yt' : Sp V ⟶ (locModel Y b hb).X := pullback.lift yt (spMap b') (by rw [sp, hb', hb₀])
  have hy' : yt' ≫ pullback.fst Y.s (spMap b) = yt := pullback.lift_fst _ _ _
  obtain ⟨m', -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := yt') (locMap Y b) (hy'.symm ▸ m)
  exact unitAt_local (locModel Y b hb) hpq (locModel_pushInvertible Y b hb (GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W).1 hP) (localisedModel_uniformisation_baseChange Y b hb h3)
    (GlobalTheory.T.arcProperty_localisationBaseChange_of_model E H D l Xo c O β Y _ _ b hb h4) (GlobalTheory.T.splitFibres_localisedModel_baseChange E H D l Xo c O β Y _ _ b hb hs) hκ V K y yt' (by
      rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, Category.assoc, hy', locModel_j, hyt]) t m'

theorem keyUnitOnModels : KeyUnitOnModels := by
  intro κ hκ E _ _ _ H D l Xo c O _ β Y p h₁ h₂ _ h₄ h₅ h₆ h₇
  refine ⟨fun V K _ _ _ _ _ _ _ _ => unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V K, fun V C _ _ _ _ _ _ _ hV => ?_⟩
  obtain ⟨_, _, _⟩ := GlobalTheory.GoodRedUnitBall.valuationRing_of_unitBall hV
  exact unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V C

end GlobalTheory.KeyUnitModels
