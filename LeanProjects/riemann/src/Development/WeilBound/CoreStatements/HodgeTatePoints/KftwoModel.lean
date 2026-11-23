import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels Formalism.L2.Pj

namespace PositivityTheory.HtPt.Kftwo

theorem exists_valuationSubring_two : ∃ W : ValuationSubring ℂ, ((2 : ℕ) : ℂ) ∈ W.nonunits := by
  have h : Ideal.span {(2 : (⊥ : Subring ℂ))} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨⟨b, hb⟩, e⟩ := hu.exists_right_inv
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hb
    have e' : (2 : ℂ) * n = 1 := congrArg Subtype.val e
    have e'' : (2 : ℤ) * n = 1 := by exact_mod_cast e'
    omega
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ h
  exact ⟨W, hW ⟨2, Ideal.mem_span_singleton_self _, (map_ofNat _ 2).trans (by simp)⟩⟩

theorem exists_place (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] {V K : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (io : F →+* K) :
    ∃ (p : ℕ) (W : ValuationSubring ℂ) (b : W.comap F.val.toRingHom →+* V), p.Prime ∧ (p : ℂ) ∈ W.nonunits ∧
      (algebraMap V K).comp b = io.comp (W.comap F.val.toRingHom).subtype := by
  have hinj := IsFractionRing.injective V K
  let U : ValuationSubring F :=
    { (algebraMap V K).range.comap io with
      mem_or_inv_mem' := fun a => by
        have := ValuationRing.isInteger_or_isInteger V (io a)
        rw [← map_inv₀] at this
        exact this }
  obtain ⟨p, W, hp, hW, hle⟩ : ∃ (p : ℕ) (W : ValuationSubring ℂ), p.Prime ∧ (p : ℂ) ∈ W.nonunits ∧
      W.comap F.val.toRingHom ≤ U := by
    by_cases h : ∃ p : ℕ, p.Prime ∧ (p : F) ∈ U.nonunits
    · obtain ⟨p, hp, hpU⟩ := h
      obtain ⟨W, hWe, hWn⟩ := GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits F.val.toRingHom U
      exact ⟨p, W, hp, by simpa using hWn _ hpU, hWe.le⟩
    · obtain ⟨W, hW⟩ := exists_valuationSubring_two
      refine ⟨2, W, Nat.prime_two, hW, fun a _ => ?_⟩
      have hn : ∀ n : ℕ, (n : F)⁻¹ ∈ U := fun n => by
        induction n using Nat.recOnMul with
        | zero => simp
        | one => simp
        | prime p hp =>
          by_contra hc
          refine h ⟨p, hp, ?_⟩
          rw [ValuationSubring.mem_nonunits_iff_or]
          exact Or.inr hc
        | mul a b ha hb => rw [Nat.cast_mul, mul_inv]; exact U.mul_mem _ _ ha hb
      have hq : ∀ q : ℚ, algebraMap ℚ F q ∈ U := fun q => by
        rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
        exact U.mul_mem _ _ (intCast_mem U _) (hn _)
      let _ : Algebra ℚ U := ((algebraMap ℚ F).codRestrict U.toSubring hq).toAlgebra
      have : IsScalarTower ℚ U F := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hi : IsIntegral U a := (Algebra.IsIntegral.isIntegral (R := ℚ) a).tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
      exact hy ▸ y.2
  let e := RingEquiv.ofBijective (algebraMap V K).rangeRestrict
    ⟨fun a a' h => hinj (congrArg Subtype.val h), (algebraMap V K).rangeRestrict_surjective⟩
  refine ⟨p, W, e.symm.toRingHom.comp ((io.comp (W.comap F.val.toRingHom).subtype).codRestrict (algebraMap V K).range
    fun a => hle a.2), hp, hW, RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem key_unit {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    {T : CDVR} (z : Sp T.Fr ⟶ Xo.XF c) {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)}
    (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _)) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) {n : ℕ}
    {w : Fin n → (epsR T.V ⟶ G.G)} (hw : IsLieBasis w) {θ : G.PP.L.Sec} (hθ : Generates (X := G.G) θ) (k : KeyIn T.Fr)
    (hk : IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr)) :
    ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  classical
  obtain ⟨io, hzs⟩ : ∃ io : c.F →+* T.Fr, spMap io = z ≫ pullback.snd _ _ := ⟨_, Spec.map_preimage _⟩
  have := c.fin
  obtain ⟨p, W, b, hp, hW, hb⟩ := exists_place c.F (V := T.V) io
  have key : ∀ X : ∀ l : Level H, Moduli Dw l, ∃ Y : Model (X l) c (c.V W).subtype,
      Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := fun X => by
    obtain ⟨Y, hY, -⟩ := GlobalTheory.partI_closed.2 E H Dw hpq X
    obtain ⟨h1, h2⟩ := hY p W hp hW
    obtain ⟨h3, h4, h5⟩ := h2 ⟨l, c, hg p hp⟩
    exact ⟨_, h1.1 ⟨l, c, hg p hp⟩, h4, h5, h3⟩
  have h := key (Function.update (fun l' => Classical.choice (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l' hpq)) l Xo)
  rw [Function.update_self] at h
  obtain ⟨Y, h2, h3, h4, h5⟩ := h
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, ← hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) hb.symm
  obtain ⟨yt, h1, -⟩ := extPt Y T b z hx
  obtain ⟨tP, ⟨mP'⟩⟩ : ∃ t : SAB H (Sp T.V), Nonempty (SABMap t Y.t yt) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap m1
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP t' yt (Out.jK T.V) mP' (PullbackSections.sabMapCast mJ hj)
  have hprop : IsProper t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G tP t' hprop m2 mK
  obtain ⟨n', -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP G yt (𝟙 _) mP' ψ
  exact (((GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels κ hκ E H Dw l Xo c _ _ Y p hpq (isBaseRing_local c W) hp h2 h3 h4 h5).1 T.V T.Fr z yt h1 G
    (PullbackSections.sabMapCast n' (Category.id_comp yt)) n w hw θ k hk).1 hθ).1

end PositivityTheory.HtPt.Kftwo
