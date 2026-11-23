import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Counterexamples.UniqueMatching.ExistsUniqueMatch

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcExt

theorem exists_ramified_ext (T : CDVR) {Ω : Type} [Field Ω] [Algebra T.Fr Ω] [Algebra.IsAlgebraic T.Fr Ω] [IsAlgClosed Ω]
    (M : IntermediateField T.Fr Ω) [FiniteDimensional T.Fr M] (N : ℕ) (hN : 0 < N) (ϖ₀ : T.V) (h₀ : Irreducible ϖ₀) :
    ∃ (T' : CDVR) (g : T.V →+* T'.V) (κ : M →+* T'.Fr) (e : ℕ) (ϖ : T'.V),
      Function.Injective g ∧ IsLocalHom g ∧ Irreducible ϖ ∧
      (∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap T'.V T'.Fr (g v)) ∧
      N ∣ e ∧ Associated (g ϖ₀) (ϖ ^ e) := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap T.Fr Ω (algebraMap T.V T.Fr ϖ₀)) hN
  let A := IntermediateField.adjoin T.Fr ({α} : Set Ω)
  have : FiniteDimensional T.Fr A := IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let L : IntermediateField T.Fr Ω := M ⊔ A
  have : FiniteDimensional T.Fr L := inferInstance
  obtain ⟨W, _, _, _, _, _, _, _, hc, -, hinj, hloc, -, -⟩ := GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  have : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  have hψ : ∀ w : W, ψ (algebraMap W L w) = algebraMap W (FractionRing W) w := fun w =>
    (FractionRing.algEquiv W L).symm.commutes w
  let κ : M →+* FractionRing W := ψ.toRingHom.comp (IntermediateField.inclusion (le_sup_left : M ≤ L)).toRingHom
  have hκ : ∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap W (FractionRing W) (algebraMap T.V W v) := by
    intro v
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr v) = algebraMap W L (algebraMap T.V W v) :=
      (RingHom.congr_fun hc v).symm
    rw [← hψ, ← h1]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hg0 : algebraMap T.V W ϖ₀ ≠ 0 := fun h => h₀.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hϖ
  have hαL : α ∈ L := (le_sup_right : A ≤ L) (IntermediateField.mem_adjoin_simple_self T.Fr α)
  let b : FractionRing W := ψ ⟨α, hαL⟩
  have hb : b ^ N = algebraMap W (FractionRing W) (algebraMap T.V W ϖ₀) := by
    have h1 : (⟨α, hαL⟩ : L) ^ N = algebraMap W L (algebraMap T.V W ϖ₀) := by
      apply Subtype.ext
      have h2 := RingHom.congr_fun hc ϖ₀
      refine hα.trans ?_
      exact (congrArg (L.val) h2.symm)
    rw [← hψ, ← h1, map_pow]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hN.ne'] at hb
    exact hg0 ((IsFractionRing.injective W (FractionRing W)) (by rw [← hb, map_zero]))
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := W) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hxy, map_zero, zero_div])
  obtain ⟨m, v₁, hv₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨n, v₂, hv₂⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hW : x ^ N = algebraMap T.V W ϖ₀ * y ^ N := by
    apply IsFractionRing.injective W (FractionRing W)
    have hy' : algebraMap W (FractionRing W) y ≠ 0 := by
      simpa using hy0
    rw [map_pow, map_mul, map_pow, ← hb, ← hxy, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hy')]
  have he : m * N = e + n * N := by
    rw [hv₁, hv₂, hu, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at hW
    have : ((v₁ ^ N : Wˣ) : W) * ϖ ^ (m * N) = ((u * v₂ ^ N : Wˣ) : W) * ϖ ^ (e + n * N) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hW, pow_add]
      ring
    exact IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ _ _ _ _ this
  refine ⟨T', algebraMap T.V W, κ, e, ϖ, hinj, hloc, hϖ, hκ, ?_, ?_⟩
  · have : N ∣ e + n * N := ⟨m, by rw [← he, mul_comm]⟩
    exact (Nat.dvd_add_left (Dvd.intro_left n rfl)).1 this
  · exact ⟨u⁻¹, by
      show algebraMap T.V W ϖ₀ * ((u⁻¹ : Wˣ) : W) = ϖ ^ e
      rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩

theorem hasVal_eq_of_unit_mul_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {a : V} {n : ℤ} {m : ℕ} (w : Vˣ) (ha : a = w * ϖ ^ m) (h : HasVal ϖ (algebraMap V (FractionRing V) a) n) : n = m := by
  obtain ⟨u, hu⟩ := h
  have h0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have hu0 : algebraMap V (FractionRing V) (u : V) ≠ 0 := by simp
  have hw0 : algebraMap V (FractionRing V) (w : V) ≠ 0 := by simp
  rw [ha, map_mul, map_pow] at hu
  rcases le_total n m with hnm | hnm
  · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hnm)
    have e1 : (m : ℤ) = n + d := by omega
    have : ((u : V)) = (w : V) * ϖ ^ d := by
      apply IsFractionRing.injective V (FractionRing V)
      have e2 : algebraMap V (FractionRing V) ϖ ^ m = algebraMap V (FractionRing V) ϖ ^ n * algebraMap V (FractionRing V) ϖ ^ d := by
        rw [← zpow_natCast, e1, zpow_add₀ h0, zpow_natCast]
      rw [e2] at hu
      have h3 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 := zpow_ne_zero _ h0
      rw [map_mul, map_pow]
      apply mul_left_cancel₀ h3
      rw [← hu]; ring
    have hd0 : d = 0 := by
      by_contra hd0
      have : IsUnit (ϖ ^ d) := by
        have h4 : IsUnit ((w : V) * ϖ ^ d) := this ▸ u.isUnit
        exact isUnit_of_mul_isUnit_right h4
      exact hϖ.not_isUnit (isUnit_pow_iff hd0 |>.1 this)
    omega
  · obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hnm)
    have e1 : n = (m : ℤ) + d := by omega
    have : (w : V) = ϖ ^ d * (u : V) := by
      apply IsFractionRing.injective V (FractionRing V)
      have e2 : algebraMap V (FractionRing V) ϖ ^ n = algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) ϖ ^ d := by
        rw [e1, zpow_add₀ h0, zpow_natCast, zpow_natCast]
      rw [e2] at hu
      have h3 : algebraMap V (FractionRing V) ϖ ^ m ≠ 0 := pow_ne_zero _ h0
      rw [map_mul, map_pow]
      apply mul_left_cancel₀ h3
      rw [mul_comm _ (algebraMap V (FractionRing V) (w : V)), hu]; ring
    have hd0 : d = 0 := by
      by_contra hd0
      have : IsUnit (ϖ ^ d) := by
        have h4 : IsUnit (ϖ ^ d * (u : V)) := this ▸ w.isUnit
        exact isUnit_of_mul_isUnit_left h4
      exact hϖ.not_isUnit (isUnit_pow_iff hd0 |>.1 this)
    omega

theorem dvd_bOf_of_pull {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (g : V →+* V') {D : DegData V (maximalIdeal V)} {D' : DegPre V'}
    (hD : IsPullDeg g D.toPre D') {ϖ₀ : V} (h₀ : Irreducible ϖ₀) {ϖ : V'} (hϖ : Irreducible ϖ) {e : ℕ}
    (he : Associated (g ϖ₀) (ϖ ^ e)) (Q : D'.X → ℤ) (hQ : QForm.IsQ D' ϖ Q) (u v : D'.X) :
    (e : ℤ) ∣ QForm.bOf D' Q u v := by
  have key : ∀ χ : D'.X, ∃ n : ℕ, Q χ = e * n := by
    intro χ
    obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre (hD.xe χ)).2
      (GlobalTheory.PeriodFormCompare.psiIn_top D (hD.xe χ))
    have hr0 : r ≠ 0 := GlobalTheory.PsiCoordLocal.ne_zero_of_coord hr
    obtain ⟨s, hs⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD χ r hr
    have hv := GlobalTheory.ValForm.hasVal_coord (hQ χ) hs
    obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 h₀
    obtain ⟨c, hc⟩ := he
    have hgw : IsUnit (g (w : V)) := (w.isUnit).map g
    obtain ⟨w', hw'⟩ := hgw
    have e1 : (s : V') * g r = ((s * w' * (c⁻¹) ^ m : V'ˣ) : V') * ϖ ^ (e * m) := by
      have h1 : g ϖ₀ = ϖ ^ e * ((c⁻¹ : V'ˣ) : V') := by
        rw [← hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      rw [hw, map_mul, map_pow, h1, ← hw', mul_pow, ← pow_mul]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    exact ⟨m, by exact_mod_cast (hasVal_eq_of_unit_mul_pow hϖ _ e1 hv)⟩
  choose n hn using key
  have h1 : QForm.bOf D' Q u v = e * (n (u + v) - n u - n v) := by
    simp only [QForm.bOf, hn]; ring
  exact ⟨_, h1⟩

section Level

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isCN_cdvr (T : CDVR) : IsCN T.V := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem isGrpPullback_gen {V : Type} [CommRing V] [IsDomain V] {Z : Scheme.{0}} {I : Ideal V} {t : SAB H (Sp V)}
    {G : Over Z} [GrpObj G] {y : Sp V ⟶ Z} {φ : t.G.left ⟶ G.left} (h : IsGrpPullback t.G G y φ) (P : PELUnif I t) :
    IsGrpPullback P.A.A G (jK V ≫ y) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V) ≫ φ) := by
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  exact ((isGrpPullback_of_iso P.U.gen.symm).comp ((isGrpPullback_pullback t.G (jK V)).comp h)).congr
    (Category.id_comp _) rfl

theorem isGrpPullback_gen₀ {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} (P : PELUnif I t) :
    IsGrpPullback P.A.A t.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) := by
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK V))).congr (Category.id_comp _) rfl

theorem exists_torsion_pt (Y : Model Xo c β) {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {y : Sp V ⟶ Y.X}
    {z : Sp (FractionRing V) ⟶ Xo.XF c} (hz : z ≫ Y.j = jK V ≫ y) {t : SAB H (Sp V)} (m : SABMap t Y.t y)
    (P : PELUnif I t) {k : ℕ} {σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G} (hσ : σ ^ k = 1) :
    ∃ ξ : 𝟙_ (Over (Sp (FractionRing V))) ⟶ P.A.A, ξ ^ k = 1 ∧
      ξ.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V) ≫ m.φ = z ≫ σ.left ≫ Y.m.φ := by
  have gpG := isGrpPullback_gen m.cart P
  have gpO : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := by
    have := Y.m.cart
    have hb := Y.m.base
    exact this
  have hw : (z ≫ σ.left ≫ Y.m.φ) ≫ Y.t.G.hom = 𝟙 _ ≫ jK V ≫ y := by
    have e₁ : σ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σ
    rw [Category.assoc, Category.assoc, gpO.1.w, reassoc_of% e₁, Category.id_comp, hz]
  let x₀ := gpG.1.lift _ _ hw
  have hx₀ : x₀ ≫ P.A.A.hom = 𝟙 _ := gpG.1.lift_snd _ _ _
  let ξ : 𝟙_ (Over (Sp (FractionRing V))) ⟶ P.A.A := Over.homMk x₀ hx₀
  have hξ : ξ.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V) ≫ m.φ = z ≫ σ.left ≫ Y.m.φ := gpG.1.lift_fst _ _ _
  refine ⟨ξ, ?_, hξ⟩
  let T₀ : Over (Xo.XF c) := Over.mk z
  let σ₀ : T₀ ⟶ Y.oF.t.G := toUnit T₀ ≫ σ
  have hσ₀ : σ₀ ^ k = 1 := by
    rw [← MonObj.comp_pow, hσ, MonObj.comp_one]
  let U : Over.mk ((𝟙_ (Over (Sp (FractionRing V)))).hom ≫ jK V ≫ y) ⟶ Over.mk (T₀.hom ≫ Y.j) :=
    Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ z ≫ Y.j = (𝟙_ (Over (Sp (FractionRing V)))).hom ≫ jK V ≫ y
      rw [hz, Category.id_comp]
      exact (Category.id_comp _).symm)
  have e₁ : pushHom gpG _ ξ = U ≫ pushHom gpO T₀ σ₀ := Over.OverMorphism.ext (by
    show ξ.left ≫ _ = 𝟙 _ ≫ (toUnit T₀ ≫ σ).left ≫ Y.m.φ
    have hu : (toUnit T₀).left = z := (Category.comp_id _).symm.trans (Over.w (toUnit T₀))
    rw [hξ, Category.id_comp, Over.comp_left, hu, Category.assoc])
  have e₂ : pushHom gpG _ (ξ ^ k) = pushHom gpG _ 1 := by
    rw [map_pow, e₁, ← MonObj.comp_pow, ← map_pow, hσ₀, map_one, MonObj.comp_one, map_one]
  refine Over.OverMorphism.ext (gpG.1.hom_ext (congrArg (fun q => q.left) e₂) ?_)
  exact (Over.w (ξ ^ k)).trans (Over.w (1 : _ ⟶ P.A.A)).symm

end Level

theorem map_nsmul_of_add {A G : Type} [AddCommGroup A] [Group G] (f : A → G) (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ)
    (a : A) : f (n • a) = f a ^ n :=
  congrArg Additive.toMul (map_nsmul (AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) hf) n a)

theorem natCast_M_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h

theorem eta_pow_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (v : D.La) :
    o.eta v ^ l.M = 1 := by
  rw [← map_nsmul_of_add o.eta o.eta_add]
  refine o.eta_ker _ ?_
  have h : (l.M : 𝓞 E) • v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top
  rwa [Nat.cast_smul_eq_nsmul] at h

theorem etaA_pow_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (v : D.La) :
    o.etaA v ^ l.A = 1 := by
  rw [← map_nsmul_of_add o.etaA o.etaA_add]
  exact o.etaA_ker v

theorem exists_algHom_of_isAlgebraic (M Ω F : Type) [Field M] [Field Ω] [Field F] [Algebra M Ω] [Algebra M F] [IsAlgClosed F]
    [Algebra.IsAlgebraic M Ω] : Nonempty (Ω →ₐ[M] F) := ⟨IsAlgClosed.lift⟩

section Level2

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

set_option maxHeartbeats 1600000 in

theorem levelRep_pull (Y : Model Xo c β) [Mono (spMap β)] (T T' : CDVR) (g : T.V →+* T'.V) {y : Sp T.V ⟶ Y.X}
    {z : Sp T.Fr ⟶ Xo.XF c} (hz : z ≫ Y.j = jK T.V ≫ y) {t : SAB H (Sp T.V)} (m : SABMap t Y.t y)
    (P : PELUnif (maximalIdeal T.V) t) (hP : P.TorsionIso) {t' : SAB H (Sp T'.V)}
    (P' : PELUnif (maximalIdeal T'.V) t') (hP' : P'.TorsionIso) (hD : IsPullDeg g P.D.toPre P'.D.toPre)
    (bc : t'.G ≅ (Over.pullback (specOf g)).obj t.G) (mbc : IsMonHom bc.hom) (hU : IsPullUnif g hD bc P.U P'.U)
    (m' : SABMap t' Y.t (spMap g ≫ y)) (hm' : m'.φ = bc.hom.left ≫ pullback.fst t.G.hom (specOf g) ≫ m.φ)
    {Ω : Type} [Field Ω] [Algebra T.Fr Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic T.Fr Ω]
    (M : IntermediateField T.Fr Ω) (κ : M →+* T'.Fr)
    (hκ : ∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap T'.V T'.Fr (g v))
    {k : ℕ} (hk : 1 ≤ k)
    (hM : ∀ q : QkPt P.D.toPre Ω k, ∃ z₀ : QkPt P.D.toPre M k,
      qkExt P.D.tau_bimult M.val.toRingHom (val_comp M) z₀ = q)
    {σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G} (hσ : σ ^ k = 1) :
    LevelRep Y (spMap g ≫ y) t' m' P' k σ := by
  obtain ⟨hL, -⟩ := GlobalTheory.allSixLaws
  have hG := hL.globalFns
  have hB := P.D.tau_bimult
  have hB' := P'.D.tau_bimult
  have aR := admissibleBase_of_completeNormalLocalCharZero (isCN_cdvr T)
  have aR' := admissibleBase_of_completeNormalLocalCharZero (isCN_cdvr T')
  have := GlobalTheory.ArcTieProbe.mono_j Y
  obtain ⟨ξ, hξk, hξ⟩ := exists_torsion_pt Y hz m P hσ
  let xΩ : TFK (R := T.V) Ω ⟶ P.A.A := toUnit _ ≫ ξ
  have hxΩ : xΩ ^ k = 1 := by rw [← MonObj.comp_pow, hξk, MonObj.comp_one]
  obtain ⟨fΩ, hfΩ, honto, -⟩ := hP Ω k hk
  obtain ⟨p, hp⟩ := honto xΩ hxΩ
  have hpA : P.ToA Ω k p xΩ := (hfΩ p xΩ).2 hp.symm
  obtain ⟨z₀, rfl⟩ := hM p
  let f : T.Fr →+* T'.Fr := κ.comp (algebraMap T.Fr M)
  letI : Algebra T.Fr T'.Fr := f.toAlgebra
  have hK : Compat g T'.Fr := hκ
  have hκ' : κ.comp (algebraMap T.Fr M) = algebraMap T.Fr T'.Fr := rfl
  let q₁ := qkExt hB κ hκ' z₀
  let r := pullQk hD hG hK hB hB' q₁
  refine ⟨r, fun F _ _ _ yF hyF q x hq hx => ?_⟩
  letI aKF : Algebra T.Fr F := ((algebraMap T'.Fr F).comp f).toAlgebra
  letI aMF : Algebra M F := ((algebraMap T'.Fr F).comp κ).toAlgebra
  haveI : IsScalarTower T.Fr M F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := T.Fr) M
  obtain ⟨ιF⟩ := exists_algHom_of_isAlgebraic M Ω F
  letI aΩF : Algebra Ω F := ιF.toRingHom.toAlgebra
  have hιM : ∀ a : M, algebraMap Ω F (a : Ω) = algebraMap M F a := fun a => ιF.commutes a
  haveI : IsScalarTower T.Fr Ω F := IsScalarTower.of_algebraMap_eq fun a => (hιM (algebraMap T.Fr M a)).symm
  have hF : Compat g F := fun v => congrArg (algebraMap T'.Fr F) (hκ v)
  have h₀ : (algebraMap Ω F).comp (algebraMap T.Fr Ω) = algebraMap T.Fr F := (IsScalarTower.algebraMap_eq _ _ _).symm
  let pF := qkExt hB (algebraMap Ω F) h₀ (qkExt hB M.val.toRingHom (val_comp M) z₀)
  have hpF : QkExt (algebraMap Ω F) (qkExt hB M.val.toRingHom (val_comp M) z₀) pF := (qkExt_iff hB _ h₀ _ _).2 rfl
  have h₂ : QkToAkU P.U.toUnifPre F k pF (GlobalTheory.TorsionExt.fieldMap Ω F ≫ xΩ) :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hG hL.kerPow P.U hk hpF xΩ).1 hpA
  have h₄ : (algebraMap T'.Fr F).comp (algebraMap T.Fr T'.Fr) = algebraMap T.Fr F := rfl
  have e₁ : QkExt (algebraMap T'.Fr F) q₁ pF := (qkExt_iff hB _ h₄ _ _).2 (qk_ext rfl (by
    have h₅ : (algebraMap T'.Fr F).comp κ = (algebraMap Ω F).comp M.val.toRingHom :=
      RingHom.ext fun a => (hιM a).symm
    have h₆ : ((algebraMap T'.Fr F).comp κ).comp (algebraMap T.Fr M) = algebraMap T.Fr F := rfl
    exact (gtExt_gtExt _ (val_comp M) _ h₀ _ h₆ h₅.symm _).trans
      (gtExt_gtExt _ hκ' _ h₄ _ h₆ rfl _).symm))
  have hsq : jFK (R := T'.V) F ≫ jK T'.V ≫ spMap g = jFK (R := T.V) F ≫ jK T.V := by
    show spMap (algebraMap T'.Fr F) ≫ spMap (algebraMap T'.V T'.Fr) ≫ spMap g =
      spMap (algebraMap T.Fr F) ≫ spMap (algebraMap T.V T.Fr)
    rw [← spMap_comp, ← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun v => (hF v).symm)
  obtain ⟨f', hf', -⟩ := hP' F k hk
  have h₁ : P'.ToA F k q (f' q) := (hf' q _).2 rfl
  haveI := mbc
  have gΨ : IsGrpPullback t'.G t.G (specOf g) (bc.hom.left ≫ pullback.fst t.G.hom (specOf g)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback t.G (specOf g))).congr (Category.id_comp _) rfl
  have gA' := isGrpPullback_gen gΨ P'
  have gA := isGrpPullback_gen₀ P
  let w : Sp F ⟶ t.G.left := (f' q).left ≫ P'.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK T'.V) ≫ bc.hom.left ≫
    pullback.fst t.G.hom (specOf g)
  have hw : w ≫ t.G.hom = jFK (R := T.V) F ≫ jK T.V := by
    have e := gA'.1.w
    simp only [Category.assoc] at e
    simp only [w, Category.assoc]
    rw [e, ← Category.assoc, Over.w (f' q)]
    exact hsq
  let x₃ : TFK (R := T.V) F ⟶ P.A.A := Over.homMk (gA.1.lift w (jFK (R := T.V) F) hw) (gA.1.lift_snd _ _ _)
  have hx₃ : x₃.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK T.V) = w := gA.1.lift_fst _ _ _
  have h₃ : QkToAkU P.U.toUnifPre F k pF x₃ :=
    GlobalTheory.qkToAk_of_baseChange hG hL.secBaseChange T.V T'.V _ _ aR aR' g P.D P.A t.G P.U t'.G bc mbc P'.A P'.D hD P'.U hU F hF
      k hk pF x₃ q (f' q) hq.1 (isPullGtF_ext hD hF (algebraMap T'.Fr F) (RingHom.comp_id _)
        (isPullGtF_pullGt hD hG hK q₁.g) e₁ hq) hx₃.symm h₁
  obtain ⟨fF, hfF, -⟩ := hP F k hk
  have e₃ : x₃ = GlobalTheory.TorsionExt.fieldMap Ω F ≫ xΩ := ((hfF pF _).1 h₃).trans ((hfF pF _).1 h₂).symm
  have hyF' : yF = jFK (R := T.V) F ≫ z := by
    rw [← cancel_mono Y.j, hyF, Category.assoc, hz, reassoc_of% hsq]
  have e₄ : x₃.left = jFK (R := T.V) F ≫ ξ.left := by
    rw [e₃]
    have : GlobalTheory.TorsionExt.fieldMap Ω F ≫ xΩ = toUnit _ ≫ ξ := by
      show GlobalTheory.TorsionExt.fieldMap Ω F ≫ toUnit _ ≫ ξ = _
      rw [← Category.assoc, toUnit_unique (GlobalTheory.TorsionExt.fieldMap Ω F ≫ toUnit _) (toUnit _)]
    rw [this, Over.comp_left]
    exact congrArg (· ≫ ξ.left) ((Category.comp_id _).symm.trans (Over.w (toUnit (TFK (R := T.V) F))))
  have gp' := isGrpPullback_gen m'.cart P'
  have hxx : x = f' q := by
    refine Over.OverMorphism.ext (gp'.1.hom_ext ?_ ((Over.w x).trans (Over.w (f' q)).symm))
    refine hx.trans ?_
    have e₅ : (f' q).left ≫ P'.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK T'.V) ≫ m'.φ = w ≫ m.φ := by
      rw [hm']; simp only [w, Category.assoc]
    refine Eq.trans ?_ e₅.symm
    rw [← hx₃, e₄, hyF']
    simp only [Category.assoc]
    rw [hξ]
  exact (hf' q x).2 hxx

end Level2
section Main

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

set_option maxHeartbeats 1600000 in

theorem exists_ext_levelReps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Mono (spMap β) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), P.TorsionIso → ∃ (T' : CDVR) (g : T.V →+* T'.V) (ϖ : T'.V) (io' : c.F →+* T'.Fr) (z' : Sp T'.Fr ⟶ Xo.XF c) (t' : SAB H (Sp T'.V)) (m' : SABMap t' Y.t (spMap g ≫ y)) (P' : PELUnif (maximalIdeal T'.V) t'), Function.Injective g ∧ IsLocalHom g ∧ Irreducible ϖ ∧ (algebraMap T'.V T'.Fr).comp (g.comp b) = io'.comp β ∧ z' ≫ pullback.snd _ _ = spMap io' ∧ z' ≫ Y.j = spMap (algebraMap T'.V T'.Fr) ≫ spMap g ≫ y ∧ P'.TorsionIso ∧ (∀ Q : P'.D.toPre.X → ℤ, ReciprocityTheory.ChartRestriction.G.DVR.QForm.IsQ P'.D.toPre ϖ Q → ∀ u v, (2 * l.M' : ℤ) ∣ ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf P'.D.toPre Q u v) ∧ GlobalTheory.ArcExt.LevelReps Y (spMap g ≫ y) t' m' P' := by
  intro E _ _ _ H D l Xo c O _ β Y hβ T io b y z h1 h2 h3 h4 t m P hP
  obtain ⟨hL, -, hL3, hL4, hL5, -⟩ := GlobalTheory.allSixLaws
  haveI := hβ
  have hB := P.D.tau_bimult
  haveI : CharZero T.Fr := algebraRat.charZero _
  have hM0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  obtain ⟨M, hMf, HM⟩ := exists_finite_qk (D := P.D.toPre) (L := AlgebraicClosure T.Fr) hL hB (N := l.M')
    (Nat.cast_ne_zero.2 hM0)
  obtain ⟨ϖ₀, h₀⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨T', g, κ, e, ϖ, hg, hl, hϖ, hκ, hN, he⟩ := exists_ramified_ext T M (2 * l.M') (by omega) ϖ₀ h₀
  have aR := admissibleBase_of_completeNormalLocalCharZero (isCN_cdvr T)
  have aR' := admissibleBase_of_completeNormalLocalCharZero (isCN_cdvr T')
  have hI : (maximalIdeal T.V).map g ≤ maximalIdeal T'.V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff g a).2 ha
  obtain ⟨t', m₀, P', hD, bc, mbc, hU, hm₀, -, -⟩ :=
    GlobalTheory.ArcDataDescent.exists_pelUnif_pull hL3.cubePull hL.polBaseChange hL4.unifBaseChange hL5 aR aR' t P g hg hI
  have hP' := GlobalTheory.FlatTors.torsionIso_holds E H T'.V _ aR' t' P'
  obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_comp m m₀
  have hm'' : m'.φ = bc.hom.left ≫ pullback.fst t.G.hom (specOf g) ≫ m.φ := by
    rw [hm', hm₀, Category.assoc]
  let f : T.Fr →+* T'.Fr := κ.comp (algebraMap T.Fr M)
  have hf : f.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp g := RingHom.ext hκ
  have hsq : spMap (algebraMap T'.V T'.Fr) ≫ spMap g = spMap f ≫ spMap (algebraMap T.V T.Fr) := by
    rw [← spMap_comp, ← spMap_comp, hf]
  refine ⟨T', g, ϖ, f.comp io, spMap f ≫ z, t', m', P', hg, hl, hϖ, ?_, ?_, ?_, hP', ?_, ?_, ?_⟩
  · refine RingHom.ext fun x => ?_
    have e₁ := RingHom.congr_fun h1 x
    have e₂ := RingHom.congr_fun hf (b x)
    simp only [RingHom.comp_apply] at e₁ e₂ ⊢
    rw [← e₂, e₁]
  · rw [Category.assoc, h3]
    exact (spMap_comp io f).symm
  · rw [Category.assoc, h4, ← Category.assoc, ← Category.assoc, hsq]
  · intro Q hQ u v
    have h := dvd_bOf_of_pull g hD h₀ hϖ he Q hQ u v
    exact dvd_trans (by exact_mod_cast hN) h
  · exact fun v => levelRep_pull Y T T' g h4 m P hP P' hP' hD bc mbc hU m' hm'' M κ hκ l.A_pos
      (fun q => HM _ (Nat.dvd_lcm_right _ _) q) (etaA_pow_eq_one Y.oF v)
  · exact fun v _ => levelRep_pull Y T T' g h4 m P hP P' hP' hD bc mbc hU m' hm'' M κ hκ
      (by have := l.three_le; omega) (fun q => HM _ (Nat.dvd_lcm_left _ _) q) (eta_pow_eq_one Y.oF v)

end Main

end GlobalTheory.ArcExt
