import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcFrame

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mem_V_of_forall (W : ValuationSubring ℂ) (h : ∀ p : ℕ, p.Prime → (p : ℂ) ∉ W.nonunits) (x : c.F) :
    x ∈ c.V W := by
  have hv1 : ∀ n : ℕ, n ≠ 0 → W.valuation (n : ℂ) = 1 := by
    intro n hn
    induction n using Nat.recOnMul with
    | zero => exact absurd rfl hn
    | one => simp
    | prime p hp =>
      refine le_antisymm ((W.valuation_le_one_iff _).2 (natCast_mem W p)) (not_lt.1 fun hlt => h p hp ?_)
      exact (W.mem_nonunits_iff).2 hlt
    | mul a b iha ihb =>
      have ha : a ≠ 0 := left_ne_zero_of_mul hn
      have hb : b ≠ 0 := right_ne_zero_of_mul hn
      rw [Nat.cast_mul, map_mul, iha ha, ihb hb, one_mul]
  have hvi : ∀ n : ℤ, n ≠ 0 → ((n : ℂ))⁻¹ ∈ W := by
    intro n hn
    have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
    have e : W.valuation (n : ℂ) = 1 := by
      rcases Int.natAbs_eq n with h1 | h1
      · rw [h1, Int.cast_natCast]; exact hv1 _ hn'
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact hv1 _ hn'
    refine (W.valuation_le_one_iff _).1 ?_
    rw [map_inv₀, e, inv_one]
  haveI := c.fin
  obtain ⟨n, hn, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := x)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).mpr (Algebra.IsAlgebraic.isAlgebraic _))
  let i : c.F →+* ℂ := c.F.val.toRingHom
  have h1 : _root_.IsIntegral ℤ (i (n • x)) := hint.map i.toIntAlgHom
  have h2 : _root_.IsIntegral W (i (n • x)) := h1.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : i (n • x) ∈ W := by
    have hw' : (w : ℂ) = i (n • x) := hw
    rw [← hw']; exact w.2
  have h4 : i x = ((n : ℂ))⁻¹ * i (n • x) := by
    have hn0 : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
    rw [zsmul_eq_mul, map_mul, map_intCast, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  change i x ∈ W
  rw [h4]
  exact W.mul_mem _ _ (hvi n hn) h3

theorem isOpenImmersion_j (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) : IsOpenImmersion Y.j := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ (p : ℂ) ∈ W.nonunits
  · obtain ⟨p, hp, hW⟩ := h
    exact GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hW Y
  · push_neg at h
    have hbij : Function.Bijective (c.V W).subtype :=
      ⟨Subtype.val_injective, fun x => ⟨⟨x, mem_V_of_forall W h x⟩, rfl⟩⟩
    have h1 : IsIso (CommRingCat.ofHom (c.V W).subtype) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have : IsIso (spMap (c.V W).subtype) := by
      unfold spMap; infer_instance
    have := Y.jQ_open
    unfold Model.j
    infer_instance

end GlobalTheory.TriplesAlong

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDominant_jK (R : Type) [CommRing R] [IsDomain R] : IsDominant (Out.jK R) := by
  constructor
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hz : (Out.jK R) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R (FractionRing R)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range (Out.jK R) := ⟨_, hz⟩
  exact closure_mono (Set.singleton_subset_iff.2 hmem)
    ((PrimeSpectrum.le_iff_mem_closure _ _).1 (show (⊥ : Ideal R) ≤ y.asIdeal from bot_le))

theorem exists_sab_congr {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f f' : S' ⟶ S} (m : SABMap t' t f)
    (h : f = f') : ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

end GlobalTheory.TriplesAlong

open GlobalTheory.TriplesAlong in

theorem GlobalTheory.TriplesAlong.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype)
    (bV : 𝓞 c.F →+* c.V W), (∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χZ : Sp R ⟶ Z.X) (χY : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo.XF c), Out.jK R ≫ χZ = y ≫ Z.j → Out.jK R ≫ χY = y ≫ Y.j →
      ∃ (t : SAB H (Sp R)) (m₁ : SABMap t Z.t χZ) (m₂ : SABMap t Y.t χY),
        ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
          g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
          g ≫ m₂.φ = g₂ ≫ Y.m.φ := by
  intro E _ _ _ H D l Xo c W Z Y bV hbV R _ _ _ _ χZ χY y hZ hY
  haveI : IsDominant (Out.jK R) := isDominant_jK R
  haveI hmono : Mono (spMap bV) := GlobalTheory.PolArcData.mono_spMap_incl bV hbV
  have hsub : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV :=
    GlobalTheory.PolArcData.spMap_algebraMap_eq bV hbV
  haveI : Mono (spMap (c.V W).subtype) := mono_spMap_subtype _
  haveI : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by rw [hsub]; exact mono_comp _ _
  haveI hZj : Mono Z.j := GlobalTheory.ThetaShiftProofs.mono_j Z inferInstance
  haveI hYj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  haveI hYo : IsOpenImmersion Y.j := isOpenImmersion_j W Y
  haveI : IsProper Z.s := isProper_toroidalModel_structureMap Z

  have h1 : χZ ≫ Z.s = (χY ≫ Y.s) ≫ spMap bV := by
    refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) (Out.jK R) ?_
    simp only [Category.assoc]
    rw [reassoc_of% hZ, reassoc_of% hY, Model.j_s, reassoc_of% (Model.j_s Y), hsub]

  let U : (Sp R).Opens := χY ⁻¹ᵁ Y.j.opensRange
  have hKU : Set.range (Out.jK R) ⊆ (U : Set (Sp R)) := by
    rintro _ ⟨p, rfl⟩
    show χY (Out.jK R p) ∈ Set.range Y.j
    rw [← Scheme.Hom.comp_apply, hY, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hKU' : Set.range (Out.jK R) ⊆ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hKU
  let jU : Sp (FractionRing R) ⟶ U.toScheme := IsOpenImmersion.lift U.ι (Out.jK R) hKU'
  have hjU : jU ≫ U.ι = Out.jK R := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant (jU ≫ U.ι) := by rw [hjU]; infer_instance
  haveI : IsDominant jU := IsDominant.of_comp_of_isOpenImmersion jU U.ι
  haveI hdomU : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact (Out.jK R).denseRange.mono hKU⟩
  have hUr : Set.range (U.ι ≫ χY) ⊆ Set.range Y.j := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact p.2
  let v : U.toScheme ⟶ Xo.XF c := IsOpenImmersion.lift Y.j (U.ι ≫ χY) hUr
  have hv : v ≫ Y.j = U.ι ≫ χY := IsOpenImmersion.lift_fac _ _ _
  have hjv : jU ≫ v = y := by
    rw [← cancel_mono Y.j, Category.assoc, hv, ← Category.assoc, hjU, hY]
  have hvZ : v ≫ Z.j = U.ι ≫ χZ := by
    refine ext_of_isDominant_of_isSeparated Z.s ?_ jU ?_
    · rw [Category.assoc, Model.j_s, Category.assoc, h1, hsub]
      simp only [Category.assoc]
      rw [← reassoc_of% hv, reassoc_of% (Model.j_s Y)]
    · rw [← Category.assoc, hjv, ← Category.assoc, hjU, hZ]

  obtain ⟨tZ, ⟨mZ⟩⟩ := GlobalTheory.TraitOrder.exists_pull χZ Z.t
  obtain ⟨tY, ⟨mY⟩⟩ := GlobalTheory.TraitOrder.exists_pull χY Y.t
  obtain ⟨t₀, ⟨n₀⟩⟩ := GlobalTheory.TraitOrder.exists_pull v Z.oF.t
  have hprop : IsProper t₀.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper
  obtain ⟨nZ, hnZ⟩ := GlobalTheory.ObjMaps.exists_sab_comp (show SABMap Z.oF.t Z.t Z.j from Z.m) n₀
  obtain ⟨nZ', hnZ'⟩ := exists_sab_congr nZ hvZ
  obtain ⟨a, ha⟩ := GlobalTheory.ObjMaps.exists_sab_cancel mZ nZ'
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.ObjMaps.exists_sab_comp Z.m0.toSABMap n₀
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.ObjMaps.exists_sab_cancel Y.m0.toSABMap n₁
  obtain ⟨n₃, hn₃⟩ := GlobalTheory.ObjMaps.exists_sab_comp (show SABMap Y.oF.t Y.t Y.j from Y.m) n₂
  obtain ⟨n₃', hn₃'⟩ := exists_sab_congr n₃ hv
  obtain ⟨a', ha'⟩ := GlobalTheory.ObjMaps.exists_sab_cancel mY n₃'

  have hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R
  obtain ⟨b, hb⟩ := GlobalTheory.TorRef.sabExtNormalSt_of_homExtNormalSt GlobalTheory.homExtNormal E H (Sp R) U.toScheme U.ι hnorm
    inferInstance hdomU t₀ tZ tY a a' hprop
  obtain ⟨m₂', hm₂'⟩ := GlobalTheory.ObjMaps.exists_sab_comp mY b
  obtain ⟨m₂, hm₂⟩ := exists_sab_congr m₂' (Category.id_comp χY)
  refine ⟨tZ, mZ, m₂, ?_⟩

  intro T g g₁ g₂ e1 e2 e3
  set q := g ≫ tZ.G.hom with hqdef
  set x := g₁ ≫ Z.oF.t.G.hom with hxdef
  have hq : q ≫ χZ = x ≫ Z.j := by
    have w1 := congrArg (· ≫ Z.t.G.hom) e1
    simp only [Category.assoc] at w1
    rw [mZ.cart.1.w, (show SABMap Z.oF.t Z.t Z.j from Z.m).cart.1.w] at w1
    simpa only [Category.assoc, hqdef, hxdef] using w1
  have hqY : (q ≫ χY) ≫ Y.s = (x ≫ pullback.snd _ _) ≫ spMap (c.V W).subtype := by
    rw [← cancel_mono (spMap bV)]
    simp only [Category.assoc]
    rw [← Category.assoc χY, ← h1, reassoc_of% hq, Model.j_s, hsub]
    all_goals simp only [Category.assoc]
  let L := pullback.lift (q ≫ χY) (x ≫ pullback.snd _ _) hqY
  have hab : ∀ p : T, q p ∈ abLocus tZ.G := fun p => by
    refine (abLocus_pullback abLocusOne Z.t.semi mZ.cart.1 (q p)).1 ?_
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply]
    exact GlobalTheory.ThetaShiftProofs.j_mem_abLocus Z _
  have hLr : Set.range L ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    refine (abLocus_pullback abLocusOne Y.t.semi mY.cart.1 (q p)).2 ?_
    exact (abLocus_pullback abLocusOne tY.semi b.cart.1 (q p)).2 (hab p)
  have hqU : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨z, hz⟩ := hLr ⟨p, rfl⟩
    refine ⟨z, ?_⟩
    show Y.j z = χY (q p)
    rw [Model.j, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
  let q' : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι q hqU
  have hq' : q' ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  have hw : g ≫ tZ.G.hom = q' ≫ U.ι := by rw [hq']
  let g' : T ⟶ t₀.G.left := a.cart.1.lift g q' hw
  have hg'1 : g' ≫ a.φ = g := a.cart.1.lift_fst _ _ _
  have hg'2 : g' ≫ t₀.G.hom = q' := a.cart.1.lift_snd _ _ _
  have hx' : q' ≫ v = x := by
    rw [← cancel_mono Z.j, Category.assoc, hvZ, ← Category.assoc, hq', hq]
  have hbase : g' ≫ t₀.G.hom ≫ v = x := by rw [← Category.assoc, hg'2, hx']
  have c1 : g' ≫ n₀.φ = g₁ := by
    refine (show SABMap Z.oF.t Z.t Z.j from Z.m).cart.1.hom_ext ?_ ?_
    · change (g' ≫ n₀.φ) ≫ Z.m.φ = g₁ ≫ Z.m.φ
      rw [Category.assoc, ← hnZ, ← hnZ', ha, ← Category.assoc, hg'1, e1]
    · rw [Category.assoc, n₀.cart.1.w, hbase]
  have c2 : g' ≫ n₂.φ = g₂ := by
    refine Y.m0.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, ← hn₂, hn₁, ← Category.assoc, c1, e2]
    · rw [Category.assoc, n₂.cart.1.w, hbase]
      exact e3
  rw [hm₂, hm₂', ← hg'1, Category.assoc, ← Category.assoc a.φ, hb, ← ha', hn₃', hn₃, ← Category.assoc, c2]
