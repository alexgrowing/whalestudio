import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalOfGenericFibreDvrStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfPolarisedAtEveryPointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCoveredStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectOfCoveringPullbacksStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLevelExtendsFromDenseOpenNormalStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirationalStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvrStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFullStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteOfAmpleDeterminantFramesPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AmpleDeterminantFramesPullbackOfIsAffineHomStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGenericStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfCommonGenericFibre
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.AbelianLocusNormalisation

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem exists_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m' : SABMap t'' t' g) (m : SABMap t' t f) {h : S'' ⟶ S} (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_comp m m'

theorem exists_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) {g : S'' ⟶ S'} (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_cancel m n

theorem isProper_pull {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (h : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 h

theorem isAbelianScheme_of_isProper {S : Scheme.{0}} (t : SAB H S) (h : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨inferInstance, t.semi.smooth, h, t.semi.geomConnected⟩

theorem pol_of_map {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (h : IsProper t.G.hom) : (Out.RelAmple t.G t.PP.L → Out.RelAmple t'.G t'.PP.L) ∧
      (Out.KTriv t.G t.PP.L → Out.KTriv t'.G t'.PP.L) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact (pol_pull S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB (isAbelianScheme_of_isProper t h) m.cart
    ⟨w, hw⟩).2

theorem isNormalScheme_of_open {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (h : Geo.Tor.IsNormalScheme X) :
    Geo.Tor.IsNormalScheme Y := fun x => by
  obtain ⟨_, _⟩ := h (f x)
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem isReduced_of_normal {X : Scheme.{0}} (h : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    obtain ⟨_, _⟩ := h x
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem exists_full_through (hE : GlobalTheory.LN.HomExtSt) (h1 : Out.Laws) (h2 : Out.Laws2) {D : Datum H} {n N : ℕ}
    (hN : 0 < N) {S W : Scheme.{0}} [IsLocallyNoetherian S] (s : S ⟶ Sp (RZ H n N)) (t : SAB H S)
    (lv : D.La → (𝟙_ (Over S) ⟶ t.G)) (hp : IsProper t.G.hom) (add : ∀ a c, lv (a + c) = lv a * lv c)
    (ker : ∀ a, lv (N • a) = 1) (j : W ⟶ S) [IsOpenImmersion j] [IsDominant j] (tW : SAB H W) (ν : SABMap tW t j)
    (lW : D.La → (𝟙_ (Over W) ⟶ tW.G)) (hl : ∀ a, (lW a).left ≫ ν.φ = j ≫ (lv a).left)
    (o : FullObj D (j ≫ s) tW lW) (p : S) :
    ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)),
      p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv' := by
  obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes p
  have hξj := genericPoints_subset_range_of_isDominant j hξ
  by_cases hne : ξ = p
  · exact ⟨W, j, tW, ν, lW, hne ▸ hξj, hl, o⟩
  obtain ⟨V, _, _, -, f, hf₀, hf₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
  let K := FractionRing V
  let g : Sp K ⟶ Sp V := spMap (algebraMap V K)
  have hr : Set.range (g ≫ f) ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    have : g q = (⊥ : PrimeSpectrum V) := by
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap V K) q.asIdeal = ⊥
      rw [Subsingleton.elim (α := PrimeSpectrum K) q ⊥]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)
    rw [Scheme.Hom.comp_apply, this, hf₀]
    exact hξj
  let x : Sp K ⟶ W := IsOpenImmersion.lift j (g ≫ f) hr
  have hx : x ≫ j = g ≫ f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨tV, ⟨νV⟩⟩ := exists_pull (S' := Sp V) f t
  obtain ⟨tK, ⟨νK⟩⟩ := exists_pull g tV
  obtain ⟨κ, hκ⟩ := exists_comp νK νV rfl
  obtain ⟨κ', hκ'⟩ := exists_cancel ν κ hx
  let lV := fun a => ObjPull.secPull νV.cart (lv a)
  let lK := fun a => ObjPull.secPull κ'.cart (lW a)
  have oK : FullObj D (x ≫ j ≫ s) tK lK :=
    (GlobalTheory.T.fullLevelObject_pullback_exists_and_full E H D n N W _ (j ≫ s) tW lW x).2 tK κ' lK (fun a => ObjPull.secPull_left _ _) o
  have hpV := isProper_pull νV hp
  obtain ⟨am, kt⟩ := GlobalTheory.T.relAmple_principal_of_genericFibre_dvr hE h1 h2 E H V K tV tK νK hpV oK.ample oK.ktriv
  refine ⟨Sp V, f, tV, νV, lV, ⟨_, hf₁⟩, fun a => ObjPull.secPull_left _ _, ?_⟩
  refine GlobalTheory.T.fullObject_of_genericFibre_dvr h1 h2 E H D n N V K (f ≫ s) tV lV tK νK lK hN hpV am kt (fun a c => ?_) (fun a => ?_)
    (fun a => ?_) ?_
  · simp only [lV, add, map_mul]
  · simp only [lV, ker, map_one]
  · apply νV.cart.1.hom_ext
    · have e₁ : (lK a).left ≫ κ'.φ = x ≫ (lW a).left := ObjPull.secPull_left _ _
      have e₂ : (lV a).left ≫ νV.φ = f ≫ (lv a).left := ObjPull.secPull_left _ _
      change ((lK a).left ≫ νK.φ) ≫ νV.φ = (g ≫ (lV a).left) ≫ νV.φ
      rw [Category.assoc, ← hκ, hκ', ← Category.assoc, e₁, Category.assoc, hl, ← Category.assoc, hx, Category.assoc,
        Category.assoc, e₂]
    · rw [Category.assoc, νK.cart.1.w, ← Category.assoc, Over.w (lK a), Category.assoc, Over.w (lV a)]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  · rwa [← Category.assoc, hx, Category.assoc] at oK

theorem exists_full (hE : GlobalTheory.LN.HomExtSt) (h1 : Out.Laws) (h2 : Out.Laws2) {D : Datum H} {n N : ℕ}
    (hN : 0 < N) (hu : IsUnit (N : RZ H n N)) {S W : Scheme.{0}} [IsLocallyNoetherian S]
    (hS : Geo.Tor.IsNormalScheme S) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (hp : IsProper t.G.hom)
    (hq : IsQProjOver (t.G.hom ≫ s)) (j : W ⟶ S) [IsOpenImmersion j] [IsDominant j] (tW : SAB H W)
    (ν : SABMap tW t j) (lW : D.La → (𝟙_ (Over W) ⟶ tW.G)) (o : FullObj D (j ≫ s) tW lW) :
    ∃ lv : D.La → (𝟙_ (Over S) ⟶ t.G), FullObj D s t lv ∧ ∀ a, (lW a).left ≫ ν.φ = j ≫ (lv a).left := by
  have hu' : IsUnit (N : Γ(S, ⊤)) := by
    simpa using hu.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (RZ H n N))).inv.hom)
  obtain ⟨lv, add, ker, hl⟩ := GlobalTheory.T.torsionLevel_extends_from_dense_open_normal D.La N S W j t.G tW.G ν.φ lW hS ‹_› ‹_› hp hu' ν.cart o.add o.ker
  have th := exists_full_through hE h1 h2 hN s t lv hp add ker j tW ν lW hl o
  have am : Out.RelAmple t.G t.PP.L := GlobalTheory.T.relAmple_of_polarised_at_every_point E H S t hp
    (fun A _ y B φ h => GlobalTheory.T.isProjOver_baseChange_of_proper_quasiProjective _ A S s t.G y B φ hp hq h) fun p => by
      obtain ⟨S', f, t', ν', _, a, -, b⟩ := th p
      exact ⟨S', f, t', ν', a, b.ample, b.ktriv⟩
  have kt : Out.KTriv t.G t.PP.L := GlobalTheory.T.kernelTrivial_of_every_point_covered h1 E H S t hp am fun p => by
    obtain ⟨S', f, t', ν', _, a, -, b⟩ := th p
    exact ⟨S', f, t', ν', a, b.ktriv⟩
  exact ⟨lv, GlobalTheory.T.fullLevelObject_of_covering_pullbacks h1 E H D n N S s t lv hN hp am kt add ker th, hl⟩

theorem isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (h : IsProjOver s) :
    IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem separated_finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsSeparated s ∧ LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem isProper_of_abLocus (hE : GlobalTheory.LN.HomExtSt) {R : Type} [CommRing R] [IsNoetherianRing R] {Z M : Scheme.{0}}
    {sZ : Z ⟶ Sp R} {sM : M ⟶ Sp R} (hZ : IsProjOver sZ) (hM : IsQProjOver sM) {t : SAB H Z} {tM : SAB H M}
    (hp : IsProper tM.G.hom) {U : Z.Opens} (hU : abLocus t.G ⊆ U) {u : U.toScheme ⟶ M} (hu : u ≫ sM = U.ι ≫ sZ)
    {tU : SAB H U.toScheme} (mU : SABMap tU t U.ι) (mM : SABMap tU tM u) : IsProper u := by
  have := isProper_of_isProjOver hZ
  obtain ⟨_, _⟩ := separated_finiteType_of_isQProjOver hM
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian sM
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  refine GlobalTheory.T.isProper_of_completeDVR_lift_generic R _ M u sM ‹_› ?_ fun V K _ _ _ _ _ _ _ x y _ hxy => ?_
  · obtain ⟨N, i, hi, e⟩ := hZ
    exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by rw [hu, Category.assoc, e]⟩
  obtain ⟨z, hz, -⟩ := valuative_lift_of_isProper sZ (x ≫ U.ι) (y ≫ sM)
    (by rw [Category.assoc, ← hu, reassoc_of% hxy])
  obtain ⟨tz, ⟨mz⟩⟩ := exists_pull z t
  obtain ⟨ty, ⟨my⟩⟩ := exists_pull y tM
  obtain ⟨tx, ⟨mx⟩⟩ := exists_pull x tU
  obtain ⟨a, -⟩ := exists_comp mx mU rfl
  obtain ⟨b, -⟩ := exists_comp mx mM rfl
  obtain ⟨a', -⟩ := exists_cancel mz a hz
  obtain ⟨b', -⟩ := exists_cancel my b hxy.symm
  have hA : IsAbelianScheme tz.G := isAbelianScheme_of_common_generic_fibre ty.G tz.G
    (isAbelianScheme_of_isProper ty (isProper_pull my hp)) tz.semi (fun f hf => by
      obtain ⟨F, hF, -⟩ := hE V K ty.G tz.G ty.semi tz.semi f hf
      exact ⟨F, hF.2⟩) tx.G b'.cart a'.cart
  have := hA.proper
  have hr : Set.range z ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact (range_subset_abLocus_of_isProper t.semi mz.cart.1).trans hU
  exact ⟨IsOpenImmersion.lift U.ι z hr, by rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, hz]⟩

theorem isAffineHom_of_isProper {R : Type} [CommRing R] {X Z V : Scheme.{0}} [IsAffine V] (g : X ⟶ Z) [IsImmersion g]
    (u : X ⟶ V) [IsProper u] (sZ : Z ⟶ Sp R) [IsSeparated sZ] (sV : V ⟶ Sp R) (h : u ≫ sV = g ≫ sZ) :
    IsAffineHom g := by
  let l : X ⟶ pullback sV sZ := pullback.lift u g h
  have e₁ : l ≫ pullback.fst sV sZ = u := pullback.lift_fst _ _ _
  have e₂ : l ≫ pullback.snd sV sZ = g := pullback.lift_snd _ _ _
  have : IsProper (l ≫ pullback.fst sV sZ) := by rwa [e₁]
  have : IsProper l := IsProper.of_comp l (pullback.fst sV sZ)
  have : IsImmersion (l ≫ pullback.snd sV sZ) := by rwa [e₂]
  have : IsImmersion l := IsImmersion.of_comp l (pullback.snd sV sZ)
  have : IsClosedImmersion l := IsClosedImmersion.of_isPreimmersion l l.isClosedMap.isClosed_range
  have : IsAffineHom sV := inferInstance
  have : IsAffineHom (pullback.snd sV sZ) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback sV sZ) ‹_›
  rw [← e₂]
  infer_instance

theorem isFinite_of_isProper (h1 : Out.Laws) (h2 : Out.Laws2) {R : Type} [CommRing R] {Z M : Scheme.{0}}
    [IsLocallyNoetherian Z] (sZ : Z ⟶ Sp R) [IsSeparated sZ] (sM : M ⟶ Sp R) (z : Z ⟶ Sp ℤ) [Flat z]
    (hn : Geo.Tor.IsNormalScheme Z) {t : SAB H Z} {tM : SAB H M} (hp : IsProper tM.G.hom)
    (am : Out.RelAmple tM.G tM.PP.L) (kt : Out.KTriv tM.G tM.PP.L) {N : ℕ} (hN : 0 < N)
    (A : GlobalTheory.LN.AmpFrames t.G t.PP.L N) {U : Z.Opens} {u : U.toScheme ⟶ M} [IsProper u] (hu : u ≫ sM = U.ι ≫ sZ)
    {tU : SAB H U.toScheme} (mU : SABMap tU t U.ι) (mM : SABMap tU tM u) : IsFinite u := by
  suffices h : ∀ V : M.affineOpens, IsFinite (u ∣_ V.1) by
    refine IsFinite.iff_isProper_and_isAffineHom.2 ⟨‹_›, ⟨fun V hV => ?_⟩⟩
    have := h ⟨V, hV⟩
    have : IsAffine V.toScheme := hV
    exact isAffine_of_isAffineHom (u ∣_ V)
  intro V
  have : IsAffine V.1.toScheme := V.2
  have ha := isAffineHom_of_isProper ((u ⁻¹ᵁ V.1).ι ≫ U.ι) (u ∣_ V.1) sZ (V.1.ι ≫ sM)
    (by rw [morphismRestrict_ι_assoc, hu, Category.assoc])
  obtain ⟨t', ⟨m'⟩⟩ := exists_pull (u ⁻¹ᵁ V.1).ι tU
  obtain ⟨tV, ⟨mV⟩⟩ := exists_pull V.1.ι tM
  obtain ⟨a, -⟩ := exists_comp m' mU rfl
  obtain ⟨b, -⟩ := exists_comp m' mM rfl
  obtain ⟨b', -⟩ := exists_cancel mV b (morphismRestrict_ι u V.1)
  obtain ⟨A', -⟩ := GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom E H Z _ t t' _ a N A ha
  exact GlobalTheory.T.isFinite_of_ampleDeterminantFrames_pullback h1 h2 E H _ _ (((u ⁻¹ᵁ V.1).ι ≫ U.ι) ≫ z) t' tV (u ∣_ V.1) b' N A' hN
    (isNormalScheme_of_open ((u ⁻¹ᵁ V.1).ι ≫ U.ι) hn) inferInstance (isProper_pull b hp) ((pol_of_map b hp).1 am)
    ((pol_of_map b hp).2 kt) inferInstance

theorem isIso_restrict_of_section {U M : Scheme.{0}} [IsReduced U] (u : U ⟶ M) [IsSeparated u] (W : M.Opens)
    (j : W.toScheme ⟶ U) [IsDominant j] (h : j ≫ u = W.ι) :
    IsIso (u ∣_ W) ∧ Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) := by
  have hr : Set.range j ⊆ Set.range (u ⁻¹ᵁ W).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    show u (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h]
    exact w.2
  refine ⟨?_, j.denseRange.mono (hr.trans (Scheme.Opens.range_ι _).le)⟩
  let σ := IsOpenImmersion.lift (u ⁻¹ᵁ W).ι j hr
  have hσ : σ ≫ (u ⁻¹ᵁ W).ι = j := IsOpenImmersion.lift_fac _ _ _
  have h₁ : σ ≫ u ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hσ, h, Category.id_comp]
  have : IsDominant σ := by
    constructor
    have hd := Dense.preimage j.denseRange (u ⁻¹ᵁ W).ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, (u ⁻¹ᵁ W).ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hσ]; rfl
  refine ⟨σ, ?_, h₁⟩
  refine ext_of_isDominant_of_isSeparated (u ∣_ W) ?_ σ ?_
  · rw [Category.assoc, h₁, Category.comp_id, Category.id_comp]
  · rw [reassoc_of% h₁, Category.comp_id]

theorem normal_stalk_of_generic {O : Type} [CommRing O] [IsDomain O] {M : Scheme.{0}} (s : M ⟶ Sp O)
    (h : Smooth (pullback.snd s (spMap (algebraMap O (FractionRing O))))) (x : M) (hx : (s x).asIdeal = ⊥) :
    IsDomain (M.presheaf.stalk x) ∧ IsIntegrallyClosed (M.presheaf.stalk x) := by
  have hb : IsPreimmersion (spMap (algebraMap O (FractionRing O))) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := FractionRing O) (nonZeroDivisors O)
  have hbf : Flat (spMap (algebraMap O (FractionRing O))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (nonZeroDivisors O))
  have h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap O (FractionRing O)))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hx' : x ∈ Set.range (pullback.fst s (spMap (algebraMap O (FractionRing O)))) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨(⊥ : PrimeSpectrum (FractionRing O)), PrimeSpectrum.ext ?_⟩
    rw [hx]
    exact Ideal.comap_bot_of_injective (algebraMap O (FractionRing O)) (IsFractionRing.injective O _)
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨_, _⟩ := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ h).2.1 y
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap (algebraMap O (FractionRing O)))) y
  let e := (asIso ((pullback.fst s (spMap (algebraMap O (FractionRing O)))).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

theorem exists_isIso_restrict {U M : Scheme.{0}} (u : U ⟶ M) (T : M → Prop)
    (h : ∀ x, T x → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V)) : ∃ W : M.Opens, (∀ x, T x → x ∈ W) ∧ IsIso (u ∣_ W) := by
  let W : M.Opens := ⨆ V : {V : M.Opens // IsIso (u ∣_ V)}, V.1
  refine ⟨W, fun x hx => ?_, ?_⟩
  · obtain ⟨V, a, b⟩ := h x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, b⟩, a⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun V : {V : M.Opens // IsIso (u ∣_ V)} => W.ι ⁻¹ᵁ V.1) ?_ fun V => ?_
  · rw [← Scheme.Hom.preimage_iSup]
    exact W.ι_preimage_self
  · have e : W.ι ''ᵁ (W.ι ⁻¹ᵁ V.1) = V.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 (le_iSup (fun V : {V : M.Opens // IsIso (u ∣_ V)} => V.1) V)
    refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u W (W.ι ⁻¹ᵁ V.1))).2 ?_
    rw [e]
    exact V.2

theorem exists_finite_map : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m) (U : C.Z.Opens), n.Prime → (∃ j, N = n ^ j) → 0 < m → FamCore D sM tM lev → (U : Set C.Z) = abLocus C.t.G → ∃ (u : U.toScheme ⟶ MM) (tU : SAB H U.toScheme) (mU : SABMap tU C.t U.ι) (mM : SABMap tU tM u), u ≫ sM = U.ι ≫ C.s ∧ IsFinite u ∧ Surjective u ∧ (∃ W : MM.Opens, (∀ x : MM, (sM x).asIdeal = ⊥ → x ∈ W) ∧ IsIso (u ∣_ W)) ∧ ∀ j' : C.W.toScheme ⟶ U.toScheme, j' ≫ U.ι = C.j → j' ≫ u = C.W.ι := by
  intro hE h1 h2 E _ _ _ H D n N MM sM tM lev m C U hn ⟨e, he⟩ hm F hU
  have := BaseRing.finiteType_RZ H n N
  have : IsNoetherianRing (RZ H n N) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
  have hun : IsUnit (n : RZ H n N) := IsUnit.of_mul_eq_one
    ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr (Or.inl rfl))⟩ (Subtype.ext (by simp [hn₀]))
  have huN : IsUnit (N : RZ H n N) := by simpa only [he, Nat.cast_pow] using hun.pow e
  have hN : 0 < N := he ▸ pow_pos hn.pos e
  have := isProper_of_isProjOver C.proj
  obtain ⟨_, _⟩ := separated_finiteType_of_isQProjOver F.qproj
  have : IsLocallyNoetherian MM := LocallyOfFiniteType.isLocallyNoetherian sM
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.s
  have := C.flat
  have := F.flat
  have := F.red
  have := C.j_open
  have := C.j_dom
  have hnU := isNormalScheme_of_open U.ι C.normal
  have := isReduced_of_normal hnU
  obtain ⟨tU, ⟨mU⟩⟩ := exists_pull U.ι C.t
  have hpU : IsProper tU.G.hom := by
    obtain ⟨U', hU', hP⟩ := C.good.1
    obtain rfl : U' = U := TopologicalSpace.Opens.ext (hU'.trans hU.symm)
    have i := mU.cart.1.isoIsPullback_hom_snd _ _ (isPullback_morphismRestrict C.t.G.hom U').flip
    rw [← i]
    infer_instance
  have hqU : IsQProjOver (tU.G.hom ≫ U.ι ≫ C.s) := by
    obtain ⟨k, i, _, _, hi⟩ := C.qproj
    have : IsOpenImmersion mU.φ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) mU.cart.1.flip inferInstance
    have : QuasiCompact mU.φ := MorphismProperty.of_isPullback (P := @QuasiCompact) mU.cart.1.flip inferInstance
    exact ⟨k, mU.φ ≫ i, inferInstance, inferInstance, by rw [Category.assoc, hi, mU.cart.1.w_assoc]⟩
  have hpW := isProper_pull C.m₁ F.obj.proper
  have hr : Set.range C.j ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, hU]
    exact range_subset_abLocus_of_isProper C.t.semi C.m₂.cart.1
  let j : C.W.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι C.j hr
  have hj : j ≫ U.ι = C.j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (j ≫ U.ι) := by rwa [hj]
  have : IsOpenImmersion j := IsOpenImmersion.of_comp j U.ι
  have : IsDominant j := by
    constructor
    have hd := Dense.preimage C.j.denseRange U.ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hj]; rfl
  obtain ⟨ν, -⟩ := exists_cancel mU C.m₂ hj
  let lW := fun a => ObjPull.secPull C.m₁.cart (lev a)
  have hlW : ∀ a, (lW a).left ≫ C.m₁.φ = C.W.ι ≫ (lev a).left := fun a => ObjPull.secPull_left _ _
  have oW : FullObj D (C.W.ι ≫ sM) C.tW lW := (GlobalTheory.T.fullLevelObject_pullback_exists_and_full E H D n N MM _ sM tM lev C.W.ι).2 C.tW C.m₁ lW hlW F.obj
  have hjs : j ≫ U.ι ≫ C.s = C.W.ι ≫ sM := by rw [reassoc_of% hj, C.j_over]
  obtain ⟨lv, o, hl⟩ := exists_full hE h1 h2 hN huN hnU (U.ι ≫ C.s) tU hpU hqU j C.tW ν lW (by rwa [hjs])
  obtain ⟨u, ⟨hu, mM, hM⟩, -⟩ := F.rep _ (U.ι ≫ C.s) tU lv inferInstance inferInstance inferInstance o
  have hju : j ≫ u = C.W.ι := by
    obtain ⟨k, hk⟩ := exists_comp ν mM rfl
    refine (F.rep _ (C.W.ι ≫ sM) C.tW lW inferInstance inferInstance inferInstance oW).unique
      ⟨by rw [Category.assoc, hu, hjs], k, fun a => ?_⟩ ⟨rfl, C.m₁, hlW⟩
    rw [hk, ← Category.assoc, hl, Category.assoc, hM, Category.assoc]
  have := isProper_of_abLocus hE C.proj F.qproj F.obj.proper hU.ge hu mU mM
  have : Flat (spMap (algebraMap ℤ (RZ H n N))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hf : IsFinite u := isFinite_of_isProper h1 h2 C.s sM (C.s ≫ spMap (algebraMap ℤ (RZ H n N))) C.normal
    F.obj.proper F.obj.ample F.obj.ktriv (pow_pos hm 2) C.amp hu mU mM
  obtain ⟨hi, hd⟩ := isIso_restrict_of_section u C.W j hju
  refine ⟨u, tU, mU, mM, hu, hf, ⟨?_⟩, exists_isIso_restrict u _ fun x hx => ?_, fun j' hj' => ?_⟩
  · have hd' : Dense (Set.range u) := C.dense.mono fun w hw =>
      ⟨j ⟨w, hw⟩, congrArg (fun f => f (⟨w, hw⟩ : C.W.toScheme)) hju⟩
    rw [← Set.range_eq_univ, ← u.isClosedMap.isClosed_range.closure_eq]
    exact hd'.closure_eq
  · obtain ⟨a, b⟩ := normal_stalk_of_generic sM F.gen x hx
    exact GlobalTheory.T.isIso_near_normal_point_of_finite_birational _ MM u C.W hf inferInstance hi C.dense hd x a b
  · obtain rfl : j' = j := by rw [← cancel_mono U.ι, hj, hj']
    exact hju

end GlobalTheory.AbelianLocusNormalisation
