import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainFrameExtendsIntegrally
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLieAlgebraCoordinateLinearEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CochSat
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieCoord lieAdd IsSaturatedTorus TorusSaturated IsLieLinear)
open Formalism.L2.Pj (dualMap)
open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs (lieScale)

theorem ext_of_injective_of_isSeparated {A B : Type} [CommRing A] [CommRing B] (p : A →+* B)
    (hp : Function.Injective p) {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsSeparated s] (f g : Sp A ⟶ Y)
    (hs : f ≫ s = g ≫ s) (h : spMap p ≫ f = spMap p ≫ g) : f = g := by
  have hci : IsClosedImmersion (equalizer.ι f g) := GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated s hs
  have hl : equalizer.lift (spMap p) h ≫ equalizer.ι f g = spMap p := equalizer.lift_ι _ _
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hci
  have hI : ∀ x ∈ I, p x = 0 := by
    intro x hx
    have hl' := hl
    rw [he, ← Category.assoc] at hl'
    have h6 : Spec.map (Spec.preimage (equalizer.lift (spMap p) h ≫ e.hom)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = Spec.map (CommRingCat.ofHom p) := by
      rw [Spec.map_preimage]; exact hl'
    rw [← Spec.map_comp] at h6
    have h7 := Spec.map_injective h6
    have h8 := congrArg (fun φ => φ.hom x) h7
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h8
    rw [← h8, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  have hbot : I = ⊥ := le_bot_iff.mp fun x hx => (Submodule.mem_bot _).2 (hp ((hI x hx).trans (map_zero p).symm))
  subst hbot
  have hiso : IsIso (equalizer.ι f g) := by
    rw [he]
    have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal (CommRingCat.of A)))) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact (RingEquiv.quotientBot A).symm.bijective
    infer_instance
  rw [← cancel_epi (equalizer.ι f g), equalizer.condition]

theorem bcTan_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (hφ : Function.Injective φ)
    {x : Sp S ⟶ X} {x' : Sp T ⟶ X} (hx : spMap φ ≫ x = x') :
    Function.Injective (bcTan φ hx : TanM x t.G → TanM x' t.G) := by
  intro v w h
  have h1 : spMap (dualMap φ) ≫ (tv v).left = spMap (dualMap φ) ≫ (tv w).left := by
    have := congrArg (fun z : TanM x' t.G => (tv z).left) h
    simpa only [left_bcTan] using this
  haveI : IsSeparated t.G.hom := t.semi.separated
  have hd : Function.Injective (dualMap φ) := fun a b hab => by
    have h1 := congrArg TrivSqZeroExt.fst hab
    have h2 := congrArg TrivSqZeroExt.snd hab
    simp [dualMap] at h1 h2
    exact TrivSqZeroExt.ext (hφ h1) (hφ h2)
  exact tan_ext (ext_of_injective_of_isSeparated (dualMap φ) hd t.G.hom _ _
    ((isTan_tv v).1.trans (isTan_tv w).1.symm) h1)

theorem tanOf_lieAdd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) (a b : LieG ((Over.pullback x).obj t.G)) :
    tanOf (GlobalTheory.CochInt.isTan_of_lieG t x (lieAdd _ a b)) =
      tanOf (GlobalTheory.CochInt.isTan_of_lieG t x a) + tanOf (GlobalTheory.CochInt.isTan_of_lieG t x b) := by
  refine tan_ext ?_
  rw [left_tanOf, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_add]
  exact ((isGrpPullback_pullback t.G x).2 _ a.1 b.1 _ _ rfl rfl).symm

theorem tanOf_lieScale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) (c : R)
    (a : LieG ((Over.pullback x).obj t.G)) :
    tanOf (GlobalTheory.CochInt.isTan_of_lieG t x (lieScale _ c a)) = c • tanOf (GlobalTheory.CochInt.isTan_of_lieG t x a) := by
  refine tan_ext ?_
  rw [left_tanOf, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_smul, Formalism.L2.Pj.smT_left, left_tanOf]
  show ((ptMap (ReciprocityTheory.ChartRestriction.G.Pdiv.dualScale c) ≫ a.1).left ≫ _) = _
  rw [Over.comp_left, Category.assoc]
  rfl

theorem tanOf_lieG_bijective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) :
    Function.Bijective (fun v : LieG ((Over.pullback x).obj t.G) => tanOf (GlobalTheory.CochInt.isTan_of_lieG t x v)) := by
  refine ⟨fun v v' h => ?_, fun w => ?_⟩
  · have h1 : v.1.left ≫ pullback.fst t.G.hom x = v'.1.left ≫ pullback.fst t.G.hom x := by
      have := congrArg (fun z : TanM x t.G => (tv z).left) h
      simpa only [left_tanOf] using this
    exact Subtype.ext (Over.OverMorphism.ext (pullback.hom_ext h1 ((Over.w v.1).trans (Over.w v'.1).symm)))
  · have hw := isTan_tv w
    let m : specO R (DualNumber R) ⟶ (Over.pullback x).obj t.G :=
      Over.homMk (pullback.lift (tv w).left (spMap (algebraMap R (DualNumber R))) hw.1) (pullback.lift_snd _ _ _)
    have hm : m.left ≫ pullback.fst t.G.hom x = (tv w).left := pullback.lift_fst _ _ _
    have e : (specO R R).hom ≫ x = x :=
      (congrArg (· ≫ x) (Spec.map_id (CommRingCat.of R))).trans (Category.id_comp x)
    have key : ∀ (y : Sp R ⟶ X), (specO R R).hom ≫ x = y → (1 : specO R R ⟶ (Over.pullback x).obj t.G).left ≫
        pullback.fst t.G.hom x = (1 : Over.mk y ⟶ t.G).left := by
      rintro _ rfl
      exact (Formalism.L2.Pj.grpPull_one (isGrpPullback_pullback t.G x) (specO R R)).symm
    have hu : ptMap (TrivSqZeroExt.fstHom R R R) ≫ m = toUnit (specO R R) ≫ η[(Over.pullback x).obj t.G] := by
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
      · change _ = (1 : specO R R ⟶ (Over.pullback x).obj t.G).left ≫ _
        rw [Over.comp_left, Category.assoc, hm]
        exact hw.2.trans (key x e).symm
      · exact (Over.w (ptMap (TrivSqZeroExt.fstHom R R R) ≫ m)).trans
          (Over.w (toUnit (specO R R) ≫ η[(Over.pullback x).obj t.G])).symm
    exact ⟨⟨m, hu⟩, tan_ext (by simp only [left_tanOf]; exact hm)⟩

theorem exists_saturated_model (hTS : TorusSaturated) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (xR : Sp R ⟶ X) (xK : Sp K ⟶ X)
    (hx : spMap (algebraMap R K) ≫ xR = xK) (r : ℕ) (u : torus K r ⟶ (Over.pullback xK).obj t.G) (hu : IsMonHom u)
    (hc : IsClosedImmersion u.left) :
    ∃ (uR : torus R r ⟶ (Over.pullback xR).obj t.G) (_ : IsMonHom uR), IsSaturatedTorus uR ∧
      SplitTorus.bcMap (spMap (algebraMap R K)) (Fin r → ℤ) ≫ uR.left ≫ pullback.fst t.G.hom xR =
        u.left ≫ pullback.fst t.G.hom xK := by
  let f : Sp K ⟶ Sp R := spMap (algebraMap R K)
  let GR := (Over.pullback xR).obj t.G
  let ψ : ((Over.pullback xK).obj t.G).left ⟶ GR.left :=
    pullback.lift (pullback.fst t.G.hom xK) (pullback.snd t.G.hom xK ≫ f)
      (by rw [Category.assoc, hx, pullback.condition])
  have hψ₁ : ψ ≫ pullback.fst t.G.hom xR = pullback.fst t.G.hom xK := pullback.lift_fst _ _ _
  have hψ : IsGrpPullback ((Over.pullback xK).obj t.G) GR f ψ :=
    (isGrpPullback_pullback t.G xR).cancel ((isGrpPullback_pullback t.G xK).congr hx.symm hψ₁.symm)
      (pullback.lift_snd _ _ _)
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hψ (isGrpPullback_pullback GR f)
  haveI := hu
  haveI := he
  let uK : (Over.pullback f).obj (torus R r) ⟶ (Over.pullback f).obj GR :=
    (SplitTorus.bcIso f (Fin r → ℤ)).inv ≫ u ≫ e.hom
  have hmon : IsMonHom uK := inferInstance
  have hcl : IsClosedImmersion uK.left := by
    haveI : IsIso (SplitTorus.bcIso f (Fin r → ℤ)).inv.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (SplitTorus.bcIso f (Fin r → ℤ)).inv))
    haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    simp only [uK, Over.comp_left]
    infer_instance
  obtain ⟨uR, huR, hbc, -, hsat⟩ :=
    hTS R K GR (IsSemiAbelian.pullback xR t.G t.semi) r uK hmon hcl
  refine ⟨uR, huR, hsat, ?_⟩
  have A : ((Over.pullback f).map uR).left ≫ pullback.fst GR.hom f =
      pullback.fst (torus R r).hom f ≫ uR.left := pullback.lift_fst _ _ _
  have B : ((Over.pullback f).map uR).left = uK.left := congrArg (·.left) hbc
  rw [← SplitTorus.bcIso_hom_fst f (Fin r → ℤ), Category.assoc, ← Category.assoc (pullback.fst _ _), ← A, B]
  simp only [uK, Over.comp_left, Category.assoc]
  rw [← Category.assoc e.hom.left, heψ, hψ₁, ← Over.comp_left_assoc, Iso.hom_inv_id, Over.id_left,
    Category.id_comp]

theorem tv_sum_lieCoord {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {K : Type} [CommRing K] (xK : Sp K ⟶ X) {r : ℕ}
    (u : torus K r ⟶ (Over.pullback xK).obj t.G) [IsMonHom u] (ε : Fin r → TanM xK t.G)
    (hε : ∀ i, ∃ e : LieG (torus K r), lieCoord e = Pi.single i 1 ∧
      (tv (ε i)).left = e.1.left ≫ u.left ≫ pullback.fst t.G.hom xK)
    (e : LieG (torus K r)) : (tv (∑ i, lieCoord e i • ε i)).left = e.1.left ≫ u.left ≫ pullback.fst t.G.hom xK := by
  obtain ⟨hbij, hadd, hsm⟩ := GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul K r
  let L := Equiv.ofBijective _ hbij
  let T : LieG (torus K r) → TanM xK t.G := fun y => tanOf (GlobalTheory.CochInt.isTan_of_lieG t xK (lieMap u y))
  have hT : ∀ y, (tv (T y)).left = y.1.left ≫ u.left ≫ pullback.fst t.G.hom xK := fun y => by
    show (lieMap u y).1.left ≫ _ = _
    rw [lieMap, Over.comp_left, Category.assoc]
  have hLs : ∀ c, lieCoord (L.symm c) = c := fun c => Equiv.ofBijective_apply_symm_apply _ hbij c
  have hL1 : ∀ c d, L.symm (c + d) = lieAdd _ (L.symm c) (L.symm d) := fun c d =>
    L.symm_apply_eq.2 (by show c + d = lieCoord _; rw [hadd, hLs, hLs])
  have hL2 : ∀ (k : K) c, L.symm (k • c) = lieScale _ k (L.symm c) := fun k c =>
    L.symm_apply_eq.2 (by show k • c = lieCoord _; rw [hsm, hLs])
  let Ψ : (Fin r → K) →ₗ[K] TanM xK t.G :=
    { toFun := fun c => T (L.symm c)
      map_add' := fun c d => by
        show T (L.symm (c + d)) = T (L.symm c) + T (L.symm d)
        simp only [T]
        rw [hL1, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap u).1, tanOf_lieAdd]
      map_smul' := fun k c => by
        show T (L.symm (k • c)) = k • T (L.symm c)
        simp only [T]
        rw [hL2, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap u).2, tanOf_lieScale] }
  have hΨ : ∀ i, Ψ (Pi.single i 1) = ε i := fun i => by
    obtain ⟨e', he', hε'⟩ := hε i
    have : L.symm (Pi.single i 1) = e' := L.symm_apply_eq.2 he'.symm
    refine tan_ext ?_
    show (tv (T (L.symm (Pi.single i 1)))).left = _
    rw [this, hT, hε']
  have hsum : ∑ i, lieCoord e i • ε i = Ψ (lieCoord e) := by
    conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ Ψ (lieCoord e)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hΨ i]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hsum]
  show (tv (T (L.symm (L e)))).left = _
  rw [Equiv.symm_apply_apply, hT]

theorem mem_range_of_dvr (hTS : TorusSaturated) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (xR : Sp R ⟶ X) (xK : Sp K ⟶ X)
    (hx : spMap (algebraMap R K) ≫ xR = xK) (r : ℕ) (ε : Fin r → TanM xK t.G) (hε : IsCochFrame t xK ε)
    (a : Fin r → K) (w : TanM xR t.G) (hw : bcTan (algebraMap R K) hx w = ∑ i, a i • ε i) (i : Fin r) :
    a i ∈ Set.range (algebraMap R K) := by
  obtain ⟨u, hu, hc, hεe⟩ := hε
  obtain ⟨uR, huR, ⟨-, -, ⟨hbij, -, hsm⟩, ρ, hρlin, hρ⟩, hrel⟩ :=
    exists_saturated_model hTS t R K xR xK hx r u hu hc
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (Finset.univ : Finset (Fin r)) a
  choose c hc' using fun j => hs j (Finset.mem_univ j)
  obtain ⟨xc, hxc⟩ := hbij.2 c
  obtain ⟨xK', hxK'⟩ := (GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul K r).1.2 (fun j => algebraMap R K (c j))
  have h1 : bcTan (algebraMap R K) hx (tanOf (GlobalTheory.CochInt.isTan_of_lieG t xR (lieMap uR xc))) =
      ∑ j, algebraMap R K (c j) • ε j := by
    refine tan_ext ?_
    have hb := GlobalTheory.CochInt.left_comp_bcMap (algebraMap R K) xc xK' fun j => by rw [hxK', hxc]
    have e1 : ∀ j, algebraMap R K (c j) = lieCoord xK' j := fun j => by rw [hxK']
    simp only [e1]
    rw [left_bcTan, left_tanOf, tv_sum_lieCoord t xK u ε hεe xK']
    show spMap (dualMap (algebraMap R K)) ≫ (xc.1 ≫ uR).left ≫ pullback.fst t.G.hom xR = _
    rw [Over.comp_left, ← Category.assoc, ← Category.assoc, ← hb, Category.assoc, Category.assoc, ← hrel]
  have h2 : bcTan (algebraMap R K) hx ((s : R) • w) = ∑ j, algebraMap R K (c j) • ε j := by
    rw [LinearMap.map_smulₛₗ, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← Algebra.smul_def, ← hc' j]
  have h3 := bcTan_injective t (algebraMap R K) hinj hx (h2.trans h1.symm)
  obtain ⟨y, hy⟩ := (tanOf_lieG_bijective t xR).2 w
  have h4 : lieScale _ (s : R) y = lieMap uR xc := (tanOf_lieG_bijective t xR).1 (by
    simp only at hy ⊢
    rw [tanOf_lieScale, hy, h3])
  have h5 : (s : R) • lieCoord (ρ y) = c := by
    rw [← hsm, ← hρlin.2, h4, hρ, hxc]
  refine ⟨lieCoord (ρ y) i, ?_⟩
  have hs0 : algebraMap R K (s : R) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero s.2)
  refine mul_left_cancel₀ hs0 ?_
  rw [← map_mul, ← smul_eq_mul, ← Pi.smul_apply, h5, hc' i, Algebra.smul_def]

theorem bcTan_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (f : S →+* T) (g : T →+* U)
    {x : Sp S ⟶ X} {y : Sp T ⟶ X} {z : Sp U ⟶ X} (hy : spMap f ≫ x = y) (hz : spMap g ≫ y = z)
    (hz' : spMap (g.comp f) ≫ x = z) (w : TanM x t.G) :
    bcTan g hz (bcTan f hy w) = bcTan (g.comp f) hz' w := by
  refine tan_ext ?_
  rw [left_bcTan, left_bcTan, left_bcTan, ← Category.assoc]
  congr 1
  rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap]

theorem cochar_saturated : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (K : Type) [Field K] [NumberField K] (xO : Sp (𝓞 K) ⟶ X) (xK : Sp K ⟶ X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) (r : ℕ) (ε : Fin r → TanM xK t.G), IsCochFrame t xK ε → ∀ (a : Fin r → K) (w : TanM xO t.G), bcTan (algebraMap (𝓞 K) K) hx w = ∑ i, a i • ε i → ∀ i, a i ∈ Set.range (algebraMap (𝓞 K) K) := by
  intro hTS E _ _ _ H X t K _ _ xO xK hx r ε hε a w hw i
  have key : ∀ v : MaximalSpectrum (𝓞 K), a i ∈ Localization.subalgebra.ofField K v.asIdeal.primeCompl
      v.asIdeal.primeCompl_le_nonZeroDivisors := by
    intro v
    let Rv := Localization.subalgebra.ofField K v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsDiscreteValuationRing Rv :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K)
        (Ideal.bot_lt_of_maximal v.asIdeal (RingOfIntegers.not_isField K)).ne' Rv
    haveI : IsFractionRing Rv K := inferInstance
    have hxR : spMap (algebraMap Rv K) ≫ spMap (algebraMap (𝓞 K) Rv) ≫ xO = xK := by
      rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
      exact hx
    have hw' : bcTan (algebraMap Rv K) hxR (bcTan (algebraMap (𝓞 K) Rv) rfl w) = ∑ i, a i • ε i := by
      rw [bcTan_comp _ _ rfl hxR (by rw [← IsScalarTower.algebraMap_eq]; exact hx), ← hw]
      refine tan_ext ?_
      rw [left_bcTan, left_bcTan, ← IsScalarTower.algebraMap_eq]
    obtain ⟨b, hb⟩ := mem_range_of_dvr hTS t Rv K _ xK hxR r ε hε a _ hw' i
    exact hb ▸ b.2
  have h : a i ∈ (⊥ : Subalgebra (𝓞 K) K) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot (𝓞 K) K, Algebra.mem_iInf]
    exact key
  exact Algebra.mem_bot.1 h

end GlobalTheory.CochSat
