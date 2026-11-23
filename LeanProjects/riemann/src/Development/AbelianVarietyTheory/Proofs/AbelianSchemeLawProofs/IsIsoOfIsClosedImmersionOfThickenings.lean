import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThickeningClosed

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.ThickeningClosed.ker_ideal_le_ker {X Z : Scheme.{0}} (ι : Z ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) {D : CommRingCat.{0}} (ψ : Γ(X, U) ⟶ D) (l : Spec D ⟶ Z)
    (hl : l ≫ ι = Spec.map ψ ≫ hU.fromSpec) :
    ι.ker.ideal ⟨U, hU⟩ ≤ RingHom.ker ψ.hom := by
  intro a ha
  have h0 : ι.app U a = 0 := ι.ideal_ker_le ⟨U, hU⟩ ha
  have e : (⊤ : (Spec D).Opens) ≤ (l ≫ ι) ⁻¹ᵁ U := by
    rw [hl, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]; simp
  have h1 : (l ≫ ι).appLE U ⊤ e a = 0 := by
    rw [Scheme.Hom.comp_appLE]; simp [h0]
  have h2 : ∀ (g) (_ : g = Spec.map ψ ≫ hU.fromSpec) (e : (⊤ : (Spec D).Opens) ≤ g ⁻¹ᵁ U),
      g.appLE U ⊤ e = ψ ≫ (Scheme.ΓSpecIso D).inv := by
    rintro g rfl e
    rw [Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self, Category.assoc]
    erw [Scheme.Hom.map_appLE]
    rw [Iso.inv_comp_eq, ← cancel_mono (Scheme.ΓSpecIso D).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Scheme.ΓSpecIso_naturality]
    rfl
  rw [h2 _ hl e, CommRingCat.comp_apply] at h1
  rw [RingHom.mem_ker]
  have h3 := congrArg (Scheme.ΓSpecIso D).hom.hom h1
  rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h3

def zeroLocusOpen {X : Scheme.{0}} (K : X.IdealSheafData) : Set X :=
  {x | ∃ V : X.affineOpens, x ∈ V.1 ∧ K.ideal V = ⊥}

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.ThickeningClosed.isOpen_zeroLocusOpen {X : Scheme.{0}} (K : X.IdealSheafData) :
    IsOpen (_root_.GlobalTheory.ThickeningClosed.zeroLocusOpen K) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨V, hxV, hV⟩
  exact ⟨V.1, fun y hy ↦ ⟨V, hy, hV⟩, V.1.2, hxV⟩

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.ThickeningClosed.exists_mul_eq_zero_of_mem {X : Scheme.{0}} (K : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U))
    (hq : U.2.fromSpec q ∈ _root_.GlobalTheory.ThickeningClosed.zeroLocusOpen K) {a : Γ(X, U)}
    (ha : a ∈ K.ideal U) : ∃ s ∉ q.asIdeal, s * a = 0 := by
  have hq' : ∃ V : X.affineOpens, U.2.fromSpec q ∈ V.1 ∧ K.ideal V = ⊥ := hq
  obtain ⟨V, hyV, hV⟩ := hq'
  have hyU : U.2.fromSpec q ∈ U.1 := by
    have : U.2.fromSpec q ∈ Set.range U.2.fromSpec := ⟨q, rfl⟩
    rwa [U.2.range_fromSpec] at this
  obtain ⟨f, hfV, hyf⟩ := U.2.exists_basicOpen_le (V := V.1) ⟨_, hyV⟩ hyU
  have hW : K.ideal (X.affineBasicOpen f) = ⊥ := by
    rw [← K.map_ideal (U := X.affineBasicOpen f) (V := V) hfV, hV, Ideal.map_bot]
  have hfq : f ∉ q.asIdeal := by
    have : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f := hyf
    rw [U.2.fromSpec_preimage_basicOpen] at this
    exact this
  have ha' := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom ha
  rw [K.map_ideal_basicOpen, hW] at ha'
  have h0 : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom a = 0 := ha'
  have := U.2.isLocalization_basicOpen f
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ a).mp h0
  exact ⟨f ^ n, fun h ↦ hfq (q.2.mem_of_pow_mem n h), hm⟩

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.ThickeningClosed.mem_of_thickenings {R : Type} [CommRing R] (I : Ideal R)
    {X Z : Scheme.{0}} [IsLocallyNoetherian X] (f : X ⟶ Spec (CommRingCat.of R)) (ι : Z ⟶ X)
    (h : ∀ n : ℕ, ∃ l : pullback f (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I n) ⟶ Z, l ≫ ι = pullback.fst f (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I n))
    (x : X) (hx : I ≤ (f x).asIdeal) : x ∈ _root_.GlobalTheory.ThickeningClosed.zeroLocusOpen ι.ker := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (X.isBasis_affineOpens).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  set φ : CommRingCat.of R ⟶ Γ(X, V) := Spec.preimage (hV.fromSpec ≫ f) with hφ
  have hφ' : Spec.map φ = hV.fromSpec ≫ f := Spec.map_preimage _
  set J : Ideal Γ(X, V) := I.map φ.hom with hJ
  have hK : ∀ n : ℕ, ι.ker.ideal ⟨V, hV⟩ ≤ J ^ (n + 1) := by
    intro n
    obtain ⟨l, hl⟩ := h n
    have hle : I ^ (n + 1) ≤ (J ^ (n + 1)).comap φ.hom :=
      Ideal.map_le_iff_le_comap.mp (Ideal.map_pow _ _ _).le
    let ψ : Γ(X, V) ⟶ CommRingCat.of (Γ(X, V) ⧸ J ^ (n + 1)) :=
      CommRingCat.ofHom (Ideal.Quotient.mk _)
    let τ : CommRingCat.of (R ⧸ I ^ (n + 1)) ⟶ CommRingCat.of (Γ(X, V) ⧸ J ^ (n + 1)) :=
      CommRingCat.ofHom (Ideal.quotientMap _ φ.hom hle)
    have hcomm : φ ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk _) ≫ τ := by
      ext r; rfl
    have hsq : (Spec.map ψ ≫ hV.fromSpec) ≫ f = Spec.map τ ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I n := by
      rw [Category.assoc, ← hφ', ← Spec.map_comp, hcomm, Spec.map_comp]
    have := _root_.GlobalTheory.ThickeningClosed.ker_ideal_le_ker ι hV ψ (pullback.lift _ _ hsq ≫ l)
      (by rw [Category.assoc, hl, pullback.lift_fst])
    simpa [ψ, Ideal.mk_ker] using this
  set p := hV.primeIdealOf ⟨x, hxV⟩ with hp
  have hpx : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hJp : J ≤ p.asIdeal := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    have : Spec.map φ p = f x := by rw [hφ', ← hpx]; rfl
    have h2 : (Spec.map φ p).asIdeal = p.asIdeal.comap φ.hom := rfl
    rw [← h2, this]
    exact hx
  have hkrull : ∀ a ∈ ι.ker.ideal ⟨V, hV⟩, ∃ g ∉ p.asIdeal, g * a = 0 := by
    intro a ha
    have hmem : a ∈ ⨅ n, J ^ n • (⊤ : Submodule Γ(X, V) Γ(X, V)) := by
      rw [Submodule.mem_iInf]
      intro n
      rw [smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right (Nat.le_succ n) (hK n ha)
    obtain ⟨g, hg1, hga⟩ := _root_.GlobalTheory.exists_smul_eq_zero_of_mem_iInf_pow_smul J hmem
    refine ⟨g, fun hg ↦ p.2.ne_top ((Ideal.eq_top_iff_one _).mpr ?_), hga⟩
    have : g - (g - 1) ∈ p.asIdeal := Ideal.sub_mem _ hg (hJp hg1)
    simpa using this
  have hfin : ∀ t : Finset Γ(X, V), (↑t : Set Γ(X, V)) ⊆ ι.ker.ideal ⟨V, hV⟩ →
      ∃ g ∉ p.asIdeal, ∀ a ∈ t, g * a = 0 := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, fun h1 ↦ p.2.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
    | insert b t _ ih =>
      intro ht
      obtain ⟨g, hg, hgt⟩ := ih ((Finset.coe_subset.mpr (Finset.subset_insert b t)).trans ht)
      obtain ⟨g', hg', hg'b⟩ := hkrull b (ht (by simp))
      refine ⟨g * g', fun hm ↦ (p.2.mem_or_mem hm).elim hg hg', ?_⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rw [mul_assoc, hg'b, mul_zero]
      · rw [mul_right_comm, hgt a ha, zero_mul]
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian (ι.ker.ideal ⟨V, hV⟩) :)
  obtain ⟨g, hg, hgt⟩ := hfin t (ht ▸ Submodule.subset_span)
  have hgK : ∀ a ∈ ι.ker.ideal ⟨V, hV⟩, g * a = 0 := by
    intro a ha
    rw [← ht] at ha
    refine Submodule.span_induction (fun b hb ↦ hgt b hb) (by simp) (fun b c _ _ hb hc ↦ ?_)
      (fun r b _ hb ↦ ?_) ha
    · rw [mul_add, hb, hc, add_zero]
    · rw [smul_eq_mul, mul_left_comm, hb, mul_zero]
  show ∃ V : X.affineOpens, x ∈ V.1 ∧ ι.ker.ideal V = ⊥
  refine ⟨X.affineBasicOpen (U := ⟨V, hV⟩) g, ?_, ?_⟩
  · have hmem : p ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hV.fromSpec_preimage_basicOpen]; exact hg
    rw [← hpx]; exact hmem
  · have := hV.isLocalization_basicOpen g
    rw [← ι.ker.map_ideal_basicOpen ⟨V, hV⟩ g]
    refine (Ideal.map_eq_bot_iff_le_ker _).mpr fun a ha ↦ ?_
    rw [RingHom.mem_ker]
    have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g) :=
      IsLocalization.Away.algebraMap_isUnit g
    have h0 := congrArg (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (hgK a ha)
    rw [map_mul, map_zero] at h0
    exact (hu.mul_right_eq_zero).mp h0

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.ThickeningClosed.noZeroDivisors_fiber {R C : Type} [CommRing R] [CommRing C]
    [Algebra R C] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap R C)) = j ≫ f)
    (p : PrimeSpectrum R) [IsIntegral (f.fiber p)] : NoZeroDivisors (p.asIdeal.Fiber C) := by
  rcases subsingleton_or_nontrivial (p.asIdeal.Fiber C) with hs | hn
  · exact ⟨fun {a b} _ ↦ Or.inl (Subsingleton.elim a 0)⟩
  let e := Spec.fiberToSpecResidueFieldIso R C p
  let s := (Spec (CommRingCat.of R)).fromSpecResidueField p
  let u₁ : Spec (CommRingCat.of (p.asIdeal.Fiber C)) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R C))) s := (Arrow.leftFunc.mapIso e).inv
  let u₂ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R C))) s ⟶ pullback (j ≫ f) s :=
    (pullback.congrHom hj rfl).hom
  let u₃ : pullback (j ≫ f) s ⟶ pullback j (pullback.fst f s) :=
    (pullbackRightPullbackFstIso f s j).inv
  let u₄ : pullback j (pullback.fst f s) ⟶ f.fiber p := pullback.snd j (pullback.fst f s)
  haveI : IsOpenImmersion u₁ := show IsOpenImmersion (Arrow.leftFunc.mapIso e).inv from inferInstance
  haveI : IsOpenImmersion u₂ := show IsOpenImmersion (pullback.congrHom hj rfl).hom from inferInstance
  haveI : IsOpenImmersion u₃ := show IsOpenImmersion (pullbackRightPullbackFstIso f s j).inv from inferInstance
  haveI : IsOpenImmersion u₄ := show IsOpenImmersion (pullback.snd j (pullback.fst f s)) from inferInstance
  haveI : AlgebraicGeometry.IsIntegral (Spec (CommRingCat.of (p.asIdeal.Fiber C))) :=
    isIntegral_of_isOpenImmersion (u₁ ≫ u₂ ≫ u₃ ≫ u₄)
  haveI : IsDomain (p.asIdeal.Fiber C) :=
    (affine_isIntegral_iff (CommRingCat.of (p.asIdeal.Fiber C))).mp inferInstance
  infer_instance

end ThickeningClosed

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.isIso_of_isClosedImmersion_of_thickenings :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
      ∀ (H : Over (Spec (CommRingCat.of R))) [Flat H.hom] [LocallyOfFiniteType H.hom]
        (_e : 𝟙_ _ ⟶ H), (∀ p, IsIntegral (H.hom.fiber p)) →
        ∀ (Z : Scheme.{0}) (ι : Z ⟶ H.left) [IsClosedImmersion ι],
          (∀ n : ℕ, ∃ l : (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj R I n H).left ⟶ Z, l ≫ ι = (_root_.ReciprocityTheory.ChartRestriction.G.Out.fstG I n H).left) →
            IsIso ι := by
  intro R _ _ I hI H _ _ e hfib Z ι _ hth
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  have hpre : ∀ U : H.left.affineOpens,
      Spec.map (Spec.preimage (U.2.fromSpec ≫ H.hom)) = U.2.fromSpec ≫ H.hom :=
    fun U ↦ Spec.map_preimage _
  have hft : ∀ U : H.left.affineOpens, (Spec.preimage (U.2.fromSpec ≫ H.hom)).hom.FiniteType := by
    intro U
    haveI := U.2.isOpenImmersion_fromSpec
    have : LocallyOfFiniteType (Spec.map (Spec.preimage (U.2.fromSpec ≫ H.hom))) := by
      rw [hpre]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  have hfl : ∀ U : H.left.affineOpens, (Spec.preimage (U.2.fromSpec ≫ H.hom)).hom.Flat := by
    intro U
    haveI := U.2.isOpenImmersion_fromSpec
    rw [← Flat.SpecMap_iff, hpre]; infer_instance
  haveI : IsLocallyNoetherian H.left := ⟨fun U ↦ by
    letI := (Spec.preimage (U.2.fromSpec ≫ H.hom)).hom.toAlgebra
    haveI : Algebra.FiniteType R Γ(H.left, U) := hft U
    exact Algebra.FiniteType.isNoetherianRing R _⟩
  have hsec : ∀ s : Spec (CommRingCat.of R), H.hom (e.left s) = s := by
    intro s
    have hw := Over.w e
    have : (e.left ≫ H.hom) s = s := by rw [hw]; rfl
    exact this
  have hqU : ∀ (U : H.left.affineOpens) (q : PrimeSpectrum Γ(H.left, U)), U.2.fromSpec q ∈ U.1 := by
    intro U q
    have : U.2.fromSpec q ∈ Set.range U.2.fromSpec := ⟨q, rfl⟩
    rwa [U.2.range_fromSpec] at this
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : H.left.affineOpens ↦ U)
    (iSup_affineOpens_eq_top _) fun U ↦ ?_
  refine eq_bot_iff.mpr fun a ha ↦ ?_
  show a = 0
  letI : Algebra R Γ(H.left, U) := (Spec.preimage (U.2.fromSpec ≫ H.hom)).hom.toAlgebra
  haveI : Module.Flat R Γ(H.left, U) := hfl U
  haveI : IsNoetherianRing Γ(H.left, U) := IsLocallyNoetherian.component_noetherian U
  haveI := U.2.isOpenImmersion_fromSpec
  have hj : Spec.map (CommRingCat.ofHom (algebraMap R Γ(H.left, U))) = U.2.fromSpec ≫ H.hom :=
    hpre U
  have hpt : ∀ q : PrimeSpectrum Γ(H.left, U),
      Ideal.under R q.asIdeal = (H.hom (U.2.fromSpec q)).asIdeal := by
    intro q
    have : Spec.map (CommRingCat.ofHom (algebraMap R Γ(H.left, U))) q = H.hom (U.2.fromSpec q) := by
      rw [hj]; rfl
    rw [← this]; rfl
  refine _root_.GlobalTheory.eq_zero_of_flat_of_forall_fiber (A := R) (B := Γ(H.left, U))
    (L := Γ(H.left, U))
    (fun p _ ↦ haveI := hfib p; _root_.GlobalTheory.ThickeningClosed.noZeroDivisors_fiber H.hom U.2.fromSpec hj p)
    (fun q _ ↦ ?_)
  obtain ⟨m, hm, hPm⟩ := Ideal.exists_le_maximal _ (H.hom (U.2.fromSpec q)).2.ne_top
  let M : Spec (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have hIM : I ≤ (H.hom (e.left M)).asIdeal := by
    rw [hsec]; exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  have hy := _root_.GlobalTheory.ThickeningClosed.mem_of_thickenings I H.hom ι hth (e.left M) hIM
  have hPM : H.hom (U.2.fromSpec q) ⤳ H.hom (e.left M) := by
    rw [hsec]; exact (PrimeSpectrum.le_iff_specializes _ M).mp hPm
  obtain ⟨y', hy'y, hy'P⟩ := Flat.generalizingMap H.hom hPM
  have hy'Z := hy'y.mem_open (_root_.GlobalTheory.ThickeningClosed.isOpen_zeroLocusOpen _) hy
  haveI := hfib (H.hom (U.2.fromSpec q))
  have hirr : IsIrreducible (H.hom ⁻¹' {H.hom (U.2.fromSpec q)}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (H.hom.fiberι _).continuous.continuousOn
  obtain ⟨z, hzP, hzZ, hzU⟩ := hirr.2 _ _ (_root_.GlobalTheory.ThickeningClosed.isOpen_zeroLocusOpen _) U.1.isOpen
    ⟨y', hy'P, hy'Z⟩ ⟨U.2.fromSpec q, rfl, hqU U q⟩
  have hq'z : U.2.fromSpec (U.2.primeIdealOf ⟨z, hzU⟩) = z := U.2.fromSpec_primeIdealOf ⟨z, hzU⟩
  refine ⟨U.2.primeIdealOf ⟨z, hzU⟩, ?_, ?_⟩
  · rw [hpt, hpt, hq'z]
    exact congrArg PrimeSpectrum.asIdeal hzP
  · rw [_root_.GlobalTheory.localizedModule_mk_one_eq_zero_iff]
    exact _root_.GlobalTheory.ThickeningClosed.exists_mul_eq_zero_of_mem ι.ker U _ (by rw [hq'z]; exact hzZ) ha

end GlobalTheory
