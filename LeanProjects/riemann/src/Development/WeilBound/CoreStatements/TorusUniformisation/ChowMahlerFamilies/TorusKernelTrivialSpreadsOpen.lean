import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.TorusKernelSpreading

theorem one_left {S : Scheme.{0}} (G : Over S) [GrpObj G] {Y : Scheme.{0}} (a : Y ⟶ S) :
    (1 : Over.mk a ⟶ G).left = a ≫ (η[G]).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem unit_w {S : Scheme.{0}} (G : Over S) [GrpObj G] : (η[G]).left ≫ G.hom = 𝟙 S := Over.w η[G]

noncomputable def pr (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    (splitTorus S X).left ⟶ Spec (torusRing ZU X) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

noncomputable def cv {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A]
    (f : Sp A ⟶ (splitTorus S X).left) : AddMonoidAlgebra (ULift.{0} ℤ) X →+* A :=
  (Spec.preimage (f ≫ pr S X)).hom

theorem cv_comp {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A B : Type} [CommRing A] [CommRing B]
    (k : A →+* B) (f : Sp A ⟶ (splitTorus S X).left) : cv (spMap k ≫ f) = k.comp (cv f) := by
  have : Spec.preimage ((spMap k ≫ f) ≫ pr S X) = Spec.preimage (f ≫ pr S X) ≫ CommRingCat.ofHom k := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc]
  exact congrArg CommRingCat.Hom.hom this

theorem ext_of_span {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A]
    (f g : Sp A ⟶ (splitTorus S X).left) (hw : f ≫ (splitTorus S X).hom = g ≫ (splitTorus S X).hom)
    (s : Set X) (hs : Submodule.span ℤ s = ⊤)
    (h : ∀ x ∈ s, cv f (AddMonoidAlgebra.single x 1) = cv g (AddMonoidAlgebra.single x 1)) : f = g := by
  have hmul : ∀ x y : X, (AddMonoidAlgebra.single (x + y) 1 : AddMonoidAlgebra (ULift.{0} ℤ) X) =
      AddMonoidAlgebra.single x 1 * AddMonoidAlgebra.single y 1 := by
    intro x y
    rw [AddMonoidAlgebra.single_mul_single, _root_.one_mul]
  have h0 : (AddMonoidAlgebra.single (0 : X) 1 : AddMonoidAlgebra (ULift.{0} ℤ) X) = 1 := rfl
  have hall : ∀ x : X, cv f (AddMonoidAlgebra.single x 1) = cv g (AddMonoidAlgebra.single x 1) := by
    intro x
    have hx : x ∈ AddSubgroup.closure s := by
      rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; trivial
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact h x hx
    | zero => rw [h0, map_one, map_one]
    | add x y _ _ hx hy => rw [hmul, map_mul, map_mul, hx, hy]
    | neg x _ hx =>
      have e1 : cv f (AddMonoidAlgebra.single (-x) 1) * cv f (AddMonoidAlgebra.single x 1) = 1 := by
        rw [← map_mul, ← hmul, neg_add_cancel, h0, map_one]
      have e2 : cv g (AddMonoidAlgebra.single x 1) * cv g (AddMonoidAlgebra.single (-x) 1) = 1 := by
        rw [← map_mul, ← hmul, add_neg_cancel, h0, map_one]
      rw [hx] at e1
      exact left_inv_eq_right_inv e1 e2
  have hcv : cv f = cv g := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) hall
    have : (cv f).comp AddMonoidAlgebra.singleZeroRingHom = (cv g).comp AddMonoidAlgebra.singleZeroRingHom := by
      have h2 : ((cv f).comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv.{0, 0} (R := ℤ)).symm.toRingHom =
          ((cv g).comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv.{0, 0} (R := ℤ)).symm.toRingHom :=
        RingHom.ext_int _ _
      ext z
      exact RingHom.congr_fun h2 z.down
    exact RingHom.congr_fun this r
  have hp : f ≫ pr S X = g ≫ pr S X := by
    have : Spec.preimage (f ≫ pr S X) = Spec.preimage (g ≫ pr S X) := CommRingCat.hom_ext hcv
    rw [← Spec.map_preimage (f ≫ pr S X), this, Spec.map_preimage]
  exact pullback.hom_ext hp hw

theorem aff_snd {P Q T : Scheme.{0}} (f : P ⟶ T) (g : Q ⟶ T) (h : IsAffineHom f) : IsAffineHom (pullback.snd f g) :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g) h

theorem cl_id (S : Scheme.{0}) : IsClosedImmersion (𝟙 S) := inferInstance

theorem exists_univ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsSeparated G.hom] {X : Type} [AddCommGroup X]
    (u : splitTorus S X ⟶ G) {R : Type} [CommRing R] (w : Sp R ⟶ S) :
    ∃ (C : Type) (_ : CommRing C) (ψ : R →+* C) (t₀ : Sp C ⟶ (splitTorus S X).left),
      t₀ ≫ (splitTorus S X).hom = spMap ψ ≫ w ∧ t₀ ≫ u.left = spMap ψ ≫ w ≫ (η[G]).left ∧
      ∀ (A : Type) [CommRing A] (h : R →+* A) (t : Sp A ⟶ (splitTorus S X).left),
        t ≫ u.left = spMap h ≫ w ≫ (η[G]).left → ∃ k : C →+* A, k.comp ψ = h ∧ spMap k ≫ t₀ = t := by
  have hcl : IsClosedImmersion (η[G]).left := by
    have : IsClosedImmersion ((η[G]).left ≫ G.hom) := by
      rw [unit_w]; exact cl_id S
    exact IsClosedImmersion.of_comp _ G.hom
  have haT : IsAffineHom (splitTorus S X).hom := by
    have : IsAffine (splitTorusAff ZU X).left := inferInstanceAs (IsAffine (Spec (torusRing ZU X)))
    have : IsAffineHom (splitTorusAff ZU X).hom := inferInstance
    exact aff_snd _ _ this
  have hq : pullback.snd u.left (η[G]).left = pullback.fst u.left (η[G]).left ≫ (splitTorus S X).hom := by
    rw [← Over.w u, ← Category.assoc, pullback.condition, Category.assoc, unit_w]
    exact (Category.comp_id _).symm
  have haq : IsAffineHom (pullback.snd u.left (η[G]).left) := by rw [hq]; infer_instance
  let e : Sp R ⟶ G.left := w ≫ (η[G]).left
  have hK : IsAffine (pullback u.left e) := by
    have : IsAffine (pullback (pullback.snd u.left (η[G]).left) w) := inferInstance
    exact .of_isIso (pullbackLeftPullbackSndIso u.left (η[G]).left w).inv
  let K := pullback u.left e
  let ψ : CommRingCat.of R ⟶ Γ(K, ⊤) := Spec.preimage (K.isoSpec.inv ≫ pullback.snd u.left e)
  have hψ : spMap ψ.hom = K.isoSpec.inv ≫ pullback.snd u.left e := Spec.map_preimage _
  have hu : (K.isoSpec.inv ≫ pullback.fst u.left e) ≫ u.left = spMap ψ.hom ≫ e := by
    rw [hψ, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨Γ(K, ⊤), inferInstance, ψ.hom, K.isoSpec.inv ≫ pullback.fst u.left e, ?_, hu, ?_⟩
  · rw [← Over.w u, ← Category.assoc, hu]
    simp only [e, Category.assoc, unit_w, Category.comp_id]
  · intro A _ h t ht
    let l : Sp A ⟶ K := pullback.lift t (spMap h) ht
    let k : Γ(K, ⊤) ⟶ CommRingCat.of A := Spec.preimage (l ≫ K.isoSpec.hom)
    have hk : spMap k.hom = l ≫ K.isoSpec.hom := Spec.map_preimage _
    refine ⟨k.hom, ?_, ?_⟩
    · have : ψ ≫ k = CommRingCat.ofHom h := by
        apply Spec.map_injective
        rw [Spec.map_comp]
        change spMap k.hom ≫ spMap ψ.hom = _
        rw [hk, hψ, Category.assoc, Iso.hom_inv_id_assoc]
        exact pullback.lift_snd _ _ _
      exact congrArg CommRingCat.Hom.hom this
    · rw [hk, Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.lift_fst _ _ _

theorem exists_factor {Z : Scheme.{0}} [IsIntegral Z] {L : Type} [Field L] {j : Sp L ⟶ Z}
    (hj : GlobalTheory.IsGenericPointHom j) {W : Z.Opens} (hW : IsAffineOpen W) [Nonempty W] {A : Type} [CommRing A]
    (m : Γ(Z, W) →+* A) (hm : ∀ y : nonZeroDivisors Γ(Z, W), IsUnit (m y)) :
    ∃ g : L →+* A, spMap g ≫ j = spMap m ≫ hW.fromSpec := by
  obtain ⟨e, rfl⟩ := hj
  have := functionField_isFractionRing_of_isAffineOpen Z W hW
  let g₀ : Z.functionField →+* A := IsLocalization.lift hm
  have hg₀ : g₀.comp (algebraMap _ _) = m := IsLocalization.lift_comp hm
  let g : CommRingCat.of L ⟶ CommRingCat.of A := Spec.preimage (spMap g₀ ≫ e.inv)
  have hg : spMap g.hom = spMap g₀ ≫ e.inv := Spec.map_preimage _
  refine ⟨g.hom, ?_⟩
  have hmem : genericPoint Z ∈ W := ((genericPoint_spec Z).mem_open_set_iff W.isOpen).2 (by
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty W›
    exact ⟨x, trivial, hx⟩)
  rw [hg, Category.assoc, Iso.inv_hom_id_assoc, ← hW.fromSpecStalk_eq_fromSpecStalk hmem, ← hg₀,
    IsAffineOpen.fromSpecStalk, ← Category.assoc]
  congr 1
  exact (Spec.map_comp _ _).symm

end PositivityTheory.Xgn.TorusKernelSpreading

open PositivityTheory.Xgn.TorusKernelSpreading in
theorem PositivityTheory.Xgn.torus_kernel_trivial_spreads_open : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (G : Over Z') [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus Z' X ⟶ G) [IsMonHom u] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → (∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Z'), ⊤ ≤ a ⁻¹ᵁ V → ∀ t : Over.mk a ⟶ splitTorus Z' X, t ≫ u = 1 → t = 1 := by
  intro Z' _ G _ _ X _ _ _ u _ L' _ j hj H
  classical
  obtain ⟨x₀⟩ : Nonempty Z' := inferInstance
  obtain ⟨_, ⟨W, hW, rfl⟩, hx₀, -⟩ := Z'.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x₀) isOpen_univ
  have : Nonempty W := ⟨⟨x₀, hx₀⟩⟩
  let w : Sp Γ(Z', W) ⟶ Z' := hW.fromSpec
  have : IsOpenImmersion w := IsAffineOpen.isOpenImmersion_fromSpec hW
  obtain ⟨C, _, ψ, t₀, ht₁, ht₂, huniv⟩ := exists_univ G u w
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  let o : Sp C ⟶ (splitTorus Z' X).left := spMap ψ ≫ w ≫ (η[splitTorus Z' X]).left
  let M : Submonoid C := (nonZeroDivisors Γ(Z', W)).map ψ
  have hsp : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  have hloc : spMap (algebraMap C (Localization M)) ≫ t₀ = spMap (algebraMap C (Localization M)) ≫ o := by
    obtain ⟨g, hg⟩ := exists_factor hj hW ((algebraMap C (Localization M)).comp ψ)
      (fun y => IsLocalization.map_units (Localization M) (⟨ψ y, y, y.2, rfl⟩ : M))
    rw [hsp, Category.assoc] at hg
    have h1 := H (Localization M) g (Over.homMk (spMap (algebraMap C (Localization M)) ≫ t₀) (by
      change (_ ≫ t₀) ≫ _ = spMap g ≫ j
      rw [hg, Category.assoc, ht₁])) (by
      apply Over.OverMorphism.ext
      rw [one_left]
      change (_ ≫ t₀) ≫ u.left = (spMap g ≫ j) ≫ _
      rw [hg]
      simp only [Category.assoc, ht₂, w])
    have h2 := congrArg (·.left) h1
    simp only [one_left, hg] at h2
    simpa only [o, w, Category.assoc, Over.homMk_left] using h2
  have hr : ∀ x : X, ∃ r : Γ(Z', W), r ≠ 0 ∧
      ψ r * cv t₀ (AddMonoidAlgebra.single x 1) = ψ r * cv o (AddMonoidAlgebra.single x 1) := by
    intro x
    have h1 := RingHom.congr_fun (congrArg cv hloc) (AddMonoidAlgebra.single x 1)
    rw [cv_comp, cv_comp] at h1
    obtain ⟨⟨_, r, hr, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 h1
    exact ⟨r, nonZeroDivisors.ne_zero hr, hc⟩
  choose r hr0 hr using hr
  let p : Γ(Z', W) := ∏ x ∈ s, r x
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => hr0 x
  let D : (Sp Γ(Z', W)).Opens := PrimeSpectrum.basicOpen p
  refine ⟨w ''ᵁ D, ⟨w (⊥ : PrimeSpectrum Γ(Z', W)), (⊥ : PrimeSpectrum Γ(Z', W)), hp, rfl⟩, ?_⟩
  intro A _ a ha t ht
  have hrange : Set.range a ⊆ Set.range w := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, -, hz⟩ : a y ∈ w ''ᵁ D := ha (Set.mem_univ y)
    exact ⟨z, hz⟩
  let l := IsOpenImmersion.lift w a hrange
  have hl : l ≫ w = a := IsOpenImmersion.lift_fac _ _ _
  let h : Γ(Z', W) →+* A := (Spec.preimage l).hom
  have hh : spMap h = l := Spec.map_preimage l
  have hunit : IsUnit (h p) := by
    by_contra hn
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
    let y : Sp A := (⟨m, hm.isPrime⟩ : PrimeSpectrum A)
    obtain ⟨z, hzD, hz⟩ : a y ∈ w ''ᵁ D := ha (Set.mem_univ y)
    rw [← hl, Scheme.Hom.comp_apply] at hz
    have hz' : z = spMap h y := by rw [hh]; exact w.isOpenEmbedding.injective hz
    subst hz'
    exact hzD hmem
  have ha' : a = spMap h ≫ w := by rw [hh, hl]
  have htu : t.left ≫ u.left = spMap h ≫ w ≫ (η[G]).left := by
    have := congrArg (·.left) ht
    simp only [one_left, Over.comp_left] at this
    rw [this, ← Category.assoc, ← ha']
  obtain ⟨k, hk₁, hk₂⟩ := huniv A h t.left htu
  apply Over.OverMorphism.ext
  have ho : (1 : Over.mk a ⟶ splitTorus Z' X).left = spMap k ≫ o := by
    rw [one_left, ha', ← hk₁, hsp]
    simp only [o, Category.assoc]
  refine ext_of_span (A := A) _ _ ((Over.w t).trans (Over.w _).symm) s hs fun x hx => ?_
  have hux : IsUnit (k (ψ (r x))) := by
    have : k (ψ (r x)) = h (r x) := RingHom.congr_fun hk₁ _
    rw [this]
    exact isUnit_of_dvd_unit (map_dvd h (Finset.dvd_prod_of_mem r hx)) hunit
  have e1 := congrArg k (hr x)
  rw [map_mul, map_mul] at e1
  have e2 := hux.mul_left_cancel e1
  have e3 : cv (A := A) t.left = k.comp (cv t₀) := by rw [← cv_comp, hk₂]
  have e4 : cv (A := A) (1 : Over.mk a ⟶ splitTorus Z' X).left = k.comp (cv o) := by rw [← cv_comp, ← ho]
  rw [e3, e4]
  exact e2
