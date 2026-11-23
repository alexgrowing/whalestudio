import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TransSec
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

section Units

variable {X : Scheme.{0}} [IsIntegral X]

def UnitAt (x : X) (t : X.functionField) : Prop :=
  ∃ u : (X.presheaf.stalk x)ˣ, algebraMap _ X.functionField (u : X.presheaf.stalk x) = t

theorem UnitAt.mul {x : X} {s t : X.functionField} (hs : UnitAt x s) (ht : UnitAt x t) : UnitAt x (s * t) := by
  obtain ⟨u, rfl⟩ := hs
  obtain ⟨v, rfl⟩ := ht
  exact ⟨u * v, by rw [Units.val_mul, map_mul]⟩

theorem UnitAt.inv {x : X} {s : X.functionField} (hs : UnitAt x s) : UnitAt x s⁻¹ := by
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u⁻¹, by rw [map_units_inv]⟩

theorem UnitAt.ne_zero {x : X} {s : X.functionField} (hs : UnitAt x s) : s ≠ 0 := by
  obtain ⟨u, rfl⟩ := hs
  exact (u.isUnit.map _).ne_zero

theorem isOpen_unitAt (t : X.functionField) : IsOpen {x : X | UnitAt x t} := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro x ⟨u, hu⟩
  obtain ⟨V, hV, s, hs⟩ := X.presheaf.exists_germ_eq (u : X.presheaf.stalk x)
  refine ⟨X.basicOpen s, fun y hy => ?_, (X.basicOpen s).isOpen,
    (X.mem_basicOpen s x hV).2 (by rw [hs]; exact u.isUnit)⟩
  have hyV := X.basicOpen_le s hy
  refine ⟨((X.mem_basicOpen s y hyV).1 hy).unit, ?_⟩
  rw [← hu, ← hs, IsUnit.unit_spec]
  exact (X.presheaf.germ_stalkSpecializes_apply hyV _ _).trans
    (X.presheaf.germ_stalkSpecializes_apply hV _ _).symm

theorem exists_unit_eq [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (V : X.Opens) [Nonempty V]
    (t : X.functionField) (h0 : t ≠ 0) (h : ∀ x ∈ V, Order.coheight x = 1 → UnitAt x t) :
    ∃ u : Γ(X, V)ˣ, X.germToFunctionField V u = t := by
  obtain ⟨s, hs⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V t fun x hx h1 =>
    let ⟨u, hu⟩ := h x hx h1; ⟨u, hu⟩
  obtain ⟨s', hs'⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V t⁻¹ fun x hx h1 =>
    let ⟨u, hu⟩ := (h x hx h1).inv; ⟨u, hu⟩
  have : IsUnit s := IsUnit.of_mul_eq_one s' (X.germToFunctionField_injective V (by
    rw [map_mul, hs, hs', map_one, mul_inv_cancel₀ h0]))
  exact ⟨this.unit, hs⟩

end Units

theorem exists_basicOpen {R : Type} [CommRing R] [IsDedekindDomain R] {X : Scheme.{0}} [NoetherianSpace X]
    (q : X ⟶ Sp R) (v : Sp R) (S : Set X) (hS : IsOpen S) (h0 : ∀ x, (q x).asIdeal = ⊥ → x ∈ S)
    (hv : v.asIdeal ≠ ⊥ → ∃ ξ ∈ S, Order.coheight ξ = 1 ∧ ∀ x, q x = v → ξ ⤳ x) :
    ∃ f : R, f ∉ v.asIdeal ∧ ∀ x, f ∉ (q x).asIdeal → Order.coheight x = 1 → x ∈ S := by
  classical
  obtain ⟨T, hT, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS.isClosed_compl
  have key : ∀ Z : T, ∃ f : R, f ∉ v.asIdeal ∧ ∀ x ∈ Z.1, f ∉ (q x).asIdeal → q x = v ∧ v.asIdeal ≠ ⊥ := by
    rintro ⟨Z, hZ⟩
    have hg := (hi Z hZ).isGenericPoint_genericPoint (hc Z hZ)
    set z := (hi Z hZ).genericPoint
    have hz : (q z).asIdeal ≠ ⊥ := fun h => (hU.ge (Set.subset_sUnion_of_mem hZ hg.mem)) (h0 z h)
    have hm : (q z).asIdeal.IsMaximal := (q z).2.isMaximal hz
    have hx : ∀ x ∈ Z, q x = q z := fun x hx => PrimeSpectrum.ext (hm.eq_of_le (q x).2.ne_top
      ((PrimeSpectrum.le_iff_specializes _ _).2 ((hg.specializes hx).map q.continuous))).symm
    by_cases h : q z = v
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.2.ne_top, fun x hx' _ => ⟨(hx x hx').trans h, h ▸ hz⟩⟩
    · obtain ⟨f, hf, hf'⟩ := SetLike.not_le_iff_exists.1 fun hle : (q z).asIdeal ≤ v.asIdeal =>
        h (PrimeSpectrum.ext (hm.eq_of_le v.2.ne_top hle))
      exact ⟨f, hf', fun x hx' hn => (hn (by rw [hx x hx']; exact hf)).elim⟩
  choose f hf hf' using key
  have := hT.fintype
  refine ⟨∏ Z, f Z, v.asIdeal.primeCompl.prod_mem fun Z _ => hf Z, fun x hx h1 => ?_⟩
  by_contra hxS
  obtain ⟨Z, hZ, hxZ⟩ := hU.le hxS
  obtain ⟨e, hne⟩ := hf' ⟨Z, hZ⟩ x hxZ fun h =>
    hx (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem f (Finset.mem_univ _)) h)
  obtain ⟨ξ, hξ, h1', hs⟩ := hv hne
  have hlt : x < ξ := lt_of_le_not_ge (hs x e) fun h' =>
    hxS ((show x ⤳ ξ from h').mem_open hS hξ)
  have := Order.coheight_add_one_le hlt
  rw [h1, h1'] at this
  exact absurd this (by decide)

theorem constFn_top {A : Type} [CommRing A] {X : Scheme.{0}} (q : X ⟶ Sp A) (a : A) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn q ⊤ a = q.appTop ((Scheme.ΓSpecIso (.of A)).inv a) :=
  congrArg (fun m : Γ(Sp A, ⊤) ⟶ Γ(X, ⊤) => m ((Scheme.ΓSpecIso (.of A)).inv a)) (q.appLE_eq_app (U := ⊤))

theorem app_constFn {A C : Type} [CommRing A] [CommRing C] {g : A →+* C} {X Y : Scheme.{0}} {q : X ⟶ Sp A}
    {p : Y ⟶ Sp C} {φ : Y ⟶ X} (w : φ ≫ q = p ≫ spMap g) (a : A) :
    φ.app ⊤ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn q ⊤ a) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p ⊤ (g a) := by
  have h₁ := congrArg (fun φ : Y ⟶ Sp A ↦ φ.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) w
  have h₂ := congrArg (fun φ : CommRingCat.of A ⟶ Γ(Spec (.of C), ⊤) ↦ φ a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  rw [constFn_top, constFn_top]
  exact h₁.trans (congrArg p.appTop h₂.symm)

theorem exists_fibre_generic {R : Type} [CommRing R] [IsDedekindDomain R] {X : Scheme.{0}} [IsIntegral X]
    (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (v : Sp R) (hv : v.asIdeal ≠ ⊥) :
    ∃ (ξ : X) (π : R), π ≠ 0 ∧ (∀ x, q x = v → ξ ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧
      Irreducible (X.presheaf.germ ⊤ ξ trivial (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn q ⊤ π)) := by
  let V := Localization.AtPrime v.asIdeal
  have : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hv V
  obtain ⟨π, hπ⟩ : ∃ π : R, Irreducible (algebraMap R V π) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨⟨π, s⟩, e⟩ := IsLocalization.surj v.asIdeal.primeCompl ϖ
    exact ⟨π, e ▸ (irreducible_mul_isUnit (IsLocalization.map_units V s)).2 hϖ⟩
  let l := spMap (algebraMap R V)
  have : Flat l := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : IsPreimmersion l := IsPreimmersion.of_isLocalization v.asIdeal.primeCompl
  have H := IsPullback.of_hasPullback q l
  set ψ := pullback.fst q l
  set f := pullback.snd q l
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks ψ
  obtain ⟨h₁, h₂⟩ := DvrModel.isDiscreteValuationRing_stalk_generic hπ hs
  have h₃ := DvrModel.notMem_basicOpen_iff_specializes hπ hs
  generalize (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))) (genericPoint _) = ξ
    at h₁ h₂ h₃
  let E := (asIso (ψ.stalkMap ξ)).commRingCatIsoToRingEquiv
  refine ⟨ψ ξ, π, fun h => hπ.ne_zero (by rw [h, map_zero]), fun x hx => ?_,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.symm, ?_⟩
  · obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback H x (IsLocalRing.closedPoint V)
      (hx.trans (PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := v.asIdeal)).symm))
    exact ((h₃ y).1 ((DvrModel.notMem_basicOpen_iff f hπ y).2 hy)).map ψ.continuous
  · rw [← MulEquiv.irreducible_iff E.toMulEquiv]
    convert h₂ using 1
    exact (ψ.germ_stalkMap_apply ⊤ ξ trivial _).trans
      (congrArg _ ((app_constFn H.w π).trans (constFn_top _ _)))

section Transport

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) (hφ : φ (genericPoint Y) ⤳ genericPoint X)

noncomputable def ffMap : X.functionField ⟶ Y.functionField :=
  X.presheaf.stalkSpecializes hφ ≫ φ.stalkMap (genericPoint Y)

theorem ffMap_germ (V : X.Opens) [Nonempty V] (W : Y.Opens) [Nonempty W] (h : W ≤ φ ⁻¹ᵁ V) (s : Γ(X, V)) :
    ffMap φ hφ (X.germToFunctionField V s) = Y.germToFunctionField W (φ.appLE V W h s) := by
  refine (congrArg (φ.stalkMap _) (X.presheaf.germ_stalkSpecializes_apply _ hφ s)).trans
    ((φ.germ_stalkMap_apply V _ _ s).trans ?_)
  exact (Y.presheaf.germ_res_apply (homOfLE h) _ _ _).symm

variable [∀ y, IsIso (φ.stalkMap y)]

theorem ffMap_bijective : Function.Bijective (ffMap φ hφ) := by
  have : IsIso (X.presheaf.stalkSpecializes hφ) :=
    (X.presheaf.stalkCongr ((genericPoint_specializes _).antisymm hφ)).isIso_hom
  have : IsIso (ffMap φ hφ) := by unfold ffMap; infer_instance
  exact ConcreteCategory.bijective_of_isIso _

theorem unitAt_of_isUnit {W : Y.Opens} [Nonempty W] {τ : Γ(Y, W)} (hτ : IsUnit τ) {y : Y} (hy : y ∈ W)
    {t : X.functionField} (ht : ffMap φ hφ t = Y.germToFunctionField W τ) : UnitAt (φ y) t := by
  obtain ⟨σ, hσ⟩ := (ConcreteCategory.bijective_of_isIso (φ.stalkMap y)).2 (Y.presheaf.germ W y hy τ)
  have hu : IsUnit σ := (isUnit_map_iff (φ.stalkMap y).hom σ).1 (by
    rw [hσ]; exact hτ.map _)
  refine ⟨hu.unit, (ffMap_bijective φ hφ).1 ?_⟩
  rw [ht, IsUnit.unit_spec]
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq σ
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  have : Nonempty (φ ⁻¹ᵁ V) := ⟨⟨y, hV⟩⟩
  refine (congrArg (ffMap φ hφ) (X.presheaf.germ_stalkSpecializes_apply hV _ s)).trans
    ((ffMap_germ φ hφ V (φ ⁻¹ᵁ V) le_rfl s).trans ?_)
  rw [φ.germ_stalkMap_apply] at hσ
  rw [φ.appLE_eq_app]
  have := congrArg (Y.presheaf.stalkSpecializes (genericPoint_specializes y)) hσ
  rwa [Y.presheaf.germ_stalkSpecializes_apply, Y.presheaf.germ_stalkSpecializes_apply] at this

end Transport

open MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.MBX
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_const_mul_eq_unit : ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K) (M : LB X.left) (c : LB.Gen (M.pull φ)), Smooth X.hom → QuasiCompact X.hom → GeometricallyConnected X.hom → IsPullback φ p X.hom (spMap (algebraMap R K)) → M.IsLB → c.IsGen → ∀ v : Sp R, ∃ (f : R) (a : Kˣ), f ∉ v.asIdeal ∧ ∀ i : M.ι, ∃ u : Γ(X.left, M.U i ⊓ X.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f)ˣ, ∀ (W : Y.Opens) (h₁ : W ≤ (M.pull φ).U fun _ => i) (h₂ : W ≤ φ ⁻¹ᵁ (M.U i ⊓ X.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f)), (φ.appLE _ W h₂).hom (u : Γ(X.left, _)) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p W (a : K) * resG Y h₁ (c.s fun _ => i : Γ(Y, _)) := by
  intro R K _ _ _ _ _ _ X Y φ p M c hsm hqc hgc H hM hc v
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ X.hom hsm hgc
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian X.hom
  have : IsIntegral Y := DvrModel.isIntegral_of_geometricallyIntegral H
  have := isNormalScheme_of_smooth X.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : AlgebraicGeometry.IsNoetherian X.left := {}
  have hinj := IsFractionRing.injective R K
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) H.flip
    (Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip
    (IsPreimmersion.of_isLocalization (nonZeroDivisors R))
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks φ
  have lift : ∀ x : X.left, (X.hom x).asIdeal = ⊥ → ∃ y, φ y = x := fun x hx => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum K)
      (PrimeSpectrum.ext (hx.trans (Ideal.comap_bot_of_injective _ hinj).symm))
    exact ⟨y, hy⟩
  have hφ : φ (genericPoint Y) ⤳ genericPoint X.left := by
    obtain ⟨y, hy⟩ := (Flat.generalizingMap φ).stableUnderGeneralization_range
      (genericPoint_specializes (φ (genericPoint Y))) ⟨_, rfl⟩
    exact hy ▸ (genericPoint_specializes y).map φ.continuous
  have hne : ∀ (V : X.left.Opens) [Nonempty V], Nonempty (φ ⁻¹ᵁ V) := fun V _ =>
    ⟨⟨_, hφ.mem_open V.isOpen (genericPoint_mem_opens V)⟩⟩
  have hne' : ∀ i [Nonempty (M.U i)], Nonempty ((M.pull φ).U fun _ => i) := fun i _ => by
    rw [DvrModel.pull_U]; exact hne _
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  have hb := ffMap_bijective φ hφ
  obtain ⟨r, hr⟩ : ∃ r : M.ι → X.left.functionField, ∀ i [Nonempty ((M.pull φ).U fun _ => i)],
      ffMap φ hφ (r i) = Y.germToFunctionField _ (c.s fun _ => i).val := by
    have : ∀ i, ∃ t : X.left.functionField, ∀ [Nonempty ((M.pull φ).U fun _ => i)],
        ffMap φ hφ t = Y.germToFunctionField _ (c.s fun _ => i).val := fun i => by
      by_cases h : Nonempty ((M.pull φ).U fun _ => i)
      · exact (hb.2 (Y.germToFunctionField _ (c.s fun _ => i).val)).imp fun _ h => h
      · exact ⟨0, @fun h' => (h h').elim⟩
    exact ⟨fun i => (this i).choose, fun i => (this i).choose_spec⟩
  let k : K →+* Γ(Y, ⊤) := (p.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let κ : K →+* X.left.functionField := (RingEquiv.ofBijective (ffMap φ hφ).hom hb).symm.toRingHom.comp
    ((Y.germToFunctionField ⊤).hom.comp k)
  have hκ : ∀ a, ffMap φ hφ (κ a) = Y.germToFunctionField ⊤ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p ⊤ a) := fun a =>
    (RingEquiv.ofBijective (ffMap φ hφ).hom hb).apply_symm_apply _
  have hr0 : ∀ i x, x ∈ M.U i → r i ≠ 0 := fun i x hx h => by
    have : Nonempty (M.U i) := ⟨⟨x, hx⟩⟩
    have := hne' i
    have e := hr i
    rw [h, map_zero] at e
    exact ((Units.isUnit _).map _).ne_zero e.symm
  have htr : ∀ i j x t, x ∈ M.U i → x ∈ M.U j → UnitAt x (t * r j) → UnitAt x (t * r i) := by
    intro i j x t hi hj h
    have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
    have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
    have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
    have := hne' i
    have := hne' j
    have := nonempty_inf_of_isIntegral ((M.pull φ).U fun _ => i) ((M.pull φ).U fun _ => j)
    have e : r i = X.left.germToFunctionField _ (M.g i j).val * r j := hb.1 (by
      have e := congrArg (Y.germToFunctionField _) (congrArg Units.val (hc (fun _ => i) fun _ => j))
      rw [Units.val_mul, map_mul, DvrModel.coe_pull_g, ← ffMap_germ φ hφ] at e
      rw [map_mul, hr, hr]
      exact (germToFunctionField_res _ _).symm.trans (e.trans (congrArg _ (germToFunctionField_res _ _))))
    rw [e, mul_left_comm]
    exact UnitAt.mul ⟨Units.map (X.left.presheaf.germ (M.U i ⊓ M.U j) x ⟨hi, hj⟩).hom (M.g i j),
      X.left.presheaf.germ_stalkSpecializes_apply _ _ _⟩ h
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, v.asIdeal ≠ ⊥ → ∃ ξ, (∃ i, ξ ∈ M.U i ∧ UnitAt ξ (κ a * r i)) ∧
      Order.coheight ξ = 1 ∧ ∀ x, X.hom x = v → ξ ⤳ x := by
    by_cases hv : v.asIdeal = ⊥
    · exact ⟨1, fun h => (h hv).elim⟩
    obtain ⟨ξ, π, hπ, hξ, hd, hirr⟩ := exists_fibre_generic X.hom v hv
    obtain ⟨i, hi⟩ := LB.mem_of_cover hM ξ
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hirr (hr0 i ξ hi)
    have hπ' : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ
    have e : algebraMap _ X.left.functionField (X.left.presheaf.germ ⊤ ξ trivial (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn X.hom ⊤ π)) =
        κ (algebraMap R K π) := hb.1 (by
      rw [hκ, ← app_constFn H.w, ← φ.appLE_eq_app]
      exact (congrArg (ffMap φ hφ) (X.left.presheaf.germ_stalkSpecializes_apply _ _ _)).trans
        (ffMap_germ φ hφ ⊤ ⊤ le_top _))
    refine ⟨Units.mk0 _ hπ' ^ (-n), fun _ => ⟨ξ, ⟨i, hi, u, ?_⟩, ?_, hξ⟩⟩
    · rw [hu, e, Units.smul_def, Algebra.smul_def, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0,
        mul_left_comm, ← zpow_add₀ ((map_ne_zero κ).2 hπ'), neg_add_cancel, zpow_zero, _root_.mul_one]
    · have e := IsDiscreteValuationRing.ringKrullDim_eq_one (X.left.presheaf.stalk ξ)
      rw [ringKrullDim_stalk_eq_coheight] at e
      exact_mod_cast e
  obtain ⟨f, hf, hf'⟩ := exists_basicOpen X.hom v {x | ∃ i, x ∈ M.U i ∧ UnitAt x (κ a * r i)} (by
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun i => (M.U i).isOpen.inter (isOpen_unitAt _)) (fun x hx => by
    obtain ⟨y, rfl⟩ := lift x hx
    obtain ⟨i, hi⟩ := LB.mem_of_cover hM (φ y)
    have : Nonempty (M.U i) := ⟨⟨_, hi⟩⟩
    have := hne' i
    exact ⟨i, hi, (unitAt_of_isUnit φ hφ (a.isUnit.map k) trivial (hκ a)).mul
      (unitAt_of_isUnit φ hφ (Units.isUnit _) ((DvrModel.pull_U M φ _).ge hi) (hr i))⟩) ha
  refine ⟨f, a, hf, fun i => ?_⟩
  by_cases hV : Nonempty (M.U i ⊓ X.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f : X.left.Opens)
  swap
  · refine ⟨1, fun W h₁ h₂ => ?_⟩
    obtain rfl : W = ⊥ := eq_bot_iff.2 fun y hy => (hV ⟨⟨_, h₂ hy⟩⟩).elim
    exact Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := exists_unit_eq (M.U i ⊓ X.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f) (κ a * r i)
    (mul_ne_zero ((map_ne_zero κ).2 a.ne_zero) (hr0 i _ hV.some.2.1)) fun x hx h1 => by
      obtain ⟨j, hj, h⟩ := hf' x hx.2 h1
      exact htr i j x _ hx.1 hj h
  refine ⟨u, fun W h₁ h₂ => ?_⟩
  by_cases hW : Nonempty W
  swap
  · obtain rfl : W = ⊥ := eq_bot_iff.2 fun y hy => (hW ⟨⟨_, hy⟩⟩).elim
    exact Subsingleton.elim _ _
  have : Nonempty ((M.pull φ).U fun _ => i) := ⟨⟨_, h₁ hW.some.2⟩⟩
  refine Y.germToFunctionField_injective W ((ffMap_germ φ hφ _ W h₂ _).symm.trans ?_)
  rw [hu, map_mul, map_mul, hκ, hr]
  refine congrArg₂ (· * ·) ?_ (germToFunctionField_res h₁ _).symm
  exact (germToFunctionField_res (le_top : W ≤ ⊤) _).symm.trans (congrArg _ (res_appLE_apply p _ _ _))

end GlobalTheory.VerticalUnit
