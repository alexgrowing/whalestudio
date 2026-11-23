import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.ExtendLineBundle

variable {X Y : Scheme.{0}} [IsIntegral X]

theorem genericPoint_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

def localSubring (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

theorem algebraMap_germ {U : X.Opens} {x : X} (hx : x ∈ U) (h : genericPoint X ∈ U)
    (s : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) =
      X.presheaf.germ U _ h s :=
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  Scheme.algebraMap_germ_eq_germToFunctionField X hx s

theorem germ_mem {U : X.Opens} {x : X} (hx : x ∈ U) (h : genericPoint X ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U _ h s ∈ localSubring x :=
  ⟨_, algebraMap_germ hx h s⟩

theorem exists_section_of_mem {x : X} {t : X.functionField} (ht : t ∈ localSubring x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
      X.presheaf.germ U _ (genericPoint_mem hx) s = t := by
  obtain ⟨a, rfl⟩ := ht
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  exact ⟨U, hx, s, (algebraMap_germ hx _ s).symm⟩

theorem eventually_mem {x : X} {t : X.functionField} (ht : t ∈ localSubring x) :
    ∀ᶠ y in nhds x, t ∈ localSubring y := by
  obtain ⟨U, hx, s, rfl⟩ := exists_section_of_mem ht
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact germ_mem hy _ s

theorem exists_section {U : X.Opens} (h : genericPoint X ∈ U) {t : X.functionField}
    (ht : ∀ x ∈ U, t ∈ localSubring x) : ∃ s : Γ(X, U), X.presheaf.germ U _ h s = t := by
  choose V hV s hs using fun x : U => exists_section_of_mem (ht x.1 x.2)
  have hη : ∀ x : U, genericPoint X ∈ V x ⊓ U := fun x => ⟨genericPoint_mem (hV x), h⟩
  have hs' : ∀ x : U, X.presheaf.germ (V x ⊓ U) _ (hη x)
      (X.presheaf.map (homOfLE (inf_le_left : V x ⊓ U ≤ V x)).op (s x)) = t := fun x =>
    (X.presheaf.germ_res_apply _ _ _ _).trans (hs x)
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => V x ⊓ U) U
    (fun x => homOfLE inf_le_right)
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _, hy⟩)
    (fun x => X.presheaf.map (homOfLE (inf_le_left : V x ⊓ U ≤ V x)).op (s x))
    (fun x y => germ_injective_of_isIntegral X (U := (V x ⊓ U) ⊓ (V y ⊓ U)) _ ⟨hη x, hη y⟩
      (((X.presheaf.germ_res_apply _ _ _ _).trans (hs' x)).trans
        ((X.presheaf.germ_res_apply _ _ _ _).trans (hs' y)).symm))
  refine ⟨a, ?_⟩
  rw [← hs' ⟨_, h⟩]
  exact (X.presheaf.germ_res_apply (homOfLE inf_le_right) _ (hη ⟨_, h⟩) a).symm.trans
    (congrArg _ (ha ⟨_, h⟩))

theorem exists_pow_mul_mem {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U))
    (h : genericPoint X ∈ U) (ha : genericPoint X ∈ X.basicOpen a) {t : X.functionField}
    (ht : ∀ y ∈ X.basicOpen a, t ∈ localSubring y) :
    ∃ n : ℕ, ∀ x ∈ U, X.presheaf.germ U _ h a ^ n * t ∈ localSubring x := by
  obtain ⟨s, rfl⟩ := exists_section ha ht
  obtain ⟨n, b, e⟩ := exists_eq_pow_mul_of_isAffineOpen X U hU a s
  refine ⟨n, fun x hx => ?_⟩
  have e' := congrArg (X.presheaf.germ _ _ ha) e
  rw [map_mul, map_pow] at e'
  have r : ∀ c : Γ(X, U), X.presheaf.germ _ _ ha (c |_ X.basicOpen a) =
      X.presheaf.germ U _ h c := fun c => X.presheaf.germ_res_apply _ _ _ _
  rw [r, r] at e'
  rw [← e']
  exact germ_mem hx h b

theorem inv_germ_mem {U : X.Opens} (a : Γ(X, U)) (h : genericPoint X ∈ U) {y : X}
    (hy : y ∈ X.basicOpen a) :
    X.presheaf.germ U _ h a ≠ 0 ∧ (X.presheaf.germ U _ h a)⁻¹ ∈ localSubring y := by
  have hyU := X.basicOpen_le a hy
  obtain ⟨b, hb⟩ := ((X.mem_basicOpen a y hyU).1 hy).exists_right_inv
  have e := congrArg (algebraMap (X.presheaf.stalk y) X.functionField) hb
  rw [map_mul, map_one, algebraMap_germ hyU h] at e
  exact ⟨left_ne_zero_of_mul_eq_one e, b, eq_inv_of_mul_eq_one_right e⟩

theorem exists_gcd_fraction {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ι : Type*} [Finite ι] (c : ι → K)
    (hc : ∀ k, c k ≠ 0) :
    ∃ h : K, h ≠ 0 ∧ (∀ k, c k / h ∈ (algebraMap R K).range) ∧
      ∀ t : K, Nonempty ι → (∀ k, c k * t ∈ (algebraMap R K).range) →
        h * t ∈ (algebraMap R K).range := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨1, one_ne_zero, fun k => h.elim k, fun _ ⟨k⟩ => h.elim k⟩
  | inr hι =>
  obtain ⟨k₀⟩ := hι
  have := Fintype.ofFinite ι
  letI : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid R := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨⟨d, hd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
  choose e he using hdc
  have hd0 : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr (nonZeroDivisors.ne_zero hd)
  have he' : ∀ k, algebraMap R K (e k) = algebraMap R K d * c k := fun k => by
    rw [he k, Algebra.smul_def]
  have hg : Finset.univ.gcd e ≠ 0 := fun h => by
    have := he' k₀
    rw [Finset.gcd_eq_zero_iff.1 h k₀ (Finset.mem_univ _), map_zero] at this
    exact mul_ne_zero hd0 (hc k₀) this.symm
  have hg0 : algebraMap R K (Finset.univ.gcd e) ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr hg
  refine ⟨algebraMap R K (Finset.univ.gcd e) / algebraMap R K d, div_ne_zero hg0 hd0,
    fun k => ?_, fun t _ ht => ?_⟩
  · obtain ⟨r, hr⟩ := Finset.gcd_dvd (f := e) (Finset.mem_univ k)
    refine ⟨r, ?_⟩
    have := he' k
    rw [hr, map_mul] at this
    field_simp
    linear_combination this
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) t
    have hq0 : algebraMap R K q ≠ 0 :=
      IsFractionRing.to_map_eq_zero_iff.not.mpr (nonZeroDivisors.ne_zero hq)
    have h1 : d * q ∣ Finset.univ.gcd fun k => p * e k := Finset.dvd_gcd fun k _ => by
      obtain ⟨r, hr⟩ := ht k
      refine ⟨r, IsFractionRing.injective R K ?_⟩
      rw [map_mul, map_mul, map_mul, he', hr]
      field_simp
    obtain ⟨r, hr⟩ := h1.trans (Finset.gcd_mul_left' _ _ p).dvd
    refine ⟨r, ?_⟩
    have := congrArg (algebraMap R K) hr
    rw [map_mul, map_mul, map_mul] at this
    field_simp
    linear_combination -this

def localUnits (x : X) : Subgroup X.functionFieldˣ := (localSubring x).toSubmonoid.units

theorem mem_localUnits {x : X} {t : X.functionFieldˣ} :
    t ∈ localUnits x ↔ t.val ∈ localSubring x ∧ t.val⁻¹ ∈ localSubring x := by
  rw [← Units.val_inv_eq_inv_val]
  rfl

def Compatible (T : Set (X.Opens × X.functionFieldˣ)) : Prop :=
  ∀ p ∈ T, ∀ q ∈ T, ∀ y, y ∈ p.1 → y ∈ q.1 → p.2 / q.2 ∈ localUnits y

theorem exists_local_equation [NoetherianSpace X] {T : Set (X.Opens × X.functionFieldˣ)}
    (hT : Compatible T) (x : X) [UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    ∃ (W : X.Opens) (h : X.functionFieldˣ), x ∈ W ∧
      ∀ p ∈ T, ∀ y, y ∈ W → y ∈ p.1 → h / p.2 ∈ localUnits y := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hη : genericPoint X ∈ U := genericPoint_mem hxU
  let C : Set X := {y | y ∈ U ∧ ∃ p ∈ T, y ∈ p.1}
  have hC : ∀ y : C, ∃ p ∈ T, ∃ a : Γ(X, U), X.basicOpen a ≤ p.1 ∧ y.1 ∈ X.basicOpen a := by
    rintro ⟨y, hy, p, hp, hyp⟩
    obtain ⟨a, ha, hya⟩ := IsAffineOpen.exists_basicOpen_le hU (V := p.1) ⟨y, hyp⟩ hy
    exact ⟨p, hp, a, ha, hya⟩
  choose P hP a ha hya using hC
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact C).elim_finite_subcover
    (fun y : C => (X.basicOpen (a y) : Set X)) (fun y => (X.basicOpen (a y)).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hya _⟩)
  let α : t → X.functionField := fun k => X.presheaf.germ U _ hη (a k)
  let f : t → X.functionField := fun k => (P k).2
  have hα : ∀ k, α k ≠ 0 := fun k => (inv_germ_mem _ hη (hya k)).1
  have hf : ∀ k, f k ≠ 0 := fun k => Units.ne_zero _
  have h1 : ∀ kl : t × t, ∃ n : ℕ, (α kl.1 * α kl.2) ^ n * (f kl.1 / f kl.2) ∈ localSubring x := by
    rintro ⟨k, l⟩
    obtain ⟨n, hn⟩ := exists_pow_mul_mem hU (a k * a l) hη (t := f k / f l)
      (by rw [Scheme.basicOpen_mul]; exact ⟨genericPoint_mem (hya _), genericPoint_mem (hya _)⟩)
      (fun y hy => by
        rw [Scheme.basicOpen_mul] at hy
        have := (mem_localUnits.1 (hT _ (hP k) _ (hP l) y (ha _ hy.1) (ha _ hy.2))).1
        rwa [Units.val_div_eq_div_val] at this)
    refine ⟨n, ?_⟩
    have := hn x hxU
    rwa [map_mul] at this
  choose n hn using h1
  obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
  have h2 : ∀ k l, (α k ^ N * f k) * (α l ^ N / f l) ∈ localSubring x := fun k l => by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hN ⟨(k, l), rfl⟩)
    have := mul_mem (pow_mem (mul_mem (germ_mem hxU hη (a k)) (germ_mem hxU hη (a l))) m)
      (hn (k, l))
    convert this using 1
    change _ = (α k * α l) ^ m * _
    rw [hm]
    ring
  obtain ⟨h, h0, h3, h4⟩ := exists_gcd_fraction (R := X.presheaf.stalk x)
    (fun k => α k ^ N * f k) (fun k => mul_ne_zero (pow_ne_zero _ (hα k)) (hf k))
  have h5 : ∀ᶠ y in nhds x, ∀ k, α k ^ N * f k / h ∈ localSubring y ∧
      h * (α k ^ N / f k) ∈ localSubring y :=
    Filter.eventually_all.2 fun k =>
      (eventually_mem (h3 k)).and (eventually_mem (h4 _ ⟨k⟩ fun l => h2 l k))
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1 h5
  refine ⟨⟨W, hWo⟩ ⊓ U, Units.mk0 h h0, ⟨hxW, hxU⟩, fun p hp y hy hyp => ?_⟩
  obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (ht (show y ∈ C from ⟨hy.2, p, hp, hyp⟩))
  have hi : (α ⟨k, hk⟩ ^ N)⁻¹ ∈ localSubring y := by
    rw [← inv_pow]
    exact pow_mem (inv_germ_mem _ hη hyk).2 N
  obtain ⟨h6, h7⟩ := hW y hy.1 ⟨k, hk⟩
  have h8 : Units.mk0 h h0 / (P k).2 ∈ localUnits y := by
    rw [mem_localUnits, Units.val_div_eq_div_val]
    have := pow_ne_zero N (hα ⟨k, hk⟩)
    have := hf ⟨k, hk⟩
    constructor
    · convert mul_mem hi h7 using 1
      change h / f ⟨k, hk⟩ = _
      field_simp
    · convert mul_mem hi h6 using 1
      change (h / f ⟨k, hk⟩)⁻¹ = _
      field_simp
  have := mul_mem h8 (hT _ (hP k) _ hp y (ha _ hyk) hyp)
  rwa [div_mul_div_cancel] at this

theorem exists_compatible_cover [NoetherianSpace X]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {T₀ : Set (X.Opens × X.functionFieldˣ)} (h₀ : Compatible T₀) :
    ∃ T, T₀ ⊆ T ∧ Compatible T ∧ ∀ x, ∃ p ∈ T, x ∈ p.1 := by
  obtain ⟨T, h₁, hT⟩ := zorn_subset_nonempty {T : Set (X.Opens × X.functionFieldˣ) | Compatible T}
    (fun c hc hch _ => ⟨⋃₀ c, fun p ⟨s, hs, hp⟩ q ⟨s', hs', hq⟩ => by
      rcases hch.total hs hs' with h | h
      exacts [hc hs' p (h hp) q hq, hc hs p hp q (h hq)], fun s hs => Set.subset_sUnion_of_mem hs⟩)
    T₀ h₀
  refine ⟨T, h₁, hT.prop, fun x => ?_⟩
  have := hX x
  obtain ⟨W, h, hx, hW⟩ := exists_local_equation hT.prop x
  refine ⟨(W, h), hT.2 (y := insert (W, h) T) ?_ (Set.subset_insert _ _) (Set.mem_insert _ _), hx⟩
  rintro p (rfl | hp) q (rfl | hq) y hyp hyq
  · rw [div_self']
    exact one_mem _
  · exact hW q hq y hyp hyq
  · rw [← inv_div]
    exact inv_mem (hW p hp y hyq hyp)
  · exact hT.prop p hp q hq y hyp hyq

open Classical in

def unitVal (U : X.Opens) : Γ(X, U)ˣ →* X.functionFieldˣ :=
  if h : genericPoint X ∈ U then Units.map (X.presheaf.germ U _ h).hom else 1

theorem val_unitVal {U : X.Opens} (h : genericPoint X ∈ U) (a : Γ(X, U)ˣ) :
    (unitVal U a).val = X.presheaf.germ U _ h a.val := by
  rw [unitVal, dif_pos h]
  rfl

theorem unitVal_res {U V : X.Opens} (hle : V ≤ U) (h : genericPoint X ∈ V) (a : Γ(X, U)ˣ) :
    unitVal V (res hle a) = unitVal U a := by
  apply Units.ext
  rw [val_unitVal h, val_unitVal (hle h)]
  exact X.presheaf.germ_res_apply (homOfLE hle) _ h a.val

theorem unit_ext {U : X.Opens} {a b : Γ(X, U)ˣ}
    (h : genericPoint X ∈ U → unitVal U a = unitVal U b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  have hη := genericPoint_mem hx
  have e := congrArg Units.val (h hη)
  rw [val_unitVal hη, val_unitVal hη] at e
  rw [germ_injective_of_isIntegral X _ hη e]

theorem unitVal_mem {U : X.Opens} {y : X} (hy : y ∈ U) (a : Γ(X, U)ˣ) :
    unitVal U a ∈ localUnits y := by
  have hη := genericPoint_mem hy
  rw [mem_localUnits, ← Units.val_inv_eq_inv_val, ← map_inv, val_unitVal hη, val_unitVal hη]
  exact ⟨germ_mem hy _ _, germ_mem hy _ _⟩

theorem exists_unit {U : X.Opens} {t : X.functionFieldˣ} (ht : ∀ y ∈ U, t ∈ localUnits y) :
    ∃ a : Γ(X, U)ˣ, genericPoint X ∈ U → unitVal U a = t := by
  by_cases h : genericPoint X ∈ U
  · obtain ⟨a, ha⟩ := exists_section h fun y hy => (mem_localUnits.1 (ht y hy)).1
    obtain ⟨b, hb⟩ := exists_section h fun y hy => (mem_localUnits.1 (ht y hy)).2
    have hab : a * b = 1 := germ_injective_of_isIntegral X _ h (by
      rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ t.ne_zero])
    exact ⟨Units.mkOfMulEqOne a b hab, fun _ => Units.ext ((val_unitVal h _).trans ha)⟩
  · exact ⟨1, fun h' => (h h').elim⟩

variable (j : Y ⟶ X) [IsOpenImmersion j]

def imageUnit (V : Y.Opens) : Γ(Y, V)ˣ ≃* Γ(X, j ''ᵁ V)ˣ :=
  Units.mapEquiv (j.appIso V).symm.commRingCatIsoToRingEquiv.toMulEquiv

omit [IsIntegral X] in
theorem imageUnit_res {U V : Y.Opens} (hle : V ≤ U) (a : Γ(Y, U)ˣ) :
    imageUnit j V (res hle a) = res (j.image_mono hle) (imageUnit j U a) :=
  Units.ext (congrArg (fun q => q.hom a.val) (j.appIso_inv_naturality (homOfLE hle).op))

omit [IsIntegral X] in
theorem imageUnit_pull (U : X.Opens) (a : Γ(X, U)ˣ) :
    imageUnit j (j ⁻¹ᵁ U) (pullU j U a) = res (Set.image_preimage_subset j U.1) a :=
  Units.ext (congrArg (fun q => q.hom a.val) (j.app_appIso_inv U))

def imageVal (V : Y.Opens) : Γ(Y, V)ˣ →* X.functionFieldˣ :=
  (unitVal (j ''ᵁ V)).comp (imageUnit j V).toMonoidHom

theorem imageVal_res {U V : Y.Opens} (hle : V ≤ U) (h : genericPoint X ∈ j ''ᵁ V)
    (a : Γ(Y, U)ˣ) : imageVal j V (res hle a) = imageVal j U a :=
  (congrArg (unitVal _) (imageUnit_res j hle a)).trans (unitVal_res _ h _)

theorem imageVal_res_pull {U : X.Opens} {V : Y.Opens} (hle : V ≤ j ⁻¹ᵁ U)
    (h : genericPoint X ∈ j ''ᵁ V) (a : Γ(X, U)ˣ) :
    imageVal j V (res hle (pullU j U a)) = unitVal U a :=
  (imageVal_res j hle h _).trans ((congrArg (unitVal _) (imageUnit_pull j U a)).trans
    (unitVal_res _ (j.image_mono hle h) _))

theorem image_unit_ext {V : Y.Opens} {a b : Γ(Y, V)ˣ}
    (h : genericPoint X ∈ j ''ᵁ V → imageVal j V a = imageVal j V b) : a = b :=
  (imageUnit j V).injective (unit_ext h)

theorem exists_image_unit {V : Y.Opens} {t : X.functionFieldˣ}
    (ht : ∀ y ∈ V, t ∈ localUnits (j y)) :
    ∃ a : Γ(Y, V)ˣ, genericPoint X ∈ j ''ᵁ V → imageVal j V a = t := by
  obtain ⟨a, ha⟩ := exists_unit (U := j ''ᵁ V) (t := t) (by
    rintro _ ⟨y, hy, rfl⟩
    exact ht y hy)
  refine ⟨(imageUnit j V).symm a, fun h => ?_⟩
  rw [← ha h]
  exact congrArg (unitVal _) ((imageUnit j V).apply_symm_apply a)

omit [IsIntegral X] in
theorem mem_image_inf {U V : Y.Opens} {x : X} (hU : x ∈ j ''ᵁ U) (hV : x ∈ j ''ᵁ V) :
    x ∈ j ''ᵁ (U ⊓ V) := by
  obtain ⟨y, hy, rfl⟩ := hU
  exact j.apply_mem_image_iff.2 ⟨hy, j.apply_mem_image_iff.1 hV⟩

theorem exists_equations (L : LB Y) (hL : L.IsLB) : ∃ f : L.ι → X.functionFieldˣ,
    ∀ i k, genericPoint X ∈ j ''ᵁ L.U i → genericPoint X ∈ j ''ᵁ L.U k →
      imageVal j _ (L.g i k) = f i / f k := by
  by_cases h : ∃ i₀, genericPoint X ∈ j ''ᵁ L.U i₀
  · obtain ⟨i₀, h₀⟩ := h
    refine ⟨fun i => imageVal j _ (L.g i i₀), fun i k hi hk => ?_⟩
    have hη := mem_image_inf j (mem_image_inf j hi hk) h₀
    have e := congrArg (imageVal j _) (hL.cocycle i k i₀)
    rw [map_mul, imageVal_res j _ hη, imageVal_res j _ hη, imageVal_res j _ hη] at e
    exact eq_div_iff_mul_eq'.2 e
  · exact ⟨1, fun i _ hi => (h ⟨i, hi⟩).elim⟩

theorem isGen_of_equations (M N : LB Y) (a : M.ι → X.functionFieldˣ) (b : N.ι → X.functionFieldˣ)
    (ha : ∀ i k, genericPoint X ∈ j ''ᵁ M.U i → genericPoint X ∈ j ''ᵁ M.U k →
      imageVal j _ (M.g i k) = a i / a k)
    (hb : ∀ i k, genericPoint X ∈ j ''ᵁ N.U i → genericPoint X ∈ j ''ᵁ N.U k →
      imageVal j _ (N.g i k) = b i / b k)
    (s : ∀ p : M.ι × N.ι, Γ(Y, M.U p.1 ⊓ N.U p.2)ˣ)
    (hs : ∀ p, genericPoint X ∈ j ''ᵁ (M.U p.1 ⊓ N.U p.2) → imageVal j _ (s p) = a p.1 / b p.2) :
    LB.Gen.IsGen (⟨s⟩ : LB.Iso N M) := by
  intro (p : M.ι × N.ι) (q : M.ι × N.ι)
  refine image_unit_ext j (V := M.U p.1 ⊓ N.U p.2 ⊓ (M.U q.1 ⊓ N.U q.2)) fun h => ?_
  have hp := j.image_mono inf_le_left h
  have hq := j.image_mono inf_le_right h
  have e₁ := ha p.1 q.1 (j.image_mono inf_le_left hp) (j.image_mono inf_le_left hq)
  have e₂ := hb p.2 q.2 (j.image_mono inf_le_right hp) (j.image_mono inf_le_right hq)
  have key : ∀ (V : Y.Opens) (_ : genericPoint X ∈ j ''ᵁ V) (l₁ : V ≤ M.U p.1 ⊓ N.U p.2)
      (l₂ : V ≤ M.U p.1 ⊓ M.U q.1) (l₃ : V ≤ N.U p.2 ⊓ N.U q.2) (l₄ : V ≤ M.U q.1 ⊓ N.U q.2),
      imageVal j V (res l₁ (s p)) =
        imageVal j V (res l₂ (M.g p.1 q.1) * (res l₃ (N.g p.2 q.2))⁻¹ * res l₄ (s q)) := by
    intro V h l₁ l₂ l₃ l₄
    rw [map_mul, map_mul, map_inv, imageVal_res j _ h, imageVal_res j _ h, imageVal_res j _ h,
      imageVal_res j _ h, e₁, e₂, hs p hp, hs q hq]
    rw [inv_div, mul_right_comm, div_mul_div_cancel, div_mul_div_cancel]
  exact key _ h _ _ _ _

theorem imageVal_pull (M : LB X) (p q : PUnit → M.ι)
    (h : genericPoint X ∈ j ''ᵁ (LB.wchart M (fun _ => j) p ⊓ LB.wchart M (fun _ => j) q)) :
    imageVal j _ ((M.pull j).g p q) = unitVal _ (M.g (p ⟨⟩) (q ⟨⟩)) := by
  refine (congrArg (imageVal j _) ((Fintype.prod_unique (ι := PUnit) _).trans (zpow_one _))).trans ?_
  exact imageVal_res_pull j (U := M.U (p ⟨⟩) ⊓ M.U (q ⟨⟩)) _ h _

end GlobalTheory.ExtendLineBundle

namespace GlobalTheory

open ExtendLineBundle

theorem exists_lineBundle_extension (X Y : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [CompactSpace X] (j : Y ⟶ X) (hj : IsOpenImmersion j)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (L : LB Y) (hL : L.IsLB) :
    ∃ L' : LB X, L'.IsLB ∧ ∃ φ : LB.Iso (L'.pull j) L, φ.IsGen := by
  have : IsNoetherian X := {}
  obtain ⟨f, hf⟩ := exists_equations j L hL
  obtain ⟨T, h₀, hT, hc⟩ := exists_compatible_cover hX
    (T₀ := Set.range fun i => (j ''ᵁ L.U i, f i)) (by
      rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩ y hi hk
      rw [← hf i k (genericPoint_mem hi) (genericPoint_mem hk)]
      exact unitVal_mem (mem_image_inf j hi hk) _)
  choose g hg using fun p q : T => exists_unit (U := p.1.1 ⊓ q.1.1) (t := p.1.2 / q.1.2)
    fun y hy => hT _ p.2 _ q.2 y hy.1 hy.2
  let L' : LB X := ⟨T, fun p => p.1.1, g⟩
  choose s hs using fun p : L.ι × (PUnit → T) => exists_image_unit j
    (V := L.U p.1 ⊓ LB.wchart L' (fun _ => j) p.2) (t := f p.1 / (p.2 ⟨⟩).1.2) fun y hy =>
      hT _ (h₀ ⟨p.1, rfl⟩) _ (p.2 ⟨⟩).2 (j y) (j.apply_mem_image_iff.2 hy.1)
        (LB.wchart_le L' (fun _ => j) p.2 ⟨⟩ hy.2)
  refine ⟨L', ⟨?_, fun p => unit_ext fun h => ?_, fun p q r => unit_ext fun h => ?_⟩,
    ⟨s⟩, isGen_of_equations j L (L'.pull j) f (fun p => (p ⟨⟩).1.2) hf (fun p q hp hq => ?_) s hs⟩
  · refine top_unique fun x _ => ?_
    obtain ⟨p, hp, hx⟩ := hc x
    exact Opens.mem_iSup.2 ⟨⟨p, hp⟩, hx⟩
  · rw [unitVal_res _ h, map_one]
    exact (hg p p ⟨h, h⟩).trans (div_self' _)
  · rw [map_mul, unitVal_res _ h, unitVal_res _ h, unitVal_res _ h]
    exact (congrArg₂ (· * ·) (hg p q h.1) (hg q r ⟨h.1.2, h.2⟩)).trans
      ((div_mul_div_cancel _ _ _).trans (hg p r ⟨h.1.1, h.2⟩).symm)
  · have hw := mem_image_inf j hp hq
    refine (imageVal_pull j L' p q hw).trans (hg (p ⟨⟩) (q ⟨⟩) ?_)
    obtain ⟨y, hy, e⟩ := hw
    rw [← e]
    exact ⟨LB.wchart_le L' (fun _ => j) p ⟨⟩ hy.1, LB.wchart_le L' (fun _ => j) q ⟨⟩ hy.2⟩

end GlobalTheory
