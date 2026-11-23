import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitAlgebraMapEqOfValuationEqOne

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.PrimeSection

theorem res_res {X : Scheme.{u}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE h').op s) =
      X.presheaf.map (homOfLE (h.trans h')).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_self {X : Scheme.{u}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op s = s := by
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem germ_res {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) {x : X} (hx : x ∈ V) (s : Γ(X, U)) :
    X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s) = X.presheaf.germ U x (h hx) s := by
  rw [X.presheaf.germ_res_apply (homOfLE h) x hx s]

theorem exists_unit_eq_res {X : Scheme.{u}} (t : Γ(X, ⊤)) :
    ∃ τ : Γ(X, X.basicOpen t)ˣ,
      (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t := by
  refine ⟨(X.toRingedSpace.isUnit_res_basicOpen t).unit, ?_⟩
  rfl

section Integral

variable {X : Scheme.{u}} [IsIntegral X]

theorem genericPoint_mem {W : X.Opens} {x : X} (hx : x ∈ W) : genericPoint X ∈ W := ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hx⟩

theorem genericPoint_mem_basicOpen {W : X.Opens} {s : Γ(X, W)} (hs : s ≠ 0) :
    genericPoint X ∈ X.basicOpen s := by
  have hne : X.basicOpen s ≠ ⊥ := fun h => hs ((basicOpen_eq_bot_iff s).mp h)
  obtain ⟨x, hx⟩ : ∃ x, x ∈ X.basicOpen s := by
    by_contra hcon
    exact hne (eq_bot_iff.mpr fun x hx => (hcon ⟨x, hx⟩).elim)
  exact genericPoint_mem hx

theorem algebraMap_germ {W : X.Opens} {x : X} (hx : x ∈ W) (s : Γ(X, W)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx s) =
      X.presheaf.germ W (genericPoint X) (genericPoint_mem hx) s := by
  have : Nonempty W := ⟨⟨x, hx⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]

theorem eq_of_germ_eq {W : X.Opens} {s s' : Γ(X, W)}
    (h : ∀ hW : genericPoint X ∈ W, X.presheaf.germ W _ hW s = X.presheaf.germ W _ hW s') :
    s = s' := by
  by_cases hW : genericPoint X ∈ W
  · exact germ_injective_of_isIntegral X (genericPoint X) hW (h hW)
  · refine TopCat.Presheaf.section_ext X.sheaf W s s' fun x hx => ?_
    exact (hW (genericPoint_mem hx)).elim

theorem res_inf_injective {D : X.Opens} (hD : genericPoint X ∈ D) (W : X.Opens) :
    Function.Injective (X.presheaf.map (homOfLE (inf_le_left : W ⊓ D ≤ W)).op) := by
  intro s s' hss
  refine eq_of_germ_eq fun hW => ?_
  have hWD : genericPoint X ∈ W ⊓ D := ⟨hW, hD⟩
  rw [← germ_res (inf_le_left : W ⊓ D ≤ W) hWD s, ← germ_res (inf_le_left : W ⊓ D ≤ W) hWD s', hss]

theorem eq_zero_of_component_eq_zero {ι : Type v} {U : ι → X.Opens}
    (g : ∀ a b, Γ(X, U a ⊓ U b)) (s : ∀ a, Γ(X, U a))
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a : ι} {x : X} (hx : x ∈ U a) (h : s a = 0) (b : ι) : s b = 0 := by
  have hgen : genericPoint X ∈ U a := genericPoint_mem hx
  apply res_inf_injective hgen (U b)
  rw [hs b a, h, map_zero, mul_zero, map_zero]

theorem eq_zero_of_forall_pow_dvd_germ [IsLocallyNoetherian X] {t : Γ(X, ⊤)}
    {ι : Type v} {U : ι → X.Opens} (g : ∀ a b, Γ(X, U a ⊓ U b)) (s : ∀ a, Γ(X, U a))
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a : ι} {x : X} (hx : x ∈ U a) (hxt : x ∉ X.basicOpen t)
    (h : ∀ e : ℕ, X.presheaf.germ ⊤ x trivial t ^ e ∣ X.presheaf.germ (U a) x hx (s a))
    (b : ι) : s b = 0 := by
  have hnu : ¬ IsUnit (X.presheaf.germ ⊤ x trivial t) := fun hu => hxt ((X.mem_basicOpen_top t x).mpr hu)
  have h0 : X.presheaf.germ (U a) x hx (s a) = 0 := GlobalTheory.PrimeElement.eq_zero_of_forall_pow_dvd hnu h
  have hsa : s a = 0 := germ_injective_of_isIntegral X x hx (by rw [h0, map_zero])
  exact eq_zero_of_component_eq_zero g s hs hx hsa b

end Integral

variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))

include hη in
theorem mem_of_notMem_basicOpen {W : X.Opens} {x : X} (hx : x ∈ W) (hxt : x ∉ X.basicOpen t) :
    η ∈ W := ((hη x).mp hxt).mem_open W.isOpen hx

include hη in
theorem le_basicOpen_of_notMem {W : X.Opens} (hW : η ∉ W) : W ≤ X.basicOpen t := by
  intro x hx
  by_contra hxt
  exact hW (mem_of_notMem_basicOpen hη hx hxt)

include hp in
theorem ne_zero : t ≠ 0 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  intro ht
  have := (hp V hV hηV).ne_zero
  rw [ht, map_zero] at this
  exact this rfl

theorem mem_primeIdealOf_iff {U : X.Opens} (hU : IsAffineOpen U) (x : U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf x).asIdeal ↔ x.1 ∉ X.basicOpen s := by
  rw [hU.primeIdealOf_eq_map_closedPoint x, X.mem_basicOpen s x.1 x.2]
  change X.presheaf.germ U x.1 x.2 s ∈ IsLocalRing.maximalIdeal _ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

include hη hp in

theorem primeIdealOf_eq_span {U : X.Opens} (hU : IsAffineOpen U) (h : η ∈ U) :
    (hU.primeIdealOf ⟨η, h⟩).asIdeal =
      Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t} := by
  have hπ := hp U hU h
  have hηt : η ∉ X.basicOpen t := (hη η).mpr (specializes_refl η)
  have hP : (Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t}).IsPrime :=
    GlobalTheory.PrimeElement.isPrime_span hπ
  apply le_antisymm
  ·
    let P : PrimeSpectrum Γ(X, U) := ⟨_, hP⟩
    let y : U := hU.isoSpec.inv P
    have hy : hU.primeIdealOf y = P := by
      change hU.isoSpec.hom (hU.isoSpec.inv P) = P
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have hyt : y.1 ∉ X.basicOpen t := by
      intro hyt
      have hmem : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∈ (hU.primeIdealOf y).asIdeal := by
        rw [hy]
        exact Ideal.subset_span rfl
      rw [mem_primeIdealOf_iff hU y, Scheme.basicOpen_res] at hmem
      exact hmem ⟨y.2, hyt⟩
    have hsp : (⟨η, h⟩ : U) ⤳ y :=
      (Topology.IsInducing.subtypeVal.specializes_iff).mp ((hη y.1).mp hyt)
    have hsp' := hsp.map hU.isoSpec.hom.continuous
    rw [← PrimeSpectrum.le_iff_specializes] at hsp'
    change (hU.primeIdealOf ⟨η, h⟩).asIdeal ≤ (hU.primeIdealOf y).asIdeal at hsp'
    rw [hy] at hsp'
    exact hsp'
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_primeIdealOf_iff hU ⟨η, h⟩,
      Scheme.basicOpen_res]
    exact fun hm => hηt hm.2

include hη hp in

theorem dvd_iff_notMem_basicOpen {U : X.Opens} (hU : IsAffineOpen U) (h : η ∈ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∣ s ↔ η ∉ X.basicOpen s := by
  rw [← Ideal.mem_span_singleton, ← primeIdealOf_eq_span hη hp hU h]
  exact mem_primeIdealOf_iff hU ⟨η, h⟩ s

variable [IsIntegral X]

include hη hp in

theorem isDiscreteValuationRing_stalk [IsLocallyNoetherian X] :
    IsDiscreteValuationRing (X.presheaf.stalk η) ∧
      Irreducible (X.presheaf.germ ⊤ η trivial t) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  have hπ := hp U hU hηU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Nonempty U := ⟨⟨η, hηU⟩⟩
  have := GlobalTheory.PrimeElement.isPrime_span hπ
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨η, hηU⟩ : U)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk η) (Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t}) := by
    have h0 := hU.isLocalization_stalk ⟨η, hηU⟩
    unfold IsLocalization.AtPrime at h0 ⊢
    convert h0 using 3
    exact (primeIdealOf_eq_span hη hp hU hηU).symm
  refine ⟨GlobalTheory.PrimeElement.isDiscreteValuationRing (X.presheaf.stalk η) hπ.ne_zero, ?_⟩
  have hirr := GlobalTheory.PrimeElement.irreducible_algebraMap (X.presheaf.stalk η) hπ.ne_zero
  convert hirr using 1
  exact (germ_res le_top hηU t).symm

include hp in
theorem genericPoint_mem_inf {W : X.Opens} (h : η ∈ W) : genericPoint X ∈ W ⊓ X.basicOpen t := ⟨genericPoint_mem h, genericPoint_mem_basicOpen (ne_zero hp)⟩

private theorem exists_section_restrict_eq_of_germ_eq {V : X.Opens} (hV : IsAffineOpen V) (hηV : η ∈ V)
    (hπ : Prime (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    (hq : (hV.primeIdealOf ⟨η, hηV⟩).asIdeal = Ideal.span {X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t})
    (hY : genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    (y : Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))) (z : X.presheaf.stalk η)
    (h : X.presheaf.germ _ (genericPoint X) hY y = algebraMap (X.presheaf.stalk η) X.functionField z) :
    ∃ r : Γ(X, V), X.presheaf.map (homOfLE (X.basicOpen_le _)).op r = y ∧
      (IsUnit y → IsUnit z → IsUnit r) := by
  have := GlobalTheory.PrimeElement.isPrime_span hπ
  have : Nonempty V := ⟨⟨η, hηV⟩⟩
  have : Nonempty (X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)) := ⟨⟨_, hY⟩⟩
  let _ : Algebra Γ(X, V) Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))).op).hom.toAlgebra
  have : IsLocalization.Away (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)) :=
    hV.isLocalization_basicOpen _
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨η, hηV⟩ : V)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk η) (Ideal.span {X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t}) := by
    have h0 := hV.isLocalization_stalk ⟨η, hηV⟩
    unfold IsLocalization.AtPrime at h0 ⊢
    convert h0 using 3
    exact hq.symm
  have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
      X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (germ_res (X.basicOpen_le _) hY a).symm
  have : FaithfulSMul Γ(X, V) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (X.germToFunctionField_injective V)
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk η) X.functionField :=
    functionField_isScalarTower X V ⟨η, hηV⟩
  have hh : algebraMap _ X.functionField y = algebraMap (X.presheaf.stalk η) X.functionField z := h
  obtain ⟨r, hr⟩ := GlobalTheory.PrimeElement.exists_algebraMap_eq (K := X.functionField) hπ.ne_zero hh
  refine ⟨r, hr, fun hy hz => ?_⟩
  obtain ⟨r', hr'u, hr'⟩ :=
    GlobalTheory.PrimeElement.exists_unit_algebraMap_eq (K := X.functionField) hπ.ne_zero hy hz hh
  have hinj := IsLocalization.injective
    (M := Submonoid.powers (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero)
  have hrr : r' = r := hinj (hr'.trans hr.symm)
  exact hrr ▸ hr'u

include hη in

theorem exists_res_eq {W : X.Opens} (r : Γ(X, W ⊓ X.basicOpen t))
    (hr : ∀ h : η ∈ W, ∃ z : X.presheaf.stalk η, algebraMap _ X.functionField z =
      X.presheaf.germ _ (genericPoint X) (genericPoint_mem_inf hp h) r) :
    ∃ s : Γ(X, W), X.presheaf.map (homOfLE inf_le_left).op s = r := by
  classical

  have hloc : ∀ x : {x // x ∈ W ∧ x ∉ X.basicOpen t}, ∃ V : X.Opens, IsAffineOpen V ∧ x.1 ∈ V ∧ V ≤ W := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open x.2.1 W.isOpen
    exact ⟨V, hV, hxV, hVW⟩
  choose V hV hxV hVW using hloc
  have hηV : ∀ x, η ∈ V x := fun x => mem_of_notMem_basicOpen hη (hxV x) x.2.2

  have hsec : ∀ x, ∃ sx : Γ(X, V x), X.presheaf.germ (V x) (genericPoint X) (genericPoint_mem (hxV x)) sx =
      X.presheaf.germ _ (genericPoint X) (genericPoint_mem_inf hp (hVW x (hηV x))) r := by
    intro x
    have hπ := hp (V x) (hV x) (hηV x)
    have hq := primeIdealOf_eq_span hη hp (hV x) (hηV x)
    have hYle : X.basicOpen (X.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op t) ≤ W ⊓ X.basicOpen t := by
      rw [Scheme.basicOpen_res]
      exact fun y hy => ⟨hVW x hy.1, hy.2⟩
    have hY : genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op t) := by
      rw [Scheme.basicOpen_res]
      exact genericPoint_mem_inf hp (hηV x)
    obtain ⟨z, hz⟩ := hr (hVW x (hηV x))
    obtain ⟨sx, hsx, -⟩ := exists_section_restrict_eq_of_germ_eq (hV x) (hηV x) hπ hq hY
      (X.presheaf.map (homOfLE hYle).op r) z (by rw [germ_res]; exact hz.symm)
    refine ⟨sx, ?_⟩
    rw [← germ_res (X.basicOpen_le _) hY sx, hsx, germ_res]
  choose sx hsx using hsec

  let O : Option {x // x ∈ W ∧ x ∉ X.basicOpen t} → X.Opens := fun i => i.elim (W ⊓ X.basicOpen t) V
  let f : ∀ i, Γ(X, O i) := fun i => Option.rec (motive := fun i => Γ(X, O i)) r sx i
  have hOW : ∀ i, O i ≤ W := by
    intro i
    cases i with
    | none => exact inf_le_left
    | some x => exact hVW x
  have hcov : W ≤ iSup O := by
    intro y hy
    by_cases hyt : y ∈ X.basicOpen t
    · exact (le_iSup O none) ⟨hy, hyt⟩
    · exact (le_iSup O (some ⟨y, hy, hyt⟩)) (hxV ⟨y, hy, hyt⟩)
  have hgD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hgerm : ∀ i (hi : genericPoint X ∈ O i), X.presheaf.germ (O i) (genericPoint X) hi (f i) =
      X.presheaf.germ _ (genericPoint X) (⟨hOW i hi, hgD⟩ : genericPoint X ∈ W ⊓ X.basicOpen t) r := by
    intro i hi
    cases i with
    | none => rfl
    | some x => exact hsx x
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 O f := by
    intro i j
    refine eq_of_germ_eq fun hij => ?_
    change X.presheaf.germ _ _ hij (X.presheaf.map (Opens.infLELeft (O i) (O j)).op (f i)) =
      X.presheaf.germ _ _ hij (X.presheaf.map (Opens.infLERight (O i) (O j)).op (f j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hgerm i, hgerm j]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' O W (fun i => homOfLE (hOW i)) hcov f hcompat
  exact ⟨s, hs none⟩

include hη hp in

theorem isUnit_of_isUnit_res {W : X.Opens} {s : Γ(X, W)}
    (hs : IsUnit (X.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen t ≤ W)).op s))
    (hsη : η ∈ W → η ∈ X.basicOpen s) : IsUnit s := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ W s fun x hx => ?_
  change IsUnit (X.presheaf.germ W x hx s)
  by_cases hxt : x ∈ X.basicOpen t
  · have hx' : x ∈ W ⊓ X.basicOpen t := ⟨hx, hxt⟩
    rw [← germ_res inf_le_left hx' s]
    exact hs.map _
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW0⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
    have hVW : V ≤ W := hVW0
    have hηV : η ∈ V := mem_of_notMem_basicOpen hη hxV hxt
    have hηW : η ∈ W := hVW hηV
    rw [← germ_res hVW hxV s]
    refine IsUnit.map _ ?_
    have hπ := hp V hV hηV
    have hq := primeIdealOf_eq_span hη hp hV hηV
    have hYle : X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t) ≤ W ⊓ X.basicOpen t := by
      rw [Scheme.basicOpen_res]
      exact fun y hy => ⟨hVW hy.1, hy.2⟩
    have hY : genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t) := by
      rw [Scheme.basicOpen_res]
      exact genericPoint_mem_inf hp hηV
    have hres : X.presheaf.map (homOfLE hYle).op (X.presheaf.map (homOfLE inf_le_left).op s) =
        X.presheaf.map (homOfLE (X.basicOpen_le _)).op (X.presheaf.map (homOfLE hVW).op s) := by
      rw [res_res, res_res]
    have hz : IsUnit (X.presheaf.germ V η hηV (X.presheaf.map (homOfLE hVW).op s)) := by
      rw [germ_res]
      exact (X.mem_basicOpen s η hηW).mp (hsη hηW)
    obtain ⟨r, hr, hru⟩ := exists_section_restrict_eq_of_germ_eq hV hηV hπ hq hY
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op (X.presheaf.map (homOfLE hVW).op s))
      (X.presheaf.germ V η hηV (X.presheaf.map (homOfLE hVW).op s))
      (by rw [algebraMap_germ, germ_res, germ_res])
    have hinj : r = X.presheaf.map (homOfLE hVW).op s := by
      have : Nonempty V := ⟨⟨η, hηV⟩⟩
      refine eq_of_germ_eq fun hgV => ?_
      rw [← germ_res (X.basicOpen_le _) hY r, hr, germ_res]
    rw [← hinj]
    refine hru ?_ hz
    rw [← hres]
    exact hs.map _

section Cocycle

variable {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}

theorem germ_eq_mul_germ {D : X.Opens} {r : ∀ a, Γ(X, U a ⊓ D)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ D ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_right)).op (r b))
    {a b : ι} {x : X} (ha : x ∈ U a ⊓ D) (hb : x ∈ U b ⊓ D) :
    X.presheaf.germ _ x ha (r a) =
      X.presheaf.germ _ x (show x ∈ U a ⊓ U b from ⟨ha.1, hb.1⟩) (g a b) *
        X.presheaf.germ _ x hb (r b) := by
  have hx : x ∈ U a ⊓ U b ⊓ D := ⟨⟨ha.1, hb.1⟩, ha.2⟩
  have h := congrArg (X.presheaf.germ _ x hx) (hr a b)
  rw [map_mul, germ_res, germ_res, germ_res] at h
  exact h

theorem compatible_of_res_eq {D : X.Opens} (hD : genericPoint X ∈ D) {r : ∀ a, Γ(X, U a ⊓ D)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ D ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_right)).op (r b))
    (c : Γ(X, D)) {s : ∀ a, Γ(X, U a)}
    (hs : ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      X.presheaf.map (homOfLE inf_le_right).op c * r a) (a b : ι) :
    X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b) := by
  refine eq_of_germ_eq fun hab => ?_
  have hga : genericPoint X ∈ U a ⊓ D := ⟨hab.1, hD⟩
  have hgb : genericPoint X ∈ U b ⊓ D := ⟨hab.2, hD⟩
  rw [map_mul, germ_res, germ_res]
  rw [← germ_res (inf_le_left : U a ⊓ D ≤ U a) hga (s a), hs a,
    ← germ_res (inf_le_left : U b ⊓ D ≤ U b) hgb (s b), hs b]
  rw [map_mul, map_mul, germ_res, germ_res, germ_eq_mul_germ hr hga hgb]
  ring

omit [IsIntegral X] in

theorem mem_basicOpen_of_compatible (hg : ∀ a b, IsUnit (g a b)) {s : ∀ a, Γ(X, U a)}
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a b : ι} {x : X} (ha : x ∈ U a) (hb : x ∈ X.basicOpen (s b)) : x ∈ X.basicOpen (s a) := by
  have hxb : x ∈ U b := X.basicOpen_le (s b) hb
  have hab : x ∈ U a ⊓ U b := ⟨ha, hxb⟩
  have h := congrArg (X.presheaf.germ _ x hab) (hs a b)
  rw [map_mul, germ_res, germ_res] at h
  rw [X.mem_basicOpen (s a) x ha, h]
  exact (IsUnit.mul (IsUnit.map (X.presheaf.germ _ x hab).hom (hg a b)) ((X.mem_basicOpen (s b) x hxb).mp hb))

variable [IsLocallyNoetherian X]

include hη hp in

theorem existsUnique_zpow_mul (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(X, U a),
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a) ∧
      ∃ a, ∃ x, x ∉ X.basicOpen t ∧ x ∈ X.basicOpen (s a) := by
  have hgD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hηD : η ∉ X.basicOpen t := (hη η).mpr (specializes_refl η)
  obtain ⟨a₀, ha₀⟩ := hU η
  have hga₀ : genericPoint X ∈ U a₀ := genericPoint_mem ha₀

  have hf : X.presheaf.germ _ (genericPoint X) (⟨hga₀, hgD⟩ : genericPoint X ∈ U a₀ ⊓ X.basicOpen t) (r a₀) ≠ 0 := by
    intro hf0
    obtain ⟨b, hb⟩ := hr0
    apply hb
    refine eq_of_germ_eq fun hgb => ?_
    rw [map_zero, germ_eq_mul_germ hr hgb ⟨hga₀, hgD⟩, hf0, mul_zero]

  obtain ⟨hdvr, hirr⟩ := isDiscreteValuationRing_stalk hη hp
  have := hdvr

  have hφ : ∀ n : ℤ, X.presheaf.germ _ (genericPoint X) hgD (↑(τ ^ n) : Γ(X, X.basicOpen t)) =
      (algebraMap (X.presheaf.stalk η) X.functionField (X.presheaf.germ ⊤ η trivial t)) ^ n := by
    intro n
    have h1 : X.presheaf.germ _ (genericPoint X) hgD (τ : Γ(X, X.basicOpen t)) =
        algebraMap _ X.functionField (X.presheaf.germ ⊤ η trivial t) := by
      rw [hτ, germ_res, algebraMap_germ]
    rw [← h1]
    change ((Units.map (X.presheaf.germ _ (genericPoint X) hgD).hom.toMonoidHom (τ ^ n) : X.functionField)) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨n, ⟨u, hu, hun⟩, huniq⟩ :=
    GlobalTheory.PrimeElement.existsUnique_zpow_mul_eq_unit (K := X.functionField) hirr hf

  have hext : ∀ a, ∃ sa : Γ(X, U a), X.presheaf.map (homOfLE inf_le_left).op sa =
      X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
    intro a
    refine exists_res_eq hη hp _ fun hηa => ?_
    refine ⟨X.presheaf.germ _ η (⟨hηa, ha₀⟩ : η ∈ U a ⊓ U a₀) (g a a₀) * u, ?_⟩
    rw [map_mul, map_mul, hun, algebraMap_germ, germ_res, hφ n,
      germ_eq_mul_germ hr (⟨genericPoint_mem hηa, hgD⟩ : genericPoint X ∈ U a ⊓ X.basicOpen t) ⟨hga₀, hgD⟩]
    ring
  choose s hs using hext
  have hcomp := compatible_of_res_eq hgD hr (↑(τ ^ n) : Γ(X, X.basicOpen t)) hs
  refine ⟨n, ⟨s, hcomp, hs, a₀, η, hηD, ?_⟩, ?_⟩
  · rw [X.mem_basicOpen (s a₀) η ha₀]
    have hsu : X.presheaf.germ (U a₀) η ha₀ (s a₀) = u := by
      apply IsFractionRing.injective (X.presheaf.stalk η) X.functionField
      rw [hun, algebraMap_germ, ← germ_res inf_le_left (⟨hga₀, hgD⟩ : genericPoint X ∈ U a₀ ⊓ X.basicOpen t) (s a₀),
        hs a₀, map_mul, germ_res, hφ n]
    exact hsu ▸ hu
  · rintro n' ⟨s', hs'c, hs', a', x', hx'D, hx's⟩
    apply huniq n'
    have hηs' : η ∈ X.basicOpen (s' a') := ((hη x').mp hx'D).mem_open (X.basicOpen (s' a')).isOpen hx's
    have hηs₀ : η ∈ X.basicOpen (s' a₀) := mem_basicOpen_of_compatible hg hs'c ha₀ hηs'
    refine ⟨X.presheaf.germ (U a₀) η ha₀ (s' a₀), (X.mem_basicOpen _ η ha₀).mp hηs₀, ?_⟩
    rw [algebraMap_germ, ← germ_res inf_le_left (⟨hga₀, hgD⟩ : genericPoint X ∈ U a₀ ⊓ X.basicOpen t) (s' a₀),
      hs' a₀, map_mul, germ_res, hφ n']

include hη hp in

theorem exists_zpow_mul_isUnit (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hru : ∀ a, IsUnit (r a)) :
    ∃ n : ℤ, ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
  obtain ⟨a₀, ha₀⟩ := hU η
  have hgD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hr0 : ∃ a, r a ≠ 0 := by
    refine ⟨a₀, fun h0 => ?_⟩
    have : Nonempty ↥(U a₀ ⊓ X.basicOpen t) := ⟨⟨genericPoint X, genericPoint_mem ha₀, hgD⟩⟩
    exact (hru a₀).ne_zero h0
  obtain ⟨n, ⟨s, hsc, hs, a', x', hx'D, hx's⟩, -⟩ := existsUnique_zpow_mul hη hp hU hg τ hτ hr hr0
  refine ⟨n, s, fun a => ?_, hsc, hs⟩
  refine isUnit_of_isUnit_res hη hp ?_ fun hηa => ?_
  · rw [hs a]
    exact ((τ ^ n).isUnit.map _).mul (hru a)
  · have hηs' : η ∈ X.basicOpen (s a') := ((hη x').mp hx'D).mem_open (X.basicOpen (s a')).isOpen hx's
    exact mem_basicOpen_of_compatible hg hsc hηa hηs'

theorem zpow_eq_zero {A B : Type*} [CommRing A] [CommRing B] (ρ : A →+* B)
    (hρ : Function.Injective ρ) {σ u p : A} (hσ : IsUnit σ) (hu : IsUnit u) (hp : ¬ IsUnit p)
    (τ : Bˣ) (hτ : (τ : B) = ρ p) {n : ℤ} (h : ρ σ = (τ ^ n : Bˣ) * ρ u) : n = 0 := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · cases k with
    | zero => rfl
    | succ k =>
      exfalso
      have h' : ρ σ = ρ (p ^ (k + 1) * u) := by
        rw [h, map_mul, map_pow, ← hτ, zpow_natCast, Units.val_pow_eq_pow_val]
      have hσ' : IsUnit (p ^ (k + 1) * u) := hρ h' ▸ hσ
      exact hp ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp (isUnit_of_mul_isUnit_left hσ'))
  · cases k with
    | zero => simp
    | succ k =>
      exfalso
      have e : ((τ ^ (-((k + 1 : ℕ) : ℤ)) : Bˣ) : B) * ((τ ^ (k + 1) : Bˣ) : B) = 1 := by
        rw [← Units.val_mul, zpow_neg, zpow_natCast, inv_mul_cancel, Units.val_one]
      have h' : ρ (σ * p ^ (k + 1)) = ρ u := by
        rw [map_mul, map_pow, h, ← hτ, ← Units.val_pow_eq_pow_val, mul_right_comm, e, one_mul]
      have hu' : IsUnit (σ * p ^ (k + 1)) := (hρ h').symm ▸ hu
      exact hp ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp (isUnit_of_mul_isUnit_right hu'))

include hη hp in

theorem exists_isUnit_res_eq (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hru : ∀ a, IsUnit (r a)) {T : Scheme.{u}} [IsIntegral T] (e : T ⟶ X)
    (he : ∃ y', e y' ∈ X.basicOpen t) {y : T} (hy : e y ∉ X.basicOpen t) {a₀ : ι}
    (hya : e y ∈ U a₀) {u : Γ(T, e ⁻¹ᵁ U a₀)} (hu : IsUnit u)
    (hur : T.presheaf.map (homOfLE (e.preimage_mono inf_le_left)).op u =
      e.app (U a₀ ⊓ X.basicOpen t) (r a₀)) :
    ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) = r a := by
  obtain ⟨τ, hτ⟩ := exists_unit_eq_res t
  obtain ⟨n, s, hsu, hsc, hs⟩ := exists_zpow_mul_isUnit hη hp hU hg τ hτ hr hru
  suffices hn : n = 0 by
    subst hn
    refine ⟨s, hsu, hsc, fun a => ?_⟩
    rw [hs a, zpow_zero, Units.val_one, map_one, one_mul]

  have hTV : genericPoint T ∈ e ⁻¹ᵁ U a₀ := genericPoint_mem (show y ∈ e ⁻¹ᵁ U a₀ from hya)
  have hTD : genericPoint T ∈ e ⁻¹ᵁ X.basicOpen t := by
    obtain ⟨y', hy'⟩ := he
    exact genericPoint_mem (show y' ∈ e ⁻¹ᵁ X.basicOpen t from hy')
  have hψ : ∀ (W W' : X.Opens) (hWW : W' ≤ W) (h' : genericPoint T ∈ e ⁻¹ᵁ W') (f : Γ(X, W)),
      T.presheaf.germ _ (genericPoint T) h' (e.app W' (X.presheaf.map (homOfLE hWW).op f)) =
        T.presheaf.germ _ (genericPoint T) (e.preimage_mono hWW h') (e.app W f) := by
    intro W W' hWW h' f
    rw [← CommRingCat.comp_apply (X.presheaf.map (homOfLE hWW).op) (e.app W'), e.naturality, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  have hTVD : genericPoint T ∈ e ⁻¹ᵁ (U a₀ ⊓ X.basicOpen t) := ⟨hTV, hTD⟩
  let φ := (T.presheaf.germ _ (genericPoint T) hTD).hom.comp (e.app (X.basicOpen t)).hom
  refine zpow_eq_zero (T.presheaf.germ _ (genericPoint T) hTV).hom
    (germ_injective_of_isIntegral T _ hTV) (σ := e.app (U a₀) (s a₀)) (u := u)
    (p := e.app (U a₀) (X.presheaf.map (homOfLE (le_top : U a₀ ≤ ⊤)).op t))
    ((hsu a₀).map _) hu ?_ (Units.map φ.toMonoidHom τ) ?_ ?_
  ·
    intro hpu
    apply hy
    have hyb : y ∈ T.basicOpen (e.app (U a₀) (X.presheaf.map (homOfLE (le_top : U a₀ ≤ ⊤)).op t)) := by
      rw [T.basicOpen_of_isUnit hpu]
      exact hya
    rw [← Scheme.preimage_basicOpen, Scheme.basicOpen_res] at hyb
    exact hyb.2
  · change φ τ = _
    simp only [φ, RingHom.comp_apply]
    rw [hτ, hψ ⊤ (X.basicOpen t) le_top hTD t, hψ ⊤ (U a₀) le_top hTV t]
  · have h1 := congrArg (T.presheaf.germ _ (genericPoint T) hTVD) (congrArg (e.app _) (hs a₀))
    rw [hψ (U a₀) _ inf_le_left hTVD (s a₀), map_mul, map_mul, hψ (X.basicOpen t) _ inf_le_right hTVD,
      ← hur, TopCat.Presheaf.germ_res_apply] at h1
    rw [h1]
    congr 1
    change φ ↑(τ ^ n) = ((Units.map φ.toMonoidHom τ ^ n : _) : T.functionField)
    rw [← map_zpow]
    rfl

end Cocycle

end GlobalTheory.PrimeSection
