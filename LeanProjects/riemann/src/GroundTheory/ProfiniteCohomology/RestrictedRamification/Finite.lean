import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteRoots
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChange
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteCohomologyOfTrivialOfCyclic
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

section Fixed

variable {k G : Type*} [CommRing k] [Group G] [TopologicalSpace G]

theorem exists_openSubgroup_forall_fixed (A : Rep k G) [IsDiscreteRep A] [Finite A] :
    ∃ W : OpenSubgroup G, ∀ g ∈ W, ∀ a : A, A.ρ g a = a := by
  let F : Subgroup G := ⨅ a : A, stabilizer A.ρ a
  have hF : IsOpen (F : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun a => isOpen_stabilizer A a
  exact ⟨⟨F, hF⟩, fun g hg a => (mem_stabilizer _ _ _).1 (Subgroup.mem_iInf.1 hg a)⟩

end Fixed

section ULiftLinear

def uliftLinearOfAddHom {M N : Type*} [AddCommGroup M] [AddCommGroup N] {iM : Module (ULift.{0} ℤ) M}
    {iN : Module (ULift.{0} ℤ) N} (f : M →+ N) :
    @LinearMap (ULift.{0} ℤ) (ULift.{0} ℤ) _ _ (RingHom.id _) M N _ _ iM iN where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    obtain ⟨m⟩ := c
    have h1 := @Int.cast_smul_eq_zsmul (ULift.{0} ℤ) M _ _ iM m x
    have h2 := @Int.cast_smul_eq_zsmul (ULift.{0} ℤ) N _ _ iN m (f x)
    have e : ((m : ℤ) : ULift.{0} ℤ) = ULift.up m := rfl
    rw [RingHom.id_apply, ← e, h1, h2, map_zsmul]

theorem finite_cohomology_of_addEquiv_of_trivial {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (A B : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] [IsDiscreteRep B]
    (hA : ∀ (g : H) (a : A), A.ρ g a = a) (hB : ∀ (g : H) (b : B), B.ρ g b = b) (e : A ≃+ B) (r : ℕ)
    [Finite (cohomology B r)] : Finite (cohomology A r) := by
  let f : A ⟶ B := Rep.ofHom ⟨uliftLinearOfAddHom e.toAddMonoidHom, fun g => LinearMap.ext fun a => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hA]
    exact (hB g _).symm⟩
  let f' : B ⟶ A := Rep.ofHom ⟨uliftLinearOfAddHom e.symm.toAddMonoidHom,
    fun g => LinearMap.ext fun a => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hB]
      exact (hA g _).symm⟩
  have hff' : f ≫ f' = 𝟙 A := by
    ext a
    exact e.symm_apply_apply a
  refine Finite.of_injective (cohomologyMap f r).hom fun x y hxy => ?_
  have h := congrArg (cohomologyMap f' r).hom hxy
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← cohomologyMap_comp, hff',
    cohomologyMap_id] at h
  exact h

theorem finite_cohomology_of_trivial_of_cyclic {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (n r : ℕ)
    (hcyc : ∀ (C : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep C] [Finite C] [IsAddCyclic C],
      (∀ (g : H) (c : C), C.ρ g c = c) → (∀ c : C, n • c = 0) → Finite (cohomology C r))
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] [Finite A]
    (htriv : ∀ (g : H) (a : A), A.ρ g a = a) (hA : ∀ a : A, n • a = 0) :
    Finite (cohomology A r) :=
  _root_.UpperTheory.Reformulated.B.Gua5.finite_cohomology_of_trivial_of_cyclic n r hcyc A htriv hA

theorem finite_cohomology_of_res_top {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (r : ℕ)
    [Finite (cohomology (Rep.res ((⊤ : OpenSubgroup H) : Subgroup H).subtype A) r)] :
    Finite (cohomology A r) := by
  let e : ((⊤ : OpenSubgroup H) : Subgroup H) ≃* H :=
    { toFun := Subtype.val
      invFun := fun g => ⟨g, OpenSubgroup.mem_top g⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have he : Continuous e.toMonoidHom := continuous_subtype_val
  have he' : Continuous e.symm.toMonoidHom := continuous_id.subtype_mk _
  have : IsDiscreteRep (Rep.res ((⊤ : OpenSubgroup H) : Subgroup H).subtype A) :=
    isDiscreteRep_res_subtype A _
  let f : Rep.res e.toMonoidHom A ⟶ Rep.res ((⊤ : OpenSubgroup H) : Subgroup H).subtype A :=
    Rep.ofHom ⟨LinearMap.id, fun _ => LinearMap.ext fun _ => rfl⟩
  have := isIso_cohomologyMapAlong_of_mulEquiv e he he' f Function.bijective_id r
  exact Finite.of_equiv _ (asIso (cohomologyMapAlong e.toMonoidHom he f r)).toLinearEquiv.toEquiv.symm

end ULiftLinear

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

theorem exists_isPrimitiveRoot_maxUnramifiedOutside (d : ℕ) (hd0 : d ≠ 0)
    (hdS : ∀ v ∉ S, ((d : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    ∃ ζ : maxUnramifiedOutside K.1 ℚ̄ S, IsPrimitiveRoot ζ d := by
  have : NeZero d := ⟨hd0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ d
  refine ⟨⟨ζ, mem_maxUnramifiedOutside_of_pow_eq_one S hd0 hdS hζ.pow_eq_one⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) hζ
    Subtype.val_injective

theorem card_rootsOfUnity_maxUnramifiedOutside (d : ℕ) (hd0 : d ≠ 0)
    (hdS : ∀ v ∉ S, ((d : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    Nat.card (rootsOfUnity d (maxUnramifiedOutside K.1 ℚ̄ S)) = d := by
  have : NeZero d := ⟨hd0⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_maxUnramifiedOutside K S d hd0 hdS
  have hu : IsUnit ζ := hζ.isUnit hd0
  refine IsPrimitiveRoot.card_rootsOfUnity' (ζ := hu.unit) ?_
  rw [← IsPrimitiveRoot.coe_units_iff, IsUnit.unit_spec]
  exact hζ

section Trivial

variable [Finite S] (n : ℕ) (hn0 : n ≠ 0)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hS

theorem finite_cohomology_of_isAddCyclic_gs (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (V : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hV : V ≤ W₀)
    (C : Rep.{0} (ULift.{0} ℤ) (V : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) [IsDiscreteRep C]
    [Finite C] [IsAddCyclic C]
    (htriv : ∀ (g : (V : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (a : C), C.ρ g a = a)
    (hC : ∀ a : C, n • a = 0) (r : ℕ) (hr : r ≤ 2) : Finite (cohomology C r) := by
  obtain ⟨L, hKL, hL, rfl⟩ := exists_gsOpenSubgroup_eq K S V
  obtain ⟨d, hd⟩ : ∃ d, Nat.card C = d := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := hd ▸ Nat.card_pos.ne'
  have hdn : d ∣ n := by
    obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := C)
    rw [← hd, ← addOrderOf_eq_card_of_forall_mem_zmultiples hg]
    exact addOrderOf_dvd_of_nsmul_eq_zero (hC g)
  have hdS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((d : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S :=
    mem_of_dvd_of_mem K S hdn hS
  have hdS' : ∀ v ∉ S, ((d : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv h => hv (hdS v h)
  have : NeZero d := ⟨hd0⟩
  let μ := Rep.res (gsSubtype S hL) (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) d)
  have hμ : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (x : μ),
      μ.ρ g x = x := by
    intro g x
    change (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) d).ρ
      (g : galUnramifiedOutside K.1 ℚ̄ S) x = x
    rw [galRootsOfUnity_ρ_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rw [toMul_ofMul, coe_galRootsOfUnityHom_apply]
    refine hW₀ _ (hV g.2) _ ?_
    obtain ⟨c, hc⟩ := hdn
    rw [hc, pow_mul]
    exact (congrArg (· ^ c) ((mem_rootsOfUnity _ _).1 (Additive.toMul x).2)).trans (one_pow c)
  have hcard : Nat.card C = Nat.card μ := by
    change Nat.card C = Nat.card (Additive (rootsOfUnity d (maxUnramifiedOutside K.1 ℚ̄ S)))
    rw [hd, Nat.card_congr Additive.toMul, card_rootsOfUnity_maxUnramifiedOutside K S d hd0 hdS']
  have : IsAddCyclic μ :=
    inferInstanceAs (IsAddCyclic (Additive (rootsOfUnity d (maxUnramifiedOutside K.1 ℚ̄ S))))
  let e : C ≃+ μ := addEquivOfAddCyclicCardEq hcard
  have hLS : (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))).Finite :=
    placesOver_finite (Set.toFinite S)
  have : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) := hLS.to_subtype
  have hfin : Finite (cohomology μ r) := by
    have h := finite_cohomology_rootsOfUnity L (placesOver S) d hd0
      (fun w hw => mem_placesOver_of_natCast_mem hdS hw) r hr
    exact Finite.of_equiv _ (gsRootsOfUnityCohomologyIso S hL d r).toLinearEquiv.toEquiv
  exact finite_cohomology_of_addEquiv_of_trivial C μ htriv hμ e r

theorem finite_cohomology_of_trivial_gs (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (V : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hV : V ≤ W₀)
    (A : Rep.{0} (ULift.{0} ℤ) (V : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) [IsDiscreteRep A]
    [Finite A] (htriv : ∀ (g : (V : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (a : A), A.ρ g a = a)
    (hA : ∀ a : A, n • a = 0) (r : ℕ) (hr : r ≤ 2) : Finite (cohomology A r) :=
  finite_cohomology_of_trivial_of_cyclic n r
    (fun C _ _ _ hC1 hC2 => finite_cohomology_of_isAddCyclic_gs K S n hS W₀ hW₀ V hV C hC1 hC2 r hr)
    A htriv hA

end Trivial

theorem exists_openSubgroup_fixing_rootsOfUnity (n : ℕ) (hn0 : n ≠ 0) :
    ∃ W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S), ∀ σ ∈ W₀,
      ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 → σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ := by
  have : NeZero n := ⟨hn0⟩
  obtain ⟨W₀, hW⟩ :=
    exists_openSubgroup_forall_fixed (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n)
  refine ⟨W₀, fun σ hσ ζ hζ => ?_⟩
  have h := hW σ hσ (Additive.ofMul ⟨ζ, (mem_rootsOfUnity n ζ).2 hζ⟩)
  exact congrArg (fun y : Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S)) =>
    (((Additive.toMul y : rootsOfUnity n _) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
      maxUnramifiedOutside K.1 ℚ̄ S)) h

variable [Finite S]

theorem finite_cohomology_openSubgroup (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (M : Rep.{0} (ULift.{0} ℤ) (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) [IsDiscreteRep M]
    [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (r : ℕ) (hr : r ≤ 2) : Finite (cohomology M r) := by
  have hn0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
  obtain ⟨W₀, hW₀⟩ := exists_openSubgroup_fixing_rootsOfUnity K S (Nat.card M) hn0
  exact finite_cohomology_of_forall_trivial (Nat.card M) 2 W₀
    (fun V hV A _ _ htriv hA r hr =>
      finite_cohomology_of_trivial_gs K S (Nat.card M) hS W₀ hW₀ V hV A htriv hA r hr)
    U M (fun m => card_nsmul_eq_zero') r hr

theorem finite_cohomology_gs (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (r : ℕ) (hr : r ≤ 2) : Finite (cohomology M r) := by
  let M' := Rep.res ((⊤ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) :
    Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M
  have : IsDiscreteRep M' := isDiscreteRep_res_subtype M _
  have : Finite M' := inferInstanceAs (Finite M)
  have : Finite (cohomology M' r) := finite_cohomology_openSubgroup K S ⊤ M' hS r hr
  exact finite_cohomology_of_res_top M r

end GroundTheory.ProfCoh
