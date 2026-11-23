import Mathlib

open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.OnePoint

universe u v w

section Algebra

variable {K : Type u} [Field K]

theorem exists_algHom_ker_eq_of_isMaximal {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (Ω : Type w) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (m : Ideal A) [m.IsMaximal] : ∃ φ : A →ₐ[K] Ω, RingHom.ker φ = m := by
  let := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  let ψ : (A ⧸ m) →ₐ[K] Ω := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ K m), ?_⟩
  ext a
  simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem exists_algHom_ker_eq_nilradical [PerfectField K] {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [Nontrivial A] (Ω : Type w) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : A →ₐ[K] Ω, a = b) : ∃ φ : A →ₐ[K] K, RingHom.ker φ = nilradical A := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  have huniq : ∀ n : Ideal A, n.IsMaximal → n = m := fun n hn ↦ by
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq_of_isMaximal (K := K) Ω m
    obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq_of_isMaximal (K := K) Ω n
    rw [← hφ, ← hψ, h φ ψ]
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  have hnil : nilradical A = m := by
    rw [nilradical, Submodule.zero_eq_bot, Ideal.radical_eq_jacobson, Ideal.jacobson]
    refine le_antisymm (sInf_le ⟨bot_le, hm⟩) (le_sInf ?_)
    rintro n ⟨-, hn⟩
    exact (huniq n hn).ge
  let := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  have hsub : Subsingleton ((A ⧸ m) →ₐ[K] Ω) := ⟨fun a b ↦ Ideal.Quotient.algHom_ext K (h _ _)⟩
  have hcard : Module.finrank K (A ⧸ m) ≤ 1 := by
    rw [← AlgHom.card K (A ⧸ m) Ω]
    exact Fintype.card_le_one_iff_subsingleton.mpr hsub
  have hone : Module.finrank K (A ⧸ m) = 1 := le_antisymm hcard Module.finrank_pos
  have hbij : Function.Bijective (algebraMap K (A ⧸ m)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hone
  let e : K ≃ₐ[K] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId K _) hbij
  refine ⟨(e.symm : (A ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m), ?_⟩
  rw [hnil]
  ext a
  simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem isIntegrallyClosedIn_fractionField_of_residue (R : Type v) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Algebra K R] (L : Type w) [Field L] [Algebra R L]
    [IsFractionRing R L] [Algebra K L] [IsScalarTower K R L]
    (hres : ∀ r : R, ∃ c : K, ¬ IsUnit (r - algebraMap K R c)) : IsIntegrallyClosedIn K L := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap K L).injective, fun {x} hx ↦ ?_⟩
  have key : ∀ y : L, IsIntegral K y → ∃ r : R, algebraMap R L r = y := fun y hy ↦
    IsIntegrallyClosed.algebraMap_eq_of_integral (hy.tower_top (A := R))
  obtain ⟨r, rfl⟩ := key x hx
  obtain ⟨c, hc⟩ := hres r
  refine ⟨c, ?_⟩
  by_contra hne
  have h0 : algebraMap R L r - algebraMap K L c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have halg : IsIntegral K (algebraMap R L r - algebraMap K L c)⁻¹ :=
    (hx.sub isIntegral_algebraMap).isAlgebraic.inv.isIntegral
  obtain ⟨s, hs⟩ := key _ halg
  refine hc (IsUnit.of_mul_eq_one s (IsFractionRing.injective R L ?_))
  rw [map_mul, map_sub, hs, ← IsScalarTower.algebraMap_apply, map_one, mul_inv_cancel₀ h0]

theorem isIntegrallyClosedIn_fractionField_of_surjective_residue (R : Type v) [CommRing R]
    [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] [Algebra K R] (L : Type w) [Field L]
    [Algebra R L] [IsFractionRing R L] [Algebra K L] [IsScalarTower K R L]
    (hres : Function.Surjective fun c : K ↦ IsLocalRing.residue R (algebraMap K R c)) :
    IsIntegrallyClosedIn K L := by
  refine isIntegrallyClosedIn_fractionField_of_residue R L fun r ↦ ?_
  obtain ⟨c, hc⟩ := hres (IsLocalRing.residue R r)
  refine ⟨c, ?_⟩
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
    map_sub, sub_eq_zero]
  exact hc.symm

theorem isIntegrallyClosedIn_fractionField_powerSeries (L : Type w) [Field L] [Algebra K⟦X⟧ L]
    [IsFractionRing K⟦X⟧ L] [Algebra K L] [IsScalarTower K K⟦X⟧ L] :
    IsIntegrallyClosedIn K L := by
  refine isIntegrallyClosedIn_fractionField_of_residue K⟦X⟧ L fun r ↦ ?_
  refine ⟨PowerSeries.constantCoeff r, fun hu ↦ ?_⟩
  simpa using PowerSeries.isUnit_constantCoeff _ hu

theorem algebraMap_laurentSeries : algebraMap K K⸨X⸩ = HahnSeries.C := by
  ext1 c
  simp [HahnSeries.algebraMap_apply']

theorem isIntegrallyClosedIn_laurentSeries : IsIntegrallyClosedIn K K⸨X⸩ :=
  @isIntegrallyClosedIn_fractionField_powerSeries K _ K⸨X⸩ _ _ _ _
    (IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)

theorem exists_eq_C_of_isAlgebraic {x : K⸨X⸩} (hx : IsAlgebraic K x) :
    ∃ c : K, x = HahnSeries.C c := by
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp isIntegrallyClosedIn_laurentSeries).2
    hx.isIntegral
  exact ⟨c, by rw [← hc, algebraMap_laurentSeries]⟩

theorem exists_eq_C_of_eval₂_eq_zero {x : K⸨X⸩} {p : Polynomial K} (hp : p ≠ 0)
    (hx : p.eval₂ (HahnSeries.C : K →+* K⸨X⸩) x = 0) : ∃ c : K, x = HahnSeries.C c :=
  exists_eq_C_of_isAlgebraic ⟨p, hp, by rwa [Polynomial.aeval_def, algebraMap_laurentSeries]⟩

theorem exists_algHom_of_isIntegrallyClosedIn {L : Type w} [Field L] [Algebra K L]
    [IsIntegrallyClosedIn K L] {A : Type v} [CommRing A] [Algebra K A] [Algebra.IsIntegral K A]
    (φ : A →ₐ[K] L) : ∃ ψ : A →ₐ[K] K, (Algebra.ofId K L).comp ψ = φ := by
  have hmem : ∀ a : A, φ a ∈ (Algebra.ofId K L).range := fun a ↦
    (isIntegrallyClosedIn_iff.mp ‹_›).2 ((Algebra.IsIntegral.isIntegral (R := K) a).map φ)
  let e := AlgEquiv.ofInjective (Algebra.ofId K L) (algebraMap K L).injective
  refine ⟨(e.symm : _ →ₐ[K] K).comp (φ.codRestrict _ hmem), ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict _ hmem a))

end Algebra

section Scheme

local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))

theorem nilradical_le_ker {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X) :
    X.nilradical ≤ g.ker := by
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U a ha ↦ ?_
  have ha' : IsNilpotent a := mem_nilradical.mp ha
  exact (ha'.map (g.app U).hom).eq_zero

theorem ker_eq_nilradical {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X) [QuasiCompact g]
    [Surjective g] : g.ker = X.nilradical := by
  refine le_antisymm ?_ (nilradical_le_ker g)
  rw [← Scheme.IdealSheafData.vanishingIdeal_top,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  intro x _
  obtain ⟨t, rfl⟩ := g.surjective x
  exact g.range_subset_ker_support ⟨t, rfl⟩

variable {K : Type u} [Field K]

theorem epi_of_nonempty {T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K)) : Epi g :=
  have : Surjective g := ⟨Function.surjective_to_subsingleton _⟩
  Flat.epi_of_flat_of_surjective g

theorem point_ext {X T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K))
    {s s' : Spec (.of K) ⟶ X} (h : g ≫ s = g ≫ s') : s = s' :=
  have := epi_of_nonempty g
  (cancel_epi g).mp h

theorem exists_section_mem_range [PerfectField K] {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b)
    (p : F) : ∃ s : Spec (.of K) ⟶ F, s ≫ f = 𝟙 _ ∧ p ∈ Set.range s := by
  obtain ⟨A, i, _, q, rfl⟩ := Scheme.exists_Spec_apply_eq p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  let : Algebra K A := φ.hom.toAlgebra
  have : Algebra.FiniteType K A := hft
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨q⟩
  have hcomp : ∀ (L : Type u) [Field L] [Algebra K L] (a : A →ₐ[K] L),
      (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ i) ≫ f = specAlg(K, L) := fun L _ _ a ↦ by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext c
    exact a.commutes c
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq_nilradical (K := K) (A := A) Ω fun a b ↦ by
    have := Spec.map_injective ((cancel_mono i).mp (h _ _ (hcomp Ω a) (hcomp Ω b)))
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom this)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_, ⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  · rw [hcomp K ψ]
    simp
  · refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg i ?_)
    apply PrimeSpectrum.ext
    have hmax : (RingHom.ker ψ).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective ψ fun c ↦ ⟨algebraMap K A c, ψ.commutes c⟩
    have := q.isPrime
    exact hmax.eq_of_le q.isPrime.ne_top (hψ ▸ nilradical_le_prime q.asIdeal)

theorem exists_section_ker_eq_nilradical [PerfectField K] {F : Scheme.{u}} [Nonempty F]
    (f : F ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b) :
    ∃ s : Spec (.of K) ⟶ F, s ≫ f = 𝟙 _ ∧ IsClosedImmersion s ∧ Surjective s ∧
      s.ker = F.nilradical := by
  obtain ⟨s, hs, -⟩ := exists_section_mem_range f Ω h (Classical.arbitrary F)
  have hsurj : Surjective s := ⟨fun p ↦ by
    obtain ⟨s', hs', hp⟩ := exists_section_mem_range f Ω h p
    have : s = s' := point_ext specAlg(K, Ω) (h _ _ (by simp [hs]) (by simp [hs']))
    exact this ▸ hp⟩
  have : Subsingleton F := s.surjective.subsingleton
  have hci : IsClosedImmersion s :=
    have : IsClosedImmersion (s ≫ f) := hs ▸ inferInstance
    have : IsAffine F := by
      obtain ⟨A, i, _, q, -⟩ := Scheme.exists_Spec_apply_eq (Classical.arbitrary F)
      have : Nonempty (Spec A) := ⟨q⟩
      have : IsIso i := (isIso_iff_isOpenImmersion_and_surjective i).mpr
        ⟨‹_›, ⟨Function.surjective_to_subsingleton _⟩⟩
      exact .of_isIso (inv i)
    IsClosedImmersion.of_comp s f
  exact ⟨s, hs, hci, hsurj, ker_eq_nilradical s⟩

theorem isIso_reduction [PerfectField K] {F : Scheme.{u}} [Nonempty F]
    (f : F ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b) :
    IsIso (F.nilradical.subschemeι ≫ f) := by
  obtain ⟨s, hs, _, -, hker⟩ := exists_section_ker_eq_nilradical f Ω h
  have he : s.ker = F.nilradical.subschemeι.ker := by
    rw [hker, Scheme.IdealSheafData.ker_subschemeι]
  have := IsClosedImmersion.isIso_lift s _ he
  rw [← IsClosedImmersion.lift_fac s _ he.le, Category.assoc, hs, Category.comp_id]
  exact this

theorem existsUnique_section [PerfectField K] {F : Scheme.{u}} [Nonempty F]
    (f : F ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b) :
    ∃ s : Spec (.of K) ⟶ F, s ≫ f = 𝟙 _ ∧ (∀ s' : Spec (.of K) ⟶ F, s' ≫ f = 𝟙 _ → s' = s) ∧
      ∀ (T : Scheme.{u}) [IsReduced T] (t : T ⟶ F), (t ≫ f) ≫ s = t := by
  obtain ⟨s, hs, _, -, hker⟩ := exists_section_ker_eq_nilradical f Ω h
  have key : ∀ (T : Scheme.{u}) [IsReduced T] (t : T ⟶ F), (t ≫ f) ≫ s = t := fun T _ t ↦ by
    have hle : s.ker ≤ t.ker := hker ▸ nilradical_le_ker t
    obtain ⟨l, rfl⟩ : ∃ l, l ≫ s = t := ⟨_, IsClosedImmersion.lift_fac s t hle⟩
    rw [Category.assoc l, hs, Category.comp_id]
  exact ⟨s, hs, fun s' hs' ↦ by rw [← key _ s', hs', Category.id_comp], key⟩

theorem exists_point_of_subsingleton_fiber [PerfectField K] {X Y T : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyOfFiniteType κ] (y : Spec (.of K) ⟶ Y)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ X, a ≫ κ = specAlg(K, Ω) ≫ y → b ≫ κ = specAlg(K, Ω) ≫ y → a = b)
    [Nonempty T] [IsReduced T] (g : T ⟶ Spec (.of K)) (x : T ⟶ X) (hx : x ≫ κ = g ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, g ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, g ≫ x₁ = x → x₁ = x₀ := by
  have : Nonempty (pullback κ y : Scheme) := ⟨pullback.lift x g hx (Classical.arbitrary T)⟩
  obtain ⟨s, hs, -, hfac⟩ := existsUnique_section (pullback.snd κ y) Ω fun a b ha hb ↦ by
    refine pullback.hom_ext (h _ _ ?_ ?_) (ha.trans hb.symm)
    · rw [Category.assoc, pullback.condition, reassoc_of% ha]
    · rw [Category.assoc, pullback.condition, reassoc_of% hb]
  have hg : g ≫ s ≫ pullback.fst κ y = x := by
    have := hfac T (pullback.lift x g hx) =≫ pullback.fst κ y
    rwa [pullback.lift_snd, pullback.lift_fst, Category.assoc] at this
  refine ⟨s ≫ pullback.fst κ y, hg, ?_, fun x₁ h₁ ↦ point_ext g (h₁.trans hg.symm)⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hs]

theorem exists_point_of_injective [PerfectField K] {X Y : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyOfFiniteType κ]
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
      Function.Injective fun a : Spec (.of Ω) ⟶ X ↦ a ≫ κ)
    (K' : Type u) [Field K'] [Algebra K K'] (x : Spec (.of K') ⟶ X) (y : Spec (.of K) ⟶ Y)
    (hx : x ≫ κ = specAlg(K, K') ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₁ = x → x₁ = x₀ :=
  exists_point_of_subsingleton_fiber κ y (AlgebraicClosure K)
    (fun _ _ ha hb ↦ h _ (ha.trans hb.symm)) _ x hx

theorem exists_point_of_injective_of_charZero {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (κ : X ⟶ Y) (π : Y ⟶ Spec (.of k)) [LocallyOfFiniteType κ]
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] (a b : Spec (.of Ω) ⟶ X),
      a ≫ κ ≫ π = specAlg(k, Ω) → a ≫ κ = b ≫ κ → a = b)
    (K' : Type u) [Field K'] [Algebra K K'] (x : Spec (.of K') ⟶ X) (y : Spec (.of K) ⟶ Y)
    (hx : x ≫ κ = specAlg(K, K') ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₁ = x → x₁ = x₀ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ π)
  let : Algebra k K := φ.hom.toAlgebra
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  refine exists_point_of_subsingleton_fiber κ y (AlgebraicClosure K)
    (fun a b ha hb ↦ h _ a b ?_ (ha.trans hb.symm)) _ x hx
  rw [reassoc_of% ha, ← hφ, ← Spec.map_comp]
  rfl

theorem exists_section_of_locallyQuasiFinite {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ F) (hx : x ≫ f = specAlg(K, L)) :
    ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, L) ≫ x₀ = x ∧ x₀ ≫ f = 𝟙 _ ∧
      ∀ x₁ : Spec (.of K) ⟶ F, specAlg(K, L) ≫ x₁ = x → x₁ = x₀ := by
  suffices H : ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, L) ≫ x₀ = x by
    obtain ⟨x₀, h₀⟩ := H
    refine ⟨x₀, h₀, point_ext specAlg(K, L) ?_, fun x₁ h₁ ↦ point_ext _ (h₁.trans h₀.symm)⟩
    rw [reassoc_of% h₀, hx, Category.comp_id]
  obtain ⟨A, i, _, q, hq⟩ := Scheme.exists_Spec_apply_eq (x (Classical.arbitrary _))
  have hle : Set.range x ⊆ Set.range i := by
    rintro _ ⟨t, rfl⟩
    exact ⟨q, hq.trans (congrArg x (Subsingleton.elim _ _))⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ i = x := ⟨_, IsOpenImmersion.lift_fac i x hle⟩
  obtain ⟨a, rfl⟩ := Spec.map_surjective l
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hqf : φ.hom.QuasiFinite := by
    have : LocallyQuasiFinite (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp this
  let : Algebra K A := φ.hom.toAlgebra
  have : Algebra.QuasiFinite K A := hqf
  have : Module.Finite K A := .of_quasiFinite
  rw [Category.assoc, ← hφ, ← Spec.map_comp] at hx
  have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
  let a' : A →ₐ[K] L := ⟨a.hom, fun c ↦ DFunLike.congr_fun hc c⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_isIntegrallyClosedIn a'
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext t
  exact DFunLike.congr_fun hψ t

theorem exists_point_of_locallyQuasiFinite {X Y : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyQuasiFinite κ] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ X) (y : Spec (.of K) ⟶ Y) (hx : x ≫ κ = specAlg(K, L) ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, L) ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, L) ≫ x₁ = x → x₁ = x₀ := by
  obtain ⟨s, hs, hs', -⟩ := exists_section_of_locallyQuasiFinite (K := K) (pullback.snd κ y) L
    (pullback.lift x _ hx) (pullback.lift_snd _ _ _)
  have hg : specAlg(K, L) ≫ s ≫ pullback.fst κ y = x := by
    rw [reassoc_of% hs, pullback.lift_fst]
  refine ⟨s ≫ pullback.fst κ y, hg, ?_, fun x₁ h₁ ↦ point_ext _ (h₁.trans hg.symm)⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hs']

theorem exists_section_laurentSeries {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (x : Spec (.of K⸨X⸩) ⟶ F) (hx : x ≫ f = specAlg(K, K⸨X⸩)) :
    ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, K⸨X⸩) ≫ x₀ = x ∧ x₀ ≫ f = 𝟙 _ ∧
      ∀ x₁ : Spec (.of K) ⟶ F, specAlg(K, K⸨X⸩) ≫ x₁ = x → x₁ = x₀ :=
  have := isIntegrallyClosedIn_laurentSeries (K := K)
  exists_section_of_locallyQuasiFinite f _ x hx

theorem exists_point_laurentSeries {X Y : Scheme.{u}} (κ : X ⟶ Y) [LocallyQuasiFinite κ]
    (x : Spec (.of K⸨X⸩) ⟶ X) (y : Spec (.of K) ⟶ Y) (hx : x ≫ κ = specAlg(K, K⸨X⸩) ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K⸨X⸩) ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, K⸨X⸩) ≫ x₁ = x → x₁ = x₀ :=
  have := isIntegrallyClosedIn_laurentSeries (K := K)
  exists_point_of_locallyQuasiFinite κ _ x y hx

theorem one_geometric_point (K : Type u) [Field K] [PerfectField K] :
    (∀ (F : Scheme.{u}) [Nonempty F] (f : F ⟶ Spec (.of K)) [LocallyOfFiniteType f]
      (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω],
      (∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b) →
      IsIso (F.nilradical.subschemeι ≫ f)) ∧
    (∀ (X Y : Scheme.{u}) (κ : X ⟶ Y) [LocallyOfFiniteType κ],
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        Function.Injective fun a : Spec (.of Ω) ⟶ X ↦ a ≫ κ) →
      ∀ (K' : Type u) [Field K'] [Algebra K K'] (x : Spec (.of K') ⟶ X) (y : Spec (.of K) ⟶ Y),
        x ≫ κ = specAlg(K, K') ≫ y →
        ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₀ = x ∧ x₀ ≫ κ = y) ∧
    (∀ x : K⸨X⸩, IsAlgebraic K x → ∃ c : K, x = HahnSeries.C c) ∧
    (∀ (F : Scheme.{u}) (f : F ⟶ Spec (.of K)) [LocallyQuasiFinite f]
      (x : Spec (.of K⸨X⸩) ⟶ F), x ≫ f = specAlg(K, K⸨X⸩) →
      ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, K⸨X⸩) ≫ x₀ = x ∧ x₀ ≫ f = 𝟙 _) := by
  refine ⟨fun F _ f _ Ω _ _ _ h ↦ isIso_reduction f Ω h, fun X Y κ _ h K' _ _ x y hx ↦ ?_,
    fun x hx ↦ exists_eq_C_of_isAlgebraic hx, fun F f _ x hx ↦ ?_⟩
  · obtain ⟨x₀, h₁, h₂, -⟩ := exists_point_of_injective κ h K' x y hx
    exact ⟨x₀, h₁, h₂⟩
  · obtain ⟨x₀, h₁, h₂, -⟩ := exists_section_laurentSeries f x hx
    exact ⟨x₀, h₁, h₂⟩

end Scheme
end GlobalTheory.OnePoint
