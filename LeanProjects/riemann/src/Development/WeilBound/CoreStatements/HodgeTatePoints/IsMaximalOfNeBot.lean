import GroundTheory.FunctionField.PlaceBridge
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PNoetherIntegralClosure

namespace PositivityTheory.HtPt.Plen

open GroundTheory.FunctionField IsLocalRing

theorem finite_closure (k K A : Type) [Field k] [Field K] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra A K] [IsFractionRing A K] [Algebra.EssFiniteType k A] :
    Module.Finite A (integralClosure A K) := by
  classical
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hR : ∀ r : Algebra.EssFiniteType.subalgebra k A, algebraMap _ K r = algebraMap A K (r : A) :=
    fun _ => rfl
  have hfs : FaithfulSMul (Algebra.EssFiniteType.subalgebra k A) K := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact Subtype.ext (hinj h)
  have hfr : IsFractionRing (Algebra.EssFiniteType.subalgebra k A) K := by
    refine IsFractionRing.of_field _ K fun z => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨⟨a₁, s⟩, ha⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid k A) a
    obtain ⟨⟨b₁, t⟩, hb'⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid k A) b
    have hs : IsUnit ((s.1 : Algebra.EssFiniteType.subalgebra k A) : A) := s.2
    have ht : IsUnit ((t.1 : Algebra.EssFiniteType.subalgebra k A) : A) := t.2
    have hs0 : algebraMap A K (s.1 : A) ≠ 0 := (hs.map _).ne_zero
    have ht0 : algebraMap A K (t.1 : A) ≠ 0 := (ht.map _).ne_zero
    have hb0 : algebraMap A K b ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)
    have ha2 : a * (s.1 : A) = (a₁ : A) := ha
    have hb2 : b * (t.1 : A) = (b₁ : A) := hb'
    refine ⟨a₁ * t.1, b₁ * s.1, ?_⟩
    rw [map_mul, map_mul, hR, hR, hR, hR, ← ha2, ← hb2, map_mul, map_mul]
    field_simp
  have hfin := GroundTheory.Heights₂.Heights.FieldNumbers.NoetherIntegralClosureFinite.proof k
    (Algebra.EssFiniteType.subalgebra k A) K K
  have hfg : (integralClosure (Algebra.EssFiniteType.subalgebra k A) K).toSubmodule.FG :=
    Module.Finite.iff_fg.1 hfin
  obtain ⟨t, ht⟩ := hfg
  have hmem : ∀ x : K, IsIntegral (Algebra.EssFiniteType.subalgebra k A) x ↔
      x ∈ Submodule.span (Algebra.EssFiniteType.subalgebra k A) (t : Set K) := by
    intro x
    rw [ht]
    rfl
  have : (integralClosure A K).toSubmodule.FG := by
    refine ⟨t, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      exact ((hmem x).2 (Submodule.subset_span hx)).tower_top
    · intro x hx
      have hx' : IsIntegral A x := hx
      obtain ⟨m, hm⟩ := hx'.exists_multiple_integral_of_isLocalization
        (Algebra.EssFiniteType.submonoid k A)
      have h1 := Submodule.span_le_restrictScalars (Algebra.EssFiniteType.subalgebra k A) A
        (t : Set K) ((hmem _).1 hm)
      have hu : IsUnit ((m.1 : Algebra.EssFiniteType.subalgebra k A) : A) := m.2
      obtain ⟨u, hu⟩ := hu
      have h2 : (u : A) • x ∈ Submodule.span A (t : Set K) := by
        rw [hu]
        exact h1
      have h3 := Submodule.smul_mem _ ((u⁻¹ : Aˣ) : A) h2
      rwa [smul_smul, Units.inv_mul, one_smul] at h3
  exact Module.Finite.iff_fg.2 this

variable {k K : Type} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

noncomputable def resHom (A : Type) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
    (v : Place k K) (hv : ∀ a : A, algebraMap A K a ∈ v.ring) : A →ₐ[k] v.ResidueField where
  toRingHom := (residue v.ring).comp (RingHom.codRestrict (algebraMap A K) v.ring hv)
  commutes' c := by
    change residue v.ring _ = residue v.ring (algebraMap k v.ring c)
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply k A K c).symm

omit [IsFunctionField k K] in
theorem resHom_eq_zero (A : Type) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
    (v : Place k K) (hv : ∀ a : A, algebraMap A K a ∈ v.ring) (a : A) :
    resHom A v hv a = 0 ↔ v.ring.valuation (algebraMap A K a) < 1 := by
  change residue v.ring ⟨algebraMap A K a, hv a⟩ = 0 ↔ _
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

theorem isMaximal_center (A : Type) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
    (v : Place k K) (hv : ∀ a : A, algebraMap A K a ∈ v.ring) (p : Ideal A)
    (hp : ∀ a, a ∈ p ↔ v.ring.valuation (algebraMap A K a) < 1) : p.IsMaximal := by
  have hker : p = RingHom.ker (resHom A v hv) := by
    ext a
    rw [hp, RingHom.mem_ker, resHom_eq_zero]
  subst hker
  have hinj := Ideal.kerLiftAlg_injective (resHom A v hv)
  have : Module.Finite k (A ⧸ RingHom.ker (resHom A v hv)) :=
    Module.Finite.of_injective (Ideal.kerLiftAlg (resHom A v hv)).toLinearMap hinj
  have : IsArtinianRing (A ⧸ RingHom.ker (resHom A v hv)) := IsArtinianRing.of_finite k _
  have : (RingHom.ker (resHom A v hv)).IsPrime := RingHom.ker_isPrime _
  exact Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)

theorem isMaximal_of_ne_bot (A : Type) [CommRing A] [Algebra k A] [Algebra A K]
    [IsScalarTower k A K] (hinj : Function.Injective (algebraMap A K)) (p : Ideal A) (hp0 : p ≠ ⊥)
    (hp : p.IsPrime) : p.IsMaximal := by
  have hu : ∀ y : p.primeCompl, IsUnit (algebraMap A K y) := fun y => by
    refine IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 fun h => y.2 ?_)
    rw [h]
    exact p.zero_mem
  let g : Localization.AtPrime p →+* K := IsLocalization.lift (M := p.primeCompl) hu
  have hg : ∀ a, g (algebraMap A _ a) = algebraMap A K a := fun a => IsLocalization.lift_eq hu a
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing g
  have hA : ∀ a, algebraMap A K a ∈ V := fun a => hg a ▸ hV (algebraMap A _ a)
  have key : ∀ a, a ∈ p ↔ V.valuation (algebraMap A K a) < 1 := by
    intro a
    have h1 : IsUnit (g.codRestrict V.toSubring hV (algebraMap A _ a)) ↔
        IsUnit (algebraMap A (Localization.AtPrime p) a) := isUnit_map_iff _ _
    have h2 : IsUnit (g.codRestrict V.toSubring hV (algebraMap A _ a)) ↔
        V.valuation (g (algebraMap A _ a)) = 1 :=
      V.valuation_eq_one_iff ⟨g (algebraMap A _ a), hV _⟩
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p, h2, hg] at h1
    have h3 : V.valuation (algebraMap A K a) ≤ 1 := (V.valuation_le_one_iff _).2 (hA a)
    rw [lt_iff_le_and_ne, and_iff_right h3, Ne, h1]
    exact not_not.symm
  have hne : V ≠ ⊤ := by
    rintro rfl
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
    have h1 := (key a).1 ha
    have h0 : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
    have h2 := ((⊤ : ValuationSubring K).valuation_le_one_iff (algebraMap A K a)⁻¹).2
      (ValuationSubring.mem_top _)
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0))] at h2
    exact absurd h1 (not_lt.2 h2)
  let v : Place k K := ⟨V, hne, fun c => by
    rw [IsScalarTower.algebraMap_apply k A K]
    exact hA _⟩
  exact isMaximal_center A v hA p key

theorem ord_eq (v : Place k K) (x : v.ring) (hx : x ≠ 0) :
    ∃ n : ℕ, Ring.ord v.ring x = n ∧ v.ord (x : K) = n := by
  have hx' : x ∈ nonZeroDivisors v.ring := mem_nonZeroDivisors_of_ne_zero hx
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hx')
  refine ⟨n, hn.symm, ?_⟩
  have h1 := Ring.ordMonoidWithZeroHom_eq_intValuation hx'
  rw [Ring.ordMonoidWithZeroHom_eq_coe _ hx' hn.symm] at h1
  have h2 : v.valuation (x : K) = (IsDiscreteValuationRing.maximalIdeal v.ring).intValuation x :=
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v.heightOneSpectrum x
  have h3 : v.valuation (x : K) = WithZero.exp (-(n : ℤ)) := by
    rw [h2, WithZero.exp_neg, WithZero.exp_eq_coe_ofAdd, h1, inv_inv]
  rw [Place.ord, h3, WithZero.log_exp, neg_neg]

end PositivityTheory.HtPt.Plen
