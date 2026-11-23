import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors Pointwise UpperHalfPlane

namespace GlobalTheory.Mem.PerField

theorem ideal_eq_of_pow_eq {A : Type} [CommRing A] [IsDedekindDomain A] {I J : Ideal A} {n : ℕ} (hn : n ≠ 0)
    (h : I ^ n = J ^ n) : I = J := by
  apply le_antisymm
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn, h]
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn, h]

theorem exists_pow_eq_span {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ β : 𝓞 E, I ^ n = Ideal.span {β} := by
  classical
  by_cases hI : I = ⊥
  · exact ⟨1, one_ne_zero, 0, by simp [hI]⟩
  have hI' : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_ne_zero, ?_⟩
  have h1 : ClassGroup.mk0 (⟨I, hI'⟩ ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (pow_mem hI' (Fintype.card (ClassGroup (𝓞 E))))).1 h1
  exact ⟨_, (Ideal.span_singleton_generator _).symm⟩

theorem span_root {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (f : E →+* L)
    {I : Ideal (𝓞 E)} {n : ℕ} (hn : n ≠ 0) {β : 𝓞 E} (h : I ^ n = Ideal.span {β}) {x : L}
    (hx : x ^ n = f β) :
    Submodule.span (𝓞 L) {x} = Submodule.span (𝓞 L) {y | ∃ c ∈ I, y = f (c : E)} := by
  have hi : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hx]
    exact (RingOfIntegers.isIntegral_coe β).map f.toIntAlgHom
  let x' : 𝓞 L := ⟨x, hi⟩
  let f' : 𝓞 E →+* 𝓞 L := RingOfIntegers.mapRingHom f
  have e : Ideal.span {x'} = I.map f' := by
    apply ideal_eq_of_pow_eq hn
    rw [← Ideal.map_pow, h, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    congr 2
    exact RingOfIntegers.ext hx
  have e2 := congrArg (Submodule.map (Algebra.linearMap (𝓞 L) L)) e
  rw [Ideal.map, Ideal.span, Ideal.span, Submodule.map_span, Submodule.map_span, Set.image_singleton] at e2
  refine e2.trans ?_
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩

variable {R : Ranks} (H : Host R)

theorem cmInverseHalfDifferent_mul_relativeDifferent :
    H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have h1 : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  have hb : H.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    rw [h1, h0, Ideal.bot_mul]
  rw [h1, FractionalIdeal.coeIdeal_mul, Host.AA0, ← mul_assoc,
    inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb), one_mul]

theorem ellLat_eq {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL) (g : R.GG) :
    ellLat H embE g = Submodule.span (𝓞 LL)
      {y | ∃ c ∈ (H.conj • H.𝔟 : Ideal (𝓞 H.E)), y = (embE.comp (H.sigmaOf g : H.E →+* H.E)) (c : H.E)} := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have : a * (b : H.E) ∈ H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) :=
      FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
    rw [cmInverseHalfDifferent_mul_relativeDifferent] at this
    obtain ⟨c, hc, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 this
    exact ⟨c, hc, by rw [← e]; rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    have : (c : H.E) ∈ H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
      rw [cmInverseHalfDifferent_mul_relativeDifferent]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ hc
    refine FractionalIdeal.mul_induction_on
      (C := fun z => (embE.comp (H.sigmaOf g : H.E →+* H.E)) z ∈ ellLat H embE g) this ?_ ?_
    · intro a ha b hb
      obtain ⟨b', hb', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      exact Submodule.subset_span ⟨a, ha, b', hb', rfl⟩
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy

theorem mem_baseLat (w : ℂ) : w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem finrank_K : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)

theorem discr_K : NumberField.discr H.K = -(H.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_K H) H.hyp.2.1.squarefree
    (by have := H.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := QuadraticZeta.exists_periodPair (finrank_K H) (discr_K H) σ
    (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe, hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩

theorem isIntegral_jLat : IsIntegral ℤ (jLat (baseLat H)) := by
  obtain ⟨L, hL⟩ := exists_periodPair_baseLat H
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [jLat, TaylorLogMetric.discr, hd.1, hd.2.1, g₂_cube_div_eq_modularJ ha h]
  refine isIntegral_modularJ_of_ringOfIntegers (finrank_K H) (H.φ₀.comp H.K.val.toRingHom) fun α x hx ↦ ?_
  have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
    rw [h, Submodule.mem_span_pair]
    simp [mul_right_inj' ha]
  rw [key, ← hL, mem_baseLat] at hx ⊢
  obtain ⟨c, hc, e⟩ := hx
  refine ⟨α * c, H.ccK.mul_mem_left α hc, ?_⟩
  rw [mul_left_comm, e]
  simp

theorem exists_fieldOK : ∀ (R : Ranks) (H : Host R) (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ M' : IntermediateField ℚ ℂ, FiniteDimensional ℚ M' ∧ M ≤ M' ∧ ∀ (LL : Type) [Field LL] [NumberField LL] (emb : LL →+* ℂ) (embE : H.E →+* LL), emb.comp embE = H.φ₀ → (∀ x ∈ M', ∃ a, emb a = x) → FieldOK H emb embE := by
  intro R H M hM
  obtain ⟨n, hn, β, hβ⟩ := exists_pow_eq_span (H.conj • H.𝔟 : Ideal (𝓞 H.E))
  choose z hz using fun σ : H.E ≃ₐ[ℚ] H.E =>
    IsAlgClosed.exists_pow_nat_eq (H.φ₀ (σ (β : H.E))) (Nat.pos_of_ne_zero hn)
  let T : Set ℂ := insert (jLat (baseLat H)) (Set.range z)
  have : Finite T := (Set.finite_range z).insert _
  have hT : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx ↦ ?_
    rcases hx with rfl | ⟨σ, rfl⟩
    · exact (isIntegral_jLat H).tower_top
    · refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
      rw [hz]
      exact (Algebra.IsIntegral.isIntegral (R := ℚ) (σ (β : H.E))).map H.φ₀.toRatAlgHom
  refine ⟨M ⊔ IntermediateField.adjoin ℚ T, inferInstance, le_sup_left, ?_⟩
  intro LL _ _ emb embE he hM'
  have hT' : ∀ x ∈ T, ∃ a, emb a = x := fun x hx =>
    hM' x ((le_sup_right : _ ≤ M ⊔ _) (IntermediateField.subset_adjoin ℚ T hx))
  refine ⟨hT' _ (Set.mem_insert _ _), fun g => ?_⟩
  obtain ⟨x, hx⟩ := hT' _ (Set.mem_insert_of_mem _ ⟨H.sigmaOf g, rfl⟩)
  refine ⟨x, ?_⟩
  rw [IsGen, ellLat_eq]
  refine span_root _ hn hβ ?_
  apply emb.injective
  rw [map_pow, hx, hz, ← he]
  rfl

end GlobalTheory.Mem.PerField
