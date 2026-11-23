import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order

section Gen

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ℓ : ℕ) (hℓ : ℓ.Prime)

def primeTo : Submonoid R where
  carrier := {r | ∃ n : ℕ, ¬ ℓ ∣ n ∧ r = (n : R)}
  one_mem' := ⟨1, hℓ.not_dvd_one, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, fun h => (hℓ.dvd_mul.1 h).elim ha hb, by push_cast; ring⟩

theorem primeTo_le : primeTo R ℓ hℓ ≤ nonZeroDivisors R := by
  rintro _ ⟨n, hn, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  have : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  exact_mod_cast this

theorem finite_primes [IsDedekindDomain R] [Module.Finite ℤ R] :
    {I : Ideal (Localization (primeTo R ℓ hℓ)) | I.IsPrime}.Finite := by
  have hint : ∀ P : Ideal R, P.IsPrime → Disjoint (primeTo R ℓ hℓ : Set R) P → P ≠ ⊥ → Ideal.span {(ℓ : R)} ≤ P := by
    intro P hP hdis hne
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hc := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hx0 hxP (Algebra.IsIntegral.isIntegral x)
    obtain ⟨m, hmP, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
    have hN : ((m.natAbs : ℕ) : R) ∈ P := by
      rw [Ideal.mem_comap] at hmP
      rcases Int.natAbs_eq m with h | h
      · rw [h] at hmP
        simpa using hmP
      · rw [h] at hmP
        have := P.neg_mem_iff.mpr hmP
        simpa using this
    obtain ⟨e, n, hn, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hm0) ℓ hℓ.one_lt.ne'
    rw [hmn, Nat.cast_mul, Nat.cast_pow] at hN
    rcases hP.mem_or_mem hN with h | h
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hP.mem_of_pow_mem _ h
    · exact absurd h (Set.disjoint_left.mp hdis ⟨n, hn, rfl⟩)
  have hfree : Module.Free ℤ R := Module.free_of_finite_type_torsion_free'
  have hℓ0 : Ideal.span {(ℓ : R)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.ne_zero
  haveI := Ideal.finiteQuotientOfFreeOfNeBot _ hℓ0
  have hfinI : Finite (Ideal (R ⧸ Ideal.span {(ℓ : R)})) :=
    Finite.of_injective (fun I : Ideal (R ⧸ Ideal.span {(ℓ : R)}) => (I : Set (R ⧸ Ideal.span {(ℓ : R)}))) SetLike.coe_injective
  have hfinU : {P : Ideal R | Ideal.span {(ℓ : R)} ≤ P}.Finite := by
    refine (Set.finite_range (fun K : Ideal (R ⧸ Ideal.span {(ℓ : R)}) => K.comap (Ideal.Quotient.mk _))).subset ?_
    intro P hP
    refine ⟨P.map (Ideal.Quotient.mk _), ?_⟩
    simp only
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hP
  refine ((hfinU.insert ⊥).image (fun P => P.map (algebraMap R (Localization (primeTo R ℓ hℓ))))).subset ?_
  intro Q hQ
  have hQ' := (IsLocalization.isPrime_iff_isPrime_disjoint (primeTo R ℓ hℓ) _ Q).mp hQ
  refine ⟨Ideal.under R Q, ?_, IsLocalization.map_comap (primeTo R ℓ hℓ) _ Q⟩
  by_cases h0 : Ideal.under R Q = ⊥
  · exact Or.inl h0
  · exact Or.inr (hint _ hQ'.1 hQ'.2 h0)

include hℓ in

theorem locBasis [IsDedekindDomain R] [Module.Finite ℤ R] {M : Type} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : ∃ (g : ℕ) (b : Fin g → M), IsLocBasis R ℓ b := by
  classical
  haveI : IsDomain (Localization (primeTo R ℓ hℓ)) := IsLocalization.isDomain_localization (primeTo_le R ℓ hℓ)
  haveI : IsDedekindDomain (Localization (primeTo R ℓ hℓ)) := IsLocalization.isDedekindDomain R (primeTo_le R ℓ hℓ) _
  haveI : IsPrincipalIdealRing (Localization (primeTo R ℓ hℓ)) := IsPrincipalIdealRing.of_finite_primes (finite_primes R ℓ hℓ)
  haveI : Module.Finite (Localization (primeTo R ℓ hℓ)) (LocalizedModule (primeTo R ℓ hℓ) M) :=
    Module.Finite.of_isLocalizedModule (primeTo R ℓ hℓ) (LocalizedModule.mkLinearMap (primeTo R ℓ hℓ) M)
  haveI : Module.Free (Localization (primeTo R ℓ hℓ)) (LocalizedModule (primeTo R ℓ hℓ) M) := Module.free_of_finite_type_torsion_free'
  have hinj : Function.Injective (algebraMap R (Localization (primeTo R ℓ hℓ))) :=
    IsLocalization.injective _ (primeTo_le R ℓ hℓ)
  haveI : FaithfulSMul R (Localization (primeTo R ℓ hℓ)) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  set f := LocalizedModule.mkLinearMap (primeTo R ℓ hℓ) M with hf
  set v := Module.finBasis (Localization (primeTo R ℓ hℓ)) (LocalizedModule (primeTo R ℓ hℓ) M) with hv
  choose q hq using fun i => IsLocalizedModule.mk'_surjective (primeTo R ℓ hℓ) f (v i)
  have hu : ∀ i, IsUnit (algebraMap R (Localization (primeTo R ℓ hℓ)) ((q i).2 : R)) :=
    fun i => IsLocalization.map_units _ (q i).2
  have hfb : ∀ i, f (q i).1 = (hu i).unit • v i := by
    intro i
    rw [Units.smul_def, IsUnit.unit_spec, algebraMap_smul, ← hq i]
    exact (IsLocalizedModule.mk'_cancel' f _ _).symm
  have hfb' : ⇑f ∘ (fun i => (q i).1) = (fun i => (hu i).unit) • ⇑v := by
    funext i
    exact hfb i
  have hliL : LinearIndependent (Localization (primeTo R ℓ hℓ)) (⇑f ∘ fun i => (q i).1) := by
    rw [hfb']
    exact v.linearIndependent.units_smul _
  have hliR : LinearIndependent R (fun i => (q i).1) :=
    LinearIndependent.of_comp f (hliL.restrict_scalars' R)
  have hspan : Submodule.span (Localization (primeTo R ℓ hℓ)) (Set.range (⇑f ∘ fun i => (q i).1)) = ⊤ := by
    rw [eq_top_iff, ← v.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : v i = (hu i).unit⁻¹ • f (q i).1 := by
      rw [hfb i, inv_smul_smul]
    rw [h1]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hpt : ∀ y : M, ∃ t : primeTo R ℓ hℓ, (t : R) • y ∈ Submodule.span R (Set.range fun i => (q i).1) := by
    intro y
    have hy : f y ∈ Submodule.localized' (Localization (primeTo R ℓ hℓ)) (primeTo R ℓ hℓ) f
        (Submodule.span R (Set.range fun i => (q i).1)) := by
      rw [Submodule.localized'_span, ← Set.range_comp, hspan]
      trivial
    obtain ⟨m0, hm0, s0, hs0⟩ := (Submodule.mem_localized' _ _ f _ _).mp hy
    rw [IsLocalizedModule.mk'_eq_iff] at hs0
    have h2 : f m0 = f (s0 • y) := by
      rw [hs0, Submonoid.smul_def, Submonoid.smul_def, map_smul]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := primeTo R ℓ hℓ) h2
    refine ⟨c * s0, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← Submonoid.smul_def, ← hc, Submonoid.smul_def]
    exact Submodule.smul_mem _ _ hm0
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  choose t ht using fun j => hpt (g j)
  choose nn hnn hnn' using fun j => (t j).2
  refine ⟨_, fun i => (q i).1, hliR, ∏ j, nn j, ?_, ?_⟩
  · intro h
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finset_prod_iff hℓ.prime _).mp h
    exact hnn j hj
  · intro y
    have hy : y ∈ Submodule.span R (Set.range g) := by
      rw [hg]
      trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_comm, mul_smul, ← Nat.cast_smul_eq_nsmul R (nn j), ← hnn' j]
      exact Submodule.smul_of_tower_mem _ _ (ht j)
    | zero => simp
    | add x z _ _ hx hz =>
      rw [smul_add]
      exact add_mem hx hz
    | smul r x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ _ hx

include hℓ in

theorem locBasis' [IsDedekindDomain R] [Module.Finite ℤ R] {M : Type} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : ∃ b : Fin (Module.finrank R M) → M, IsLocBasis R ℓ b := by
  obtain ⟨g, b, hli, n, hn, hsp⟩ := locBasis R ℓ hℓ (M := M)
  have hn0 : (n : R) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hn (dvd_zero ℓ)
    exact_mod_cast this
  have hmem : ∀ y : M, (n : R) • y ∈ Submodule.span R (Set.range b) := by
    intro y
    rw [Nat.cast_smul_eq_nsmul]
    exact hsp y
  have h1 : Module.finrank R (Submodule.span R (Set.range b)) = g := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have h2 := Submodule.finrank_le (Submodule.span R (Set.range b))
  have hinj : Function.Injective ((n : R) • LinearMap.id : M →ₗ[R] M) := by
    intro x y hxy
    exact smul_right_injective M hn0 hxy
  have h3 := LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.codRestrict (Submodule.span R (Set.range b)) ((n : R) • LinearMap.id) hmem)
    (by
      intro x y hxy
      apply hinj
      simpa using congrArg Subtype.val hxy)
  have hg : g = Module.finrank R M := by omega
  subst hg
  exact ⟨b, hli, n, hn, hsp⟩

end Gen

end GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order

namespace PositivityTheory.Xgf

theorem exists_local_basis_cm_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : ℕ), ℓ.Prime → ∃ (f : ℕ) (b : Fin f → 𝓞 E), 2 * f = Module.finrank ℚ E ∧ IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b := by
  classical
  intro E _ _ _ H ℓ hℓ
  obtain ⟨hD, hrep, -, -, hrank, hproj⟩ := CM.OK_isDedekindDomain_and_projective E H
  haveI := hD
  haveI := (hproj (𝓞 E) (Module.Finite.self (𝓞 E)) inferInstance).1
  haveI : Module.Finite ℤ (CM.OK H) := by
    refine ⟨⟨({1, CM.wK H} : Finset (CM.OK H)), ?_⟩⟩
    rw [eq_top_iff]
    intro a _
    obtain ⟨⟨m1, m2⟩, hm, -⟩ := hrep a
    rw [hm]
    refine add_mem ?_ ?_
    · rw [← zsmul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [← zsmul_eq_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order.locBasis' (CM.OK H) ℓ hℓ (M := 𝓞 E)
  exact ⟨_, b, hrank, hb⟩

end PositivityTheory.Xgf
