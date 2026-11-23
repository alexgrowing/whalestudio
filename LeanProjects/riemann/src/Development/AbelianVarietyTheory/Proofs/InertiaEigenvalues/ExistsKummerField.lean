import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowDescentCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobFixesRootOfOneModPlace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ChevalleySUnits

theorem exists_kummer_field (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (Γ : Subgroup Eˣ) [hΓ : Group.FG Γ] (M : ℕ) (hM : 0 < M)
    (ζ : F) (hζ : IsPrimitiveRoot ζ M) : ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : Γ) (w : Ω), w ^ M = algebraMap E Ω ((u : Eˣ) : E) → w ∈ L := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  obtain ⟨s, hs⟩ := hΓ.out
  set p : F[X] := ∏ g ∈ s, (X ^ M - C (algebraMap E F ((g : Eˣ) : E))) with hp
  have hp0 : p ≠ 0 :=
    (Polynomial.monic_prod_of_monic _ _ fun g _ => Polynomial.monic_X_pow_sub_C _ hM.ne').ne_zero
  have hsplit : (p.map (algebraMap F Ω)).Splits := IsAlgClosed.splits _
  set L : IntermediateField F Ω := IntermediateField.adjoin F (p.rootSet Ω) with hL
  haveI : IsSplittingField F L p := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  haveI : FiniteDimensional F L := IsSplittingField.finiteDimensional L p
  haveI : Normal F L := Normal.of_isSplittingField p
  haveI : IsGalois F L := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨L, inferInstance, inferInstance, ?_⟩
  have hζΩ : IsPrimitiveRoot (algebraMap F Ω ζ) M := hζ.map_of_injective (algebraMap F Ω).injective
  haveI : NeZero M := ⟨hM.ne'⟩
  have hunit : ∀ w : Ω, w ^ M = 1 → w ∈ L := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := hζΩ.eq_pow_of_pow_eq_one hw
    exact pow_mem (L.algebraMap_mem ζ) i
  have hgen : ∀ g ∈ s, ∀ w : Ω, w ^ M = algebraMap E Ω ((g : Eˣ) : E) → w ∈ L := by
    intro g hg w hw
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hp0, ?_⟩
    rw [hp, map_prod]
    apply Finset.prod_eq_zero hg
    simp [hw, ← IsScalarTower.algebraMap_apply]
  intro u
  have hu : u ∈ Subgroup.closure (s : Set Γ) := hs ▸ Subgroup.mem_top u
  induction hu using Subgroup.closure_induction with
  | mem g hg => exact hgen g hg
  | one =>
    intro w hw
    apply hunit
    simpa using hw
  | mul a b _ _ ha hb =>
    intro w hw
    have ha0 : algebraMap E Ω ((a : Eˣ) : E) ≠ 0 := (_root_.map_ne_zero _).mpr (Units.ne_zero _)
    obtain ⟨w1, hw1⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω ((a : Eˣ) : E)) hM
    have hw10 : w1 ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne'] at hw1
      exact ha0 hw1.symm
    have hq : (w / w1) ^ M = algebraMap E Ω ((b : Eˣ) : E) := by
      rw [div_pow, hw, hw1]
      simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
      field_simp
    have hwq : w = w / w1 * w1 := by field_simp
    rw [hwq]
    exact mul_mem (hb _ hq) (ha w1 hw1)
  | inv a _ ha =>
    intro w hw
    have h' : w⁻¹ ^ M = algebraMap E Ω ((a : Eˣ) : E) := by
      rw [inv_pow, hw]
      simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
    have := inv_mem (ha _ h')
    rwa [inv_inv] at this

theorem exists_integral_mul {E : Type} [Field E] [NumberField E] (t : HeightOneSpectrum (𝓞 E)) (x : E)
    (hx : t.valuation E (x - 1) < 1) (M : ℕ) (hM : 0 < M) :
    ∃ (d : E) (z : 𝓞 E), d ≠ 0 ∧ (z : E) = d ^ M * x ∧ z - 1 ∈ t.asIdeal := by
  classical
  have hx1 : t.valuation E x ≤ 1 := by
    have hsplit : x = (x - 1) + 1 := by ring
    rw [hsplit]
    exact (Valuation.map_add _ _ _).trans (max_le hx.le (by simp))
  obtain ⟨n, d, hnd⟩ := t.exists_primeCompl_mul_eq_of_integer x hx1
  have hd : (d : 𝓞 E) ∉ t.asIdeal := d.2
  obtain ⟨a, i, hi, hai⟩ := t.isMaximal.exists_inv hd
  have hD1 : Ideal.Quotient.mk t.asIdeal (a * d) = 1 := by
    rw [← map_one (Ideal.Quotient.mk t.asIdeal), Ideal.Quotient.eq]
    have hrw : a * (d : 𝓞 E) - 1 = -i := by rw [← hai]; ring
    rw [hrw]
    exact neg_mem hi
  have hnd2 : x * ((d : 𝓞 E) : E) = ((n : 𝓞 E) : E) := hnd
  have hnd' : Ideal.Quotient.mk t.asIdeal n = Ideal.Quotient.mk t.asIdeal d := by
    rw [Ideal.Quotient.eq]
    have hrw : algebraMap (𝓞 E) E (n - d) = (x - 1) * algebraMap (𝓞 E) E d := by
      rw [map_sub, ← hnd]; ring
    have key : t.valuation E (algebraMap (𝓞 E) E (n - d)) < 1 := by
      rw [hrw, map_mul]
      exact mul_lt_one_of_lt_of_le hx (t.valuation_le_one _)
    exact (t.valuation_lt_one_iff_mem (K := E) _).mp key
  have hD0 : ((a * d : 𝓞 E) : E) ≠ 0 := by
    intro h
    have h0 : (a * d : 𝓞 E) = 0 := by exact_mod_cast h
    rw [h0, map_zero] at hD1
    exact zero_ne_one hD1
  refine ⟨((a * d : 𝓞 E) : E), (a * d) ^ (M - 1) * (a * n), hD0, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    show algebraMap (𝓞 E) E ((a * d) ^ k * (a * n)) = (algebraMap (𝓞 E) E (a * d)) ^ (k + 1) * x
    simp only [map_mul, map_pow]
    rw [← hnd]
    ring
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, map_pow, hD1, one_pow, one_mul,
      hnd', ← map_mul, hD1, map_one, sub_self]

theorem core (E : Type) [Field E] [NumberField E] (Γ : Subgroup Eˣ) [Group.FG Γ] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (l r : ℕ) (hl : l.Prime) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 E)), Disjoint S T ∧
      ∀ x ∈ Γ, (∀ t ∈ T, t.valuation E ((x : E) - 1) < 1) → ∃ y : E, y ^ (l ^ r) = x := by
  classical
  obtain ⟨M, hM, -, hdesc⟩ := GlobalTheory.exists_pow_descent_cyclotomic E l r hl
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : CharZero (AlgebraicClosure E) :=
    charZero_of_injective_algebraMap (algebraMap E (AlgebraicClosure E)).injective
  obtain ⟨ζ, hζr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic M (AlgebraicClosure E))
    (Polynomial.degree_cyclotomic_pos M _ hM).ne'
  have hζ : IsPrimitiveRoot ζ M := Polynomial.isRoot_cyclotomic_iff.mp hζr
  set K : IntermediateField E (AlgebraicClosure E) := IntermediateField.adjoin E {ζ} with hK
  have hζint : IsIntegral E ζ := (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
  haveI : FiniteDimensional E K := IntermediateField.adjoin.finiteDimensional hζint
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosure K (AlgebraicClosure E) := ⟨inferInstance, Algebra.IsAlgebraic.extendScalars (algebraMap E K).injective⟩
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζK : IsPrimitiveRoot ζK M :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap K (AlgebraicClosure E)) hζ
      (algebraMap K (AlgebraicClosure E)).injective
  obtain ⟨L, hLfin, hLgal, hLroots⟩ := exists_kummer_field E K (AlgebraicClosure E) Γ M hM ζK hζK
  haveI := hLfin
  haveI := hLgal

  have hSne : ∀ s : HeightOneSpectrum (𝓞 E), ∃ b ∈ s.asIdeal, b ≠ 0 :=
    fun s => Submodule.exists_mem_ne_zero_of_ne_bot s.ne_bot
  choose a ha ha0 using hSne
  set N : 𝓞 E := (M : 𝓞 E) * ∏ s ∈ S, a s with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    refine mul_ne_zero (by exact_mod_cast hM.ne') (Finset.prod_ne_zero_iff.mpr fun s _ => ha0 s)
  set N' : 𝓞 K := algebraMap (𝓞 E) (𝓞 K) N with hN'
  have hN'0 : N' ≠ 0 := by
    rw [hN']
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 K))).mpr hN0
  set MainNotions : Set (HeightOneSpectrum (𝓞 K)) := {w | N' ∈ w.asIdeal} with hSK
  have hSKfin : MainNotions.Finite := by
    have hI : Ideal.span {N'} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hN'0
    refine (Ideal.finite_factors hI).subset ?_
    intro w hw
    exact Ideal.dvd_span_singleton.mpr hw
  have hcheb := fun τ : L ≃ₐ[K] L =>
    GlobalTheory.Published.chebotarevDegreeOne' K (AlgebraicClosure E) L τ MainNotions hSKfin
  choose v hvS _ B hB _ σ hσ hres using hcheb
  refine ⟨Finset.univ.image (fun τ => HeightOneSpectrum.under (𝓞 E) (v τ)), ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro s hs hsT
    obtain ⟨τ, -, hτ⟩ := Finset.mem_image.mp hsT
    apply hvS τ
    show N' ∈ (v τ).asIdeal
    have has : a s ∈ (HeightOneSpectrum.under (𝓞 E) (v τ)).asIdeal := hτ ▸ ha s
    have hdvd : a s ∣ N := Dvd.dvd.mul_left (Finset.dvd_prod_of_mem a hs) _
    obtain ⟨c, hc⟩ := hdvd
    rw [hN', hc, map_mul]
    exact Ideal.mul_mem_right _ _ has
  · intro x hx hxT
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E (AlgebraicClosure E) (x : E)) hM
    have hwL : w ∈ L := hLroots ⟨x, hx⟩ w hw
    have hfix : ∀ τ : L ≃ₐ[K] L, τ ⟨w, hwL⟩ = ⟨w, hwL⟩ := by
      intro τ
      set t := HeightOneSpectrum.under (𝓞 E) (v τ) with ht
      have htT : t ∈ Finset.univ.image (fun τ => HeightOneSpectrum.under (𝓞 E) (v τ)) :=
        Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, rfl⟩
      obtain ⟨d, z, hd0, hz, hz1⟩ := exists_integral_mul t (x : E) (hxT t htT) M hM
      have hzK : algebraMap (𝓞 E) (𝓞 K) z - 1 ∈ (v τ).asIdeal := by
        have h1 : z - 1 ∈ (v τ).asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) := hz1
        rw [Ideal.mem_comap, map_sub, map_one] at h1
        exact h1
      have hMv : ((M : ℕ) : 𝓞 K) ∉ (v τ).asIdeal := by
        intro hMin
        apply hvS τ
        show N' ∈ (v τ).asIdeal
        rw [hN', hN, map_mul, map_natCast]
        exact Ideal.mul_mem_right _ _ hMin
      have hroot : (algebraMap E (AlgebraicClosure E) d * w) ^ M =
          algebraMap K (AlgebraicClosure E) ((algebraMap (𝓞 E) (𝓞 K) z : 𝓞 K) : K) := by
        have hzc : ((algebraMap (𝓞 E) (𝓞 K) z : 𝓞 K) : K) = algebraMap E K (z : E) := rfl
        rw [hzc, ← IsScalarTower.algebraMap_apply, hz, mul_pow, hw, map_mul, map_pow]
      have hσw := GlobalTheory.frob_fixes_root_of_one_mod K (AlgebraicClosure E) M ζK hζK (v τ) hMv (B τ) (hB τ) (σ τ)
        (hσ τ) _ hzK _ hroot
      have hσd : (σ τ) (algebraMap E (AlgebraicClosure E) d) = algebraMap E (AlgebraicClosure E) d := by
        rw [IsScalarTower.algebraMap_apply E K (AlgebraicClosure E)]
        exact (σ τ).commutes _
      have hdΩ : algebraMap E (AlgebraicClosure E) d ≠ 0 := (_root_.map_ne_zero _).mpr hd0
      rw [map_mul, hσd] at hσw
      have hσw' : (σ τ) w = w := mul_left_cancel₀ hdΩ hσw
      apply Subtype.ext
      rw [← hres τ]
      change ((σ τ).restrictNormal L ⟨w, hwL⟩ : AlgebraicClosure E) = w
      have hc := AlgEquiv.restrictNormal_commutes (σ τ) L ⟨w, hwL⟩
      exact hc.trans hσw'
    have hbot : (⟨w, hwL⟩ : L) ∈ (⊥ : IntermediateField K L) := (IsGalois.mem_bot_iff_fixed _).mpr hfix
    rw [IntermediateField.mem_bot] at hbot
    obtain ⟨k, hk⟩ := hbot
    have hwK : w ∈ K := by
      have hkw : ((k : K) : AlgebraicClosure E) = w := congrArg Subtype.val hk
      rw [← hkw]
      exact k.2
    exact hdesc (AlgebraicClosure E) ζ hζ (x : E) w hwK hw

theorem exists_places_of_fg (E : Type) [Field E] [NumberField E] (Γ : Subgroup Eˣ) [Group.FG Γ]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) (hm : 0 < m) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 E)), Disjoint S T ∧
      ∀ x ∈ Γ, (∀ t ∈ T, t.valuation E ((x : E) - 1) < 1) → ∃ y : E, y ^ m = x := by
  classical
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp _ => exact core E Γ S p n hp
  | zero => exact absurd hm (lt_irrefl 0)
  | one => exact ⟨∅, Finset.disjoint_empty_right S, fun x _ _ => ⟨x, pow_one _⟩⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨Ta, hSa, hTa⟩ := iha (by omega)
    obtain ⟨Tb, hSb, hTb⟩ := ihb (by omega)
    refine ⟨Ta ∪ Tb, Finset.disjoint_union_right.mpr ⟨hSa, hSb⟩, ?_⟩
    intro x hx hxT
    obtain ⟨ya, hya⟩ := hTa x hx fun t ht => hxT t (Finset.mem_union_left _ ht)
    obtain ⟨yb, hyb⟩ := hTb x hx fun t ht => hxT t (Finset.mem_union_right _ ht)
    have hx0 : (x : E) ≠ 0 := Units.ne_zero x
    have hbez : (a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hab, Nat.cast_one]
    refine ⟨ya ^ (Nat.gcdB a b) * yb ^ (Nat.gcdA a b), ?_⟩
    rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul]
    have e1 : ya ^ (Nat.gcdB a b * ((a * b : ℕ) : ℤ)) = (x : E) ^ ((b : ℤ) * Nat.gcdB a b) := by
      rw [← hya, ← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    have e2 : yb ^ (Nat.gcdA a b * ((a * b : ℕ) : ℤ)) = (x : E) ^ ((a : ℤ) * Nat.gcdA a b) := by
      rw [← hyb, ← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e1, e2, ← zpow_add₀ hx0, add_comm, hbez, zpow_one]

theorem exists_places (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) (hm : 0 < m) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 E)), Disjoint S T ∧
      ∀ x : Eˣ, (∀ v, v ∉ S → v.valuation E (x : E) = 1) → (∀ t ∈ T, t.valuation E ((x : E) - 1) < 1) →
        ∃ y : E, y ^ m = x := by
  haveI := GlobalTheory.QNorm.sUnits_fg E S
  obtain ⟨T, hST, hT⟩ := exists_places_of_fg E (GlobalTheory.QNorm.sUnits E S) S m hm
  exact ⟨T, hST, fun x hx hxT => hT x ((GlobalTheory.QNorm.mem_sUnits E S x).mpr hx) hxT⟩

end GlobalTheory.ChevalleySUnits

end
