import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.WeightCharacterKernel

private theorem open_ker {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [TopologicalSpace K] [T2Space K]
    [ContinuousMul K] (δ : G ℚ Ω →* Kˣ) (hc : Continuous fun g => (δ g : K)) (N : ℕ) (hN : N ≠ 0)
    (h : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := ℚ) A, δ g ^ N = 1) : IsOpen (δ.ker : Set (G ℚ Ω)) := by
  classical
  have hpow : ∀ g, δ g ^ N = 1 := by
    intro g
    by_contra hg
    obtain ⟨a, ha⟩ : ∃ a : K, a = ((δ g ^ N : Kˣ) : K) := ⟨_, rfl⟩
    have ha1 : a ≠ 1 := fun h1 => hg (Units.val_eq_one.mp (ha ▸ h1))
    have hUo : IsOpen ((fun x => (δ x : K) ^ N) ⁻¹' ({a}ᶜ : Set K)) :=
      isOpen_compl_singleton.preimage (hc.pow N)
    have h1U : (1 : G ℚ Ω) ∈ ((fun x => (δ x : K) ^ N) ⁻¹' ({a}ᶜ : Set K)) := by
      simpa [eq_comm] using ha1
    obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
    have hsup : W.toSubgroup ⊔ ((powMonoidHom N).comp δ).ker = ⊤ := by
      refine B3.minkowski Ω _ inferInstance (Subgroup.isOpen_mono le_sup_left W.isOpen) ?_
      intro B x hx
      apply Subgroup.mem_sup_right
      simpa using h B x hx
    have hg' : g ∈ W.toSubgroup ⊔ ((powMonoidHom N).comp δ).ker := hsup ▸ Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hg'
    have hz' : δ z ^ N = 1 := by simpa using hz
    have heq : (δ y : K) ^ N = a := by
      rw [ha, ← hyz, map_mul, mul_pow, hz', mul_one, Units.val_pow_eq_pow_val]
    exact (hW hy) heq
  have hfin : ({x : K | x ^ N = 1} \ {1}).Finite := by
    refine (Finset.finite_toSet (Polynomial.nthRoots N (1 : K)).toFinset).subset ?_
    intro x hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)).mpr hx.1
  have hopen : IsOpen ((fun g => (δ g : K)) ⁻¹' ({x : K | x ^ N = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hc
  convert hopen using 1
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff, Set.mem_diff,
    Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h1
    simp [h1]
  · intro h2
    have hN1 : (δ g : K) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hpow g, Units.val_one]
    exact Units.val_eq_one.mp (by by_contra hne; exact h2 ⟨hN1, hne⟩)

end UpperTheory.V.Ws.WeightCharacterKernel

open UpperTheory.V.Ws.WeightCharacterKernel in
theorem UpperTheory.V.Ws.wtChar :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good →
          ∀ (κ : G ℚ Ω →* PadicAlgCl l) (n : ℕ), Continuous κ → D.UnrT κ 1 → (∀ p ∈ D.Sb, ∀ g ∈ D.Ip p ⊓ D.ψ.ker, κ g = 1) →
          (∀ s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker, κ s = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l s : ℤ_[l]) ^ n) →
          ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, κ g = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ n := by
  intro Ω _ _ _ l _ c D hD κ n hκc hU hSb hl
  classical
  have hF := facts D hD
  have hrb : IsOpen (D.rbar.ker : Set (G ℚ Ω)) := hF.2.2.2.2.2.2.2.2.2.2.2.1
  have hom : IsOpen (D.om.ker : Set (G ℚ Ω)) := hF.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hps : IsOpen (D.ψ.ker : Set (G ℚ Ω)) := hD.psi_open
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℕ, M ≠ 0 ∧ ∀ g : G ℚ Ω, g ^ M ∈ D.rbar.ker ⊓ D.ψ.ker ⊓ D.om.ker := by
    have ho : IsOpen ((D.rbar.ker ⊓ D.ψ.ker ⊓ D.om.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
      simpa only [Subgroup.coe_inf] using (hrb.inter hps).inter hom
    have := Subgroup.quotient_finite_of_isOpen _ ho
    exact ⟨_, Subgroup.index_ne_zero_of_finite, fun g => Subgroup.pow_index_mem _ g⟩
  have two : ∀ (B : ValuationSubring Ω) (p q : ℕ), p.Prime → q.Prime → p ≠ q →
      B.valuation (p : Ω) < 1 → ¬ B.valuation (q : Ω) < 1 := by
    intro B p q hp hq hpq h1 h2
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
    have hab' : (a : Ω) * p + (b : Ω) * q = 1 := by
      have := congrArg (Int.cast : ℤ → Ω) hab
      push_cast at this
      exact this
    have ha : B.valuation (a : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (intCast_mem B a)
    have hb : B.valuation (b : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (intCast_mem B b)
    have e1 : B.valuation ((a : Ω) * p) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) h1
    have e2 : B.valuation ((b : Ω) * q) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hb) h2
    have := B.valuation.map_add ((a : Ω) * p) ((b : Ω) * q)
    rw [hab', map_one] at this
    exact absurd this (not_le.mpr (max_lt e1 e2))
  have halg : Continuous fun x : ℤ_[l] => algebraMap ℤ_[l] (PadicAlgCl l) x := by
    have e : ∀ x : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l]) :=
      fun x => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] _ x
    simp_rw [e]
    exact (continuous_algebraMap ℚ_[l] _).comp continuous_subtype_val
  let cU : G ℚ Ω →* (PadicAlgCl l)ˣ :=
    (Units.map (algebraMap ℤ_[l] (PadicAlgCl l)).toMonoidHom).comp (cycZ ℚ Ω l)
  have hcU : ∀ g, ((cU g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) := by
    intro g
    rfl
  let δ : G ℚ Ω →* (PadicAlgCl l)ˣ := κ.toHomUnits * (cU ^ n)⁻¹
  have hδ : ∀ g, δ g = κ.toHomUnits g * (cU g ^ n)⁻¹ := fun g => by simp [δ]
  have hker : ∀ g, δ g = 1 ↔ κ g = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ n := by
    intro g
    rw [hδ, mul_inv_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val, hcU, MonoidHom.coe_toHomUnits]
  have hval : ∀ g, ((δ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = κ g * ((cU g⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ n := by
    intro g
    rw [hδ, map_inv, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits]
  have hcont : Continuous fun g => ((δ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    simp_rw [hval, hcU]
    exact hκc.mul (((halg.comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))).comp continuous_inv).pow n)
  have hδ1 : ∀ h, κ h = 1 → cycZ ℚ Ω l h = 1 → δ h = 1 := by
    intro h h1 h2
    rw [hker, h1, h2]
    simp
  have hN : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := ℚ) A, δ g ^ M = 1 := by
    intro A g hg
    by_cases hA : Raw.Away D.T A
    · rw [← map_pow]
      have hgM : g ^ M ∈ Ine (F := ℚ) A := Subgroup.pow_mem _ hg M
      have hr : g ^ M ∈ D.rbar.ker := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hM g)).1).1
      refine hδ1 _ (hU A hA _ hgM hr) ?_
      have hlA : ¬ A.valuation (l : Ω) < 1 := hA l (by unfold Raw.T; simp)
      exact (places ℚ Ω l A).2.2.2 hlA hgM
    · have hA' : ∃ p ∈ D.T, A.valuation (p : Ω) < 1 := by
        unfold Raw.Away at hA
        push_neg at hA
        exact hA
      obtain ⟨p, hpT, hpA⟩ := hA'
      have hpT' : p = l ∨ p ∈ D.Sb := by
        unfold Raw.T at hpT
        simpa using hpT
      have hp : p.Prime := by
        rcases hpT' with rfl | hpS
        · exact Fact.out
        · exact (hF.1 p hpS).1
      obtain ⟨x, hx⟩ := (B3.placesQ Ω).2.2 p (D.pl p) A hp (hD.pl_over p hp) hpA
      have hconj : δ g ^ M = δ ((x⁻¹ * g * x) ^ M) := by
        rw [map_pow, map_mul, map_mul, map_inv]
        congr 1
        rw [mul_comm (δ x)⁻¹ (δ g), mul_assoc, inv_mul_cancel, mul_one]
      rw [hconj]
      have hI : (x⁻¹ * g * x) ^ M ∈ Ine (F := ℚ) (D.pl p) := Subgroup.pow_mem _ (hx g hg) M
      have hm := hM (x⁻¹ * g * x)
      have hψ : (x⁻¹ * g * x) ^ M ∈ D.ψ.ker := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hm).1).2
      have ho : (x⁻¹ * g * x) ^ M ∈ D.om.ker := (Subgroup.mem_inf.mp hm).2
      rcases hpT' with rfl | hpS
      · exact (hker _).mpr (hl _ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hI, hψ⟩, ho⟩))
      · refine hδ1 _ (hSb p hpS _ (Subgroup.mem_inf.mpr ⟨hI, hψ⟩)) ?_
        have hne : p ≠ l := (hF.1 p hpS).2.1
        have hnl : ¬ (D.pl p).valuation (l : Ω) < 1 := two (D.pl p) p l hp Fact.out hne (hD.pl_over p hp)
        exact (places ℚ Ω l (D.pl p)).2.2.2 hnl hI
  refine ⟨δ.ker, open_ker δ hcont M hM0 hN, fun g hg => (hker g).mp hg⟩
