import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCohomologyVanishesOfPrimeToLNormalNoInStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct Pointwise

namespace GlobalTheory.PrimeToInertia
open GlobalTheory.TameInertiaGen

section Galois
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_pow_apply_eq (σ : G E Ω) (y : Ω) : ∃ d : ℕ, 0 < d ∧ (σ ^ d) y = y := by
  have : IsGalois E Ω := {}
  have ho : IsOpen ((MulAction.stabilizer (G E Ω) y : Subgroup (G E Ω)) : Set (G E Ω)) :=
    isOpen_setOf_apply (F := E) y (fun t => t = y)
  have hf : Finite (G E Ω ⧸ MulAction.stabilizer (G E Ω) y) := Subgroup.quotient_finite_of_isOpen _ ho
  obtain ⟨d, hd, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := MulAction.stabilizer (G E Ω) y)) σ
  exact ⟨d, hd, h⟩

theorem valuation_apply_eq {A : ValuationSubring Ω} {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (y : Ω) :
    A.valuation (σ y) = A.valuation y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  obtain ⟨d, hd, h⟩ := exists_pow_apply_eq σ y
  have key : ∀ (τ : G E Ω), τ ∈ Dec (F := E) A → ∀ a b : Ω, b ≠ 0 →
      A.valuation a < A.valuation b → A.valuation (τ a) < A.valuation (τ b) := by
    intro τ hτ a b hb hab
    have hb' : 0 < A.valuation b := zero_lt_iff.2 (by simpa using hb)
    have hb'' : 0 < A.valuation (τ b) := zero_lt_iff.2 (by simpa using hb)
    have h1 : A.valuation (a / b) < 1 := by rw [map_div₀, div_lt_one₀ hb']; exact hab
    rw [← valuation_apply_lt_one_iff hτ, map_div₀, map_div₀, div_lt_one₀ hb''] at h1
    exact h1
  rcases lt_trichotomy (A.valuation (σ y)) (A.valuation y) with h1 | h1 | h1
  · have : StrictAnti fun i : ℕ => A.valuation ((σ ^ i) y) := strictAnti_nat_of_succ_lt fun i => by
      rw [pow_succ, AlgEquiv.mul_apply]
      exact key _ (pow_mem hσ i) _ _ hy h1
    have := this hd
    simp [h] at this
  · exact h1
  · have : StrictMono fun i : ℕ => A.valuation ((σ ^ i) y) := strictMono_nat_of_lt_succ fun i => by
      rw [pow_succ, AlgEquiv.mul_apply]
      exact key _ (pow_mem hσ i) _ _ (by simpa using hy) h1
    have := this hd
    simp [h] at this

noncomputable def cobChar (A : ValuationSubring Ω) (y : Ωˣ) :
    Ine (F := E) A →* Ωˣ ⧸ A.principalUnitGroup :=
  MonoidHom.mk' (fun σ => QuotientGroup.mk (cob σ.1 y)) fun σ τ => by
    have h : cob σ.1 (cob τ.1 y) ∈ A.principalUnitGroup :=
      cob_mem_of_unit σ.2 (by
        rw [coe_cob, map_div₀, valuation_apply_eq (Ine_le_Dec A τ.2), div_self (by simp)])
    rw [Subgroup.coe_mul, cob_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 h, one_mul]

theorem cobChar_pow_eq_one (A : ValuationSubring Ω) (y : Ω) (hy : y ≠ 0) (σ : Ine (F := E) A) (n : ℕ) :
    cobChar A (Units.mk0 y hy) σ ^ n = 1 ↔ A.valuation ((σ.1 y / y) ^ n - 1) < 1 := by
  change (QuotientGroup.mk (cob σ.1 (Units.mk0 y hy)) : Ωˣ ⧸ A.principalUnitGroup) ^ n = 1 ↔ _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ValuationSubring.mem_principalUnitGroup_iff,
    Units.val_pow_eq_pow_val, coe_cob, Units.val_mk0]

variable (E) in

def primeTo (A : ValuationSubring Ω) (l : ℕ) : Subgroup (G E Ω) where
  carrier := {σ | σ ∈ Ine (F := E) A ∧ ∀ y : Ω, y ≠ 0 → ∃ n : ℕ, Nat.Coprime n l ∧
    A.valuation ((σ y / y) ^ n - 1) < 1}
  one_mem' := ⟨one_mem _, fun y hy => ⟨1, by simp, by simp [div_self hy]⟩⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, h1⟩ ⟨hτ, h2⟩
    refine ⟨mul_mem hσ hτ, fun y hy => ?_⟩
    obtain ⟨n, hn, h1⟩ := h1 y hy
    obtain ⟨m, hm, h2⟩ := h2 y hy
    have e1 := (cobChar_pow_eq_one A y hy ⟨σ, hσ⟩ n).2 h1
    have e2 := (cobChar_pow_eq_one A y hy ⟨τ, hτ⟩ m).2 h2
    refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
    refine (cobChar_pow_eq_one A y hy (⟨σ, hσ⟩ * ⟨τ, hτ⟩) (n * m)).1 ?_
    rw [map_mul, mul_pow, pow_mul, e1, mul_comm n m, pow_mul, e2]
    simp
  inv_mem' := by
    rintro σ ⟨hσ, h1⟩
    refine ⟨inv_mem hσ, fun y hy => ?_⟩
    obtain ⟨n, hn, h1⟩ := h1 y hy
    have e1 := (cobChar_pow_eq_one A y hy ⟨σ, hσ⟩ n).2 h1
    refine ⟨n, hn, (cobChar_pow_eq_one A y hy (⟨σ, hσ⟩⁻¹) n).1 ?_⟩
    rw [map_inv, inv_pow, e1, inv_one]

theorem isClosed_primeTo (A : ValuationSubring Ω) (l : ℕ) : IsClosed (primeTo E A l : Set (G E Ω)) := by
  have e : (primeTo E A l : Set (G E Ω)) = (Ine (F := E) A : Set (G E Ω)) ∩
      ⋂ y, {σ : G E Ω | y ≠ 0 → ∃ n : ℕ, Nat.Coprime n l ∧ A.valuation ((σ y / y) ^ n - 1) < 1} := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact Iff.rfl
  rw [e]
  exact (isClosed_Ine A).inter (isClosed_iInter fun y => isClosed_setOf_apply y
    (fun t => y ≠ 0 → ∃ n : ℕ, Nat.Coprime n l ∧ A.valuation ((t / y) ^ n - 1) < 1))

theorem normal_primeTo (A : ValuationSubring Ω) (l : ℕ) :
    ((primeTo E A l).subgroupOf (Dec (F := E) A)).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨h1, h2⟩ := hn
    refine ⟨by simpa using conj_mem_Ine g.2 h1, fun y hy => ?_⟩
    obtain ⟨m, hm, h⟩ := h2 ((g.1⁻¹ : G E Ω) y) (by simpa using hy)
    refine ⟨m, hm, ?_⟩
    rw [← valuation_apply_lt_one_iff g.2, map_sub, map_pow, map_div₀, mul_inv_apply, map_one] at h
    exact h

theorem mem_of_pow_mem {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A v)
    {l : ℕ} (hl : l.Prime) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (H : Subgroup (G E Ω))
    (ho : IsOpen (H : Set (G E Ω))) {σ : G E Ω} (hσ : σ ∈ primeTo E A l) (a : ℕ)
    (hH : σ ^ (l ^ a) ∈ H) : σ ∈ H := by
  have : IsGalois E Ω := {}
  let C : ClosedSubgroup (G E Ω) := ⟨H, H.isClosed_of_isOpen ho⟩
  have hC : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField C
  rw [← hC, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hy' : (σ ^ (l ^ a)) y = y := (IntermediateField.mem_fixedField_iff H y).1 hy _ hH
  by_contra hne
  have hx : σ y - y ≠ 0 := sub_ne_zero.2 hne
  have hx' : (σ ^ (l ^ a)) (σ y - y) = σ y - y := by
    rw [map_sub, ← AlgEquiv.mul_apply, ← pow_succ, pow_succ', AlgEquiv.mul_apply, hy']
  obtain ⟨n, hn, h1⟩ := hσ.2 _ hx
  have e1 := (cobChar_pow_eq_one A _ hx ⟨σ, hσ.1⟩ n).2 h1
  have e2 : cobChar A (Units.mk0 _ hx) (⟨σ, hσ.1⟩ : Ine (F := E) A) ^ (l ^ a) = 1 := by
    rw [← map_pow, ← pow_one (cobChar A _ _), cobChar_pow_eq_one]
    simp [hx', div_self hx]
  have e3 : cobChar A (Units.mk0 _ hx) (⟨σ, hσ.1⟩ : Ine (F := E) A) = 1 := by
    have := (pow_eq_one_iff_of_coprime (hn.pow_right a)).1 ⟨e1, e2⟩
    exact this
  have e4 : ∀ i : ℕ, A.valuation ((σ ^ i) (σ y - y) / (σ y - y) - 1) < 1 := fun i => by
    have := (cobChar_pow_eq_one A _ hx (⟨σ, hσ.1⟩ ^ i) 1).1 (by rw [map_pow, e3]; simp)
    simpa using this
  have hsum : ∑ i ∈ Finset.range (l ^ a), (σ ^ i) (σ y - y) = 0 := by
    have : ∀ i, (σ ^ i) (σ y - y) = (σ ^ (i + 1)) y - (σ ^ i) y := by
      intro i
      rw [map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (σ ^ i) y), hy']
    simp
  have hlt : A.valuation (∑ i ∈ Finset.range (l ^ a), ((σ ^ i) (σ y - y) / (σ y - y) - 1)) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun i _ => e4 i
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum] at hlt
  apply hv
  apply v.isPrime.mem_of_pow_mem a
  rw [← hA]
  simpa using hlt

theorem exists_coprime_pow_mem {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A v)
    {l : ℕ} (hl : l.Prime) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (U : Subgroup (Dec (F := E) A))
    (ho : IsOpen (U : Set (Dec (F := E) A))) (j : Dec (F := E) A)
    (hj : j ∈ (primeTo E A l).subgroupOf (Dec (F := E) A)) : ∃ n, Nat.Coprime n l ∧ j ^ n ∈ U := by
  have : IsGalois E Ω := {}
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.1 ho
  have h1 : (1 : G E Ω) ∈ V := by
    have : (1 : Dec (F := E) A) ∈ (U : Set (Dec (F := E) A)) := U.one_mem
    rw [← hVU] at this
    exact this
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
  have hf : Finite (G E Ω ⧸ H.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ H.isOpen
  obtain ⟨d, hd, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := H.toSubgroup)) j.1
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' l hl.ne_one
  refine ⟨m, ((Nat.Prime.coprime_iff_not_dvd hl).2 hm).symm, ?_⟩
  have := mem_of_pow_mem hA hl hv H.toSubgroup H.isOpen (pow_mem (Subgroup.mem_subgroupOf.1 hj) m) a
    (by rw [← pow_mul, mul_comm]; exact h)
  have h2 : j ^ m ∈ (U : Set (Dec (F := E) A)) := by
    rw [← hVU]
    exact hH this
  exact h2

theorem exists_limit (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) :
    ∃ j ∈ primeTo E A l, ∀ C : Set (G E Ω), IsClosed C → (∀ᶠ n in Filter.atTop, σ ^ (l ^ n) ∈ C) → j ∈ C := by
  have : IsGalois E Ω := {}
  obtain ⟨j, hj⟩ := exists_clusterPt_of_compactSpace (Filter.map (fun n : ℕ => σ ^ (l ^ n)) Filter.atTop)
  have key : ∀ C : Set (G E Ω), IsClosed C → (∀ᶠ n in Filter.atTop, σ ^ (l ^ n) ∈ C) → j ∈ C :=
    fun C hC h => hC.mem_of_mapClusterPt hj h
  refine ⟨j, ⟨key _ (isClosed_Ine A) (Filter.Eventually.of_forall fun n => pow_mem hσ _), fun y hy => ?_⟩, key⟩
  refine key _ (isClosed_setOf_apply y
    (fun t => ∃ n : ℕ, Nat.Coprime n l ∧ A.valuation ((t / y) ^ n - 1) < 1)) ?_
  obtain ⟨d, hd, h⟩ := exists_pow_apply_eq σ y
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' l hl.ne_one
  filter_upwards [Filter.eventually_ge_atTop a] with n hn
  refine ⟨m, ((Nat.Prime.coprime_iff_not_dvd hl).2 hm).symm, ?_⟩
  have e2 : cobChar A (Units.mk0 _ hy) (⟨σ, hσ⟩ : Ine (F := E) A) ^ (l ^ a * m) = 1 := by
    rw [← map_pow, ← pow_one (cobChar A _ _), cobChar_pow_eq_one]
    simp [h, div_self hy]
  refine (cobChar_pow_eq_one A y hy (⟨σ, hσ⟩ ^ (l ^ n)) m).1 ?_
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [map_pow, ← pow_mul, pow_add, mul_right_comm, pow_mul, e2, one_pow]

end Galois

section Algebra
open IsLocalRing

theorem isUnit_det_pow_sub_one {O : Type} [CommRing O] [IsLocalRing O] {l : ℕ} (hl : l.Prime)
    (hO : (l : O) ∈ maximalIdeal O) {r : ℕ} (M : Matrix (Fin r) (Fin r) O) (h : IsUnit (M - 1).det) (n : ℕ) :
    IsUnit (M ^ (l ^ n) - 1).det := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [Matrix.det_isEmpty]
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have : Fact l.Prime := ⟨hl⟩
  have : CharP (ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (residue O), residue_eq_zero_iff]; exact hO)
  rw [← residue_ne_zero_iff_isUnit, RingHom.map_det] at h ⊢
  rw [map_sub, map_one] at h
  rw [map_sub, map_one, map_pow, ← one_pow (l ^ n), ← sub_pow_char_pow_of_commute _ _ (Commute.one_right _),
    Matrix.det_pow]
  exact pow_ne_zero _ h

theorem isUnit_sub_one_of_orderOf {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {l q : ℕ}
    (hlq : Nat.Coprime l q) (hq : 1 < q) (hO : (l : O) ∈ maximalIdeal O) (ζ : Oˣ) (h : orderOf ζ = q) :
    IsUnit ((ζ : O) - 1) := by
  have hp : IsPrimitiveRoot (ζ : O) q := by
    rw [IsPrimitiveRoot.coe_units_iff, ← h]; exact IsPrimitiveRoot.orderOf ζ
  have h0 := hp.geom_sum_eq_zero hq
  by_contra hn
  have h1 : residue O ζ = 1 := by
    rw [← residue_ne_zero_iff_isUnit, not_not, map_sub, map_one, sub_eq_zero] at hn
    exact hn
  have h2 : ((q : ℕ) : ResidueField O) = 0 := by
    have := congrArg (residue O) h0
    simpa [h1] using this
  have h3 : ((l : ℕ) : ResidueField O) = 0 := by
    rw [← map_natCast (residue O), residue_eq_zero_iff]; exact hO
  have := (Nat.isCoprime_iff_coprime.2 hlq).map (Int.castRingHom (ResidueField O))
  simp [h2, h3] at this

theorem continuous_algebraMap_padicInt {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (I : Ideal O) (hI : IsAdic I) (hO : (l : O) ∈ I) :
    Continuous (algebraMap ℤ_[l] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[l] O) ?_
  rw [ContinuousAt, map_zero, hI.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO n)

variable {Γ O Λ B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ]
  [IsLocalHom (algebraMap O Λ)] [AddCommGroup B] [Module Λ B] {r : ℕ}

omit [Algebra O Λ] in
theorem exists_pow_kill (hB : ∀ b : B, ∃ n, ∀ x ∈ maximalIdeal Λ ^ n, x • b = 0) (m : Fin r → B) :
    ∃ n, ∀ x ∈ maximalIdeal Λ ^ n, ∀ a, x • m a = 0 := by
  choose n hn using hB
  refine ⟨∑ a, n (m a), fun x hx a => hn _ x (Ideal.pow_le_pow_right ?_ hx)⟩
  exact Finset.single_le_sum (f := fun a => n (m a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem map_mem_pow {x : O} {n : ℕ} (hx : x ∈ maximalIdeal O ^ n) : algebraMap O Λ x ∈ maximalIdeal Λ ^ n := by
  have h1 : (maximalIdeal O).map (algebraMap O Λ) ≤ maximalIdeal Λ := map_maximalIdeal_le _
  have := Ideal.mem_map_of_mem (algebraMap O Λ) hx
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h1 n this

theorem contAction_repOn [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace O] [IsTopologicalRing O]
    [TopologicalSpace B] [DiscreteTopology B] (hO : IsAdic (maximalIdeal O))
    (ρ : Γ →* GL (Fin r) O) (hρ : Continuous fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O))
    (κ : Γ →* Λˣ) (hκ : IsOpen (κ.ker : Set Γ)) (hB : ∀ b : B, ∃ n, ∀ x ∈ maximalIdeal Λ ^ n, x • b = 0) :
    ContAction (repOn ρ κ B) := by
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  refine continuous_iff_continuousAt.2 fun g => ?_
  obtain ⟨n, hn⟩ := exists_pow_kill hB m
  have hopen : IsOpen ((maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hO).1 n
  have h1 : ∀ᶠ h in nhds g, κ h = κ g := by
    have : IsOpen ((fun h => g⁻¹ * h) ⁻¹' (κ.ker : Set Γ)) := hκ.preimage (by fun_prop)
    filter_upwards [this.mem_nhds (show g ∈ _ by simp)] with h hh
    have : κ (g⁻¹ * h) = 1 := hh
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  have h2 : ∀ᶠ h in nhds g, ∀ a b, ((ρ h : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b -
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b ∈ maximalIdeal O ^ n := by
    simp only [Filter.eventually_all]
    intro a b
    exact (hopen.preimage ((hρ.matrix_elem a b).sub continuous_const)).mem_nhds (by simp)
  refine (continuousAt_const (y := repOn ρ κ B g m)).congr ?_
  filter_upwards [h1, h2] with h e1 e2
  funext a
  change (κ g : Λ) • ∑ b, algebraMap O Λ (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b) • m b =
    (κ h : Λ) • ∑ b, algebraMap O Λ (((ρ h : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b) • m b
  rw [e1]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  have := hn _ (map_mem_pow (Λ := Λ) (e2 a b)) b
  rw [map_sub, sub_smul, sub_eq_zero] at this
  exact this.symm

omit [IsLocalRing O] [IsLocalRing Λ] [IsLocalHom (algebraMap O Λ)] in
theorem eq_zero_of_fixed (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) {j : Γ} (hκ : κ j = 1)
    (hρ : IsUnit (((ρ j : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) - 1).det) (m : Fin r → B)
    (hm : repOn ρ κ B j m = m) : m = 0 := by
  set M := ((ρ j : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) with hM
  have h1 : Formalism.MainNotions.BlochKatoReduction.matAct (M := B) ((M - 1).map (algebraMap O Λ)) m = 0 := by
    funext a
    have := congrFun hm a
    change (κ j : Λ) • ∑ b, algebraMap O Λ (M a b) • m b = m a at this
    rw [hκ, Units.val_one, one_smul] at this
    change ∑ b, algebraMap O Λ ((M - 1) a b) • m b = 0
    simp [sub_smul, Finset.sum_sub_distrib, this, Matrix.one_apply]
  have h2 : Formalism.MainNotions.BlochKatoReduction.matAct (M := B) (((M - 1)⁻¹ * (M - 1)).map (algebraMap O Λ)) m = 0 := by
    rw [Matrix.map_mul, Formalism.MainNotions.BlochKatoReduction.matAct_mul, Module.End.mul_apply, h1, map_zero]
  rw [Matrix.nonsing_inv_mul _ hρ, Matrix.map_one _ (map_zero _) (map_one _), Formalism.MainNotions.BlochKatoReduction.matAct_one] at h2
  exact h2

end Algebra

open IsLocalRing in

theorem vanishing {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A v)
    {l : ℕ} (hl : l.Prime) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal)
    {O Λ B : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ]
    [IsLocalHom (algebraMap O Λ)] [AddCommGroup B] [Module Λ B] {r : ℕ}
    [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace B] [DiscreteTopology B]
    (hO : IsAdic (maximalIdeal O)) (hlO : (l : O) ∈ maximalIdeal O)
    (ρ : G E Ω →* GL (Fin r) O) (hρ : Continuous fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O))
    (κ : G E Ω →* Λˣ) (hκ : IsOpen (κ.ker : Set (G E Ω))) (hκl : ∀ g, ∃ n, κ g ^ (l ^ n) = 1)
    (hB : ∀ b : B, ∃ n, ∀ x ∈ maximalIdeal Λ ^ n, x • b = 0)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A)
    (hu : IsUnit (((ρ σ : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) - 1).det) :
    H0 ((repOn ρ κ B).comp (Dec (F := E) A).subtype) = ⊥ ∧
      Subsingleton (H1 ((repOn ρ κ B).comp (Dec (F := E) A).subtype)) ∧
      Subsingleton (H2 ((repOn ρ κ B).comp (Dec (F := E) A).subtype)) := by
  have : IsGalois E Ω := {}
  have : CompactSpace (Dec (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  refine GlobalTheory.T.continuousCohomology_vanishes_of_primeToL_normal_no_invariants (Dec (F := E) A) Λ (Fin r → B) _ l ((primeTo E A l).subgroupOf (Dec (F := E) A)) hl
    (normal_primeTo A l) ((isClosed_primeTo A l).preimage continuous_subtype_val)
    (fun U _ ho j hj => exists_coprime_pow_mem hA hl hv U ho j hj) ?_ ?_ ?_
  · exact (contAction_repOn hO ρ hρ κ hκ hB).comp
      (f := fun p : Dec (F := E) A × (Fin r → B) => ((p.1 : G E Ω), p.2)) (by fun_prop)
  · intro m
    obtain ⟨n, hn⟩ := exists_pow_kill hB m
    refine ⟨n, funext fun a => ?_⟩
    have := hn _ (map_mem_pow (Λ := Λ) (Ideal.pow_mem_pow hlO n)) a
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
    exact this
  · intro m hm
    obtain ⟨j, hj, hC⟩ := exists_limit A hl hσ
    have h1 : κ j = 1 := by
      refine hC _ (κ.ker.isClosed_of_isOpen hκ) ?_
      obtain ⟨a, ha⟩ := hκl σ
      filter_upwards [Filter.eventually_ge_atTop a] with n hn
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
      change κ _ = 1
      rw [map_pow, pow_add, pow_mul, ha, one_pow]
    have hopen : IsOpen ((maximalIdeal O : Ideal O) : Set O) := by
      simpa using (isAdic_iff.1 hO).1 1
    have h2 : j ∈ (fun g => (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) - 1).det) ⁻¹'
        ((maximalIdeal O : Ideal O) : Set O)ᶜ := by
      refine hC _ (hopen.isClosed_compl.preimage (hρ.sub continuous_const).matrix_det)
        (Filter.Eventually.of_forall fun n => ?_)
      have := isUnit_det_pow_sub_one hl hlO _ hu n
      rw [← notMem_maximalIdeal] at this
      simpa using this
    exact eq_zero_of_fixed ρ κ h1 (notMem_maximalIdeal.1 h2) m (hm ⟨j, Ine_le_Dec A hj.1⟩ hj)

section HidaSetting
variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem l_mem (i : X.Tw) : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  rw [← not_not (a := _ ∈ _), IsLocalRing.notMem_maximalIdeal]
  intro h
  have := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at this
  exact IsLocalRing.notMem_maximalIdeal.2 this (X.O_l i)

theorem continuous_Tmat (i : X.Tw) (s : X.Sig i) : Continuous (Tmat i s) := by
  have h1 : Continuous fun g : GE N => (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) := by
    simp_rw [← map_inv]
    exact (X.twistCharacterFamily_continuous i _ _).comp continuous_inv
  exact h1.smul (X.rhoS_cont i s)

theorem Tmat_inv (i : X.Tw) (s : X.Sig i) (g : GE N) : (Tmat i s g)⁻¹ = Tmat i s g⁻¹ := by
  rw [← Tgl_coe, ← Tgl_coe, map_inv, Matrix.coe_units_inv]

theorem continuous_Tdual (i : X.Tw) (s : X.Sig i) : Continuous (Tdual i s) := by
  have h1 : Continuous fun g : GE N => ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) :=
    (continuous_algebraMap_padicInt _ (X.twistBaseCoefficientRing_isAdic i) (l_mem i)).comp
      (Units.continuous_val.comp (continuous_cycZ D.host.E N.Om (X.l i)))
  have h2 : Continuous fun g : GE N => (Tmat i s g)⁻¹.transpose := by
    simp_rw [Tmat_inv]
    exact ((continuous_Tmat i s).comp continuous_inv).matrix_transpose
  exact h1.smul h2

theorem exists_inertia (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (h : GalHyp bkP i s)
    (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ Spl (X := X) i) :
    ∃ σ ∈ Ine (F := D.host.E) (N.plOm.1 v), IsUnit (Tmat i s σ - 1).det := by
  obtain ⟨hv1, hv2⟩ := hv
  have hA := N.plOm.2 v
  by_cases hg : ∃ k, v ∈ placesOver D.host.E (D.host.g k)
  · obtain ⟨k, hk⟩ := hg
    obtain ⟨σ, hσ, hd⟩ := (h.2.1.2 k (fun e => hv2 (e ▸ hk)) v hk _ hA).2
    refine ⟨σ, hσ, ?_⟩
    have e : Tmat i s σ - 1 = (((chiS i s σ)⁻¹ : (X.O0 i)ˣ) : X.O0 i) •
        (((X.rhoS i s σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) -
          ((chiS i s σ : (X.O0 i)ˣ) : X.O0 i) • 1) := by
      rw [smul_sub, smul_smul, Units.inv_mul, one_smul]; rfl
    rw [e, Matrix.det_smul]
    refine ((Units.isUnit _).pow _).mul ?_
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    convert hd using 2
    ext a b
    by_cases hab : a = b <;> simp [rbar, Matrix.one_apply, hab]
  · have hg' : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk => hg ⟨k, hk⟩
    have hp : v ∈ X.pD i := by
      rcases hv1 with h1 | h1
      · exact absurd (Set.mem_iUnion.1 h1) hg
      · exact h1
    have hl : (X.l i).Prime := Fact.out
    obtain ⟨q, hq, hq15, hql⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ 15 ∧ X.l i ≠ q := by
      by_cases h3 : X.l i = 3
      · exact ⟨5, by norm_num, by norm_num, by omega⟩
      · exact ⟨3, by norm_num, by norm_num, h3⟩
    have : Fact q.Prime := ⟨hq⟩
    have hc := X.delta_15 i v hp _ hA
    have : Finite ((Ine (F := D.host.E) (N.plOm.1 v)).map (X.delta i)) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    obtain ⟨⟨_, σ, hσ, rfl⟩, hz⟩ := exists_prime_orderOf_dvd_card' q (hc ▸ hq15)
    rw [← Subgroup.orderOf_coe] at hz
    refine ⟨σ, hσ, ?_⟩
    have ho : orderOf (chiS i s σ)⁻¹ = q := by
      rw [orderOf_inv, chiS, X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hp _ hA σ hσ]
      split_ifs
      · exact hz
      · rw [orderOf_inv]; exact hz
    have hu := isUnit_sub_one_of_orderOf ((Nat.coprime_primes hl hq).2 hql) hq.one_lt (l_mem i) _ ho
    have e : Tmat i s σ - 1 = ((((chiS i s σ)⁻¹ : (X.O0 i)ˣ) : X.O0 i) - 1) • 1 := by
      rw [Tmat, h.1.1 v hv2 hg' _ hA σ hσ, sub_smul, one_smul]; rfl
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one]
    exact hu.pow _

end HidaSetting

theorem local_cohomology_vanishes : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ v ∈ Spl (X := X) i, ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ), IsOpen (κ.ker : Set (GE N)) → (∀ g, ∃ n, κ g ^ (X.l i ^ n) = 1) → ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], (∀ b : B, ∃ n, ∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, x • b = 0) → ∀ ρ : GE N →* GL (Fin D.R.r) (X.O0 i), (ρ = Tgl i s ∨ ∀ g, (ρ g : Matrix _ _ (X.O0 i)) = Tdual i s g) → H0 ((repOn ρ κ B).comp (DecV N v).subtype) = ⊥ ∧ Subsingleton (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) ∧ Subsingleton (H2 ((repOn ρ κ B).comp (DecV N v).subtype)) := by
  intro D N X bkP i s h v hv Λ _ _ _ _ κ hκ hκl B _ _ _ _ hB ρ hρ
  obtain ⟨σ, hσ, hu⟩ := exists_inertia bkP i s h v hv
  have hA := N.plOm.2 v
  have hvl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := hv.2
  refine vanishing hA Fact.out hvl (X.twistBaseCoefficientRing_isAdic i) (l_mem i) ρ ?_ κ hκ hκl hB hσ ?_
  · rcases hρ with rfl | hρ
    · simp_rw [Tgl_coe]; exact continuous_Tmat i s
    · simp_rw [hρ]; exact continuous_Tdual i s
  · rcases hρ with rfl | hρ
    · rw [Tgl_coe]; exact hu
    · have h1 : cycZ D.host.E N.Om (X.l i) σ = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq hvl hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
        simp
      have h2 : eps0 X i σ = 1 := by
        rw [eps0, MonoidHom.comp_apply, h1, map_one]
      have h3 : IsUnit (Tmat i s σ).det := by
        rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
      have e : Tdual i s σ - 1 = (-((Tmat i s σ)⁻¹ * (Tmat i s σ - 1))).transpose := by
        rw [Tdual, h2, Units.val_one, one_smul, mul_sub, Matrix.nonsing_inv_mul _ h3, mul_one, neg_sub,
          Matrix.transpose_sub, Matrix.transpose_one]
      rw [hρ, e, Matrix.det_transpose, Matrix.det_neg, Matrix.det_mul]
      exact (isUnit_neg_one.pow _).mul ((Matrix.isUnit_nonsing_inv_det _ h3).mul hu)

end GlobalTheory.PrimeToInertia
