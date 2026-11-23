import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.QNorm WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.AdmChars

section Ideals

variable {E : Type} [Field E] [NumberField E]

theorem exists_order_nat (T : Finset (HeightOneSpectrum (𝓞 E))) (n : HeightOneSpectrum (𝓞 E) → ℕ) :
    ∃ α : Eˣ, ∀ v ∈ T, v.valuation E (α : E) = exp (-(n v : ℤ)) := by
  choose π hπ using fun v : HeightOneSpectrum (𝓞 E) => v.intValuation_exists_uniformizer
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) (fun v => n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h e => h (HeightOneSpectrum.ext e)) (fun v => π v.1 ^ n v.1)
  have key : ∀ v ∈ T, v.intValuation y = exp (-(n v : ℤ)) := fun v hv => by
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
    have h2 : v.intValuation (π v ^ n v) = exp (-(n v : ℤ)) := by
      rw [map_pow, hπ, ← exp_nsmul]; simp
    rw [← h2]
    refine Valuation.map_eq_of_sub_lt _ (h1.trans_lt ?_)
    rw [h2, exp_lt_exp]
    push_cast
    omega
  by_cases h0 : y = 0
  · refine ⟨1, fun v hv => ?_⟩
    have := key v hv
    rw [h0, map_zero] at this
    exact absurd this.symm exp_ne_zero
  · exact ⟨Units.mk0 (y : E) (by exact_mod_cast h0), fun v hv => by
      rw [← key v hv]; exact v.valuation_of_algebraMap y⟩

theorem exists_order (T : Finset (HeightOneSpectrum (𝓞 E))) (n : HeightOneSpectrum (𝓞 E) → ℤ) :
    ∃ α : Eˣ, ∀ v ∈ T, v.valuation E (α : E) = exp (-n v) := by
  obtain ⟨a, ha⟩ := exists_order_nat T fun v => (n v).toNat
  obtain ⟨b, hb⟩ := exists_order_nat T fun v => (-n v).toNat
  refine ⟨a / b, fun v hv => ?_⟩
  rw [Units.val_div_eq_div_val, map_div₀, ha v hv, hb v hv, ← exp_sub]
  congr 1
  omega

def GenAway (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (α : Eˣ) : Prop :=
  ∀ v, v ∉ S → v.valuation E (α : E) = exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))

theorem GenAway.mul {S : Finset (HeightOneSpectrum (𝓞 E))} {J K : (FractionalIdeal (𝓞 E)⁰ E)ˣ} {α β : Eˣ}
    (h : GenAway S J α) (h' : GenAway S K β) : GenAway S (J * K) (α * β) := fun v hv => by
  rw [Units.val_mul, map_mul, h v hv, h' v hv, Units.val_mul, FractionalIdeal.count_mul E v J.ne_zero K.ne_zero,
    neg_add, exp_add]

theorem genAway_of_eq (S : Finset (HeightOneSpectrum (𝓞 E))) {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ} {α : Eˣ}
    (h : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (α : E)) : GenAway S J α :=
  fun v _ => by rw [h]; exact GlobalTheory.Idele.valuation_eq_exp_neg_count v α.ne_zero

theorem exists_genAway (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ v ∈ S, v ∉ T) ∧ ∀ J, ∃ α, GenAway S J α := by
  have : Finite ((FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range) :=
    Finite.of_equiv _ (ClassGroup.equiv (R := 𝓞 E) E).toEquiv
  choose a ha using fun q : (FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range =>
    exists_order T fun v => FractionalIdeal.count E v (q.out : FractionalIdeal (𝓞 E)⁰ E)
  have hfin : (⋃ q, {v : HeightOneSpectrum (𝓞 E) | v.valuation E (a q : E) ≠
      exp (-FractionalIdeal.count E v (q.out : FractionalIdeal (𝓞 E)⁰ E))}).Finite := by
    refine Set.finite_iUnion fun q => ?_
    have := (FractionalIdeal.finite_factors (q.out : FractionalIdeal (𝓞 E)⁰ E)).and
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 E)⁰ (a q : E)))
    refine (Filter.eventually_cofinite.1 this).subset fun v hv h => hv ?_
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count v (a q).ne_zero, h.1, h.2]
  refine ⟨hfin.toFinset, fun v hv hT => ?_, fun J => ?_⟩
  · obtain ⟨q, hq⟩ := Set.mem_iUnion.1 (hfin.mem_toFinset.1 hv)
    exact hq (ha q v hT)
  · obtain ⟨⟨_, β, rfl⟩, hβ⟩ := QuotientGroup.mk_out_eq_mul (toPrincipalIdeal (𝓞 E) E).range J
    have h1 : GenAway hfin.toFinset (QuotientGroup.mk J : _ ⧸ (toPrincipalIdeal (𝓞 E) E).range).out
        (a (QuotientGroup.mk J)) := fun v hv => by
      by_contra h
      exact hv (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨_, h⟩))
    have h2 := h1.mul (genAway_of_eq _ (coe_toPrincipalIdeal β⁻¹))
    rw [hβ, map_inv, mul_inv_cancel_right] at h2
    exact ⟨_, h2⟩

theorem exists_ideal_char {S : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ J, ∃ α, GenAway S J α) {B : Type} [CommGroup B]
    (ω : Eˣ →* B) (hω : sUnits E S ≤ ω.ker) :
    ∃ f : (FractionalIdeal (𝓞 E)⁰ E)ˣ →* B, ∀ J α, GenAway S J α → f J = ω α := by
  choose g hg using hS
  have key : ∀ J α β, GenAway S J α → GenAway S J β → ω α = ω β := fun J α β h h' => by
    rw [← div_eq_one, ← map_div]
    refine hω fun v hv => ?_
    rw [Units.val_div_eq_div_val, map_div₀, h v hv, h' v hv, div_self exp_ne_zero]
  exact ⟨MonoidHom.mk' (fun J => ω (g J)) fun J K => by
    rw [← map_mul]; exact key _ _ _ (hg _) ((hg J).mul (hg K)), fun J α h => key J _ _ (hg J) h⟩

end Ideals

section Kummer

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem valuation_int_eq_one {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {x : 𝓞 E}
    (hx : x ∉ v.asIdeal) : A.valuation (algebraMap E Ω (x : E)) = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).2
    (mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom))) (not_lt.1 ((hA x).not.2 hx))

theorem valuation_eq_one {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {α : E}
    (h : v.valuation E α = 1) : A.valuation (algebraMap E Ω α) = 1 := by
  obtain ⟨n, d, e⟩ := v.exists_primeCompl_mul_eq_of_integer α h.le
  have hd : (d : 𝓞 E) ∉ v.asIdeal := d.2
  have hn : n ∉ v.asIdeal := by
    have h1 : v.valuation E (algebraMap (𝓞 E) E d) = 1 :=
      le_antisymm (v.valuation_le_one _) (not_lt.1 ((v.valuation_lt_one_iff_mem _).not.2 hd))
    rw [← v.valuation_lt_one_iff_mem (K := E), not_lt]
    change 1 ≤ v.valuation E (algebraMap (𝓞 E) E n)
    rw [← e, map_mul, h, h1, one_mul]
  have h2 := valuation_int_eq_one hA hn
  have h3 := valuation_int_eq_one hA hd
  have e' : α * ((d : 𝓞 E) : E) = (n : E) := e
  rwa [← e', map_mul, map_mul, h3, mul_one] at h2

theorem not_valuation_natCast_lt_one {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {N : ℕ}
    (hN : (N : 𝓞 E) ∉ v.asIdeal) : ¬ A.valuation (N : Ω) < 1 := by
  simpa using (hA (N : 𝓞 E)).not.2 hN

theorem valuation_root {A : ValuationSubring Ω} {N : ℕ} (hN : N ≠ 0) {y : Ω} (h : A.valuation (y ^ N) = 1) :
    A.valuation y = 1 := by
  rw [map_pow] at h
  rcases lt_trichotomy (A.valuation y) 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le h1 hN).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hN).ne'

variable (Ω) in

def rootSet (N : ℕ) (U : Set Eˣ) : Set Ω := {y | ∃ u ∈ U, y ^ N = algebraMap E Ω (u : E)}

omit [NumberField E] in
theorem finite_rootSet {N : ℕ} (hN : N ≠ 0) {U : Set Eˣ} (hU : U.Finite) : (rootSet Ω N U).Finite := by
  classical
  refine (hU.biUnion fun u _ => (Polynomial.nthRoots N (algebraMap E Ω (u : E))).toFinset.finite_toSet).subset ?_
  rintro y ⟨u, hu, e⟩
  exact Set.mem_biUnion hu (by simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)] using e)

variable (Ω) in

def kummerGroup (N : ℕ) (U : Set Eˣ) : Subgroup (G E Ω) := fixingSubgroup (G E Ω) (rootSet Ω N U)

omit [NumberField E] in
theorem mem_kummerGroup {N : ℕ} {U : Set Eˣ} {σ : G E Ω} :
    σ ∈ kummerGroup Ω N U ↔ ∀ y ∈ rootSet Ω N U, σ y = y := mem_fixingSubgroup_iff _

omit [NumberField E] in
theorem normal_kummerGroup (N : ℕ) (U : Set Eˣ) : (kummerGroup Ω N U).Normal := ⟨fun σ hσ g => by
  rw [mem_kummerGroup] at hσ ⊢
  rintro y ⟨u, hu, e⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hσ _ ⟨u, hu, by rw [← map_pow, e, AlgEquiv.commutes]⟩]
  exact g.apply_symm_apply y⟩

omit [NumberField E] in
theorem isOpen_kummerGroup [IsAlgClosure E Ω] {N : ℕ} (hN : N ≠ 0) {U : Set Eˣ} (hU : U.Finite) :
    IsOpen (kummerGroup Ω N U : Set (G E Ω)) := by
  have := (finite_rootSet (Ω := Ω) hN hU).isOpen_biInter (f := fun y => {σ : G E Ω | σ y = y})
    fun y _ => isOpen_setOf_apply (F := E) y (· = y)
  convert this using 1
  ext σ
  simp [mem_kummerGroup]

theorem ine_le_kummerGroup {N : ℕ} {U : Set Eˣ} {v : HeightOneSpectrum (𝓞 E)} (hN : (N : 𝓞 E) ∉ v.asIdeal)
    (hU : ∀ u ∈ U, v.valuation E (u : E) = 1) {A : ValuationSubring Ω} (hA : IsPlaceOver A v) :
    Ine (F := E) A ≤ kummerGroup Ω N U := fun σ hσ => by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (by simp)
  rw [mem_kummerGroup]
  rintro y ⟨u, hu, e⟩
  have h1 : A.valuation y = 1 := valuation_root hN0 (e ▸ valuation_eq_one hA (hU u hu))
  have h0 : y ≠ 0 := by rintro rfl; simp at h1
  rw [← div_eq_one_iff_eq h0]
  refine eq_one_of_pow_eq_one A (not_valuation_natCast_lt_one hA hN) ?_ ?_
  · rw [div_pow, ← map_pow, e, AlgEquiv.commutes, ← e, div_self (pow_ne_zero _ h0)]
  · rw [div_sub_one h0, map_div₀, h1, div_one]
    exact hσ.2 y h1.le

omit [NumberField E] in

theorem exists_kummer_char [IsAlgClosure E Ω] {N : ℕ} [NeZero N] (σ : G E Ω) (hσ : ∀ y : Ω, y ^ N = 1 → σ y = y) :
    ∃ ω : Eˣ →* rootsOfUnity N Ω, ∀ (α : Eˣ) (y : Ω), y ^ N = algebraMap E Ω (α : E) →
      (((ω α : rootsOfUnity N Ω) : Ωˣ) : Ω) = σ y / y := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  choose r hr using fun α : Eˣ => IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (α : E)) (NeZero.pos N)
  have h0 : ∀ (α : Eˣ) (y : Ω), y ^ N = algebraMap E Ω (α : E) → y ≠ 0 := fun α y e h => by
    rw [h, zero_pow (NeZero.ne N)] at e
    simpa using e.symm
  have key : ∀ (α : Eˣ) (y : Ω), y ^ N = algebraMap E Ω (α : E) → σ (r α) / r α = σ y / y := fun α y e => by
    have h1 := h0 α y e
    have h2 := h0 α _ (hr α)
    have h3 := hσ (r α / y) (by rw [div_pow, hr, e, div_self (by simp)])
    rw [map_div₀, div_eq_div_iff (by simpa using h1) h1] at h3
    rw [div_eq_div_iff h2 h1, h3, mul_comm]
  let w : Eˣ → rootsOfUnity N Ω := fun α => rootsOfUnity.mkOfPowEq (σ (r α) / r α) (by
    rw [div_pow, ← map_pow, hr, AlgEquiv.commutes, div_self (by simp)])
  have hw : ∀ α, (((w α : rootsOfUnity N Ω) : Ωˣ) : Ω) = σ (r α) / r α := fun α => rfl
  refine ⟨MonoidHom.mk' w fun α β => Subtype.ext (Units.ext ?_), fun α y e => (hw α).trans (key α y e)⟩
  rw [Subgroup.coe_mul, Units.val_mul, hw, hw, hw,
    key (α * β) (r α * r β) (by rw [mul_pow, hr, hr, Units.val_mul, map_mul]), map_mul, mul_div_mul_comm]

theorem valuation_pow_sub_pow {A : ValuationSubring Ω} {a b : Ω} (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1)
    (h : A.valuation (a - b) < 1) (k : ℕ) : A.valuation (a ^ k - b ^ k) < 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact (mul_le_of_le_one_left' ha).trans_lt ih
    · exact (mul_le_of_le_one_left' (by rw [map_pow]; exact pow_le_one' hb k)).trans_lt h

theorem exists_residue_char [IsAlgClosure E Ω] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)} (hN : (N : 𝓞 E) ∉ P.asIdeal)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A P) {σ : G E Ω} (hF : IsFrob A (normV P) σ)
    (hσ : ∀ y : Ω, y ^ N = 1 → σ y = y) :
    ∃ ω : Eˣ →* Multiplicative (ZMod N),
      (∀ (α : Eˣ) (y : Ω), y ^ N = algebraMap E Ω (α : E) → σ y = y → ω α = 1) ∧
      (∀ (α : Eˣ) (x : 𝓞 E), (α : E) = x → x - 1 ∈ P.asIdeal → ω α = 1) ∧
      ∀ c, ∃ (α : Eˣ) (x : 𝓞 E), (α : E) = x ∧ x ∉ P.asIdeal ∧ ω α = c := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (by simp)
  have : NeZero N := ⟨hN0⟩
  have : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.2 hN0⟩
  have hNA := not_valuation_natCast_lt_one hA hN
  have : P.asIdeal.IsMaximal := P.isMaximal
  let : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (𝓞 E ⧸ P.asIdeal)ˣ)
  have hq : normV P = orderOf g + 1 := by
    have : 0 < Nat.card (𝓞 E ⧸ P.asIdeal) := Nat.card_pos
    rw [hg, Nat.card_units, normV]
    omega
  have hcong : ∀ y : Ω, A.valuation y = 1 → A.valuation (σ y / y - y ^ orderOf g) < 1 := fun y hy => by
    have h0 : y ≠ 0 := by rintro rfl; simp at hy
    have e : σ y / y - y ^ orderOf g = (σ y - y ^ normV P) / y := by rw [hq]; field_simp; ring
    rw [e, map_div₀, hy, div_one]
    exact hF.2 y hy.le
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  obtain ⟨m, hm⟩ : N ∣ orderOf g := by
    have h1 := hcong ζ (valuation_eq_one_of_pow_eq_one A hN0 hζ.pow_eq_one)
    rw [hσ ζ hζ.pow_eq_one, div_self (hζ.ne_zero hN0)] at h1
    exact hζ.dvd_of_pow_eq_one _ (eq_of_pow_eq_one A hNA (one_pow _)
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) h1).symm
  obtain ⟨ω, hω⟩ := exists_kummer_char (N := N) σ hσ
  have hres : ∀ (α : Eˣ) (x : 𝓞 E), (α : E) = x → x ∉ P.asIdeal → ∀ k : ℕ,
      (ω α ^ k = 1 ↔ x ^ (m * k) - 1 ∈ P.asIdeal) := fun α x e hx k => by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (α : E)) (NeZero.pos N)
    have h1 : A.valuation y = 1 := valuation_root hN0 (by rw [hy, e]; exact valuation_int_eq_one hA hx)
    have h2 := hcong y h1
    rw [← hω α y hy] at h2
    have hr : ∀ z : rootsOfUnity N Ω, ((z : Ωˣ) : Ω) ^ N = 1 := fun z => (mem_rootsOfUnity' _ _).1 z.2
    have h3 := valuation_pow_sub_pow (valuation_eq_one_of_pow_eq_one A hN0 (hr _)).le
      (by rw [map_pow, h1, one_pow]) h2 k
    have e2 : algebraMap E Ω ((x ^ (m * k) - 1 : 𝓞 E) : E) = (y ^ orderOf g) ^ k - 1 := by
      rw [hm, ← pow_mul, mul_assoc, pow_mul y N, hy, e]
      simp
    have e3 : (((ω α : rootsOfUnity N Ω) : Ωˣ) : Ω) ^ k = (((ω α ^ k : rootsOfUnity N Ω) : Ωˣ) : Ω) := by simp
    rw [e3] at h3
    rw [← hA, e2]
    constructor
    · intro h
      rw [h] at h3
      rw [Valuation.map_sub_swap]
      exact h3
    · intro h
      refine Subtype.ext (Units.ext (eq_one_of_pow_eq_one A hNA (hr _) ?_))
      have := Valuation.map_add_lt _ h3 h
      rwa [sub_add_sub_cancel] at this
  have hcard : Nat.card (rootsOfUnity N Ω) = N := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N
  let ι : rootsOfUnity N Ω ≃* Multiplicative (ZMod N) := mulEquivOfCyclicCardEq (by rw [hcard]; simp)
  refine ⟨ι.toMonoidHom.comp ω, fun α y hy h => ?_, fun α x e hx => ?_, fun c => ?_⟩
  · have h0 : y ≠ 0 := fun h => by
      rw [h, zero_pow hN0] at hy
      simpa using hy.symm
    have : ω α = 1 := Subtype.ext (Units.ext (by rw [hω α y hy, h, div_self h0]; rfl))
    rw [MonoidHom.comp_apply, this, map_one]
  · have hx' : x ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.asIdeal.sub_mem h hx))
    have := (hres α x e hx' 1).2 (by
      rw [← Ideal.Quotient.eq, map_one] at hx ⊢
      rw [map_pow, hx, one_pow])
    rw [pow_one] at this
    rw [MonoidHom.comp_apply, this, map_one]
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g : 𝓞 E ⧸ P.asIdeal)
    have hx' : x ∉ P.asIdeal := fun h => g.ne_zero (by rw [← hx]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
    have h0 : (x : E) ≠ 0 := fun h => hx' (by rw [show x = 0 by exact_mod_cast h]; exact zero_mem _)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact (orderOf_pos g).ne' hm)
    have hord : orderOf (ω (Units.mk0 _ h0)) = N := by
      refine Nat.dvd_antisymm ((orderOf_dvd_natCard _).trans hcard.dvd) ?_
      have := (hres (Units.mk0 _ h0) x rfl hx' _).1 (pow_orderOf_eq_one _)
      rw [← Ideal.Quotient.eq, map_one, map_pow, hx, ← Units.val_pow_eq_pow_val, Units.val_eq_one,
        ← orderOf_dvd_iff_pow_eq_one, hm, mul_comm] at this
      exact Nat.dvd_of_mul_dvd_mul_left hm0 this
    have htop : Subgroup.zpowers (ω (Units.mk0 _ h0)) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 (htop ▸ Subgroup.mem_top (ι.symm c)) :
      ι.symm c ∈ Submonoid.powers (ω (Units.mk0 _ h0)))
    refine ⟨Units.mk0 _ h0 ^ k, x ^ k, by simp, fun h => hx' (P.isPrime.mem_of_pow_mem k h), ?_⟩
    have hk' : ω (Units.mk0 _ h0) ^ k = ι.symm c := hk
    rw [MonoidHom.comp_apply, map_pow, hk']
    exact ι.apply_symm_apply c

end Kummer

section Ray

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem dec_le_ker {B : Type} [Group B] {φ : G E Ω →* B} (ho : IsOpen (φ.ker : Set (G E Ω)))
    {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    (hI : ∀ σ ∈ Ine (F := E) A, φ σ = 1) (hF : ∀ σ, IsFrob A (normV v) σ → φ σ = 1) :
    ∀ σ ∈ Dec (F := E) A, φ σ = 1 := fun σ hσ => by
  obtain ⟨τ, hτ⟩ := exists_isFrob hA
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine E Ω A v hA ⟨τ, hτ.1⟩ hτ
  have h2 := Subgroup.topologicalClosure_minimal _ (t := φ.ker.subgroupOf (Dec (F := E) A))
    (sup_le ((Subgroup.zpowers_le (g := (⟨τ, hτ.1⟩ : Dec (F := E) A))).2 (Subgroup.mem_subgroupOf.2 (hF τ hτ)))
      (fun g (hg : g ∈ (Ine (F := E) A).subgroupOf (Dec (F := E) A)) => hI g.1 hg))
    ((φ.ker.isClosed_of_isOpen ho).preimage continuous_subtype_val)
  rw [h] at h2
  exact h2 (Subgroup.mem_top (⟨σ, hσ⟩ : Dec (F := E) A))

variable (E Ω) in

theorem exists_ray_chars (hArt : GlobalTheory.Published.RayCharacterArtin) {N : ℕ} (hN0 : N ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (hT : ∀ v ∈ T, (N : 𝓞 E) ∉ v.asIdeal) :
    ∃ (H : Subgroup (G E Ω)) (S : Finset (HeightOneSpectrum (𝓞 E))), IsOpen (H : Set (G E Ω)) ∧ H.Normal ∧
      (∀ v ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := E) A ≤ H) ∧
      ∀ P, P ∉ S → ∀ A₀ : ValuationSubring Ω, IsPlaceOver A₀ P → Dec (F := E) A₀ ≤ H →
        ∃ χ : G E Ω →* Multiplicative (ZMod N), IsOpen (χ.ker : Set (G E Ω)) ∧
          (∀ v : HeightOneSpectrum (𝓞 E), (N : 𝓞 E) ∈ v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
            ∀ σ ∈ Dec (F := E) A, χ σ = 1) ∧
          (∀ v, v ≠ P → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := E) A, χ σ = 1) ∧
          ∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ c, ∃ σ ∈ Ine (F := E) A, χ σ = c := by
  classical
  obtain ⟨S₀, hS₀, hgen₀⟩ := exists_genAway T
  have hfin := Ideal.finite_factors (I := Ideal.span {(N : 𝓞 E)}) (by simpa using hN0)
  let S := S₀ ∪ hfin.toFinset
  have hNS : ∀ v : HeightOneSpectrum (𝓞 E), (N : 𝓞 E) ∈ v.asIdeal → v ∈ S := fun v hv =>
    Finset.mem_union_right _ (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 hv))
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => by
    rcases Finset.mem_union.1 h with h | h
    · exact hS₀ v h hv
    · exact hT v hv (Ideal.dvd_span_singleton.1 (hfin.mem_toFinset.1 h))
  have hgen : ∀ J, ∃ α, GenAway S J α := fun J =>
    (hgen₀ J).imp fun α h v hv => h v fun h' => hv (Finset.mem_union_left _ h')
  obtain ⟨U, hU, hUf⟩ := (Subgroup.fg_iff _).1 ((Group.fg_iff_subgroup_fg _).1 (sUnits_fg E S))
  refine ⟨kummerGroup Ω N (insert 1 U), S, isOpen_kummerGroup hN0 (hUf.insert 1), normal_kummerGroup _ _,
    fun v hv A hA => ine_le_kummerGroup (hT v hv) ?_ hA, fun P hP A₀ hA₀ hD => ?_⟩
  · rintro u (rfl | hu)
    · simp
    · exact (hU ▸ Subgroup.subset_closure hu : u ∈ sUnits E S) v (hTS v hv)
  obtain ⟨σ₀, hσ₀⟩ := exists_isFrob hA₀
  have hfix := mem_kummerGroup.1 (hD hσ₀.1)
  obtain ⟨ω, hω1, hω2, hω3⟩ := exists_residue_char (fun h => hP (hNS P h)) hA₀ hσ₀
    fun y hy => hfix y ⟨1, Set.mem_insert _ _, by simpa using hy⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨f, hf⟩ := exists_ideal_char hgen ω (by
    rw [← hU, Subgroup.closure_le]
    intro u hu
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (u : E)) (Nat.pos_of_ne_zero hN0)
    exact hω1 u y hy (hfix y ⟨u, Set.mem_insert_of_mem _ hu, hy⟩))
  have hf' : ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (α : Eˣ) (x : 𝓞 E), (α : E) = x →
      (J : FractionalIdeal (𝓞 E)⁰ E) = (Ideal.span {x} : Ideal (𝓞 E)) → f J = ω α := fun J α x e hJ =>
    hf J α (genAway_of_eq S (by rw [hJ, e, FractionalIdeal.coeIdeal_span_singleton]))
  obtain ⟨χ, h1, h2, h3, h4, -⟩ := hArt E Ω P.asIdeal P.ne_bot _ (f.comp (idealsPrimeTo P.asIdeal).subtype)
    fun x J hx hJ => (hf' J.1 (Units.mk0 _ (GlobalTheory.RayChar.ne_zero_of_eq_span hJ)) x rfl hJ).trans (hω2 _ x rfl hx)
  have hnd : ∀ v : HeightOneSpectrum (𝓞 E), v ≠ P → ¬ v.asIdeal ∣ P.asIdeal := fun v hv h =>
    hv (HeightOneSpectrum.ext (P.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
  refine ⟨χ, h1, fun v hv A hA => ?_, fun v hv => h2 v (hnd v hv), fun A hA c => ?_⟩
  · have hvS := hNS v hv
    have hvP : v ≠ P := by rintro rfl; exact hP hvS
    refine dec_le_ker h1 hA (h2 v (hnd v hvP) A hA) fun σ hσ => ?_
    rw [h3 v (hnd v hvP) A hA σ hσ, ← map_one ω]
    refine hf _ 1 fun w hw => ?_
    change _ = exp (-FractionalIdeal.count E w (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E))
    rw [FractionalIdeal.count_maximal_coprime E w (by rintro rfl; exact hw hvS)]
    simp
  · obtain ⟨α, x, e, hx, rfl⟩ := hω3 c
    have hd : P.asIdeal = P.asIdeal ^ 1 * ⊤ := by simp
    obtain ⟨J, hJ⟩ := GlobalTheory.Published.exists_idealsPrimeTo_eq_span hd hx Submodule.mem_top
    exact (h4 P 1 ⊤ hd (fun h => P.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))) A hA _).2
      ⟨x, J, hx, Submodule.mem_top, hJ, hf' J.1 α x e hJ⟩

end Ray

section Host

open Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwistDet GlobalTheory.AntiRamConj

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem cConj_mem_dec {B : ValuationSubring N.Om} {σ : GE N} (hσ : σ ∈ Dec (F := D.host.E) B) :
    cConj X σ ∈ Dec (F := D.host.E) (moveVal X.cc B) := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  obtain ⟨z, rfl⟩ := (cConj X σ).surjective x
  have h1 : ((cConj X σ)⁻¹ : GE N) (cConj X σ z) = z := (cConj X σ).symm_apply_apply z
  rw [h1, mem_moveVal, mem_moveVal, cConj_apply, RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hσ]

theorem moveVal_moveVal (B : ValuationSubring N.Om) : moveVal X.cc (moveVal X.cc B) = B := by
  ext x
  rw [mem_moveVal, mem_moveVal, cc_symm, cc_symm, cc_cc]

theorem goodChar_div {i : X.Tw} {M : ℕ} {P : PlE D.host} (hP : IsSplitPl D.host P)
    {χ : GE N →* Multiplicative (ZMod (X.l i ^ M))} (h1 : IsOpen (χ.ker : Set (GE N))) (h2 : TrivAbove χ (X.l i))
    (h3 : ∀ v, v ≠ P → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, χ σ = 1)
    (h4 : ∀ A : ValuationSubring N.Om, IsPlaceOver A P → ∀ c, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = c) :
    GoodChar X i M P (χ / χ.comp (cConj X)) := by
  have hv : ∀ g, (χ / χ.comp (cConj X)) g = χ g / χ (cConj X g) := fun _ => rfl
  refine ⟨?_, fun g g' hg => ?_, fun v hv' A hA σ hσ => ?_, fun v hv' A hA σ hσ => ?_, fun v hv' A hA c => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ χ.ker.comap (cConj X)) (fun g hg => ?_)
      (h1.inter (isOpen_comap_cConj X h1))
    rw [MonoidHom.mem_ker, hv, show χ g = 1 from hg.1, show χ (cConj X g) = 1 from hg.2, div_one]
  · obtain rfl : g' = cConj X g := AlgEquiv.ext hg
    rw [hv, hv, cConj_cConj, inv_div]
  · obtain ⟨w, hw⟩ := exists_isConjPl v
    rw [hv, h2 v hv' A hA σ hσ, h2 w (mem_placesOver_conj hw hv') _ (isPlaceOver_moveVal_cc X hw hA) _
      (cConj_mem_dec X hσ), div_one]
  · obtain ⟨w, hw⟩ := exists_isConjPl v
    rw [hv, h3 v (fun e => hv' (Or.inl e)) A hA σ hσ,
      h3 w (by rintro rfl; exact hv' (Or.inr (isConjPl_symm hw))) _ (isPlaceOver_moveVal_cc X hw hA) _
        (cConj_mem_ine X hσ), div_one]
  · rcases hv' with rfl | hc
    · obtain ⟨w, hw⟩ := exists_isConjPl v
      obtain ⟨σ, hσ, e⟩ := h4 A hA c
      exact ⟨σ, hσ, by rw [hv, e, h3 w (ne_of_isSplitPl hP hw).symm _ (isPlaceOver_moveVal_cc X hw hA) _
        (cConj_mem_ine X hσ), div_one]⟩
    · obtain ⟨σ, hσ, e⟩ := h4 _ (isPlaceOver_moveVal_cc X (isConjPl_symm hc) hA) c⁻¹
      have hσ' := cConj_mem_ine X hσ
      rw [moveVal_moveVal] at hσ'
      exact ⟨_, hσ', by rw [hv, cConj_cConj, e, h3 v (ne_of_isSplitPl hP hc).symm A hA _ hσ', one_div, inv_inv]⟩

theorem not_mem_of_mem_pD (i : X.Tw) {v : PlE D.host} (hv : v ∈ X.pD i) : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
  intro hl
  have h1 : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have key : ∀ p : ℕ, p.Prime → X.l i ≠ p → v ∉ placesOver D.host.E p := fun p hp hne h => by
    have hc : IsCoprime ((X.l i : ℕ) : 𝓞 D.host.E) (p : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes Fact.out hp).2 hne)
    obtain ⟨a, b, e⟩ := hc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (e ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hl) (v.asIdeal.mul_mem_left b h)))
  split_ifs at h1 with h
  · exact key _ D.host.pde'_prime (h ▸ D.host.pde_ne) h1
  · exact key _ D.host.pde_prime h h1

theorem exists_admissible_family : GlobalTheory.Published.RayCharacterArtin → K1 X := by
  intro hArt i M hM
  have hl : (X.l i).Prime := Fact.out
  obtain ⟨H, S, h1, h2, h3, h4⟩ := exists_ray_chars D.host.E N.Om hArt (pow_ne_zero M hl.ne_zero) (X.pD i)
    fun v hv h => not_mem_of_mem_pD X i hv (v.isPrime.mem_of_pow_mem M (by simpa using h))
  have key : ∀ P : PlE D.host, ∃ d : GE N →* Multiplicative (ZMod (X.l i ^ M)),
      P ∉ S → IsSplitPl D.host P → DecV N P ≤ H → GoodChar X i M P d := fun P => by
    by_cases h : P ∉ S ∧ IsSplitPl D.host P ∧ DecV N P ≤ H
    · obtain ⟨χ, c1, c2, c3, c4⟩ := h4 P h.1 _ (N.plOm.2 P) h.2.2
      refine ⟨_, fun _ _ _ => goodChar_div X h.2.1 c1 (fun v hv => c2 v ?_) c3 c4⟩
      rw [Nat.cast_pow]
      exact v.asIdeal.pow_mem_of_mem hv M hM
    · exact ⟨1, fun a b c => absurd ⟨a, b, c⟩ h⟩
  choose d hd using key
  exact ⟨H, S, d, h1, h2, h3, hd⟩

end Host

end GlobalTheory.AdmChars

end
