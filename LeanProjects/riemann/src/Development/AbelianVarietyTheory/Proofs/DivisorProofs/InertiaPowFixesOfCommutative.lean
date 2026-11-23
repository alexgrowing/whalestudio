import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemPowSucc
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TameInertia

theorem eq_one_of_pow_eq_one_of_sub_mem_sq : ∀ (A B : Type) [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra A B] (Q : Ideal B) (ρ : B ≃ₐ[A] B) (m : ℕ), Q ≠ ⊤ → IsUnit (m : B) → ρ ^ m = 1 → (∀ x, ρ x - x ∈ Q) → (∀ x ∈ Q, ρ x - x ∈ Q ^ 2) → ρ = 1 := by
  first
  | exact @_root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one
  | exact _root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one
  | (apply _root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgEquivTrivialPowerCongruence.algEquiv_eq_one ..)

theorem exists_generator_mod_sq : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (Q : Ideal B) [Q.IsPrime], Q ≠ ⊥ → (∃ π ∈ Q, π ∉ Q ^ 2 ∧ ∀ x ∈ Q, ∃ c, x - c * π ∈ Q ^ 2) ∧ ∀ a b : B, a * b ∈ Q ^ 2 → a ∉ Q → b ∈ Q ^ 2 := by
  intro B _ _ Q hQ hQ0
  have hQt : Q ≠ ⊤ := Ideal.IsPrime.ne_top hQ
  have hmax : Q.IsMaximal := Ideal.IsPrime.isMaximal hQ hQ0
  refine ⟨?_, fun a b hab ha => ?_⟩
  · obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self Q hQ0 hQt 2 le_rfl)
    refine ⟨π, hπ, hπ2, fun x hx => ?_⟩
    have hlt : Q ^ (1 + 1) < Ideal.span {π} ⊔ Q ^ 2 := by
      refine lt_of_le_of_ne le_sup_right fun h => hπ2 ?_
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
    have hle : Ideal.span {π} ⊔ Q ^ 2 ≤ Q ^ 1 := by
      rw [pow_one]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hπ) (Ideal.pow_le_self two_ne_zero)
    have heq := Ideal.eq_prime_pow_of_succ_lt_of_le hQ0 hlt hle
    rw [pow_one] at heq
    rw [← heq] at hx
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact ⟨c, by simpa using hw⟩
  · have hrad : (Q ^ 2).radical = Q := by
      rw [Ideal.radical_pow Q two_ne_zero, hQ.radical]
    have hprim : (Q ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hmax)
    rcases (Ideal.isPrimary_iff.1 hprim).2 (by rw [mul_comm]; exact hab) with h | h
    · exact h
    · rw [hrad] at h
      exact absurd h ha

theorem exists_tame_scalar : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (Q : Ideal B) (π : B), π ∈ Q → (∀ x ∈ Q, ∃ c, x - c * π ∈ Q ^ 2) → ∀ ρ : B ≃ₐ[A] B, (∀ x, ρ x - x ∈ Q) → ∃ c : B, ∀ k : ℕ, ∀ x ∈ Q, (ρ ^ k) x - c ^ k * x ∈ Q ^ 2 := by
  intro A B _ _ _ Q π hπ hgen ρ hI
  have hmul : ∀ a b : B, a ∈ Q → b ∈ Q → a * b ∈ Q ^ 2 := fun a b ha hb => by
    rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  have hρQ : ∀ x ∈ Q, ρ x ∈ Q := fun x hx => by
    have := Q.add_mem (hI x) hx
    rwa [sub_add_cancel] at this
  have hρQ2 : ∀ y ∈ Q ^ 2, ρ y ∈ Q ^ 2 := fun y hy => by
    have h1 : Q.map (ρ : B →+* B) ≤ Q := Ideal.map_le_iff_le_comap.2 fun x hx => hρQ x hx
    have h2' : (Q ^ 2).map (ρ : B →+* B) ≤ Q ^ 2 := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono h1 2
    exact h2' (Ideal.mem_map_of_mem _ hy)
  obtain ⟨c, hc⟩ := hgen (ρ π) (hρQ π hπ)
  have h1 : ∀ x ∈ Q, ρ x - c * x ∈ Q ^ 2 := fun x hx => by
    obtain ⟨d, hd⟩ := hgen x hx
    set w := x - d * π with hw
    have hx' : x = d * π + w := by rw [hw]; ring
    have e : ρ x - c * x = (ρ d - d) * ρ π + d * (ρ π - c * π) + (ρ w - c * w) := by
      rw [hx', map_add, map_mul]; ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ (hmul _ _ (hI d) (hρQ π hπ)) (Ideal.mul_mem_left _ _ hc)) ?_
    exact Ideal.sub_mem _ (hρQ2 w hd) (Ideal.mul_mem_left _ _ hd)
  refine ⟨c, fun k => ?_⟩
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have e : (ρ ^ (k + 1)) x - c ^ (k + 1) * x =
        ρ ((ρ ^ k) x - c ^ k * x) + (ρ (c ^ k) - c ^ k) * ρ x + c ^ k * (ρ x - c * x) := by
      rw [pow_succ', AlgEquiv.mul_apply, map_sub, map_mul]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hρQ2 _ (ih x hx)) (hmul _ _ (hI _) (hρQ x hx)))
      (Ideal.mul_mem_left _ _ (h1 x hx))

theorem pow_card_sub_one_sub_mem_sq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (Q : Ideal B) [Q.IsPrime] (π : B), π ∈ Q → π ∉ Q ^ 2 → (∀ x ∈ Q, ∃ c, x - c * π ∈ Q ^ 2) → (∀ a b : B, a * b ∈ Q ^ 2 → a ∉ Q → b ∈ Q ^ 2) → ∀ (ρ φ : B ≃ₐ[A] B) (q : ℕ) (c : B), IsOfFinOrder ρ → IsOfFinOrder φ → ρ * φ = φ * ρ → (∀ x, φ x - x ^ q ∈ Q) → (∀ k : ℕ, ∀ x ∈ Q, (ρ ^ k) x - c ^ k * x ∈ Q ^ 2) → ∀ x ∈ Q, (ρ ^ (q - 1)) x - x ∈ Q ^ 2 := by
  intro A B _ _ _ Q hQ π hπ hπ2 hgen hprim ρ φ q c hρf hφf hcomm hφ hc
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · intro x _; simp
  have hmul : ∀ a b : B, a ∈ Q → b ∈ Q → a * b ∈ Q ^ 2 := fun a b ha hb => by
    rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  have hQ2Q : Q ^ 2 ≤ Q := Ideal.pow_le_self two_ne_zero
  have pres : ∀ α : B ≃ₐ[A] B, (∀ x ∈ Q, α x ∈ Q) → ∀ y ∈ Q ^ 2, α y ∈ Q ^ 2 := fun α hα y hy => by
    have h1 : Q.map (α : B →+* B) ≤ Q := Ideal.map_le_iff_le_comap.2 fun x hx => hα x hx
    have h2' : (Q ^ 2).map (α : B →+* B) ≤ Q ^ 2 := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono h1 2
    exact h2' (Ideal.mem_map_of_mem _ hy)
  have hfin : ∀ α : B ≃ₐ[A] B, IsOfFinOrder α → (∀ x ∈ Q, α x ∈ Q) → α π ∈ Q ^ 2 → False := by
    intro α hαf hα hαπ
    obtain ⟨n, hn, hαn⟩ := hαf.exists_pow_eq_one
    have hk : ∀ k : ℕ, ∀ y ∈ Q ^ 2, (α ^ k) y ∈ Q ^ 2 := fun k => by
      induction k with
      | zero => intro y hy; simpa using hy
      | succ k ih => intro y hy; rw [pow_succ' α k, AlgEquiv.mul_apply]; exact pres α hα _ (ih y hy)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    apply hπ2
    have := hk n' _ hαπ
    rwa [← AlgEquiv.mul_apply, ← pow_succ, hαn, AlgEquiv.one_apply] at this
  have hc1 : ∀ x ∈ Q, ρ x - c * x ∈ Q ^ 2 := fun x hx => by simpa using hc 1 x hx
  have hρQ : ∀ x ∈ Q, ρ x ∈ Q := fun x hx => by
    have := Q.add_mem (hQ2Q (hc1 x hx)) (Q.mul_mem_left c hx)
    rwa [sub_add_cancel] at this
  have hφQ : ∀ x ∈ Q, φ x ∈ Q := fun x hx => by
    have := Q.add_mem (hφ x) (Q.pow_mem_of_mem hx q hq)
    rwa [sub_add_cancel] at this
  have hcQ : c ∉ Q := fun hcQ => hfin ρ hρf hρQ (by
    have := Ideal.add_mem _ (hc1 π hπ) (hmul c π hcQ hπ)
    rwa [sub_add_cancel] at this)
  have hφπ : φ π ∉ Q ^ 2 := fun h => hfin φ hφf hφQ h
  have hd : (φ c - c) * φ π ∈ Q ^ 2 := by
    have h1 := hc1 (φ π) (hφQ π hπ)
    have h2 := pres φ hφQ _ (hc1 π hπ)
    have hcm : φ (ρ π) = ρ (φ π) := by rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, hcomm]
    have e : (φ c - c) * φ π = (ρ (φ π) - c * φ π) - (φ (ρ π - c * π)) := by
      rw [map_sub, map_mul, hcm]; ring
    rw [e]
    exact Ideal.sub_mem _ h1 h2
  have hφc : φ c - c ∈ Q := by
    by_contra h
    exact hφπ (hprim _ _ hd h)
  have hcq : c * (c ^ (q - 1) - 1) ∈ Q := by
    have e : c * (c ^ (q - 1) - 1) = (φ c - c) - (φ c - c ^ q) := by
      rw [mul_sub, _root_.mul_one, ← pow_succ', Nat.sub_add_cancel hq]; ring
    rw [e]
    exact Ideal.sub_mem _ hφc (hφ c)
  have hcq' : c ^ (q - 1) - 1 ∈ Q := (hQ.mem_or_mem hcq).resolve_left hcQ
  intro x hx
  have e : (ρ ^ (q - 1)) x - x = ((ρ ^ (q - 1)) x - c ^ (q - 1) * x) + (c ^ (q - 1) - 1) * x := by ring
  rw [e]
  exact Ideal.add_mem _ (hc (q - 1) x hx) (hmul _ _ hcq' hx)

theorem integral_mem_and_valuation_lt_one : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → (∀ x : Ω, IsIntegral R x → x ∈ V) ∧ ∀ r : R, (V.valuation (algebraMap R Ω r) < 1 ↔ r ∈ maximalIdeal R) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  have memV : ∀ a : K, algebraMap K Ω a ∈ V ↔ a ∈ (algebraMap R K).range := fun a => by
    rw [← hV]; rfl
  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := fun r => by
    rw [IsScalarTower.algebraMap_apply R K Ω]
    exact (memV _).2 ⟨r, rfl⟩
  refine ⟨fun x hx => ?_, fun r => ?_⟩
  · letI : Algebra R V := ((algebraMap R Ω).codRestrict V hRV).toAlgebra
    haveI : IsScalarTower R V Ω := .of_algebraMap_eq fun _ => rfl
    have hxV : IsIntegral V x := hx.tower_top
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hxV
    exact y.2
  · constructor
    · intro h
      by_contra hr
      have hu : IsUnit r := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hr
      obtain ⟨u, rfl⟩ := hu
      have h1 : V.valuation (algebraMap R Ω (u : R)) * V.valuation (algebraMap R Ω ((u⁻¹ : Rˣ) : R)) = 1 := by
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
      have h2 : V.valuation (algebraMap R Ω ((u⁻¹ : Rˣ) : R)) ≤ 1 := (V.valuation_le_one_iff _).2 (hRV _)
      have h3 : V.valuation (algebraMap R Ω (u : R)) * V.valuation (algebraMap R Ω ((u⁻¹ : Rˣ) : R)) < 1 :=
        mul_lt_one_of_lt_of_le h h2
      rw [h1] at h3
      exact lt_irrefl _ h3
    · intro hr
      by_contra h
      have hle : V.valuation (algebraMap R Ω r) = 1 :=
        le_antisymm ((V.valuation_le_one_iff _).2 (hRV r)) (not_lt.1 h)
      have hne : algebraMap R Ω r ≠ 0 := fun e => by rw [e, map_zero] at hle; exact zero_ne_one hle
      have hinv : (algebraMap R Ω r)⁻¹ ∈ V := by
        rw [← V.valuation_le_one_iff, map_inv₀, hle, inv_one]
      rw [IsScalarTower.algebraMap_apply R K Ω, ← map_inv₀] at hinv
      obtain ⟨s, hs⟩ := (memV _).1 hinv
      have hrK : algebraMap R K r ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply R K Ω] at hne
        exact fun e => hne (by rw [e, map_zero])
      have hrs : algebraMap R K (r * s) = algebraMap R K 1 := by
        rw [map_mul, hs, mul_inv_cancel₀ hrK, map_one]
      have := IsFractionRing.injective R K hrs
      exact (mem_maximalIdeal _ |>.1 hr) ⟨⟨r, s, this, by rw [mul_comm]; exact this⟩, rfl⟩

theorem exists_frobenius : ∀ (R B G : Type) [CommRing R] [IsLocalRing R] [Finite (ResidueField R)] [CommRing B] [Algebra R B] [Module.Finite R B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B] [Algebra.IsInvariant R B G] (Q : Ideal B) [Q.IsPrime], Q.under R = maximalIdeal R → ∃ σ : G, ∀ x : B, σ • x - x ^ Nat.card (ResidueField R) ∈ Q := by
  intro R B G _ _ _ _ _ _ _ _ _ _ _ Q _ hQ
  haveI : Q.LiesOver (maximalIdeal R) := ⟨hQ.symm⟩
  haveI : Finite (R ⧸ maximalIdeal R) := inferInstanceAs (Finite (ResidueField R))
  haveI : Module.Finite (R ⧸ maximalIdeal R) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ maximalIdeal R) (B ⧸ Q)
  haveI : Finite (B ⧸ Q) := Module.finite_of_finite (R ⧸ maximalIdeal R)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant R G Q
  refine ⟨σ, fun x => ?_⟩
  have := hσ x
  rw [hQ] at this
  exact this

theorem inertia_pow_fixes_of_commutative : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω), FiniteDimensional K L → IsGalois K L → (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) → ∀ σ ∈ inertia K V, ∃ a : ℕ, ∀ x ∈ L, (σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a)) x = x := by
  intro R K Ω _ _ _ _ _ _ _ _ _ V hV L hfin hgal hab σ hσ
  haveI := hfin
  haveI := hgal

  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R K L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R L Ω := .of_algebraMap_eq fun _ => rfl
  let B := integralClosure R L
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension R K L B
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain R K L B
  haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
  haveI : Algebra.IsInvariant R B (B ≃ₐ[R] B) := Algebra.isInvariant_of_isGalois' R K L B
  haveI : Finite (B ≃ₐ[R] B) := Finite.of_equiv _ (galRestrict R K L B).toEquiv

  obtain ⟨hint, hres⟩ := integral_mem_and_valuation_lt_one R K Ω V hV
  have hBV : ∀ b : B, algebraMap L Ω (algebraMap B L b) ∈ V := fun b =>
    hint _ ((b.2).map (IsScalarTower.toAlgHom R L Ω))
  let f : B →+* V := ((algebraMap L Ω).comp (algebraMap B L)).codRestrict V hBV
  let Q : Ideal B := (maximalIdeal V).comap f
  have hQmem : ∀ b : B, b ∈ Q ↔ V.valuation (algebraMap L Ω (algebraMap B L b)) < 1 := fun b =>
    ValuationSubring.valuation_lt_one_iff V (f b)
  haveI : Q.IsPrime := Ideal.comap_isPrime f _
  have hunder : Q.under R = maximalIdeal R := by
    ext r
    rw [Ideal.under, Ideal.mem_comap, hQmem, ← hres r, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hQ0 : Q ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    intro h
    have h1 : algebraMap R B ϖ ∈ Q := by
      change ϖ ∈ Q.under R
      rw [hunder]
      exact hϖ.not_isUnit
    rw [h, Ideal.mem_bot] at h1
    have h2 : algebraMap R L ϖ = 0 := by
      rw [IsScalarTower.algebraMap_apply R B L, h1, map_zero]
    rw [IsScalarTower.algebraMap_apply R K L, map_eq_zero] at h2
    exact hϖ.ne_zero (IsFractionRing.injective R K (h2.trans (map_zero _).symm))
  obtain ⟨φ, hφ⟩ := exists_frobenius R B (B ≃ₐ[R] B) Q hunder
  set q := Nat.card (ResidueField R) with hq
  set τ := AlgEquiv.restrictNormal σ L with hτdef
  set ρ := galRestrict R K L B τ with hρdef
  have hσ' := (mem_inertia_iff V σ).1 hσ
  have hρ : ρ ∈ Q.inertia (B ≃ₐ[R] B) := fun b => by
    show ρ • b - b ∈ Q
    rw [hQmem]
    have e : algebraMap L Ω (algebraMap B L (ρ • b - b)) =
        σ (algebraMap L Ω (algebraMap B L b)) - algebraMap L Ω (algebraMap B L b) := by
      rw [AlgEquiv.smul_def, map_sub, map_sub, algebraMap_galRestrict_apply, AlgEquiv.restrictNormal_commutes]
    rw [e]
    exact hσ'.2 _ (hBV b)
  have hcomm : ∀ α β : B ≃ₐ[R] B, α * β = β * α := fun α β => by
    obtain ⟨α', rfl⟩ := (galRestrict R K L B).surjective α
    obtain ⟨β', rfl⟩ := (galRestrict R K L B).surjective β
    rw [← map_mul, ← map_mul, hab]
  set N := orderOf ρ with hNdef
  have hN : 0 < N := orderOf_pos ρ
  set p := ringChar (ResidueField R) with hpdef
  haveI := Fintype.ofFinite (ResidueField R)
  have hp : p.Prime := CharP.char_is_prime (ResidueField R) p
  set a := N.factorization p with hadef
  set m := N / p ^ a with hmdef
  have hNm : p ^ a * m = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hN.ne'
  have hmk : (m : ResidueField R) ≠ 0 := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop ((CharP.cast_eq_zero_iff (ResidueField R) p m).1 h))
  have hmR : IsUnit (m : R) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    exact hmk
  have hmB : IsUnit (m : B) := by simpa using hmR.map (algebraMap R B)
  set ρ1 := ρ ^ (p ^ a) with hρ1
  have hρ1I : ρ1 ∈ Q.inertia (B ≃ₐ[R] B) := Subgroup.pow_mem _ hρ _
  obtain ⟨⟨π, hπQ, hπ2, hπgen⟩, hprim⟩ := exists_generator_mod_sq B Q hQ0
  obtain ⟨c, hc⟩ := exists_tame_scalar R B Q π hπQ hπgen ρ1 hρ1I
  have h2 := pow_card_sub_one_sub_mem_sq R B Q π hπQ hπ2 hπgen hprim ρ1 φ q c (isOfFinOrder_of_finite _) (isOfFinOrder_of_finite _)
    (hcomm _ _) (fun x => hφ x) hc
  have hρ2 : ρ1 ^ (q - 1) = 1 := by
    refine eq_one_of_pow_eq_one_of_sub_mem_sq R B Q (ρ1 ^ (q - 1)) m (Ideal.IsPrime.ne_top inferInstance) hmB ?_
      (Subgroup.pow_mem _ hρ1I _) h2
    rw [hρ1, ← pow_mul, ← pow_mul, show p ^ a * ((q - 1) * m) = N * (q - 1) by rw [← hNm]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  have hτn : τ ^ ((q - 1) * p ^ a) = 1 := by
    apply (galRestrict R K L B).injective
    rw [map_pow, map_one, ← hρdef, mul_comm, pow_mul]
    exact hρ2
  refine ⟨a, fun x hx => ?_⟩
  have e1 : AlgEquiv.restrictNormal (σ ^ ((q - 1) * p ^ a)) L = τ ^ ((q - 1) * p ^ a) :=
    map_pow (AlgEquiv.restrictNormalHom L) σ _
  have := AlgEquiv.restrictNormal_commutes (σ ^ ((q - 1) * p ^ a)) L ⟨x, hx⟩
  rw [e1, hτn] at this
  simpa using this.symm

end GlobalTheory.TameInertia
