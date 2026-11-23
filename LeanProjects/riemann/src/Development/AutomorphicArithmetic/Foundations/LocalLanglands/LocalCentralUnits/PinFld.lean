import Mathlib
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PinChar
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PinNum

open Finset

namespace UpperTheory.Zero.LLC.CharacterSumPairs

theorem exists_gen_char {G : Type} [CommGroup G] [Fintype G] [IsCyclic G] : ∃ η₀ : G →* ℂˣ,
    (∀ χ : G →* ℂˣ, ∃ t < Fintype.card G, χ = η₀ ^ t) ∧
    ∀ u v : ℕ, η₀ ^ u = η₀ ^ v ↔ u % Fintype.card G = v % Fintype.card G := by
  classical
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := G)
  have hN : 0 < Fintype.card G := Fintype.card_pos
  haveI : NeZero (Fintype.card G) := ⟨hN.ne'⟩
  have hox : orderOf x = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_eq_fintype_card]
  have hζ := Complex.isPrimitiveRoot_exp (Fintype.card G) hN.ne'
  let ζu : ℂˣ := (hζ.isUnit hN.ne').unit
  have hζu : IsPrimitiveRoot ζu (Fintype.card G) := hζ.isUnit_unit hN.ne'
  have hoζ : orderOf ζu = Fintype.card G := hζu.eq_orderOf.symm
  let η₀ : G →* ℂˣ := monoidHomOfForallMemZpowers hx (g' := ζu) (by rw [hoζ, hox])
  have hη : η₀ x = ζu := monoidHomOfForallMemZpowers_apply_gen hx _
  refine ⟨η₀, fun χ => ?_, fun u v => ?_⟩
  · have h1 : ((χ x : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hox, pow_orderOf_eq_one, map_one, Units.val_one]
    obtain ⟨t, ht, hteq⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨t, ht, ?_⟩
    rw [MonoidHom.eq_iff_eq_on_generator hx, MonoidHom.pow_apply, hη]
    ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hteq]
  · rw [MonoidHom.eq_iff_eq_on_generator hx, MonoidHom.pow_apply, MonoidHom.pow_apply, hη,
      pow_eq_pow_iff_modEq, hoζ]
    all_goals exact Iff.rfl

section Fld

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

theorem fin_of (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) : Finite K := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (by rw [hr]; exact hn)
  exact Module.finite_of_finite (ZMod g)

theorem natCard_K (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) : Nat.card K = g ^ n := by
  haveI := fin_of hn hr
  letI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hr]

theorem pow_iter {z : K} {d : ℕ} (h : z ^ g ^ d = z) (k : ℕ) : z ^ g ^ (d * k) = z := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem pow_of_deg (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (z : K)
    (hd : (minpoly (ZMod g) z).natDegree ≠ n) : ∃ p ∈ n.primeFactors, z ^ g ^ (n / p) = z := by
  haveI : FiniteDimensional (ZMod g) K := Module.finite_of_finrank_pos (by rw [hr]; exact hn)
  have hint : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  set d := (minpoly (ZMod g) z).natDegree with hd_def
  have hdpos : 0 < d := minpoly.natDegree_pos hint
  have hzd : z ^ g ^ d = z := by
    set F := IntermediateField.adjoin (ZMod g) {z}
    have hF : Module.finrank (ZMod g) F = d := IntermediateField.adjoin.finrank hint
    haveI := fin_of hdpos hF
    letI := Fintype.ofFinite F
    have hc : Fintype.card F = g ^ d := by
      rw [← Nat.card_eq_fintype_card]
      exact natCard_K hdpos hF
    have := FiniteField.pow_card (⟨z, IntermediateField.mem_adjoin_simple_self (ZMod g) z⟩ : F)
    rw [hc] at this
    simpa using congrArg Subtype.val this
  have hdvd : d ∣ n := hr ▸ minpoly.degree_dvd hint
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hd (by rw [hk, mul_one])
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
  refine ⟨p, Nat.mem_primeFactors.2 ⟨hp, by rw [hk]; exact dvd_mul_of_dvd_right hpk d, hn.ne'⟩, ?_⟩
  rw [hk, Nat.mul_div_assoc d hpk]
  exact pow_iter hzd (k / p)

theorem unit_frob (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (z : Kˣ) : z ^ g ^ n = z := by
  haveI := fin_of hn hr
  letI := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_K hn hr
  ext
  push_cast
  rw [← hc, FiniteField.pow_card]

theorem char_frob (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) :
    θ ^ g ^ n = θ := by
  refine MonoidHom.ext (fun z => ?_)
  rw [MonoidHom.pow_apply, ← map_pow, unit_frob hn hr]

theorem exists_D [Fintype Kˣ] (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) :
    ∃ D : Finset Kˣ, (∀ z : Kˣ, z ∉ D → (minpoly (ZMod g) (z : K)).natDegree = n) ∧
      (∀ z ∈ D, ∃ p ∈ n.primeFactors, z ^ (g ^ (n / p) - 1) = 1) ∧ #D ≤ bd g n := by
  classical
  have key : ∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree ≠ n →
      ∃ p ∈ n.primeFactors, z ^ (g ^ (n / p) - 1) = 1 := by
    intro z hz
    obtain ⟨p, hp, hpz⟩ := pow_of_deg hn hr (z : K) hz
    refine ⟨p, hp, ?_⟩
    have hpos : 1 ≤ g ^ (n / p) := Nat.one_le_pow _ _ (Fact.out : g.Prime).pos
    have h2 : z ^ (g ^ (n / p) - 1) * z = 1 * z := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, one_mul]
      ext
      push_cast
      exact hpz
    exact mul_right_cancel h2
  refine ⟨Finset.univ.filter (fun z : Kˣ => (minpoly (ZMod g) (z : K)).natDegree ≠ n), ?_, ?_, ?_⟩
  · intro z hz
    by_contra h
    exact hz (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  · intro z hz
    exact key z (Finset.mem_filter.1 hz).2
  · calc #(Finset.univ.filter (fun z : Kˣ => (minpoly (ZMod g) (z : K)).natDegree ≠ n))
        ≤ #(n.primeFactors.biUnion
            (fun p => Finset.univ.filter (fun z : Kˣ => z ^ (g ^ (n / p) - 1) = 1))) := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨p, hp, hpz⟩ := key z (Finset.mem_filter.1 hz).2
          exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpz⟩⟩
      _ ≤ ∑ p ∈ n.primeFactors, #(Finset.univ.filter (fun z : Kˣ => z ^ (g ^ (n / p) - 1) = 1)) :=
          Finset.card_biUnion_le
      _ ≤ bd g n := by
          unfold bd
          refine Finset.sum_le_sum fun p hp => ?_
          have hpp := Nat.mem_primeFactors.1 hp
          have hle : p ≤ n := Nat.le_of_dvd hn hpp.2.1
          have hq : 0 < n / p := Nat.div_pos hle hpp.1.pos
          have hg2 : 1 < g ^ (n / p) := Nat.one_lt_pow hq.ne' (Fact.out : g.Prime).one_lt
          exact IsCyclic.card_pow_eq_one_le (by omega)

end Fld

open Classical in

noncomputable def cj {G : Type} [CommGroup G] (g n : ℕ) (θ : G →* ℂˣ) : Finset (G →* ℂˣ) :=
  (range n).image (fun j => θ ^ g ^ j)

theorem mem_cj {G : Type} [CommGroup G] {g n : ℕ} {θ χ : G →* ℂˣ} :
    χ ∈ cj g n θ ↔ ∃ j < n, θ ^ g ^ j = χ := by
  simp [cj]

theorem card_cj {G : Type} [CommGroup G] {g n : ℕ} {θ : G →* ℂˣ}
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j) : #(cj g n θ) = n := by
  classical
  unfold cj
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact hθ i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij

theorem sum_cj {G : Type} [CommGroup G] {g n : ℕ} {θ : G →* ℂˣ}
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j) (z : G) :
    ∑ χ ∈ cj g n θ, ((χ z : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) := by
  classical
  unfold cj
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [MonoidHom.pow_apply, map_pow]
  · intro i hi j hj hij
    exact hθ i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij

section Fld2

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem char_pow_pow_mul_eq_self_of_finrank (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n)
    (ψ : Kˣ →* ℂˣ) (m : ℕ) : ψ ^ g ^ (n * m) = ψ := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, char_frob hn hr]

theorem disj_cj (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (θ θ' : Kˣ →* ℂˣ)
    (hno : ¬ ∃ j < n, θ' = θ ^ g ^ j) : Disjoint (cj g n θ) (cj g n θ') := by
  rw [Finset.disjoint_left]
  intro χ h1 h2
  obtain ⟨i, hi, rfl⟩ := mem_cj.1 h1
  obtain ⟨j, hj, hj'⟩ := mem_cj.1 h2
  apply hno
  have e1 : θ' = θ ^ g ^ (i + (n - j)) := by
    calc θ' = θ' ^ g ^ n := (char_frob hn hr θ').symm
      _ = (θ' ^ g ^ j) ^ g ^ (n - j) := by
        rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hj.le]
      _ = θ ^ g ^ (i + (n - j)) := by rw [hj', ← pow_mul, ← pow_add]
  refine ⟨(i + (n - j)) % n, Nat.mod_lt _ hn, ?_⟩
  rw [e1]
  conv_lhs => rw [← Nat.mod_add_div (i + (n - j)) n]
  rw [pow_add, pow_mul, char_pow_pow_mul_eq_self_of_finrank hn hr]

end Fld2

end UpperTheory.Zero.LLC.CharacterSumPairs
