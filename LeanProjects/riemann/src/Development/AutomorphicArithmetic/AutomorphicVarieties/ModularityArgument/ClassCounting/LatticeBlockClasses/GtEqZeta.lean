import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlock

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

section

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]

private theorem gtEq_ord {l c ν : ℕ} [hl : Fact l.Prime] {ζ : (𝓞 F)ˣ} {γ : F ≃ₐ[L] F} (h : Lay l c ν ζ γ) {i i' : ℕ}
    (e : (1 + (l : ZMod (l ^ ν)) ^ c) ^ i = (1 + (l : ZMod (l ^ ν)) ^ c) ^ i') : γ ^ i = γ ^ i' := by
  obtain ⟨n, rfl⟩ : ∃ n, ν = n + c := ⟨ν - c, by have := h.c_le; omega⟩
  have h2 := hl.out.two_le
  have hc := h.c_pos
  have hpm : c + 2 ≤ l * c := by
    rcases h2.eq_or_lt with h3 | h3
    · have := h.c_two h3.symm
      rw [← h3]; omega
    · nlinarith
  have ho := ZMod.orderOf_one_add_mul_prime_pow hl.out c (by omega) hpm 1
    (by exact_mod_cast hl.out.not_dvd_one) n
  simp only [Int.cast_one, mul_one] at ho
  have hf : IsOfFinOrder (1 + (l : ZMod (l ^ (n + c))) ^ c) := by
    rw [← orderOf_pos_iff, ho]; positivity
  rw [hf.pow_eq_pow_iff_modEq, ho] at e
  rw [pow_eq_pow_iff_modEq, h.ord, Nat.add_sub_cancel]
  exact e

private theorem gtEq_zeta {l c ν : ℕ} {ζ : (𝓞 F)ˣ} {γ : F ≃ₐ[L] F} (h : Lay l c ν ζ γ) (i : ℕ) :
    (γ ^ i) ((ζ : 𝓞 F) : F) = ((ζ : 𝓞 F) : F) ^ ((1 + l ^ c) ^ i) := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h.act, ← pow_mul, ← pow_succ']

private theorem gtEq_act {l c ν : ℕ} [hl : Fact l.Prime] {ζ : (𝓞 F)ˣ} {γ : F ≃ₐ[L] F} (h : Lay l c ν ζ γ) (i : ℕ) :
    actU (γ ^ i)⁻¹ (toF ζ) ^ ((1 + (l : ZMod (l ^ ν)) ^ c) ^ i).val = toF ζ ^ (1 : ZMod (l ^ ν)).val := by
  have hq : toF ζ ^ (l ^ ν) = 1 := toF_pow h.prim.pow_eq_one
  have h1 : ∀ n : ℕ, toF ζ ^ ((n : ZMod (l ^ ν))).val = toF ζ ^ n := fun n => by
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hq]
  have h2 := h1 1
  have h3 := h1 ((1 + l ^ c) ^ i)
  push_cast at h2 h3
  rw [h2, ← map_pow, h3, pow_one]
  apply Units.ext
  change (γ ^ i)⁻¹ ((toF ζ ^ (1 + l ^ c) ^ i : Fˣ) : F) = _
  rw [Units.val_pow_eq_pow_val]
  change (γ ^ i)⁻¹ (((ζ : 𝓞 F) : F) ^ _) = ((ζ : 𝓞 F) : F)
  rw [← gtEq_zeta h i]
  exact (γ ^ i).symm_apply_apply _

end

theorem UpperTheory.V.ZK.Cl.cGtEq :
    UpperTheory.V.ZK.Cl.CGtEq := by
  classical
  intro hS L F _ _ _ _ _ J _ l c ν M _ ζ γ h χ η 𝔡 p β hj hη hβ
  obtain ⟨T, B, hT, hB, hTB⟩ : ∃ (T : ZMod (l ^ ν) → F ≃ₐ[L] F) (B : ZMod (l ^ ν) → ZMod (l ^ ν)),
      (∀ i, T ((1 + (l : ZMod (l ^ ν)) ^ c) ^ i) = γ ^ i) ∧ (∀ i, B ((1 + (l : ZMod (l ^ ν)) ^ c) ^ i) = 1) ∧
      ∀ x, actU (T x)⁻¹ (toF ζ) ^ x.val = toF ζ ^ (B x).val := by
    refine ⟨fun x => if e : ∃ i, (1 + (l : ZMod (l ^ ν)) ^ c) ^ i = x then γ ^ e.choose else 1,
      fun x => if ∃ i, (1 + (l : ZMod (l ^ ν)) ^ c) ^ i = x then 1 else x, fun i => ?_, fun i => ?_, fun x => ?_⟩
    · have e : ∃ i', (1 + (l : ZMod (l ^ ν)) ^ c) ^ i' = (1 + (l : ZMod (l ^ ν)) ^ c) ^ i := ⟨i, rfl⟩
      simp only [dif_pos e]
      exact gtEq_ord h e.choose_spec
    · exact if_pos ⟨i, rfl⟩
    · by_cases e : ∃ i, (1 + (l : ZMod (l ^ ν)) ^ c) ^ i = x
      · simp only [dif_pos e, if_pos e]
        have := gtEq_act h e.choose
        rwa [e.choose_spec] at this
      · simp only [dif_neg e, if_neg e, inv_one]
        rfl
  obtain ⟨-, hmul, hone, -, -, hadd, -⟩ := cAct L F
  let 𝔠 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ := fun j => η j • Finsupp.equivMapDomain
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv (T (χ j)).toRingEquiv)).symm 𝔡
  have h𝔠 : ∀ j P, 𝔠 j P = η j * 𝔡 (actP (T (χ j)) P) := fun j P => rfl
  have hsum : ∀ x P, ∑ j : {j // B (χ j) = x}, 𝔠 j.1 P =
      ordP P (if x = 1 then β else 1) := by
    intro x P
    have e := congrArg (Finsupp.linearCombination ℤ fun y => if B y = x then 𝔡 (actP (T y) P) else 0) hη
    rw [Finsupp.linearCombination_mapDomain, map_sum, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (by simp)] at e
    simp only [Finsupp.linearCombination_single, hT, hB, smul_eq_mul, Function.comp, mul_ite, mul_zero] at e
    rw [← Finset.sum_filter] at e
    rw [← Finset.sum_subtype (Finset.univ.filter fun j => B (χ j) = x) (by simp) (fun j => 𝔠 j P)]
    simp only [h𝔠]
    rw [e]
    by_cases hx : x = 1
    · simp [hx, hβ]
    · have h0 : ordP P (1 : Fˣ) = 0 := by simp [ordP]
      simp [hx, Ne.symm hx, h0]
  have hex : ∀ x, ∃ g : ({j // B (χ j) = x} → F) ≃ₗ[F] ({j // B (χ j) = x} → F),
      LinearEquiv.det g = (if x = 1 then β else 1) ∧
        ∀ w, InLat 0 w ↔ InLat (fun i : {j // B (χ j) = x} => 𝔠 i.1) (g w) := by
    intro x
    refine hS F {j // B (χ j) = x} 0 (fun i => 𝔠 i.1) _ ?_ fun P => ?_
    · by_cases hx : x = 1
      · obtain ⟨j, hj⟩ := hj
        exact Or.inl ⟨⟨j, by rw [hj, hx]; simpa using hB 0⟩⟩
      · exact Or.inr (if_neg hx)
    · simp [hsum]
  choose g' hdet hlat using hex
  obtain ⟨⟨g, hg⟩, hall⟩ := cBlock L F J _ (fun j => (T (χ j))⁻¹) (fun j => B (χ j)) g'
  refine ⟨g, (hall g hg).2.2 _ 𝔠 (fun j P => ?_) hlat, _, _, g', hg, fun j => hTB _, hdet⟩
  rw [h𝔠, ← hmul, mul_inv_cancel, hone]
  rfl
