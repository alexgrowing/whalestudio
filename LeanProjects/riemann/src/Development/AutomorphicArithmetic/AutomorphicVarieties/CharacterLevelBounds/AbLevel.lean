import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevChange

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem val_modEq {N : ℕ} [NeZero N] {x : ZMod N} {a : ℕ} (h : x = (a : ZMod N)) : x.val ≡ a [MOD N] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, h]

private theorem unitsMap_val {g N : ℕ} [NeZero g] [NeZero N] (h : g ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod g)ˣ) : ZMod g).val ≡ (u : ZMod N).val [MOD g] := by
  apply val_modEq
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val]

private theorem down (P : ℕ → Prop) (g : ℕ) [NeZero g] (hP : ∀ a b, a ≡ b [MOD g] → (P a ↔ P b))
    (K : Subgroup (ZMod g)ˣ) (hK : ∀ u, u ∈ K ↔ P (u : ZMod g).val)
    (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (h : g ∣ N)
    (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ) (hζ : IsPrimitiveRoot ζ N)
    (hj : ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔ P a)) : HasLevel E g K := by
  refine ((levChange E N).2 g h K).2 ⟨j, ζ, hζ, fun τ u hu => ?_⟩
  rw [hj τ _ hu, Subgroup.mem_comap, hK]
  exact (hP _ _ (unitsMap_val h u)).symm

private theorem exists_sub (P : ℕ → Prop) (g : ℕ) [NeZero g] (hP : ∀ a b, a ≡ b [MOD g] → (P a ↔ P b))
    (h1 : P 1) (hm : ∀ a b, P a → P b → P (a * b)) :
    ∃ K : Subgroup (ZMod g)ˣ, ∀ u, u ∈ K ↔ P (u : ZMod g).val := by
  let S : Submonoid (ZMod g)ˣ :=
    { carrier := {u | P (u : ZMod g).val}
      one_mem' := (hP _ _ (val_modEq (a := 1) (by simp))).2 h1
      mul_mem' := fun {u v} hu hv =>
        (hP _ _ (val_modEq (a := (u : ZMod g).val * (v : ZMod g).val) (by simp))).2 (hm _ _ hu hv) }
  refine ⟨{ S with inv_mem' := fun {u} hu => ?_ }, fun u => Iff.rfl⟩
  have : u⁻¹ ∈ Submonoid.powers u := mem_powers_iff_mem_zpowers.2 (inv_mem (Subgroup.mem_zpowers u))
  exact (Submonoid.powers_le (P := S)).2 hu this

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) : A.ker a ↔ A.ker b := by
  unfold AbF.ker
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h]

private theorem pm_iff (n a : ℕ) : (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) ↔ ((a : ZMod n) = 1 ∨ (a : ZMod n) = -1) := by
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [add_eq_zero_iff_eq_neg]

private theorem jac_congr {a b q : ℕ} (h : a ≡ b [MOD q]) : jacobiSym (a : ℤ) q = jacobiSym (b : ℤ) q :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.2 h)

theorem UpperTheory.V.Chr.abLevel :
    (∀ (A : AbF) (E : Type) [Field E] [NumberField E], IsAbField A E → HasLevel E A.m A.H) ∧
          ∀ (A : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E], IsCompField A e q d E → ∀ (N : ℕ) [NeZero N], 2 ^ (e + 2) ∣ N → A.m ∣ N → q ∣ N → d ∣ N →
            ∃ H : Subgroup (ZMod N)ˣ, HasLevel E N H ∧ ∀ (u : (ZMod N)ˣ) (a : ℕ), (u : ZMod N) = (a : ZMod N) →
              (u ∈ H ↔ (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧ jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1) := by
  refine ⟨?_, ?_⟩
  · rintro A E _ _ ⟨N, _, j, ζ, h, hζ, hj⟩
    refine down A.ker A.m (fun a b => ker_congr A) A.H (fun u => ?_) E N h j ζ hζ hj
    unfold AbF.ker
    rw [ZMod.natCast_zmod_val]
    exact ⟨fun hu => ⟨u, hu, rfl⟩, fun ⟨v, hv, e⟩ => Units.ext e ▸ hv⟩
  · rintro A e q d E _ _ ⟨M, _, j, ζ, a1, a2, a3, a4, hζ, hj⟩ N _ b1 b2 b3 b4
    haveI : NeZero (Nat.gcd M N) := ⟨(Nat.gcd_pos_of_pos_left _ (NeZero.pos M)).ne'⟩
    let P : ℕ → Prop := fun a => (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧
      jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1
    have hP : ∀ a b, a ≡ b [MOD Nat.gcd M N] → (P a ↔ P b) := fun a b h => by
      simp only [P]
      rw [pm_iff, pm_iff, (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.of_dvd (Nat.dvd_gcd a1 b1)),
        ker_congr A (h.of_dvd (Nat.dvd_gcd a2 b2)), jac_congr (h.of_dvd (Nat.dvd_gcd a3 b3)),
        jac_congr (h.of_dvd (Nat.dvd_gcd a4 b4))]
    have h1 : P 1 := ⟨Or.inl (Nat.ModEq.refl _), ⟨1, A.H.one_mem, by simp⟩, by simp, by simp⟩
    have hm : ∀ a b, P a → P b → P (a * b) := by
      rintro a b ⟨p1, ⟨u, hu, eu⟩, p3, p4⟩ ⟨r1, ⟨v, hv, ev⟩, r3, r4⟩
      refine ⟨?_, ⟨u * v, A.H.mul_mem hu hv, by rw [Units.val_mul, eu, ev, Nat.cast_mul]⟩, ?_, ?_⟩
      · rw [pm_iff] at p1 r1 ⊢
        rw [Nat.cast_mul]
        rcases p1 with p | p <;> rcases r1 with r | r <;> simp [p, r]
      · rw [Nat.cast_mul, jacobiSym.mul_left, p3, r3, mul_one]
      · rw [Nat.cast_mul, jacobiSym.mul_left, p4, r4, mul_one]
    obtain ⟨K, hK⟩ := exists_sub P _ hP h1 hm
    have hL := down P _ hP K hK E M (Nat.gcd_dvd_left M N) j ζ hζ hj
    refine ⟨_, ((levChange E N).2 _ (Nat.gcd_dvd_right M N) K).1 hL, fun u a hu => ?_⟩
    rw [Subgroup.mem_comap, hK]
    exact hP _ _ ((unitsMap_val _ u).trans ((val_modEq hu).of_dvd (Nat.gcd_dvd_right M N)))
