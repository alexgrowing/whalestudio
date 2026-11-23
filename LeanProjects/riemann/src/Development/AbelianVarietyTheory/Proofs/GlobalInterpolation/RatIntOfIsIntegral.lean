import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.SplitK

theorem rat_int_of_isIntegral {E : Type} [Field E] [CharZero E] (r : ℚ) (h : IsIntegral ℤ (r : E)) :
    ∃ m : ℤ, (m : ℚ) = r := by
  have h1 : IsIntegral ℤ r :=
    (isIntegral_algHom_iff (algebraMap ℚ E).toIntAlgHom (algebraMap ℚ E).injective).1 (by simpa using h)
  simpa using IsIntegrallyClosed.isIntegral_iff.1 h1

theorem int_of_prime_mul_sq {d : ℕ} (hd : d.Prime) (c : ℚ) (k : ℤ) (h : (d : ℚ) * c ^ 2 = k) :
    ∃ n : ℤ, (n : ℚ) = c := by
  have h1 : IsIntegral ℤ (((d : ℚ) * c) ^ 2) := by
    have : ((d : ℚ) * c) ^ 2 = algebraMap ℤ ℚ (d * k) := by
      simp only [eq_intCast]; push_cast; rw [← h]; ring
    rw [this]; exact isIntegral_algebraMap
  obtain ⟨e, he⟩ := rat_int_of_isIntegral (E := ℚ) ((d : ℚ) * c)
    (by simpa using IsIntegral.of_pow two_pos h1)
  have h2 : e ^ 2 = d * k := by
    have : (e : ℚ) ^ 2 = d * k := by rw [he, ← h]; ring
    exact_mod_cast this
  obtain ⟨n, hn⟩ := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨k, h2⟩
  refine ⟨n, ?_⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  apply mul_left_cancel₀ hd0
  rw [← he, hn]; push_cast; ring

theorem jacobi_of_eq {p : ℕ} (hp : p.Prime) (d m n : ℤ) (h : m ^ 2 + d * n ^ 2 = 4 * p)
    (hm : ¬ (p : ℤ) ∣ m) : jacobiSym (-d) p = 1 := by
  have hg : m.gcd p = 1 := by
    rw [Int.gcd_comm]
    exact Int.isCoprime_iff_gcd_eq_one.1 ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hm)
  have h1 : jacobiSym (-d * n ^ 2) p = 1 := by
    rw [← jacobiSym.sq_one' hg]
    apply jacobiSym.mod_left'
    exact (Int.emod_emod_of_dvd _ (dvd_refl _)).symm.trans
      ((Int.emod_emod_of_dvd _ (dvd_refl _)).trans (Int.modEq_iff_dvd.2 ⟨4, by linear_combination h⟩))
  rw [jacobiSym.mul_left, jacobiSym.pow_left] at h1
  rcases jacobiSym.trichotomy (-d) p with h2 | h2 | h2
  · rw [h2] at h1; simp at h1
  · exact h2
  · rw [h2] at h1; nlinarith [sq_nonneg (jacobiSym n p)]

theorem mem_K {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) {x : X.E} (hx : x ∈ X.Kq) :
    s.iE x ∈ D.host.K := by
  have hall : ∀ τ τ' : D.what₂.Tau, TaylorLogMetric.embT D τ (s.iE x) = TaylorLogMetric.embT D τ' (s.iE x) := fun τ τ' => by
    have h1 := hs.1 (s.iT.symm τ) x
    have h2 := hs.1 (s.iT.symm τ') x
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, hx (s.iT.symm τ) (s.iT.symm τ')]
  let τ₀ : D.what₂.Tau := D.eTau.symm 1
  have h := GlobalTheory.InducedType.sum_eq_trace D (s.iE x)
  rw [← GlobalTheory.InducedType.restrict_K D τ₀, Finset.sum_congr rfl (fun τ _ => hall τ τ₀), Finset.sum_const,
    ← map_nsmul] at h
  have h2 := (TaylorLogMetric.embT D τ₀).injective h
  rw [nsmul_eq_mul] at h2
  have hc : (((Finset.univ : Finset D.what₂.Tau).card : ℕ) : D.host.E) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨τ₀, Finset.mem_univ _⟩).ne'
  rw [eq_div_of_mul_eq hc ((mul_comm _ _).trans h2)]
  exact div_mem (Subtype.property _) (natCast_mem _ _)

theorem splitk : ∀ (D : D7) (X : Fields) (s : Seam D X) (ϖ : 𝓞 X.E) (p : ℕ), s.Ok → (ϖ : X.E) ∈ X.Kq → (∃ κ : 𝓞 D.host.K, ((κ : D.host.K) : D.host.E) = s.iE (ϖ : X.E)) ∧ (p.Prime → p ≠ 2 → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → jacobiSym (-(D.host.d : ℤ)) p = 1) := by
  intro D X s ϖ p hs hK
  have hmem := mem_K s hs hK
  refine ⟨?_, fun hp _ hN hco => ?_⟩
  · have h1 : IsIntegral ℤ (s.iE (ϖ : X.E)) :=
      IsIntegral.map (s.iE : X.E →+* D.host.E).toIntAlgHom ϖ.isIntegral_coe
    have h2 : IsIntegral ℤ (⟨_, hmem⟩ : D.host.K) :=
      (isIntegral_algHom_iff D.host.K.val.toRingHom.toIntAlgHom D.host.K.val.toRingHom.injective).1 h1
    exact ⟨⟨_, h2⟩, rfl⟩
  · obtain ⟨a, b, hab⟩ := GlobalTheory.QuadSubfield.exists_coords D hmem
    have hc : s.iE ((X.conjO ϖ : 𝓞 X.E) : X.E) = a - b * D.host.sqrtMinusD := by
      rw [← GlobalTheory.QuadSubfield.conj_coords, ← hab, ← hs.2]; rfl
    have hsum : ((ϖ + X.conjO ϖ : 𝓞 X.E) : X.E) = ((2 * a : ℚ) : X.E) := by
      apply s.iE.injective
      rw [map_ratCast]
      push_cast
      rw [map_add, hc, hab]; ring
    obtain ⟨m, hm⟩ := rat_int_of_isIntegral (E := X.E) (2 * a) (hsum ▸ (ϖ + X.conjO ϖ).isIntegral_coe)
    have hprod : a ^ 2 + D.host.d * b ^ 2 = p := by
      have h1 := congrArg (fun z : 𝓞 X.E => s.iE (z : X.E)) hN
      push_cast at h1
      rw [map_mul, hc, hab, map_natCast] at h1
      have h2 : (a : D.host.E) ^ 2 + D.host.d * (b : D.host.E) ^ 2 = p := by
        linear_combination h1 + (b : D.host.E) ^ 2 * D.host.sqrtMinusD_sq
      exact_mod_cast h2
    obtain ⟨n, hn⟩ := int_of_prime_mul_sq D.host.hyp.2.1 (2 * b) (4 * p - m ^ 2)
      (by push_cast; rw [hm]; linear_combination 4 * hprod)
    refine jacobi_of_eq hp _ m n ?_ ?_
    · have : (m : ℚ) ^ 2 + D.host.d * (n : ℚ) ^ 2 = 4 * p := by
        rw [hm, hn]; linear_combination 4 * hprod
      exact_mod_cast this
    · rintro ⟨t, ht⟩
      have h1 : ϖ + X.conjO ϖ = (p : 𝓞 X.E) * (t : 𝓞 X.E) := by
        apply RingOfIntegers.ext
        rw [hsum, ← hm, ht]
        simp
      rw [← hN] at h1
      have u1 : IsUnit ϖ := hco.isUnit_of_dvd' dvd_rfl ⟨X.conjO ϖ * t - 1, by linear_combination h1⟩
      have u2 : IsUnit (X.conjO ϖ) := u1.map _
      have u3 : IsUnit (algebraMap ℤ (𝓞 X.E) (p : ℤ)) := by
        simpa [hN] using u1.mul u2
      have := Algebra.IsIntegral.isLocalHom ℤ (𝓞 X.E)
      exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_map_unit _ _ u3)

end GlobalTheory.MomT.SplitK
