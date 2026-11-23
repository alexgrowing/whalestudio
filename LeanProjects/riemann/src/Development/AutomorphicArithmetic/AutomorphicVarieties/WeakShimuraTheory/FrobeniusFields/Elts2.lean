import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Adj2
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PrimeEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem bar_mul {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (γ : G ℚ Ω →* c.Oˣ) (g h : G ℚ Ω) : Raw.bar γ (g * h) = Raw.bar γ g * Raw.bar γ h := by
  simp only [Raw.bar, map_mul, Units.val_mul]

private theorem move {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (X : Set2 D) (g : G ℚ Ω) (s : ℤˣ) (hk : X.κ g = 1)
    (hs : Raw.bar D.Psi g = ((s : ℤ) : ResidueField c.O)) :
    ∃ g' ∈ X.H ⊓ X.η.ker, D.Psi g' = D.Psi g ∧ D.ξ g' = D.ξ g ∧ D.om g' = D.om g := by
  obtain ⟨g', h1, h2, h3, h4, h5, h6, h7⟩ := adj2 D hD X g s 1 1
  refine ⟨g', ⟨X.mem_H.2 ⟨?_, h2.trans h3.symm, h7.trans hk⟩, h2⟩, h4, h5, h6⟩
  rw [h1, ← hs, Raw.bar, h4]

theorem UpperTheory.V.Ws.elts2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ X : Set2 D, ∃ a u t, X.Elts a u t := by
  intro Ω _ _ _ l hl c D hD X
  obtain ⟨w1, w2, -, w4, -⟩ := away D hD
  obtain ⟨j, hj⟩ := X.kap.pow
  have hodd : Odd (l ^ j) := (hl.out.odd_of_ne_two hD.l_odd).pow
  have hk : X.κ (D.cc ^ l ^ j) = 1 := by
    rw [map_pow, ← MonoidHom.pow_apply, hj, MonoidHom.one_apply]
  have hP : D.Psi (D.cc ^ l ^ j) = 1 := by rw [map_pow, hD.Psi_even, one_pow]
  obtain ⟨a, a0, a1, a2, a3⟩ := move D hD X (D.cc ^ l ^ j) 1 hk (by simp [Raw.bar, hP])
  rw [hP] at a1
  rw [map_pow, hD.xi_odd, hodd.neg_one_pow] at a2
  rw [map_pow, w4 _ hD.isCC, hodd.neg_one_pow] at a3
  have h2 := hD.pl_over 2 Nat.prime_two
  obtain ⟨u₀, hu, b1, b2, b3⟩ := X.big2 (D.pl 2) (by exact_mod_cast h2)
  have b4 := (w2 (D.pl 2) (fun h => hD.l_odd (w1 _ _ _ hl.out Nat.prime_two h h2)) u₀ hu).1
  obtain ⟨u, u0, u1, u2, u3⟩ := move D hD X u₀ 1 b2 (by simpa using b1)
  have u1' : Raw.bar D.Psi u = 1 := by rw [Raw.bar, u1]; exact b1
  have u2' : Raw.bar D.ξ u ^ 4 ≠ 1 := by rw [Raw.bar, u2]; exact b3
  rw [b4] at u3
  obtain ⟨t₀, c1, c2, c3⟩ := X.ev
  obtain ⟨t, t0, t1, -, t3⟩ := move D hD X t₀ (-1) c2 (by simpa using c3)
  have t1' : Raw.bar D.Psi t = -1 := by rw [Raw.bar, t1]; exact c3
  rw [c1] at t3
  have a1' : Raw.bar D.Psi a = 1 := by simp [Raw.bar, a1]
  have a2' : Raw.bar D.ξ a = -1 := by simp [Raw.bar, a2]
  have a3' : Raw.bar D.om a = -1 := by simp [Raw.bar, a3]
  by_cases ht : Raw.bar D.ξ t ^ 2 = 1
  · refine ⟨a, u, t * u, a0, a2', a1', a3', u0, u2', u1', u3, mul_mem t0 u0, fun h => u2' ?_, ?_, ?_⟩
    · rw [bar_mul, mul_pow, ht, one_mul] at h
      rw [show 4 = 2 * 2 from rfl, pow_mul, h, one_pow]
    · rw [bar_mul, t1', u1', mul_one]
    · rw [map_mul, t3, u3, mul_one]
  · exact ⟨a, u, t, a0, a2', a1', a3', u0, u2', u1', u3, t0, ht, t1', t3⟩
