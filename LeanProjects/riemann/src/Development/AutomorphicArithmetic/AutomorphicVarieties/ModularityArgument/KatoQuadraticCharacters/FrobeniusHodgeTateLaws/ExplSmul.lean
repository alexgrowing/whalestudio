import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames

open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem cg_mul_left {l : ℕ} [Fact l.Prime] {n : ℕ} {a b a' b' : Qbar l} (x : Qbar l) (hx : ‖x‖ ≤ 1)
    (h : Cg n a b) (ha : a' = x * a) (hb : b' = x * b) : Cg n a' b' := by
  unfold Cg at h ⊢
  rw [ha, hb, ← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans h

theorem UpperTheory.V.Z.Kato.Joint.explSmul :
    UpperTheory.V.Z.Kato.Joint.ExplSmul := by
  intro l _ Ω _ _ ι e A c Z j s u w α B cc n β t m ⟨κ, v, m₀, c₀, hκ, hv, ζ, hζ, H⟩
  have hl1 : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) l
  have hx : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl1
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  refine ⟨(l : Qbar l) ^ m * κ, v, m₀, c₀, mul_ne_zero (pow_ne_zero _ hl0) hκ, hv, ζ, hζ, fun k hk => ?_⟩
  obtain ⟨I, inst, P, o, ⟨p1, p2, p3, p4, q1, q2, q3, q4, q5⟩, hc⟩ := H k hk
  refine ⟨I, inst, P, fun i => (l : Qbar l) ^ m * o i,
    ⟨p1, p2, fun i => c.O.mul_mem (c.O.pow_mem (natCast_mem c.O l) m) (p3 i), p4, q1, q2, q3, fun i => ?_,
      fun s hs h1 h2 => ?_⟩, fun ψ hψ => ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) (q4 i)
  · obtain ⟨kk, a1, a2⟩ := q5 s hs h1 h2
    refine ⟨kk, a1, cg_mul_left _ hx a2 rfl ?_⟩
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  · refine cg_mul_left _ hx (hc ψ hψ) ?_ ?_
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold htv
      rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    · beta_reduce
      split_ifs
      · ring
      · rw [mul_zero]
