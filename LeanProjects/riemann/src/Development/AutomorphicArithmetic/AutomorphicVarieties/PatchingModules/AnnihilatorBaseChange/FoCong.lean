import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.foCong :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (j N : ℕ), j ≤ N → fo W - fEl (T.Nq N) W.t.U ∈ maximalIdeal W.R ^ j ∧ m.ρ N (fEl (T.Nq N) W.t.U) = fEl (T.Nq N) (A.A N).U ∧ ∃ c : W.R, fo W - fEl (T.Nq N) W.t.U = (l : W.R) ^ j * c := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m j N hj
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI := IsCoef.char (l := l) (O := O)
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hl : (l : W.R) ∈ maximalIdeal W.R := by
    have hco := (inferInstance : IsCO O W.R).isLocalHom
    intro hu
    rw [← map_natCast (algebraMap O W.R)] at hu
    exact hlO (hco.map_nonunit _ hu)
  set I : Ideal W.R := Ideal.span {(l : W.R) ^ j} with hI
  have hq : ∀ jj, (T.Nq N jj : W.R) - 1 ∈ I := by
    intro jj
    obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp (T.Nq_mod N jj).symm
    have h3 := congrArg (Int.cast : ℤ → W.R) hk
    push_cast at h3
    rw [Ideal.mem_span_singleton]
    refine ⟨(l : W.R) ^ (N - j) * (k : W.R), ?_⟩
    rw [h3, ← pow_mul_pow_sub (l : W.R) hj, mul_assoc]
  have hq' : ∀ jj, Ideal.Quotient.mk I (T.Nq N jj : W.R) = 1 := by
    intro jj
    rw [← map_one (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq.mpr (hq jj)
  have hmod : Ideal.Quotient.mk I (fo W) = Ideal.Quotient.mk I (fEl (T.Nq N) W.t.U) := by
    simp only [fo, fEl, map_prod, map_mul, map_sub, hq', Nat.cast_one, map_one, one_mul]
  have hdiff : fo W - fEl (T.Nq N) W.t.U ∈ I := Ideal.Quotient.eq.mp hmod
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdiff
  refine ⟨?_, ?_, ⟨c, hc⟩⟩
  · rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl j)
  · obtain ⟨-, -, -, hU, -⟩ := m.ρ_maps N
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hU
    simp [fEl, map_prod, hU]
