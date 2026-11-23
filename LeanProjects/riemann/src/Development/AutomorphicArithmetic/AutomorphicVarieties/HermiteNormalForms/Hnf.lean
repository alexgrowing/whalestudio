import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnfone

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.hnf :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (J : ℕ),
    ∃ S : Finset (Matrix (Fin N) (Fin N) (𝓞 L)), S.card ≤ J ^ (1 + dd L N * N) ∧ ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → nrmDet A ≤ J →
      ∃ g : Gm L N, (g : Matrix (Fin N) (Fin N) (𝓞 L)) * A ∈ S := by
  intro L _ _ N J
  classical
  have hpos : ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → 0 < nrmDet A := by
    intro A hA
    unfold nrmDet
    exact Int.natAbs_pos.mpr ((Algebra.norm_ne_zero_iff (R := ℤ)).mpr hA)
  have hex : ∀ I : ℕ, ∃ S : Finset (Matrix (Fin N) (Fin N) (𝓞 L)), S.card ≤ I ^ (dd L N * N) ∧
      ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → nrmDet A = I →
        ∃ g : Gm L N, (g : Matrix (Fin N) (Fin N) (𝓞 L)) * A ∈ S := by
    intro I
    rcases Nat.eq_zero_or_pos I with rfl | hI
    · refine ⟨∅, by simp, ?_⟩
      intro A hA hn
      exact absurd hn (hpos A hA).ne'
    · exact hnfone L N I hI
  choose S hScard hS using hex
  refine ⟨(Finset.Icc 1 J).biUnion S, ?_, ?_⟩
  · calc ((Finset.Icc 1 J).biUnion S).card
        ≤ ∑ I ∈ Finset.Icc 1 J, (S I).card := Finset.card_biUnion_le
      _ ≤ ∑ I ∈ Finset.Icc 1 J, J ^ (dd L N * N) := by
        apply Finset.sum_le_sum
        intro I hI
        exact (hScard I).trans (Nat.pow_le_pow_left (Finset.mem_Icc.mp hI).2 _)
      _ = J ^ (1 + dd L N * N) := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, pow_add, pow_one]
        simp
  · intro A hA hJ
    obtain ⟨g, hg⟩ := hS (nrmDet A) A hA rfl
    refine ⟨g, Finset.mem_biUnion.mpr ⟨nrmDet A, ?_, hg⟩⟩
    exact Finset.mem_Icc.mpr ⟨hpos A hA, hJ⟩
