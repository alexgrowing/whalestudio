import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.FiniteSubfamilySpansDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearvec
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cardsub

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.nearvx :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (A : Matrix (Fin N) (Fin N) (𝓞 L)), A.det ≠ 0 →
    (nearVx A).Finite ∧ (nearVx A).ncard ≤ ((2 * RR L N + 1) ^ dd L N + 1) ^ (dd L N * N) := by
  intro L _ _ _ N A hA
  choose f hf1 hf2 hf3 using vxdet L N
  obtain ⟨hfin, hcard⟩ := nearvec L N A hA
  obtain ⟨h1, h2⟩ := cardsub (Lat L N) (nearVec A) (dd L N * N) hfin
  have hinj : Function.Injective f := fun v w e =>
    Subtype.ext (hf3 w v.1 (fun y hy => hf2 v y (e ▸ hy)))
  have hmap : ∀ v ∈ nearVx A, f v ∈
      {M : Finset (Lat L N) | (↑M : Set (Lat L N)) ⊆ nearVec A ∧ M.card ≤ dd L N * N} := by
    intro v hv
    refine ⟨fun y hy => ⟨v.1, ?_, hv, hf2 v y hy⟩, hf1 v⟩
    have := v.2.1
    rwa [poly_qc] at this
  refine ⟨Set.Finite.of_injOn hmap hinj.injOn h1, ?_⟩
  refine (Set.ncard_le_ncard_of_injOn f hmap hinj.injOn h1).trans (h2.trans ?_)
  exact Nat.pow_le_pow_left (Nat.succ_le_succ hcard) _
