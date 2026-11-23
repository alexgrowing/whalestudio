import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterConjIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemKNInvMulMemInfMapConj

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_KN_coset_reps
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)) :
    IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) →
    HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∃ r : ℕ, 0 < r ∧
      ∃ x : Fin r → GL (Fin N) k, (∀ i, x i ∈ KN k N J d hd) ∧
        ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈
          J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  intro hJo hJc hIw hpos t hdom
  have hKN : KN k N J d hd ≤ J := inf_le_left
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps (GL (Fin N) k) J
    (J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom) (KN k N J d hd) hJc
    (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen _ J hJo _) inf_le_left hKN
    (exists_mem_KN_inv_mul_mem_inf_map_conj k N h d hd J hJo hJc hIw hpos t hdom)

end GlobalTheory.CompanionTheory.Casselman
