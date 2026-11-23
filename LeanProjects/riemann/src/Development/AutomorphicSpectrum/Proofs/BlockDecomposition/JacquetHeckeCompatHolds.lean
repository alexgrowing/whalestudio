import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetRepsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetSumStatement
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem jacquet_hecke_operator_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C2 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hI hpos V _ _ π hπ t ht T hT v
  obtain ⟨r, hr, x, hx, hu⟩ := GlobalTheory.T.dominant_iwahori_coset_reps k N h d hd J hJo hJc hI hpos t ht
  have key := GlobalTheory.T.hecke_operator_coset_sum k N J hJc V π hπ (leviEmb k (stdBlocks d hd) t) T hT r x hr
    (fun i => (hx i).1) hu v
  have hmk : ∀ i, (Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    intro i
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨x i, (hx i).2⟩, π (leviEmb k (stdBlocks d hd) t) (v : V), ?_⟩
    simp [map_mul]
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  have hsum : (Submodule.Quotient.mk ((T v : fixed π J) : V) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    rw [key, Submodule.Quotient.mk_smul]
    have h2 : (Submodule.Quotient.mk (∑ i, π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
        Jacquet π (unipRad k (stdBlocks d hd))) =
        ∑ i : Fin r, Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :=
      map_sum (Submodule.mkQ _) _ _
    rw [h2, Finset.sum_congr rfl fun i _ => hmk i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [hsum, jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end GlobalTheory.CompanionTheory.Lbc
