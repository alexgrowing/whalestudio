import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfSuppAdds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLawsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraSeriesCentralIdempotentNeZeroStatement

noncomputable section

namespace GlobalTheory.SerSys.OfLabel

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem blk_eq_par {a b : ℕ} (x : Gn g a) (y : Gn g b) : blk a b (a + b) x y = par finSumFinEquiv x 0 y := by
  refine Supp.ext_entN fun i j hi hj => ?_
  rw [ParInd.blk_val, entN, dif_pos ⟨hi, hj⟩, ParInd.dg]
  dsimp only
  by_cases h1 : i < a <;> by_cases h2 : j < a
  · rw [(Supp.entN_par _ _ _ i j).1 h1 h2, if_pos ⟨h1, h2⟩]
  · rw [(Supp.entN_par _ _ _ i j).2.2.2 rfl h1 (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [(Supp.entN_par _ _ _ i j).2.1 (by omega) h2, if_neg (by omega), if_neg (by omega)]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h1)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h2)
    rw [(Supp.entN_par _ _ _ i j).2.2.1, if_neg (by omega), if_pos (by omega)]
    simp

def ofLabel (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) : Sys g where
  e := eSerC L
  idem n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).1
  central n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.1
  orth n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.1
  label n f h := by by_contra h'; exact h ((GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.2.1 f h')
  sum n := by obtain ⟨S, -, h⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.2.2; exact ⟨S, h⟩
  mul a b n hn f f' V _ _ ρ v h0 h1 h2 := by
    subst hn
    have hN : ρ.asAlgebraHom (eN g (finSumFinEquiv (m := a) (n := b))) v = v := eN_right _ ρ v fun B => by
      refine h0 _ (fun i j hj hi => ?_) ?_ ?_
      · rw [← ParInd.entN_self (par finSumFinEquiv (1 : Gn g a) B (1 : Gn g b)).val]
        exact (Supp.entN_par _ _ _ i j).2.1 hi hj
      · ext i j
        rw [tl, (Supp.entN_par _ _ _ i j).1 i.2 j.2, ParInd.entN_self]; rfl
      · ext i j
        rw [br, (Supp.entN_par _ _ _ i j).2.2.1, ParInd.entN_self]; rfl
    have hA : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (eSerC L a f)) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [blk_eq_par] at h1; exact h1
    have hB : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (eSerC L b f')) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [blk_eq_par] at h2; exact h2
    obtain ⟨S, -, hS⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG (a + b)).2.2.2.2
    have hz : ∀ F, F ≠ f * f' → ρ.asAlgebraHom (eSerC L (a + b) F) v = 0 := fun F hF => by
      have hv := ser_vanish' L h5 hG (finSumFinEquiv (m := a) (n := b)) F f f' hF
      have := congrArg (fun z => ρ.asAlgebraHom z v) hv
      simpa only [map_mul, Module.End.mul_apply, hN, hA, hB, map_zero, LinearMap.zero_apply] using this
    have e : v = ∑ F ∈ S, ρ.asAlgebraHom (eSerC L (a + b) F) v := by
      rw [← LinearMap.sum_apply, ← map_sum, hS, map_one, Module.End.one_apply]
    by_cases hm : f * f' ∈ S
    · rw [Finset.sum_eq_single_of_mem _ hm fun F _ hF => hz F hF] at e; exact e.symm
    · rw [Finset.sum_eq_zero fun F hF => hz F (by rintro rfl; exact hm hF)] at e; rw [e]; simp

end GlobalTheory.SerSys.OfLabel
