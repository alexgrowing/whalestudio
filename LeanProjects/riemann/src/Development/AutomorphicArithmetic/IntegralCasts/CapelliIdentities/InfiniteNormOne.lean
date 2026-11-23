import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsoluteValueAltAlt

theorem UpperTheory.Reformulated.B.InfiniteNormOne.infinite_norm_one :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
      {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
      {θ : NumberField.InfinitePlace F → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) E →+* ℂ}
      {ι : (NumberField.InfinitePlace F → ℂ) →+ Formalism.IndefR.DatumF.AEF F E},
      PositivityTheory.ThKW.Ctx σ B JS JT ξ₀ θ ι → {t : E | t * (σ : E → E) t = (1 : E)}.Infinite := by
  intro F E _ _ _ _ _ σ B nS nT JS JT ξ θ ι h
  obtain ⟨-, -, -, h0, hσ, -, -⟩ := h
  have hz : ∀ n : ℤ, (n : E) - ξ ≠ 0 := fun n hn => h0 <| by
    have e : ξ = (n : E) := (sub_eq_zero.mp hn).symm
    have e2 : σ ξ = ξ := by rw [e, map_intCast]
    linear_combination (1 / 2 : E) * hσ - (1 / 2 : E) * e2
  have hp : ∀ n : ℤ, (n : E) + ξ ≠ 0 := fun n hn => hz (-n) <| by
    push_cast; linear_combination -hn
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => ((n : E) + ξ) / ((n : E) - ξ))
    (fun n m hnm => ?_) (fun n => ?_)
  · have e := (div_eq_div_iff (hz n) (hz m)).mp hnm
    have e2 : ((n : E) - m) * ξ = 0 := by linear_combination (-1 / 2 : E) * e
    exact Int.cast_injective (sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right h0))
  · simp only [Set.mem_setOf_eq, map_div₀, map_add, map_sub, map_intCast, hσ, sub_neg_eq_add,
      ← sub_eq_add_neg]
    rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hz n) (hp n))]
