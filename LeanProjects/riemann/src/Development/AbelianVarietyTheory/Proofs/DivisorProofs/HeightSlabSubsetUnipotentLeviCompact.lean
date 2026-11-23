import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionWittFrameStabilizerStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem slab_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ b, IsFlowJ σ J X Y b → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, Real.exp (-1) ≤ h g → h g ≤ 1 → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ y ∈ C, g = u * m * y := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D b hb
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := by
    haveI := D.lat
    exact GlobalTheory.Doubling.isCompact_levelAll D.cm J L a
  refine ⟨(fun q : ℝ × GAd σ J => b q.1 * q.2) '' (Set.Icc (-1 : ℝ) 0 ×ˢ (levelAll σ J L a : Set (GAd σ J))), ?_, ?_⟩
  · exact (isCompact_Icc.prod hK).image ((hb.cont.comp continuous_fst).mul continuous_snd)
  · intro g h1 h2
    obtain ⟨p, l, hp, k, hk, rfl⟩ := D.iwa g
    rw [D.ht p l hp k hk] at h1 h2
    have hpos : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det l) := lt_of_lt_of_le (Real.exp_pos _) h1
    set t : ℝ := Real.log (absE F E (Matrix.GeneralLinearGroup.det l)) with ht
    have ht1 : -1 ≤ t := (Real.le_log_iff_exp_le hpos).2 h1
    have ht0 : t ≤ 0 := Real.log_nonpos hpos.le h2
    obtain ⟨l', hl', hal'⟩ := hb.onX (-t)
    have hs : ScalesBy σ J X (p * b (-t)) (l * l') := by
      unfold ScalesBy at *
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hl', ← Matrix.mul_assoc, hp, Matrix.mul_assoc, Units.val_mul]
    have hone : absE F E (Matrix.GeneralLinearGroup.det (l * l')) = 1 := by
      apply NNReal.coe_injective
      rw [map_mul, map_mul, NNReal.coe_mul, hal', Real.exp_neg, ht, Real.exp_log hpos, mul_inv_cancel₀ hpos.ne', NNReal.coe_one]
    obtain ⟨u, hu, m, -, e, -, -, hm⟩ := GlobalTheory.T.leviDecomposition_wittFrameStabilizer F E σ n J r X Y D.cm D.herm D.witt _ _ hs
    have h0 : b 0 = 1 := by
      have := hb.add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    refine ⟨u, hu, m, hm hone, b t * k, ⟨(t, k), ⟨⟨ht1, ht0⟩, hk⟩, rfl⟩, ?_⟩
    rw [← e, mul_assoc, ← mul_assoc (b (-t)), ← hb.add, neg_add_cancel, h0, one_mul]

end GlobalTheory.ResidueEisenstein
