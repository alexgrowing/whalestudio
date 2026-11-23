import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef

open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
attribute [local instance] Formalism.L2.Theta.IsVolMeasG._proof_2 Formalism.L2.Theta.IsVolMeasG._proof_1 Formalism.L2.Theta.IsDsig._proof_2 Formalism.L2.Theta.IsVolMeasG._proof_3

theorem UpperTheory.Reformulated.B.DecompositionAlmostEverywhere.decomp_AE :
    ∀ {D : Formalism.BasicNotions.D7},
    (↥D.host.F)[D.host.sqrtMinusD] = ⊤ →
      ∀ (z : Formalism.L2.Theta.AE D),
        ∃ (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) (q : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F),
          z =
            (Algebra.algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) (Formalism.L2.Theta.AE D) :
                  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F → Formalism.L2.Theta.AE D)
                p +
              (Algebra.algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) (Formalism.L2.Theta.AE D) :
                    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F → Formalism.L2.Theta.AE D)
                  q *
                (Formalism.L2.Theta.incA D : D.host.E → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) D.host.E)
                  D.host.sqrtMinusD := by
  intro D h z
  have hz : z ∈ Algebra.adjoin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) {Formalism.L2.Theta.incA D D.host.sqrtMinusD} := by
    have := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) _ h
    exact (Set.image_singleton ▸ this).ge Algebra.mem_top
  have hs : Formalism.L2.Theta.incA D D.host.sqrtMinusD ^ 2 = -(D.host.d : Formalism.L2.Theta.AE D) := by
    rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD, D.host.sqd_sq, map_neg, map_natCast]
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by rw [map_zero, map_one, zero_add, one_mul]; exact hx⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy => obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hy; exact ⟨a + c, b + e, by rw [map_add, map_add]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hy
    exact ⟨a * c - D.host.d * (b * e), a * e + b * c, by
      simp only [map_add, map_sub, map_mul, map_natCast]; linear_combination (algebraMap _ _ b * algebraMap _ _ e) * hs⟩
