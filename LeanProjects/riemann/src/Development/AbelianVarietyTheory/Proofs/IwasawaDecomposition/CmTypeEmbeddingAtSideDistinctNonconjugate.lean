import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem complexConj_eq_hostConj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem kEmbT_cmDist : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool), GlobalTheory.AlgWtF.CMDist (kEmbT D T i b) := by
  intro D T i b
  have hR : Function.Injective ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) := RingHom.injective _
  have hS : ∀ g h : D.R.GG, (∀ x : D.host.E, D.host.sigmaOf g x = D.host.sigmaOf h x) → g = h := by
    intro g h e
    exact Formalism.MainNotions.Gaps.LevGap.sigmaOf_injective D.host (AlgEquiv.ext e)
  have hk : ∀ t x, kEmbT D T i b t x =
      ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro t t' e
    apply D.eTau.injective
    apply Subtype.ext
    apply hS
    intro x
    apply hR
    rw [← hk, ← hk, e]
  · intro t t' e
    have h1 : ((D.eTau t : D.R.Psi) : D.R.GG) =
        ((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc := by
      apply hS
      intro x
      apply hR
      rw [← hk, Formalism.MainNotions.Gaps.LevGap.sigmaOf_mul, AlgEquiv.mul_apply, ← Formalism.MainNotions.Gaps.LevGap.conj_eq_sigmaOf,
        ← complexConj_eq_hostConj D x]
      exact DFunLike.congr_fun e x
    have ht : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t).2
    have ht' : ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t').2
    have h2 : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 =
        ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 * (-1) := by rw [h1]; rfl
    rw [ht, ht'] at h2
    exact absurd h2 (by decide)

end GlobalTheory.HeightCounting.FormsStep
