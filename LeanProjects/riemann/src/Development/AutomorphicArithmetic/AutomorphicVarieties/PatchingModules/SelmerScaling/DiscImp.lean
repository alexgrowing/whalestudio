import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.UrepStable
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.discImp :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Q : Ideal S.Bh, Q.IsPrime → DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Q → S.x.a = S.n ∨ ¬ ired S.U.N ≤ Q := by
  intro l _ S Q hQ hs
  rcases (UpperTheory.V.Pa.urep_stable S.U Q hQ).1 hs with ha | ⟨y, hy, z, hz, b, hb, e⟩
  · exact Or.inl ha
  · exact Or.inr fun hle => hb (hle (Ideal.subset_span ⟨y, hy, z, hz, e⟩))
