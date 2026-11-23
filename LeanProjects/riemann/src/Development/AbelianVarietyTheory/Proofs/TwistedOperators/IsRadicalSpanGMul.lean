import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank
import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldMemLevelOfCoprime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesRadical

theorem isRadical_span_g_mul : ∀ (D : D7),
    (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}).IsRadical := by
  intro D
  have hrad : ∀ i : Fin 2, (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}).IsRadical := fun i =>
    GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver D.host.E (D.host.g i) (D.host.g_prime i)
      ((Formalism.MainNotions.Inhab.primesOver_ncard D.host.E (D.host.g i) (D.host.g_prime i)).trans (D.nd.g_split i))
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  have hsup : Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E)} ⊔ Ideal.span {((D.host.g 1 : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    have h1 : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
      have h2 := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 D.host.E))
      simpa using h2
    exact Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_span_singleton_iff _ _).2 h1)
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, Ideal.mul_eq_inf_of_coprime hsup]
  exact (hrad 0).inf (hrad 1)

end GlobalTheory.TypePrimesRadical
