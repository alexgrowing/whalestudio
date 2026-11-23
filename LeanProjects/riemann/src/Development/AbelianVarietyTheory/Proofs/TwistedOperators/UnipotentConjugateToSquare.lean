import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVAlgebraMapMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralGeneratorSplitPlaceCmExtensionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralSiegelParabolicOfConjugateIdempoteStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitConj

theorem conj_to_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ W v, ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v, s * n * s⁻¹ = n * n := by
  intro F E _ _ _ _ _ σ B hB d W v hsplit h2 n hn
  obtain ⟨a, b, c, hq, hσa, hc, hb⟩ := GlobalTheory.T.exists_integral_generator_splitPlace_cmExtension F E σ B hB v hsplit
  obtain ⟨Eid, E1, E2, E3, E4⟩ := GlobalTheory.SplitConj.exists_adelic_idem σ W v a b c hq hσa hc hb
  obtain ⟨s, hs, hd, ha⟩ := GlobalTheory.T.exists_integralSiegelParabolic_of_conjugateIdempotent F E σ B hB d W v h2 Eid E1 E2 E3 E4
  refine ⟨s, hs, GlobalTheory.SplitConj.conj_eq_sq n hn s _ _ (GlobalTheory.LatVac.liftV v 1 - 1) ?_ ?_ hd ha⟩
  · rw [map_sub (evFin F v), GlobalTheory.LatVac.evFin_liftV, map_one (evFin F v), sub_self]
  · have h2' : (2 : AE F E) * ((⅟2 : AF F) • Eid) = Eid := by
      rw [Algebra.smul_def, ← mul_assoc, show (2 : AE F E) = algebraMap (AF F) (AE F E) 2 from (map_ofNat _ 2).symm,
        ← map_mul, mul_invOf_self, map_one, one_mul]
    rw [map_sub (algebraMap (AF F) (AE F E)), map_one (algebraMap (AF F) (AE F E)), ← E2]
    linear_combination h2'

end GlobalTheory.SplitConj
