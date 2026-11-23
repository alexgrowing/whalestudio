import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChrLocal

open scoped TensorProduct
open GlobalTheory.AdelicU

theorem map_eq_zero_of_at {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {B : Type} [CommRing B]
    [Algebra F B] {v : Pl F} {x : AE F E} (hx : At (evFin F v) x) {a : AF F}
    (ha : evFin F v a = 0) (f : AF F →ₐ[F] B) (hf : f a = 1) :
    Algebra.TensorProduct.map f (AlgHom.id F E) x = 0 := by
  have h := hx a ha
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply] at h
  have h2 := congrArg (Algebra.TensorProduct.map f (AlgHom.id F E)) h
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_zero] at h2
  simpa [hf, ← Algebra.TensorProduct.one_def] using h2

theorem eq_locIdele_splitPrime {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {v : Pl F} (τ : E →ₐ[F] Fv F v) (z : (AE F E)ˣ)
    (hz : At (evFin F v) ((z : AE F E) - 1)) (h1 : piW (τ.comp σ) (z : AE F E) = 1) :
    z = GlobalTheory.LFun.locIdele F (splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (splitPrime_under τ)).toMonoidHom (Units.map (piW τ).toMonoidHom z)) := by
  refine GlobalTheory.LFun.eq_locIdele ?_ (FiniteAdeleRing.ext _ fun u => ?_)
  · have h := map_eq_zero_of_at hz (a := ((1 : Ainf F), (0 : Af F))) (by
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 0 = 0
      exact map_zero _) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) rfl
    change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E) (z : AE F E) = 1
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  · by_cases hu : u.under (𝓞 F) = v
    · rw [GlobalTheory.LFun.finAdEquiv_apply hu]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : AE F E)) = compFin F E v (z : AE F E) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      rw [e]
      obtain ⟨τ', rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hσ (GlobalTheory.LFun.SplitChart.isSplit_of_algHom hσ τ) hu
      rw [GlobalTheory.LFun.SplitTie.toCompl_eq_complMap τ' hu]
      change _ = Neutral.B1.finiteSingle E (splitPrime τ) _ (splitPrime τ')
      rcases eq_or_eq_comp_conj hσ τ τ' with rfl | rfl
      · rw [GlobalTheory.LFun.finSingle_self]
        rfl
      · rw [GlobalTheory.LFun.finSingle_ne (splitPrime_comp_ne hσ τ)]
        change GlobalTheory.LFun.complMap hu (piW (τ.comp σ) (z : AE F E)) = 1
        rw [h1, map_one]
    · rw [GlobalTheory.LFun.finAdEquiv_apply rfl]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F (u.under (𝓞 F))) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : AE F E)) = compFin F E (u.under (𝓞 F)) (z : AE F E) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      have h := map_eq_zero_of_at hz (a := GlobalTheory.LatVac.liftV (u.under (𝓞 F)) 1) (by
        change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleFin (u.under (𝓞 F)) 1) = 0
        exact evalV_singleFin_ne (Ne.symm hu) 1) (evFin F (u.under (𝓞 F))) (GlobalTheory.LatVac.evFin_liftV _ 1)
      rw [map_sub, map_one, sub_eq_zero] at h
      have h' : compFin F E (u.under (𝓞 F)) (z : AE F E) = 1 := h
      rw [e, h', map_one]
      change (1 : u.adicCompletion E) = Neutral.B1.finiteSingle E (splitPrime τ) _ u
      exact (GlobalTheory.LFun.finSingle_ne (fun e => hu (by rw [e]; exact splitPrime_under τ)) _).symm

theorem chrW_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (v : Pl F) (τ : E →ₐ[F] Fv F v) (z : (AE F E)ˣ), At (evFin F v) ((z : AE F E) - 1) →
    piW (τ.comp σ) (z : AE F E) = 1 → chrW χ τ (Units.map (piW τ).toMonoidHom z) = Circle.toUnits (χ z) := by
  intro F E _ _ _ _ _ σ hσ χ v τ z hz h1
  change Circle.toUnits (χ (GlobalTheory.LFun.locIdele F (splitPrime τ) _)) = _
  rw [← eq_locIdele_splitPrime hσ τ z hz h1]

end GlobalTheory.ChrLocal
