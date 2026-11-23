import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

open scoped GlobalTheory.GaugeEx

namespace GlobalTheory.RallisMeas

variable {D : D7}

theorem borelSpace_WO (V W : HSp D) : BorelSpace (WO V W) := ⟨rfl⟩

theorem secondCountable_WO (V W : HSp D) : SecondCountableTopology (WO V W) :=
  inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin V.rank → AE D))

theorem measurable_om_uncurry {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hw : IsWeilDatumO ψ V W χV χW om)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    Measurable (fun q : GA D W × WO V W => om (1, q.1) f q.2) := by
  have := borelSpace_WO V W
  have := secondCountable_WO V W
  have h := measurable_uncurry_of_continuous_of_measurable (ι := GA D W) (α := WO V W) (β := ℂ)
    (u := fun g w => om (1, g) f w)
    (fun w => (hw.om_cont f hf w).comp (Continuous.prodMk continuous_const continuous_id))
    (fun g => (hw.om_pres (1, g) f hf).cont.measurable)
  exact h

theorem lagTerm_stronglyMeasurable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E, StronglyMeasurable (fun p : GA D W × GA D W => lagTerm μ 𝓕 C (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
  intro D ψ V W χV χW om μ 𝓕 hw hμ f₁ f₂ hf₁ hf₂ C
  have := borelSpace_WO V W
  have := secondCountable_WO V W
  have hfin : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [hμ.2.2]; simp)
  have hsf : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  have c1 : Continuous (fun u : WO V W => ratMul C.1 u) := by unfold ratMul; fun_prop
  have c2 : Continuous (fun u : WO V W => ratMul C.2 u) := by unfold ratMul; fun_prop
  have m1 : Measurable (fun x : (GA D W × GA D W) × WO V W => om (1, x.1.1) f₁ (ratMul C.1 x.2)) :=
    (measurable_om_uncurry hw hf₁).comp (measurable_fst.fst.prodMk (c1.measurable.comp measurable_snd))
  have m2 : Measurable (fun x : (GA D W × GA D W) × WO V W => om (1, x.1.2) f₂ (ratMul C.2 x.2)) :=
    (measurable_om_uncurry hw hf₂).comp (measurable_fst.snd.prodMk (c2.measurable.comp measurable_snd))
  have hG : Measurable (fun x : (GA D W × GA D W) × WO V W =>
      om (1, x.1.1) f₁ (ratMul C.1 x.2) * star (om (1, x.1.2) f₂ (ratMul C.2 x.2))) :=
    m1.mul (continuous_star.measurable.comp m2)
  exact hG.stronglyMeasurable.integral_prod_right' (ν := μ.restrict 𝓕)

end GlobalTheory.RallisMeas

end
