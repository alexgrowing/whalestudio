import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameOfFst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SWChangeVar

theorem integral_adjO_eq : ∀ (D : D7) (V W : HSp D) (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL V W) ν 𝓖' → IsCovolOne (ratL W V) μ 𝓕 → ∀ (Φ : WO V W → ℂ), (∀ (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : WO V W), Φ (ratW W V γ + u) = Φ u) → ∫ y in 𝓖', Φ (GlobalTheory.PairLift.adjO V W y) ∂ν = ∫ u in 𝓕, Φ u ∂μ := by
  intro D V W ν 𝓖' μ 𝓕 hν hμ Φ hΦ
  haveI : BorelSpace (Mx D V.rank W.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D W.rank V.rank) := ⟨rfl⟩
  let A : Mx D V.rank W.rank ≃+ Mx D W.rank V.rank :=
    { toFun := GlobalTheory.PairLift.adjO V W
      invFun := GlobalTheory.PairLift.adjO W V
      left_inv := GlobalTheory.AdjLawPf.adj_invol W V
      right_inv := GlobalTheory.AdjLawPf.adj_invol V W
      map_add' := GlobalTheory.AdjLawPf.adj_add V W }
  let L : Mx D V.rank W.rank ≃ₜ+ Mx D W.rank V.rank :=
    { A with
      continuous_toFun := GlobalTheory.AdjLawPf.adj_cont V W
      continuous_invFun := GlobalTheory.AdjLawPf.adj_cont W V }
  let e : Mx D V.rank W.rank ≃ᵐ Mx D W.rank V.rank := L.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = GlobalTheory.PairLift.adjO V W y := fun _ => rfl
  haveI := hν.1
  have hH : (ν.map e).IsAddHaarMeasure := L.isAddHaarMeasure_map ν
  have hmp : MeasurePreserving e ν (ν.map e) := e.measurable.measurePreserving ν
  let r : ratL W V ≃ ratL V W :=
    { toFun := fun g => ⟨GlobalTheory.PairLift.adjO W V g, GlobalTheory.AdjLawPf.adj_rat_of W V g g.2⟩
      invFun := fun g => ⟨GlobalTheory.PairLift.adjO V W g, GlobalTheory.AdjLawPf.adj_rat_of V W g g.2⟩
      left_inv := fun g => Subtype.ext (GlobalTheory.AdjLawPf.adj_invol V W g)
      right_inv := fun g => Subtype.ext (GlobalTheory.AdjLawPf.adj_invol W V g) }
  have hcov : IsCovolOne (ratL W V) (ν.map e) (e '' 𝓖') := by
    refine ⟨hH, ?_, ?_⟩
    · refine hν.2.1.image_of_equiv e.toEquiv (hmp.symm e).quasiMeasurePreserving r fun g a => ?_
      show GlobalTheory.PairLift.adjO V W (GlobalTheory.PairLift.adjO W V (g : Mx D W.rank V.rank) + a) =
        (g : Mx D W.rank V.rank) + GlobalTheory.PairLift.adjO V W a
      rw [GlobalTheory.AdjLawPf.adj_add, GlobalTheory.AdjLawPf.adj_invol]
    · rw [e.map_apply, e.preimage_image]; exact hν.2.2
  have hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank V.rank, ∀ a, Φ (γ + a) = Φ a := by
    rintro _ ⟨γ, rfl⟩ a
    exact hΦ γ a
  have h := GlobalTheory.MixModel.covolOne_integral_eq (μ := μ) (μ' := ν.map e) (𝓕 := 𝓕) (𝓕' := e '' 𝓖') hμ hcov Φ hφ
  rw [setIntegral_map_equiv, e.preimage_image] at h
  exact h

end GlobalTheory.SWChangeVar

end
