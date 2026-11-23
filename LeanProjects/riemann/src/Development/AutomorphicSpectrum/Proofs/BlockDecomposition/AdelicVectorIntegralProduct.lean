import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff.Split

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def rowEquiv (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ) :
    (Fin k → InfiniteAdeleRing E) ≃ᵐ (Fin k → Cinf E) :=
  MeasurableEquiv.piCongrRight fun _ =>
    { toEquiv := (infEq E).symm.toEquiv
      measurable_toFun := (GlobalTheory.CuspRep.GASplit.continuous_infEq_symm E).measurable
      measurable_invFun := (continuous_infEq E).measurable }

theorem nuInf_eq (k : ℕ) :
    nuInf E k = (Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).map (rowEquiv E k) := rfl

theorem integral_split {k : ℕ} (A : (Fin k → Cinf E) → ℂ) (B : (Fin k → Af E) → ℂ) :
    ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) =
      (∫ x, A x ∂nuInf E k) * ∫ f, B f ∂nuFin E k := by
  have hmp := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)
    (fun _ => GroundTheory.Global.infiniteAdeleMeasure E) (fun _ => GroundTheory.Global.finiteAdeleMeasure E)
  haveI : SFinite (nuFin E k) := by unfold nuFin; infer_instance
  have e : (fun y : Fin k → Ad E => A (fun i => pInf E (y i)) * B (fun i => pFin E (y i))) =
      fun x => (A ∘ rowEquiv E k) ((MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)) x).1 *
        B ((MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)) x).2 := by
    funext y
    rfl
  have h1 : ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) =
      ∫ z, (A ∘ rowEquiv E k) z.1 * B z.2 ∂((Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).prod
        (nuFin E k)) := by
    rw [e]
    exact (hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun z => (A ∘ rowEquiv E k) z.1 * B z.2))
  rw [h1, integral_prod_mul, nuInf_eq, integral_map_equiv]
  rfl

end GlobalTheory.CompanionTheory.CutOff.Split
