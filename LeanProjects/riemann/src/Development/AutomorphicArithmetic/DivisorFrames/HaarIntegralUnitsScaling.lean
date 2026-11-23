import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

private theorem integral_smul_distribHaarChar {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [ContinuousConstSMul G A] [MeasurableSpace A] [BorelSpace A] (m : Measure A) [m.IsAddHaarMeasure]
    (g : G) (f : A → ℂ) :
    ∫ s, f (g • s) ∂m = (((distribHaarChar A g : ℝ) : ℂ))⁻¹ * ∫ s, f s ∂m := by
  have h1 := integral_domSMul (μ := m) (DomMulAct.mk g⁻¹) f
  have h2 : (DomMulAct.mk g⁻¹ • m : Measure A) = (distribHaarChar A g⁻¹) • m := by
    rw [← addHaarScalarFactor_smul_eq_distribHaarChar m]
    exact Measure.isAddLeftInvariant_eq_smul _ _
  rw [h2, integral_smul_nnreal_measure, map_inv] at h1
  simp only [Equiv.symm_apply_apply, inv_inv] at h1
  rw [← h1, NNReal.smul_def, Complex.real_smul]
  push_cast
  rfl

theorem UpperTheory.haar_integral_units_scaling :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F), ∀ [MeasurableSpace (Fv F v ⊗[F] E)] [BorelSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E)) [m.IsAddHaarMeasure],
        ∀ (u : (Fv F v ⊗[F] E)ˣ) (f : Fv F v ⊗[F] E → ℂ),
          ∫ s, f ((u : Fv F v ⊗[F] E) * s) ∂m = (((GlobalTheory.Doubling.absEv F E v u : ℝ) : ℂ))⁻¹ * ∫ s, f s ∂m := by
  intro F E _ _ _ _ _ v _ _ m _ u f
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (F := F) (E := E) v
  haveI := GlobalTheory.LocTateInt.locallyCompactSpace_Ev (F := F) (E := E) v
  haveI := GlobalTheory.LocTateInt.secondCountable_Ev (F := F) (E := E) v
  have h := integral_smul_distribHaarChar m u f
  rw [GlobalTheory.LocTateInt.distribHaarChar_Ev] at h
  rw [GlobalTheory.Doubling.absEv_apply]
  exact h
