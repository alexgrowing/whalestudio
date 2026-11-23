import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHermNDInvTranspose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus.RowMat

theorem map_coord_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (f : V → V) (hf : Measurable f)
    (hfH : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map f = μ) (ρ : ℕ)
    [inst : MeasurableSpace (Fin ρ → V)] [hB : BorelSpace (Fin ρ → V)]
    (lam : Measure (Fin ρ → V)) [hlam : lam.IsAddHaarMeasure] :
    lam.map (fun b i => f (b i)) = lam := by
  have e : inst = MeasurableSpace.pi :=
    hB.measurable_eq.trans (@BorelSpace.measurable_eq (Fin ρ → V) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have hp : MeasurePreserving f (Measure.addHaar : Measure V) Measure.addHaar :=
    ⟨hf, hfH _ inferInstance⟩
  rw [Measure.isAddLeftInvariant_eq_smul lam (Measure.pi fun _ : Fin ρ => (Measure.addHaar : Measure V)),
    Measure.map_smul]
  congr 1
  exact (measurePreserving_pi (fun _ : Fin ρ => (Measure.addHaar : Measure V))
    (fun _ => Measure.addHaar) (fun _ => hp)).map_eq

theorem map_mul_mt_eq : ∀ (D : D7) (S₀ : HSp D) (ρ : ℕ) (lam : Measure (Mx D ρ S₀.rank)),
    lam.IsAddHaarMeasure → ∀ h : GA D S₀,
      lam.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) = lam := by
  intro D S₀ ρ lam hlam h
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hrow := GlobalTheory.AdelicModulus.Row.map_vecMul_unitary _ _ D.sp.cm.sig hcm.1 S₀.rank S₀.gram
    (hcm.2 S₀) h
  have e : (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) =
      fun b i => Matrix.vecMul (b i) (mt S₀ h) := by
    funext b i j
    rfl
  rw [e]
  have hm : Measurable (fun x : Fin S₀.rank → AE D => Matrix.vecMul x (mt S₀ h)) :=
    (Continuous.matrix_vecMul continuous_id continuous_const).measurable
  exact map_coord_eq (V := Fin S₀.rank → AE D) (f := fun x => Matrix.vecMul x (mt S₀ h)) (hf := hm)
    (hfH := fun μ hμ => hrow μ hμ) (ρ := ρ) (inst := measMx ρ S₀.rank)
    (hB := @BorelSpace.mk _ _ (measMx ρ S₀.rank) rfl) (lam := lam) (hlam := hlam)

end GlobalTheory.AdelicModulus.RowMat
