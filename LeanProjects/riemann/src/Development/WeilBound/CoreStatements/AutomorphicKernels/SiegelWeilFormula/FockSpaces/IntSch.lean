import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem intSchA {κ : Type} [Fintype κ] (m : MeasurableSpace (κ → AF F))
    (hm : m = @MeasurableSpace.pi κ _ fun _ => GroundTheory.Global.measurableSpace_adeleRing F)
    (μ : @Measure (κ → AF F) m) (hμ : @Measure.IsAddHaarMeasure _ _ _ m μ) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable φ μ := by
  subst hm
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have h := Measure.isAddLeftInvariant_eq_smul μ (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := κ))
  rw [h]
  exact (GlobalTheory.TowU.FourWeyl.integrable_schA hφ).smul_measure (by simp)

theorem measAF_eq : (measAF : MeasurableSpace (AF F)) = GroundTheory.Global.measurableSpace_adeleRing F :=
  (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm

section Cmb

variable (d : SD σ)

theorem cmb_add (c c' : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (c + c') = d.cmb c + d.cmb c' := by
  ext i j
  simp only [SD.cmb, Pi.add_apply, Matrix.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]

theorem cmb_eq (c : Fin d.m × Fin d.n × Fin 2 → AF F) (i : Fin d.m) (j : Fin d.n) :
    d.cmb c i j = ∑ k, c (i, j, k) • Algebra.TensorProduct.basis (AF F) d.bs k := by
  simp only [SD.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem crd_cmb' (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
  funext k
  obtain ⟨i, j, l⟩ := k
  simp only [SD.crd, cmb_eq]
  exact congrFun ((Algebra.TensorProduct.basis (AF F) d.bs).repr_sum_self fun k => c (i, j, k)) l

theorem cmb_crd (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  rw [cmb_eq]
  exact (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)

theorem continuous_cmb : Continuous d.cmb := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [cmb_eq]
  exact continuous_finset_sum _ fun k _ => ((continuous_apply (i, j, k)).smul continuous_const)

theorem continuous_crd : Continuous d.crd := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun k => ?_
  have hl : Continuous (((Finsupp.lapply k.2.2).comp (Algebra.TensorProduct.basis (AF F) d.bs).repr.toLinearMap :
      AE F E →ₗ[AF F] AF F)) := IsModuleTopology.continuous_of_linearMap _
  exact hl.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))

def cmbE : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ₜ+ Mx F E d.m d.n where
  toFun := d.cmb
  invFun := d.crd
  left_inv := crd_cmb' d
  right_inv := cmb_crd d
  map_add' := cmb_add d
  continuous_toFun := continuous_cmb d
  continuous_invFun := continuous_crd d

end Cmb

theorem int_schM (d : SD σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : Integrable f ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (cmbE d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (cmbE d).symm
  have h1 : Integrable (f ∘ e) (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    refine intSchA _ ?_ _ inferInstance hf'
    exact congrArg (fun m => @MeasurableSpace.pi (Fin d.m × Fin d.n × Fin 2) (fun _ => AF F) fun _ => m) measAF_eq
  have h2 := (integrable_map_equiv e f).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2

end PositivityTheory.SiegelWeilFormula.KFock

end
