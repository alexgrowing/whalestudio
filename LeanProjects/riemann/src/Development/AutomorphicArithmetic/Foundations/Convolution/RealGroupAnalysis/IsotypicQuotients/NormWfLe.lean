import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
import GroundTheory.AutomorphicForms.FourierWhittaker

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

namespace UpperTheory.ConvolutionTheory.R2.Pp

variable {F : Type} [Field F] [NumberField F]

theorem vn (q : A F) : (nU q).val = !![1, q; 0, 1] := rfl

theorem n_add (x y : A F) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem n_zero : gl (nU (0 : A F)) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn]

theorem cont_n : Continuous fun q : A F => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A F, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

theorem rat_n (k : F) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

theorem rat_a (t : Fˣ) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = aE (IdeleGroup.diagonal F t) := by
  refine ⟨⟨!![(t : F), 0; 0, 1], !![((t⁻¹ : Fˣ) : F), 0; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![(t : F), 0; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE]

theorem a_n (t : (A F)ˣ) (b : A F) : aE t * gl (nU b) = gl (nU ((t : A F) * b)) * aE t := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, aE, Matrix.mul_apply, Fin.sum_univ_two]

theorem ψ_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

theorem ψ_rt (k : F) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

theorem norm_ψ (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _

theorem cont_ψ : Continuous (ψ (F := F)) := continuous_subtype_val.comp continuous_adelicChar

theorem exists_cpt : ∃ C : Set (A F), IsCompact C ∧ fundamentalSet F ⊆ C :=
  ⟨_, (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F),
    fun _ hx => ⟨subset_closure hx.1, hx.2⟩⟩

theorem int_one {ι : Type} [Fintype ι] [Unique ι] (h : A F → ℂ) :
    ∫ x in vecDomain F ι, h (x default) ∂(vecMeasure F ι) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  have hp := measurePreserving_funUnique (adeleMeasure F) ι
  have e : vecDomain F ι = MeasurableEquiv.funUnique ι (A F) ⁻¹' fundamentalSet F := by
    ext x
    exact ⟨fun hx => hx default trivial, fun hx i _ => by rw [Unique.eq_default i]; exact hx⟩
  rw [e]
  convert hp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) h (fundamentalSet F) using 2
  all_goals first | rfl | congr!

theorem int_add {h : A F → ℂ} (hh : ∀ k x, h (rt k + x) = h x) (a : A F) :
    ∫ b in fundamentalSet F, h (b + a) ∂(adeleMeasure F) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  rw [← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h]
  refine setIntegral_comp_add (fun _ => a) (h := fun x => h (x default)) fun ξ hξ x => ?_
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
  exact hh _ _

theorem int_mul {h : A F → ℂ} (hh : ∀ k x, h (rt k + x) = h x) (t : Fˣ) :
    ∫ b in fundamentalSet F, h (rt (t : F) * b) ∂(adeleMeasure F) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  rw [← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h,
    ← setIntegral_comp_matVec (Matrix.GeneralLinearGroup.scalar (Fin 1) t) (f := fun x => h (x default)) fun ξ hξ x => by
      obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      exact hh _ _]
  simp [matVec_apply]

theorem Lf.per {f : GL (Fin 2) (A F) → ℂ} (hf : Lf f) (k : F) (x : A F) (g : GL (Fin 2) (A F)) :
    f (gl (nU (rt k + x)) * g) = f (gl (nU x) * g) := by
  obtain ⟨γ, hγ⟩ := rat_n k
  rw [n_add, ← hγ, mul_assoc, hf.2]

theorem intOn {h : A F → ℂ} (hc : Continuous h) : IntegrableOn h (fundamentalSet F) (adeleMeasure F) := by
  obtain ⟨C, hC, hs⟩ := exists_cpt (F := F)
  exact (hc.continuousOn.integrableOn_compact hC).mono_set hs

theorem norm_Wf_le {f : GL (Fin 2) (A F) → ℂ} {g : GL (Fin 2) (A F)} {B : ℝ} (h : ∀ b, ‖f (gl (nU b) * g)‖ ≤ B) :
    ‖Wf f g‖ ≤ B := by
  have := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasure F) (s := fundamentalSet F)
    (f := fun b => f (gl (nU b) * g) * ψ b) (C := B) (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top)
    fun b _ => by rw [norm_mul, norm_ψ, mul_one]; exact h b
  rwa [measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one, mul_one] at this

end UpperTheory.ConvolutionTheory.R2.Pp
