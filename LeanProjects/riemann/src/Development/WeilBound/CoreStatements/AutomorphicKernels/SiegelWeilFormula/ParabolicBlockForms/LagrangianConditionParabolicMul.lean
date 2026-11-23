import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.QE
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.IncMFromBlocks

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

namespace Bq

theorem QA_eq {n : ℕ} (ε : ℤˣ) : Afc.QA (F := F) (E := E) n ε = incM F (QE n ε) := by
  refine Matrix.ext fun r c => ?_
  rcases r with i | i <;> rcases c with j | j <;>
    simp [Afc.QA, QE, incM, Matrix.one_apply, Matrix.smul_apply, kfour.inclR_int] <;> split_ifs <;> simp [kfour.inclR_int]

theorem form_E {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hb : kfour.FrameEq σ Y b ε) (g : G2 σ Y)
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} (hM : inFrame b g = incM F M) :
    Mᵀ * QE n ε * M.map σ = QE n ε := by
  have h1 := Afc.frame_form hb g
  rw [hM, QA_eq, Afc.incM_transpose, Afc.incM_map_cA, ← kfour.incM_mul', ← kfour.incM_mul'] at h1
  exact kfour.incM_injective h1

theorem yrow_zero {n : ℕ} {ε : ℤˣ} {i₀ : Fin n} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E}
    (hM : Mᵀ * QE n ε * M.map σ = QE n ε) (hx : ∀ r, M r (Sum.inl i₀) = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) r (Sum.inl i₀))
    (c : Fin n ⊕ Fin n) (hc : c ≠ Sum.inr i₀) : M (Sum.inr i₀) c = 0 := by
  have h := congrFun (congrFun hM (Sum.inl i₀)) c
  have h2 : ∀ s, (Mᵀ * QE (E := E) n ε) (Sum.inl i₀) s = QE (E := E) n ε (Sum.inl i₀) s := by
    intro s
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, hx, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [Matrix.mul_apply] at h
  simp only [h2] at h
  have h3 : QE (E := E) n ε (Sum.inl i₀) c = 0 := by
    rcases c with j | j
    · simp [QE]
    · have : i₀ ≠ j := fun e => hc (by rw [e])
      simp [QE, Matrix.one_apply, this]
  rw [h3, Fintype.sum_sum_type] at h
  simp [QE, Matrix.one_apply] at h
  exact h

theorem lagrangian_condition_parabolic_mul {d : SD σ} (L : LD d) {p γ : d.G} (hp : p ∈ par2 σ d.Y) (hγ : LagrangianCondition L γ) : LagrangianCondition L (p * γ) := by
  intro i
  have hP := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p).1 hp
  have e1 : ∀ j, inFrame d.b p (Sum.inr i) (Sum.inl j) = 0 := fun j => by
    have := congrFun (congrFun hP i) j
    simpa [Matrix.toBlocks₂₁] using this
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [e1, hγ _]

theorem lagrangian_condition_embedding {d : SD σ} (L : LD d) (g : G2 σ L.Y) : LagrangianCondition L (L.j g) := by
  intro i
  exact (L.j_out g (Sum.inl L.i₀) (by simp) (Sum.inr i)).2.trans (by simp [Matrix.one_apply])

theorem par_of_j {d : SD σ} (L : LD d) {g : G2 σ L.Y} (h : L.j g ∈ par2 σ d.Y) : g ∈ par2 σ L.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame, inFrame_j] at h
  refine Matrix.ext fun a c => ?_
  have h1 := congrFun (congrFun h (L.em a)) (L.em c)
  have h2 := padM_emS L (inFrame L.b g) (Sum.inr a) (Sum.inl c)
  simp only [emS, Sum.map_inr, Sum.map_inl] at h2
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at h1 ⊢
  rw [← h2]
  exact h1

end Bq

end PositivityTheory.SiegelWeilFormula.Act.C4

end
