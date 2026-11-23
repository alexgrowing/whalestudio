import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CoordinateEmbeddingMaps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ball (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (C : ℝ) (hC : 0 ≤ C) : AddSubgroup (Fv F v) where
  carrier := {c | ‖c‖ ≤ C}
  zero_mem' := by simpa using hC
  add_mem' := by
    intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := by
    intro a ha
    simpa using ha

theorem norm_le_one_of_mem {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (a : Fv F v) (h : a ∈ v.adicCompletionIntegers F) :
    ‖a‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr h

def coordE (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (n : ℕ) (x : (_ : Fin n) × Fin (Module.finrank F E)) :
    (Fin n → E) →+ Fv F v where
  toFun y := algebraMap F (Fv F v) ((Module.finBasis F E).repr (y x.1) x.2)
  map_zero' := by simp
  map_add' := by intro a b; simp

theorem main : (let d1 : (F E : Type) → [inst : Field F] → [inst_1 : NumberField F] → [inst_2 : Field E] → [NumberField E] → [inst_4 : Algebra F E] → (n : ℕ) → Module.Basis ((_ : Fin n) × Fin (Module.finrank F E)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) := @(fun (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) ↦ Pi.basis fun (x : Fin n) ↦ Module.Basis.baseChange (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Module.finBasis F E)); ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {n : ℕ} (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), Submodule.FG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc.L W) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∃ (C : ℝ), ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ (x : (_ : Fin n) × Fin (Module.finrank F E)), ‖(GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (((Module.Basis.repr (d1 F E n) : (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → (_ : Fin n) × Fin (Module.finrank F E) →₀ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) z : (_ : Fin n) × Fin (Module.finrank F E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x)‖ ≤ C) := by
  intro d1 F E _ _ _ _ _ n W hL v
  obtain ⟨s, hs⟩ := (hL.restrictScalars : (W.L.restrictScalars ℤ).FG)
  set C : ℝ := ∑ x : (_ : Fin n) × Fin (Module.finrank F E), ∑ g ∈ s, ‖coordE (F := F) (E := E) v n x g‖ with hCdef
  have hC : 0 ≤ C := by positivity
  refine ⟨C, ?_⟩

  have hLb : ∀ x, ∀ y ∈ W.L, ‖coordE (F := F) (E := E) v n x y‖ ≤ C := by
    intro x y hy
    have hle : W.L.restrictScalars ℤ ≤ ((ball v C hC).comap (coordE (F := F) (E := E) v n x)).toIntSubmodule := by
      rw [← hs, Submodule.span_le]
      intro g hg
      show ‖coordE (F := F) (E := E) v n x g‖ ≤ C
      calc ‖coordE (F := F) (E := E) v n x g‖
          ≤ ∑ g ∈ s, ‖coordE (F := F) (E := E) v n x g‖ :=
            Finset.single_le_sum (f := fun g => ‖coordE (F := F) (E := E) v n x g‖) (fun _ _ => norm_nonneg _) hg
        _ ≤ C := Finset.single_le_sum (f := fun x => ∑ g ∈ s, ‖coordE (F := F) (E := E) v n x g‖)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ x)
    exact hle hy
  intro z hz x

  let φ : (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) →+ Fv F v :=
    (GlobalTheory.AdelicU.evFin F v).toAddMonoidHom.comp
      ((Finsupp.applyAddHom x).comp (d1 F E n).repr.toLinearMap.toAddMonoidHom)
  have hφ : ∀ z, φ z = GlobalTheory.AdelicU.evFin F v ((d1 F E n).repr z x) := fun z => rfl
  have key : GlobalTheory.InertSph.latAt W v ≤ (ball v C hC).comap φ := by
    unfold GlobalTheory.InertSph.latAt
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, -, ha, y, hy, rfl⟩
    show ‖φ _‖ ≤ C
    rw [hφ]
    have : (d1 F E n).repr (a • fun i => inclR (F := F) (AF F) (y i)) x
        = a * algebraMap F (AF F) ((Module.finBasis F E).repr (y x.1) x.2) := by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      congr 1
      simp only [d1, Pi.basis_repr]
      show ((Module.finBasis F E).baseChange (AF F)).repr ((1 : AF F) ⊗ₜ[F] y x.1) x.2 = _
      rw [Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]
    rw [this, map_mul, AlgHom.commutes, norm_mul]
    have h1 := norm_le_one_of_mem _ ha
    have h2 := hLb x y hy
    calc _ ≤ 1 * C := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  exact key hz

end GlobalTheory.CoordinateEmbeddingMaps
