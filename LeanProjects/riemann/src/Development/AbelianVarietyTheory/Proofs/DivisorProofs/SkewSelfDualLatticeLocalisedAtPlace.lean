import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.SkewLocDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_smul_left (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (c : E) (x y : Fin d → E) :
    form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

theorem form_add_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x y z : Fin d → E) :
    form σ J x (y + z) = form σ J x y + form σ J x z := by
  have h : (fun i => σ ((y + z) i)) = (fun i => σ (y i)) + fun i => σ (z i) := funext fun i => by simp
  simp only [form, h, Matrix.mulVec_add, dotProduct_add]

theorem form_zero_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x : Fin d → E) :
    form σ J x 0 = 0 := by
  have h : (fun i => σ ((0 : Fin d → E) i)) = 0 := funext fun i => by simp
  simp only [form, h, Matrix.mulVec_zero, dotProduct_zero]

theorem form_smul_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (o : 𝓞 E) (x y : Fin d → E) :
    form σ J x (o • y) = σ (o : E) * form σ J x y := by
  have h : (fun i => σ ((o • y) i)) = σ (o : E) • fun i => σ (y i) := funext fun i => by
    simp [Algebra.smul_def]
  simp only [form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem isIntegral_algebraMap_int (a : 𝓞 F) : IsIntegral ℤ (algebraMap F E (a : F)) :=
  (NumberField.RingOfIntegers.isIntegral_coe a).map (algebraMap F E).toIntAlgHom

theorem isIntegral_conj (σ : E →ₐ[F] E) (o : 𝓞 E) : IsIntegral ℤ (σ (o : E)) :=
  (NumberField.RingOfIntegers.isIntegral_coe o).map (σ : E →+* E).toIntAlgHom

end GlobalTheory.SkewLocDual

open GlobalTheory.SkewLocDual in
theorem GlobalTheory.SkewLocDual.exists_smul_mem_of_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {d r s : ℕ} (Y : Spc F E d), Y.IsSkew σ B r s → ∀ (v : Pl F) (u : Fin d → E),
    (∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * form σ Y.J u y)) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • u ∈ Y.L := by
  intro F E _ _ _ _ _ σ B d r s Y hY v u hu
  classical
  haveI := v.isPrime
  obtain ⟨S, hS⟩ := hY.lat.fg
  have hgen : ∀ y ∈ S, y ∈ Y.L := fun y hy => hS ▸ Submodule.subset_span hy
  choose! T hT using fun y (hy : y ∈ S) => hu y (hgen y hy)
  have ht : (∏ y ∈ S, T y) ∉ v.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push_neg
    exact fun y hy => (hT y hy).1
  have key : ∀ y ∈ Y.L,
      IsIntegral ℤ (algebraMap F E ((∏ y ∈ S, T y : 𝓞 F) : F) * form σ Y.J u y) := by
    rw [← hS]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have hsplit : algebraMap F E ((∏ y ∈ S, T y : 𝓞 F) : F) =
          algebraMap F E ((∏ y ∈ S.erase x, T y : 𝓞 F) : F) * algebraMap F E (T x : F) := by
        rw [← map_mul, ← Finset.prod_erase_mul S T hx]; rfl
      rw [hsplit, mul_assoc]
      exact (isIntegral_algebraMap_int _).mul (hT x hx).2
    | zero => simpa [form_zero_right] using (isIntegral_zero : IsIntegral ℤ (0 : E))
    | add x y _ _ hx hy => rw [form_add_right, mul_add]; exact hx.add hy
    | smul o x _ hx => rw [form_smul_right, mul_left_comm]; exact (isIntegral_conj σ o).mul hx
  refine ⟨∏ y ∈ S, T y, ht, (hY.dual _).2 fun x hx o => ?_⟩
  rw [form_smul_left]
  exact Algebra.isIntegral_trace ((NumberField.RingOfIntegers.isIntegral_coe o).mul (key x hx))
