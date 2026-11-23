import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section
namespace GlobalTheory.HeckeExtend.AtInf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def uInf (F : Type) [Field F] [NumberField F] : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def uFin (F : Type) [Field F] [NumberField F] : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

theorem uInf_add_uFin : uInf F + uFin F = 1 := by
  show ((1 : InfiniteAdeleRing F) + 0, (0 : FiniteAdeleRing (𝓞 F) F) + 1) = 1
  simp

theorem evI_uFin : evI F (uFin F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem pure_mem (N : ℕ) (hN : 0 < N) (a : AF F) (e : E) :
    ((uInf F * a) ⊗ₜ[F] e : AF F ⊗[F] E) ∈ CE F E N := by
  have halg : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsIntegral.isIntegral (R := ℚ) e).isAlgebraic
  obtain ⟨d, hd, hint⟩ := halg.exists_integral_multiple
  let o : 𝓞 E := ⟨d • e, hint⟩
  have ho : (o : E) = (d : E) * e := by simp [o, zsmul_eq_mul]
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd
  let c : F := ((N : F) * (d : F))⁻¹
  let s : AF F := algebraMap F (AF F) c * (uInf F * a)
  have hs : s ∈ intF F 1 := by
    refine ⟨0, fun v => zero_mem _, ?_⟩
    show (algebraMap F (AF F) c).2 * ((uInf F).2 * a.2) = 1 • 0
    simp [uInf]
  refine mem_CE.2 ⟨algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o,
    AddSubgroup.subset_closure ⟨s, hs, o, rfl⟩, ?_⟩
  have h1 : algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o = s ⊗ₜ[F] (o : E) := by
    simp [incAF, inclR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  have h2 : s = c • (uInf F * a) := (Algebra.smul_def c _).symm
  rw [h1, h2, TensorProduct.smul_tmul, ← TensorProduct.tmul_smul]
  congr 1
  rw [ho, Algebra.smul_def c, nsmul_eq_mul]
  simp only [c, map_inv₀, map_mul, map_natCast, map_intCast]
  field_simp

theorem uInf_smul_mem (N : ℕ) (hN : 0 < N) (w : AF F ⊗[F] E) : uInf F • w ∈ CE F E N := by
  induction w using TensorProduct.induction_on with
  | zero => rw [smul_zero]; exact zero_mem _
  | tmul a e => rw [TensorProduct.smul_tmul', smul_eq_mul]; exact pure_mem N hN a e
  | add x y hx hy => rw [smul_add]; exact add_mem hx hy

theorem mem_CE_of_atInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    ∀ w : AF F ⊗[F] E, At (evI F) w → w ∈ CE F E N := by
  intro F E _ _ _ _ _ N hN w hw
  have h0 : uFin F • w = 0 := hw (uFin F) evI_uFin
  have : w = uInf F • w := by
    conv_lhs => rw [← one_smul (AF F) w, ← uInf_add_uFin, add_smul, h0, add_zero]
  rw [this]
  exact uInf_smul_mem N hN w

end GlobalTheory.HeckeExtend.AtInf
