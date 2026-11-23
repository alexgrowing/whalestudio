import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def intF (N : ℕ) : Set (AF F) :=
  {x | ∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ x.2 = N • c}

theorem intF_one_mul {x y : AF F} (hx : x ∈ intF F 1) (hy : y ∈ intF F 1) : x * y ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  obtain ⟨d, hd, e'⟩ := hy
  refine ⟨c * d, fun v => mul_mem (hc v) (hd v), ?_⟩
  rw [one_smul] at e e' ⊢
  show x.2 * y.2 = c * d
  rw [e, e']

variable (F E) in

def SE : AddSubgroup (AF F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o}

theorem gen_mul {x y : AF F ⊗[F] E}
    (hx : x ∈ {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o})
    (hy : y ∈ {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o}) :
    x * y ∈ SE F E := by
  obtain ⟨s, hs, o, rfl⟩ := hx
  obtain ⟨s', hs', o', rfl⟩ := hy
  refine AddSubgroup.subset_closure ⟨s * s', intF_one_mul hs hs', o * o', ?_⟩
  have h : ((o * o' : 𝓞 E) : E) = (o : E) * o' := rfl
  rw [map_mul, h, map_mul]
  ring

theorem SE_mul {x y : AF F ⊗[F] E} (hx : x ∈ SE F E) (hy : y ∈ SE F E) : x * y ∈ SE F E := by
  induction hx using AddSubgroup.closure_induction with
  | mem g hg =>
    induction hy using AddSubgroup.closure_induction with
    | mem g' hg' => exact gen_mul hg hg'
    | zero => rw [mul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | neg a _ ha => rw [mul_neg]; exact neg_mem ha
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_mul]; exact neg_mem ha

theorem one_mem_SE : (1 : AF F ⊗[F] E) ∈ SE F E :=
  AddSubgroup.subset_closure ⟨1, ⟨1, fun v => one_mem _, by rw [one_smul]; rfl⟩, 1, by simp [Algebra.TensorProduct.one_def]⟩

variable (F E) in

def CE (N : ℕ) : AddSubgroup (AF F ⊗[F] E) := (SE F E).map (nsmulAddMonoidHom N)

theorem mem_CE {N : ℕ} {z : AF F ⊗[F] E} : z ∈ CE F E N ↔ ∃ s ∈ SE F E, N • s = z := by
  simp [CE]

theorem CE_step {N : ℕ} {x y : AF F ⊗[F] E} (hx : x - 1 ∈ CE F E N) (hy : y - 1 ∈ CE F E N) :
    x * y - 1 ∈ CE F E N := by
  obtain ⟨a, ha, ea⟩ := mem_CE.1 hx
  obtain ⟨b, hb, eb⟩ := mem_CE.1 hy
  refine mem_CE.2 ⟨a + b + N • (a * b), add_mem (add_mem ha hb) (nsmul_mem (SE_mul ha hb) N), ?_⟩
  rw [eq_add_of_sub_eq ea.symm, eq_add_of_sub_eq eb.symm]
  simp only [nsmul_eq_mul]
  ring

variable (F E) in

def WE (N : ℕ) : Subgroup (AF F ⊗[F] E)ˣ where
  carrier := {z | (z : AF F ⊗[F] E) - 1 ∈ CE F E N ∧ ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 ∈ CE F E N}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul]; exact CE_step hx.1 hy.1,
    by rw [mul_inv_rev, Units.val_mul]; exact CE_step hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem cA_gen (σ : E →ₐ[F] E) (s : AF F) (o : 𝓞 E) :
    cA σ (algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o) =
      algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E (σ o) := by
  rw [map_mul, AlgHom.commutes]
  rfl

theorem cA_mem_SE (σ : E →ₐ[F] E) {z : AF F ⊗[F] E} (hz : z ∈ SE F E) : cA σ z ∈ SE F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, o, rfl⟩ := hg
    rw [cA_gen]
    have : IsIntegral ℤ (σ (o : E)) := (o.2.map σ)
    exact AddSubgroup.subset_closure ⟨s, hs, ⟨σ o, this⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end GlobalTheory.HeckeExtend

end
