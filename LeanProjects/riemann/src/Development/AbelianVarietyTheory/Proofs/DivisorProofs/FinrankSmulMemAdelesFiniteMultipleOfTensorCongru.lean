import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend.TraceCE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def trAF : AF F ⊗[F] E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ (Algebra.trace F E).baseChange (AF F)

theorem trAF_tmul (s : AF F) (e : E) :
    trAF (s ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) * s := by
  simp [trAF, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem gen_eq (s : AF F) (o : 𝓞 E) :
    algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o = s ⊗ₜ[F] (o : E) := by
  show (s ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] (o : E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem intF_zero : (0 : AF F) ∈ intF F 1 := ⟨0, fun _ => zero_mem _, by rw [one_smul]; rfl⟩

theorem intF_add {x y : AF F} (hx : x ∈ intF F 1) (hy : y ∈ intF F 1) : x + y ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  obtain ⟨d, hd, e'⟩ := hy
  refine ⟨c + d, fun v => add_mem (hc v) (hd v), ?_⟩
  rw [one_smul] at e e' ⊢
  show x.2 + y.2 = c + d
  rw [e, e']

theorem intF_neg {x : AF F} (hx : x ∈ intF F 1) : -x ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  refine ⟨-c, fun v => neg_mem (hc v), ?_⟩
  rw [one_smul] at e ⊢
  show -x.2 = -c
  rw [e]

theorem intF_algebraMap (t : 𝓞 F) : algebraMap F (AF F) (t : F) ∈ intF F 1 :=
  ⟨algebraMap F (Af F) (t : F), fun v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v t,
    by rw [one_smul]; rfl⟩

theorem trAF_mem_of_mem_SE {z : AF F ⊗[F] E} (hz : z ∈ SE F E) : trAF z ∈ intF F 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, o, rfl⟩ := hg
    rw [gen_eq, trAF_tmul]
    have hi : IsIntegral ℤ (Algebra.trace F E (o : E)) := Algebra.isIntegral_trace o.2
    exact intF_one_mul (intF_algebraMap (⟨_, hi⟩ : 𝓞 F)) hs
  | zero => rw [map_zero]; exact intF_zero
  | add a b _ _ ha hb => rw [map_add]; exact intF_add ha hb
  | neg a _ ha => rw [map_neg]; exact intF_neg ha

theorem trAF_algebraMap (x : AF F) :
    trAF (algebraMap (AF F) (AF F ⊗[F] E) x) = Module.finrank F E • x := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, trAF_tmul]
  have h : Algebra.trace F E 1 = (Module.finrank F E : F) := by
    simpa using Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
  rw [h, map_natCast, nsmul_eq_mul]

theorem finrank_smul_mem_intF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  intro F E _ _ _ _ _ N x h
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  have h1 := trAF_algebraMap (E := E) x
  rw [← e, map_nsmul] at h1
  obtain ⟨c, hc, ec⟩ := trAF_mem_of_mem_SE hs
  refine ⟨c, hc, ?_⟩
  rw [← h1]
  rw [one_smul] at ec
  rw [← ec]
  rfl

end GlobalTheory.HeckeExtend.TraceCE

end
