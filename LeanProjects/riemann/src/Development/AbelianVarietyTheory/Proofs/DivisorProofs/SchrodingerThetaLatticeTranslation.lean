import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
namespace GlobalTheory.LagrInv

variable {F : Type} [Field F] [NumberField F]

def toA {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  ((fun k => algebraMap F (AF F) (w.1 k)), (fun k => algebraMap F (AF F) (w.2 k)))

theorem toA_dot {κ : Type} [Fintype κ] (a b : κ → F) :
    (fun k => algebraMap F (AF F) (a k)) ⬝ᵥ (fun k => algebraMap F (AF F) (b k)) = algebraMap F (AF F) (a ⬝ᵥ b) := by
  simp [dotProduct, map_sum, map_mul]

theorem iso_span {κ : Type} [Fintype κ] (Λ : Submodule F ((κ → F) × (κ → F)))
    (hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) :
    ∀ p ∈ Submodule.span (AF F) (toA '' (Λ : Set ((κ → F) × (κ → F)))),
    ∀ q ∈ Submodule.span (AF F) (toA '' (Λ : Set ((κ → F) × (κ → F)))), p.1 ⬝ᵥ q.2 = q.1 ⬝ᵥ p.2 := by
  intro p hp q hq
  induction hp using Submodule.span_induction generalizing q with
  | mem x hx =>
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      simp only [toA, toA_dot, hΛ a ha b hb]
    | zero => simp
    | add y z _ _ h1 h2 => simp [add_dotProduct, dotProduct_add, h1, h2]
    | smul c y _ h => simp [smul_dotProduct, dotProduct_smul, h]
  | zero => simp
  | add x y _ _ h1 h2 => simp [add_dotProduct, dotProduct_add, h1 q hq, h2 q hq]
  | smul c x _ h => simp [smul_dotProduct, dotProduct_smul, h q hq]

theorem lagrForm_schr_invariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] (Λ : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → ∀ (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), (∀ j, u j ∈ Λ) →
    (∀ v ∈ Λ, ∃ c : Fin r → F, v.1 = ∑ j, c j • (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (t : AF F), ∀ v ∈ Λ, ∀ φ : (κ → AF F) → ℂ,
      ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) (schr ψ (t • ((fun k => algebraMap F (AF F) (v.1 k)), (fun k => algebraMap F (AF F) (v.2 k)))) φ) 0 ∂μ = ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ := by
  intro F _ _ ψ κ _ Λ hΛ r u hu hP μ hμ t v hv φ
  obtain ⟨c, hc⟩ := hP v hv
  letI : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  change ∫ x, schr ψ (∑ j, x j • toA (u j)) (schr ψ (t • toA v) φ) 0 ∂μ = ∫ x, schr ψ (∑ j, x j • toA (u j)) φ 0 ∂μ
  set M := Submodule.span (AF F) (toA '' (Λ : Set ((κ → F) × (κ → F)))) with hM
  have hiso := iso_span Λ hΛ
  have hUM : ∀ j, toA (u j) ∈ M := fun j => Submodule.subset_span ⟨u j, hu j, rfl⟩
  have hVM : toA v ∈ M := Submodule.subset_span ⟨v, hv, rfl⟩
  set c' : Fin r → AF F := fun j => algebraMap F (AF F) (c j) with hc'
  set C : (κ → AF F) × (κ → AF F) := ∑ j, c' j • toA (u j) with hCdef
  have hCM : C ∈ M := Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hUM j))
  have hC1 : C.1 = (toA v).1 := by
    funext k
    simp [hCdef, toA, hc, Prod.fst_sum, Finset.sum_apply, map_sum, hc', Algebra.smul_def]
  have key : ∀ x : Fin r → AF F, schr ψ (∑ j, x j • toA (u j)) (schr ψ (t • toA v) φ) 0
      = schr ψ (∑ j, (x + t • c') j • toA (u j)) φ 0 := by
    intro x
    set a := ∑ j, x j • toA (u j) with ha
    have haM : a ∈ M := Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hUM j))
    have ha' : ∑ j, (x + t • c') j • toA (u j) = a + t • C := by
      simp [ha, hCdef, add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]
    rw [ha']
    set V := toA v with hV
    have e1 := hiso a haM V hVM
    have e2 := hiso a haM C hCM
    have e3 := hiso C hCM V hVM
    rw [hC1] at e2 e3
    simp only [schr, zero_dotProduct, zero_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, hC1]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    have hh : (2 : AF F) * ⅟(2 : AF F) = 1 := mul_invOf_self 2
    rw [e1, e2, ← e3]
    linear_combination (-(t * (V.1 ⬝ᵥ a.2))) * hh
  simp_rw [key]
  exact integral_add_right_eq_self (μ := μ) (fun x => schr ψ (∑ j, x j • toA (u j)) φ 0) (t • c')

end GlobalTheory.LagrInv
