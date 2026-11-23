import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DoublingEvLaw

theorem elim_dot {R : Type} [CommRing R] {κ κ' : Type} [Fintype κ] [Fintype κ'] (u v : κ → R) (x y : κ' → R) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem star_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {κ : Type} [Fintype κ] (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    star (schr ψ (w.1, -w.2) φ) = schr ψ w (star φ) := by
  funext x
  simp only [schr, Pi.star_apply, star_mul', dotProduct_neg, mul_neg, ← neg_add, AddChar.map_neg_eq_inv]
  rw [Complex.inv_eq_conj (hψ _), Complex.star_def, Complex.conj_conj]

variable {F : Type} [Field F] [NumberField F]

theorem sliceL {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (b : κ' → AF F) : (fun x => Φ (Sum.elim x b)) ∈ schA F κ := by
  have e1 : (fun x => Φ (Sum.elim x b)) = fun x => Φ (GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') b x) :=
    funext fun x => congrArg Φ (funext fun k => by cases k <;> rfl)
  rw [e1]
  exact GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.sumComm κ κ') b hΦ

theorem sliceR {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (a : κ → AF F) : (fun x => Φ (Sum.elim a x)) ∈ schA F κ' :=
  GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), (∀ x, ‖ψ x‖ = 1) →
    ∀ (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
      (A₁ B₁ A₂ B₂ : κ → AF F) (a b : κ₁ → AF F),
      (∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) →
      ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
        schr ψ (Sum.elim a a, Sum.elim b (-b)) (evDbl T φ) := by
  intro F _ _ ψ hψ κ κ₁ _ _ T A₁ B₁ A₂ B₂ a b h1 h2 h3 φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a, -b) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := star_schr' ψ hψ (a, -b) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := sliceL hΨ (s ∘ Sum.inr + a)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b) - ⅟(2 : AF F) * (a ⬝ᵥ b)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b (-b) = (s ∘ Sum.inl) ⬝ᵥ b - (s ∘ Sum.inr) ⬝ᵥ b := by
    rw [← Sum.elim_comp_inl_inr s, elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr, sub_eq_add_neg]
  rw [hs]
  ring

end GlobalTheory.DoublingEvLaw
