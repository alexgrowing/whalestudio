import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepCompHomAndMulStatement

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ProdChar

theorem isChar_of_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem eq_zero_of_ip {G : Type} [Group G] [Fintype G] {f : G → ℂ} (hf : IsClass f)
    (h : ∀ ρ, IsIrr ρ → ip f ρ = 0) : f = 0 := by
  calc f = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip f ρ • ρ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G f).2.1 hf
    _ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, (0 : G → ℂ) :=
        finsum_mem_congr rfl fun ρ hρ => by rw [h ρ hρ, zero_smul]
    _ = 0 := finsum_mem_zero _

theorem ip_prod {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ)
    (α : G₁ → ℂ) (β : G₂ → ℂ) :
    ip Φ (fun z => α z.1 * β z.2) = ip (fun y => ip (fun x => Φ (x, y)) α) β := by
  simp only [ip, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, Prod.fst_inv, Prod.snd_inv,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

theorem isIrr_prod {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    {α : G₁ → ℂ} {β : G₂ → ℂ} (hα : IsIrr α) (hβ : IsIrr β) :
    IsIrr (fun z : G₁ × G₂ => α z.1 * β z.2) := by
  have hA : IsChar (fun z : G₁ × G₂ => α z.1) :=
    (GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul).1 (G₁ × G₂) G₁ (MonoidHom.fst G₁ G₂) α (isChar_of_irr hα)
  have hB : IsChar (fun z : G₁ × G₂ => β z.2) :=
    (GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul).1 (G₁ × G₂) G₂ (MonoidHom.snd G₁ G₂) β (isChar_of_irr hβ)
  have hC : IsChar (fun z : G₁ × G₂ => α z.1 * β z.2) := (GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul).2 (G₁ × G₂) _ _ hA hB
  apply (GlobalTheory.T.character_decomposition_and_classFunction_expansion (G₁ × G₂) _).2.2.2.1 hC
  have h1 : ip α α = 1 := by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G₁ α α hα hα).2.2
  have h2 : ip β β = 1 := by simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G₂ β β hβ hβ).2.2
  have key : ∀ y, ip (fun x => α x * β y) α = β y := by
    intro y
    have e : ip (fun x => α x * β y) α = β y * ip α α := by
      simp only [ip, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e, h1, mul_one]
  rw [ip_prod]
  simp only [key]
  exact h2

theorem exists_prod_of_isIrr {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    {ρ : G₁ × G₂ → ℂ} (hρ : IsIrr ρ) :
    ∃ p : (G₁ → ℂ) × (G₂ → ℂ), (IsIrr p.1 ∧ IsIrr p.2) ∧ ρ = fun z => p.1 z.1 * p.2 z.2 := by
  by_contra hne
  push_neg at hne
  have hcl : IsClass ρ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ ρ).2.2.1 (isChar_of_irr hρ)
  have hip : ∀ α β, IsIrr α → IsIrr β → ip ρ (fun z : G₁ × G₂ => α z.1 * β z.2) = 0 := by
    intro α β hα hβ
    rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ _ hρ (isIrr_prod hα hβ)).2.2, if_neg (by simpa using hne (α, β) ⟨hα, hβ⟩)]
  have hrow : ∀ y, (fun x => ρ (x, y)) = 0 := by
    intro y
    apply eq_zero_of_ip
    · intro x k
      simpa using hcl (x, y) (k, 1)
    · intro α hα
      have hF : (fun y' => ip (fun x => ρ (x, y')) α) = 0 := by
        apply eq_zero_of_ip
        · intro y' h
          have e : (fun x => ρ (x, h * y' * h⁻¹)) = fun x => ρ (x, y') := by
            funext x
            simpa using hcl (x, y') (1, h)
          exact congrArg (fun f => ip f α) e
        · intro β hβ
          exact (ip_prod ρ α β).symm.trans (hip α β hα hβ)
      exact congrFun hF y
  have hz : ρ = 0 := by
    funext z
    obtain ⟨x, y⟩ := z
    exact congrFun (hrow y) x
  have h1 := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ ρ ρ hρ hρ).2.2
  rw [if_pos rfl, hz] at h1
  simp [ip] at h1

private theorem sum_irr_prod_eq_sum_irr_mul {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    (L : List (G₁ × G₂ → ℂ)) (hL : ∀ ρ ∈ L, IsIrr ρ) :
    ∃ L' : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L', IsIrr p.1 ∧ IsIrr p.2) ∧
      ∀ x y, L.sum (x, y) = (L'.map fun p => p.1 x * p.2 y).sum := by
  induction L with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons ρ L ih =>
    obtain ⟨p, hp, rfl⟩ := exists_prod_of_isIrr (hL ρ (by simp))
    obtain ⟨L', hL', hsum⟩ := ih fun r hr => hL r (List.mem_cons_of_mem _ hr)
    refine ⟨p :: L', ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hL' q hq
    · intro x y
      rw [List.sum_cons, Pi.add_apply, hsum]
      simp

theorem exists_list_prod : ∀ (G₁ G₂ : Type) [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ),
    IsChar Φ → ∃ L : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧
      ∀ x y, Φ (x, y) = (L.map fun p => p.1 x * p.2 y).sum := by
  intro G₁ G₂ _ _ _ _ Φ hΦ
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion (G₁ × G₂) Φ).1 hΦ
  exact sum_irr_prod_eq_sum_irr_mul L hL

end GlobalTheory.GLm.ProdChar
