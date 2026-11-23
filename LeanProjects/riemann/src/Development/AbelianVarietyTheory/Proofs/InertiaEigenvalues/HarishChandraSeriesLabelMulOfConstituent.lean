import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionExteriorProductAssocCommStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecompStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvariStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.LabelMul

theorem ip_add_right {G : Type} [Group G] [Fintype G] (χ φ ψ : G → ℂ) :
    ip χ (φ + ψ) = ip χ φ + ip χ ψ := by
  simp only [ip, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem ip_sum_eq_count {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (hχ : IsIrr χ) (L : List (G → ℂ))
    (hL : ∀ ρ ∈ L, IsIrr ρ) : ip χ L.sum = (L.count χ : ℕ) := by
  induction L with
  | nil => simp [ip]
  | cons ρ L ih =>
    rw [List.sum_cons, ip_add_right, ih (fun σ hσ => hL σ (List.mem_cons_of_mem _ hσ)),
      (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G χ ρ hχ (hL ρ List.mem_cons_self)).2.2, List.count_cons]
    by_cases h : χ = ρ
    · subst h
      simp [add_comm]
    · have h' : ¬ ρ = χ := fun e => h e.symm
      simp [h, h']

theorem ip_nat {G : Type} [Group G] [Fintype G] {χ φ : G → ℂ} (hχ : IsIrr χ) (hφ : IsChar φ) :
    ∃ k : ℕ, ip χ φ = k := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G φ).1 hφ
  exact ⟨_, ip_sum_eq_count hχ L hL⟩

theorem exists_add_of_ip_ne_zero {G : Type} [Group G] [Fintype G] {χ φ : G → ℂ} (hχ : IsIrr χ) (hφ : IsChar φ)
    (h : ip χ φ ≠ 0) : ∃ ψ, IsChar ψ ∧ φ = χ + ψ := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G φ).1 hφ
  rw [ip_sum_eq_count hχ L hL] at h
  have hm : χ ∈ L := List.count_pos_iff.1 (Nat.pos_of_ne_zero (by exact_mod_cast h))
  refine ⟨(L.erase χ).sum, (GlobalTheory.T.character_decomposition_and_classFunction_expansion G χ).2.2.2.2 _
    (fun ρ hρ => isChar_of_isIrr (hL ρ (List.mem_of_mem_erase hρ))), ?_⟩
  rw [(List.perm_cons_erase hm).sum_eq, List.sum_cons]

variable {g : ℕ} [Fact g.Prime]

theorem hc_add_left (a b n : ℕ) (α α' : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b (α + α') β n = hc a b α β n + hc a b α' β n := by
  funext x
  simp only [hc, hcT, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · ring
  · simp

theorem hc_add_right (a b n : ℕ) (α : Gn g a → ℂ) (β β' : Gn g b → ℂ) :
    hc a b α (β + β') n = hc a b α β n + hc a b α β' n := by
  funext x
  simp only [hc, hcT, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · ring
  · simp

omit [Fact g.Prime] in
theorem degL_append (P Q : List (Pc g)) : degL (P ++ Q) = degL P + degL Q := by
  simp [degL]

theorem hcL_append (P Q : List (Pc g)) (hP : ∀ p ∈ P, IsChar p.2) (hQ : ∀ p ∈ Q, IsChar p.2) :
    ∀ n, n = degL P + degL Q →
      hcL (P ++ Q) n = hc (degL P) (degL Q) (hcL P (degL P)) (hcL Q (degL Q)) n := by
  have cQ : IsClass (hcL Q (degL Q)) :=
    (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g Q Q _ rfl hQ).1
  induction P with
  | nil =>
    intro n hn
    have hn' : n = degL Q := by simpa [degL] using hn
    subst hn'
    exact (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g (degL Q) (degL Q) (degL Q) (degL Q) _ _ _ cQ cQ cQ).2.2.1.symm
  | cons p P ih =>
    intro n hn
    have hP' : ∀ q ∈ P, IsChar q.2 := fun q hq => hP q (List.mem_cons_of_mem _ hq)
    have cP : IsClass (hcL P (degL P)) :=
      (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g P P _ rfl hP').1
    have cp : IsClass p.2 := (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.1 (hP p List.mem_cons_self)
    have key : ∀ m, m = degL P + degL Q → hc p.1 m p.2 (hcL (P ++ Q) m) n =
        hc (p.1 + degL P) (degL Q) (hc p.1 (degL P) p.2 (hcL P (degL P)) (p.1 + degL P)) (hcL Q (degL Q)) n := by
      intro m hm
      subst hm
      rw [ih hP' _ rfl]
      exact ((GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g _ _ _ n _ _ _ cp cP cQ).1 hn).symm
    exact key _ (degL_append P Q)

theorem hasLabel_mul : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (a b n : ℕ) (χ : Gn g n → ℂ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (f₁ f₂ : (ZMod g)[X]), n = a + b → IsIrr χ → IsIrr α → IsIrr β → HasLabel L α f₁ → HasLabel L β f₂ → ip χ (hc a b α β n) ≠ 0 → HasLabel L χ (f₁ * f₂) := by
  intro g _ L a b n χ α β f₁ f₂ hn hχ hα hβ h₁ h₂ hip
  obtain ⟨P, hP, rfl, rfl, iP⟩ := h₁
  obtain ⟨Q, hQ, rfl, rfl, iQ⟩ := h₂
  have cP : ∀ p ∈ P.map Prod.snd, IsChar p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact isChar_of_isIrr (hP q hq).2.1.2.1
  have cQ : ∀ p ∈ Q.map Prod.snd, IsChar p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact isChar_of_isIrr (hQ q hq).2.1.2.1
  obtain ⟨A, hA, eA⟩ := exists_add_of_ip_ne_zero hα (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g _ [] _ rfl cP).1 iP
  obtain ⟨B, hB, eB⟩ := exists_add_of_ip_ne_zero hβ (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g _ [] _ rfl cQ).1 iQ
  refine ⟨P ++ Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hP p h
    · exact hQ p h
  · rw [List.map_append, degL_append, hn]
  · rw [List.map_append, List.prod_append]
  · rw [List.map_append, hcL_append _ _ cP cQ n hn, eA, eB, hc_add_left, hc_add_right, hc_add_right,
      ip_add_right, ip_add_right, ip_add_right]
    have H := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g _ _ n hn).1
    obtain ⟨k₁, e₁⟩ := ip_nat hχ (H _ _ (isChar_of_isIrr hα) (isChar_of_isIrr hβ))
    obtain ⟨k₂, e₂⟩ := ip_nat hχ (H _ _ (isChar_of_isIrr hα) hB)
    obtain ⟨k₃, e₃⟩ := ip_nat hχ (H _ _ hA (isChar_of_isIrr hβ))
    obtain ⟨k₄, e₄⟩ := ip_nat hχ (H _ _ hA hB)
    rw [e₁] at hip
    rw [e₁, e₂, e₃, e₄]
    have h1 : k₁ ≠ 0 := by exact_mod_cast hip
    have : k₁ + k₂ + (k₃ + k₄) ≠ 0 := by omega
    exact_mod_cast this

end GlobalTheory.GLq.LabelMul
