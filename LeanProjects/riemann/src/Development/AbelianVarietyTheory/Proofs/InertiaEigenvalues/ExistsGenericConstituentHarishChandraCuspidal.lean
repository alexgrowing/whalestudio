import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BernsteinZelevinskyDerivativeHarishChandraProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionPosOfCuspidalCharacterStatement

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.GenericConstituent

variable {g : ℕ} [Fact g.Prime]

theorem wh_const_mul' (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_mul_const' (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => f x * c) = wh ψ f * c := by
  unfold wh tr
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_list_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (L : List (Gn g n → ℂ)) :
    wh ψ L.sum = (L.map (wh ψ)).sum := by
  induction L with
  | nil => simp [wh, tr]
  | cons a L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold wh tr
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_list_sum_right {G : Type} [Group G] [Fintype G] (ρ : G → ℂ) (L : List (G → ℂ)) :
    ip ρ L.sum = (L.map (ip ρ)).sum := by
  induction L with
  | nil => simp [ip]
  | cons a L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold ip
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_sum_count {G : Type} [Group G] [Fintype G] (ρ : G → ℂ) (hρ : IsIrr ρ) (L : List (G → ℂ))
    (hL : ∀ σ ∈ L, IsIrr σ) : (L.map (ip ρ)).sum = (L.count ρ : ℂ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih (fun σ hσ => hL σ (List.mem_cons_of_mem a hσ)), List.count_cons,
      (GlobalTheory.GLq.ZOrth.zorth G ρ a hρ (hL a List.mem_cons_self)).2.2]
    by_cases h : ρ = a
    · subst h; simp; ring
    · simp [h, Ne.symm h]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem isClass_of_isChar {n : ℕ} {χ : Gn g n → ℂ} (h : IsChar χ) : IsClass χ :=
  (GlobalTheory.charDec (Gn g n) χ).2.2.1 h

theorem wh_hcL_prod (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) :
    ∀ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) → wh ψ (hcL L (degL L)) = (L.map fun p => wh ψ p.2).prod := by
  intro L
  induction L with
  | nil =>
    intro _
    exact GlobalTheory.GLq.Leibniz.wh_gl_zero ψ
  | cons p L ih =>
    intro hL
    have hp := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, IsCusp q.2 := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hβ : IsClass (hcL L (degL L)) :=
      isClass_of_isChar (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl
        (fun q hq => isChar_of_isIrr (hL' q hq).2.1)).1
    have hα : IsClass p.2 := isClass_of_isChar (isChar_of_isIrr hp.2.1)
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg]
    · simp_rw [wh_const_mul']
      rw [wh_mul_const', ih hL', List.map_cons, List.prod_cons]
    · intro y x z
      simp only
      rw [hα]
    · intro x y z
      simp only
      rw [hβ]

theorem exists_generic_constituent : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (L : List (Pc g)) (n : ℕ), degL L = n → (∀ p ∈ L, IsCusp p.2) →
      ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL L n) ≠ 0 := by
  intro g _ ψ hψ L n hn hL
  subst hn
  have hwh : wh ψ (hcL L (degL L)) ≠ 0 := by
    rw [wh_hcL_prod ψ hψ L hL]
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨p, hp, h1⟩ := List.mem_map.1 h0
    obtain ⟨m, hm, hm'⟩ := GlobalTheory.T.whittakerDimension_pos_of_cuspidal_character g ψ hψ p.1 p.2 (hL p hp)
    rw [hm'] at h1
    have : m = 0 := by exact_mod_cast h1
    omega
  have hch : IsChar (hcL L (degL L)) :=
    (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl (fun q hq => isChar_of_isIrr (hL q hq).2.1)).1
  obtain ⟨Lρ, hirr, hsum⟩ := (GlobalTheory.charDec _ (hcL L (degL L))).1 hch
  have hex : ∃ ρ ∈ Lρ, wh ψ ρ ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply hwh
    rw [hsum, wh_list_sum]
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
      exact hno ρ hρ
  obtain ⟨ρ, hρ, hwρ⟩ := hex
  refine ⟨ρ, hirr ρ hρ, hwρ, ?_⟩
  rw [hsum, ip_list_sum_right, ip_sum_count ρ (hirr ρ hρ) Lρ hirr]
  exact Nat.cast_ne_zero.2 (List.count_pos_iff.2 hρ).ne'

end GlobalTheory.GLq.GenericConstituent
