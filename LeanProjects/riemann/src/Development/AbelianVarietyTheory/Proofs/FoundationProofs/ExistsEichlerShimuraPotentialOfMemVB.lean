import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.H3

theorem polySlash_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (p : MvPolynomial (Fin 2) R) : slP m (MvPolynomial.map φ p) = MvPolynomial.map φ (slP m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Betti.slP_X, MvPolynomial.smul_eq_C_mul]

theorem map_mem_pot {E : Type} [CommRing E] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] E] {w : ℕ}
    {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (hF : F ∈ Pot ℤ_[l] w Γ) :
    (fun z => MvPolynomial.map (algebraMap ℤ_[l] E) (F z)) ∈ Pot E w Γ := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨fun z => (h1 z).map _, fun γ hγ => ?_⟩
  obtain ⟨p, hp⟩ := h2 γ hγ
  refine ⟨MvPolynomial.map (algebraMap ℤ_[l] E) p, fun z hz => ?_⟩
  rw [← hp z hz, map_sub, polySlash_map]

theorem exists_pot_of_mem_VB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E],
    (∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F) →
      ∀ x ∈ X.VB N l w E, ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ H3.abelian₂ X l E := by
  intro Ω _ _ ε X N l w _ E _ _ hB
  let S : Submodule E (E ⊗[ℤ_[l]] X.Fn l) :=
    { carrier := {x | ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ abelian₂ X l E}
      add_mem' := by
        rintro x y ⟨G, hG, hx⟩ ⟨G', hG', hy⟩
        exact ⟨G + G', (Betti.potSub E w (Gam N l)).add_mem hG hG', (abelian₂ X l E).add_mem hx hy⟩
      zero_mem' := ⟨0, (Betti.potSub E w (Gam N l)).zero_mem, (abelian₂ X l E).zero_mem⟩
      smul_mem' := by
        rintro c x ⟨G, hG, hx⟩
        exact ⟨c • G, (Betti.potSub E w (Gam N l)).smul_mem c hG, (abelian₂ X l E).smul_mem c hx⟩ }
  have h1 : ∀ b ∈ X.B N l w, (1 : E) ⊗ₜ[ℤ_[l]] b ∈ S := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨F, hF, hR⟩ := hB b hb
      exact ⟨_, map_mem_pot hF, Submodule.subset_span ⟨b, F, hR, rfl⟩⟩
    | zero => simpa using S.zero_mem
    | add b b' _ _ h h' => simpa [TensorProduct.tmul_add] using S.add_mem h h'
    | smul r b _ h =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul E r]
      exact S.smul_mem _ h
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  show _ ∈ S
  induction y using TensorProduct.induction_on with
  | zero => simpa using S.zero_mem
  | tmul c b =>
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]
    have : c ⊗ₜ[ℤ_[l]] (b : X.Fn l) = c • ((1 : E) ⊗ₜ[ℤ_[l]] (b : X.Fn l)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact S.smul_mem c (h1 b b.2)
  | add y y' h h' => rw [map_add]; exact S.add_mem h h'

end GlobalTheory.KZ.H3
