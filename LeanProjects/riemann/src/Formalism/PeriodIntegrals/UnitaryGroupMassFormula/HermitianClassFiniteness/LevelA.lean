import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

noncomputable section

open NumberField Matrix IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

section Generic

variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}

theorem lvA_mulVec_int {ι κ : Type} [Fintype κ] (M : Matrix ι κ R) (hM : ∀ i j, M i j ∈ S)
    (v : κ → R) (hv : ∀ i, v i ∈ S) : ∀ i, (M *ᵥ v) i ∈ S := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact S.sum_mem fun j _ => S.mul_mem (hM i j) (hv j)

theorem lvA_key {ι : Type} [Fintype ι] [DecidableEq ι] (LA : Submodule S (Fin n → R))
    (c₁ c₂ c g : R)
    (h₁ : ∀ y ∈ LA, ∀ i, c₁ * y i ∈ S) (h₂ : ∀ y : Fin n → R, (∀ i, y i ∈ S) → c₂ • y ∈ LA)
    (P : Matrix (Fin n) ι R) (Q : Matrix ι (Fin n) R) (hPQ : P * Q = 1)
    (hP : ∀ i j, (c • P) i j ∈ S) (hQ : ∀ i j, (c • Q) i j ∈ S)
    (N : Matrix ι ι R) (hN : ∀ i j, N i j ∈ S) (u : Matrix ι ι R)
    (hu : u = 1 + (g * c₂ * c * c * c₁) • N) :
    ∀ y ∈ LA, ∃ z ∈ LA, (P * u * Q - 1) *ᵥ y = g • z := by
  intro y hy
  have hcy : ∀ i, (c₁ • y) i ∈ S := fun i => by
    simpa [Pi.smul_apply, smul_eq_mul] using h₁ y hy i
  have hw : ∀ i, ((c • P) *ᵥ (N *ᵥ ((c • Q) *ᵥ (c₁ • y)))) i ∈ S :=
    lvA_mulVec_int S _ hP _ (lvA_mulVec_int S _ hN _ (lvA_mulVec_int S _ hQ _ hcy))
  refine ⟨c₂ • ((c • P) *ᵥ (N *ᵥ ((c • Q) *ᵥ (c₁ • y)))), h₂ _ hw, ?_⟩
  have hexp : P * u * Q - 1 = (g * c₂ * c * c * c₁) • (P * N * Q) := by
    rw [hu, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ, Matrix.mul_smul, Matrix.smul_mul]
    abel
  rw [hexp]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, ← Matrix.mulVec_mulVec]
  congr 1
  ring

theorem lvA_maps {ι : Type} [Fintype ι] [DecidableEq ι] (LA : Submodule S (Fin n → R))
    (c₁ c₂ c g : R) (hg : g ∈ S)
    (h₁ : ∀ y ∈ LA, ∀ i, c₁ * y i ∈ S) (h₂ : ∀ y : Fin n → R, (∀ i, y i ∈ S) → c₂ • y ∈ LA)
    (P : Matrix (Fin n) ι R) (Q : Matrix ι (Fin n) R) (hPQ : P * Q = 1)
    (hP : ∀ i j, (c • P) i j ∈ S) (hQ : ∀ i j, (c • Q) i j ∈ S)
    (N : Matrix ι ι R) (hN : ∀ i j, N i j ∈ S) (u : Matrix ι ι R)
    (hu : u = 1 + (g * c₂ * c * c * c₁) • N) :
    ∀ y ∈ LA, (P * u * Q) *ᵥ y ∈ LA := by
  intro y hy
  obtain ⟨z, hz, hzeq⟩ := lvA_key S LA c₁ c₂ c g h₁ h₂ P Q hPQ hP hQ N hN u hu y hy
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add'] at hzeq
  rw [hzeq]
  exact LA.add_mem hy (LA.smul_mem (⟨g, hg⟩ : S) hz)

theorem lvA_princ_form {ι : Type} [Fintype ι] [DecidableEq ι] (d : S) (u : GL ι R)
    (hu : u ∈ Formalism.UG.princ (n := ι) S.subtype (Ideal.span {d})) :
    ∃ N : Matrix ι ι R, (∀ i j, N i j ∈ S) ∧ (u : Matrix ι ι R) = 1 + (d : R) • N := by
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
  have h1 : Formalism.UG.redGL (Ideal.span {d}) u' = 1 := Subgroup.mem_bot.1 (Subgroup.mem_comap.1 hu')
  have hent : ∀ i j, ∃ a : S, a * d = (u' : Matrix ι ι S) i j - (1 : Matrix ι ι S) i j := by
    intro i j
    have h2 := congrArg (fun g : GL ι (S ⧸ Ideal.span {d}) => (g : Matrix ι ι (S ⧸ Ideal.span {d})) i j) h1
    simp only [Formalism.UG.redGL, Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Units.val_one] at h2
    have h3 : (u' : Matrix ι ι S) i j - (1 : Matrix ι ι S) i j ∈ Ideal.span {d} := by
      rw [← Ideal.Quotient.eq]
      have h2' : Ideal.Quotient.mk (Ideal.span {d}) ((u' : Matrix ι ι S) i j) =
          (1 : Matrix ι ι (S ⧸ Ideal.span {d})) i j := h2
      rw [h2', Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    exact Ideal.mem_span_singleton'.1 h3
  choose a ha using hent
  refine ⟨fun i j => (a i j : R), fun i j => (a i j).2, ?_⟩
  ext i j
  have h4 := congrArg (fun s : S => (s : R)) (ha i j)
  push_cast at h4
  show S.subtype ((u' : Matrix ι ι S) i j) = (1 : Matrix ι ι R) i j + (d : R) * (a i j : R)
  rw [Subring.coe_subtype, Matrix.one_apply]
  rw [Matrix.one_apply] at h4
  split_ifs at h4 ⊢ <;> simp at h4 ⊢ <;> linear_combination -h4

end Generic

end PI.UnitaryGroupMassFormula.InHHClassFin
