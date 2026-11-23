import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.DetProdCells

def cellFirst (u v : ℕ) : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin 1) (Fin (u + v))) :=
  ⟨fun i j => cond i (cond j v 0) (cond j u 1), by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · cases i
      · show (∑ j : Bool, cond j u 1) = Fintype.card (Fin (u + 1))
        simp [Fintype.sum_bool, add_comm]
      · show (∑ j : Bool, cond j v 0) = Fintype.card (Fin v)
        simp [Fintype.sum_bool]
    · cases j
      · show (∑ i : Bool, cond i 0 1) = Fintype.card (Fin 1)
        simp [Fintype.sum_bool]
      · show (∑ i : Bool, cond i v u) = Fintype.card (Fin (u + v))
        simp [Fintype.sum_bool, add_comm]⟩

def cellSecond (u v : ℕ) (hv : 1 ≤ v) : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin 1) (Fin (u + v))) :=
  ⟨fun i j => cond i (cond j (v - 1) 1) (cond j (u + 1) 0), by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · cases i
      · show (∑ j : Bool, cond j (u + 1) 0) = Fintype.card (Fin (u + 1))
        simp [Fintype.sum_bool]
      · show (∑ j : Bool, cond j (v - 1) 1) = Fintype.card (Fin v)
        simp [Fintype.sum_bool]; omega
    · cases j
      · show (∑ i : Bool, cond i 1 0) = Fintype.card (Fin 1)
        simp [Fintype.sum_bool]
      · show (∑ i : Bool, cond i (v - 1) (u + 1)) = Fintype.card (Fin (u + v))
        simp [Fintype.sum_bool]; omega⟩

theorem eq_cellFirst_or (u v : ℕ) (b : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin 1) (Fin (u + v)))) :
    b = cellFirst u v ∨ ∃ hv : 1 ≤ v, b = cellSecond u v hv := by
  obtain ⟨b, h1, h2⟩ := b
  have r0 : b false true + b false false = u + 1 := by
    have := h1 false; simp only [Fintype.sum_bool] at this
    change _ = Fintype.card (Fin (u + 1)) at this; simpa using this
  have r1 : b true true + b true false = v := by
    have := h1 true; simp only [Fintype.sum_bool] at this
    change _ = Fintype.card (Fin v) at this; simpa using this
  have c0 : b true false + b false false = 1 := by
    have := h2 false; simp only [Fintype.sum_bool] at this
    change _ = Fintype.card (Fin 1) at this; simpa using this
  have c1 : b true true + b false true = u + v := by
    have := h2 true; simp only [Fintype.sum_bool] at this
    change _ = Fintype.card (Fin (u + v)) at this; simpa using this
  rcases Nat.lt_or_ge (b false false) 1 with h | h
  · right
    refine ⟨by omega, Subtype.ext (funext fun i => funext fun j => ?_)⟩
    cases i <;> cases j <;> simp [cellSecond] <;> omega
  · left
    refine Subtype.ext (funext fun i => funext fun j => ?_)
    cases i <;> cases j <;> simp [cellFirst] <;> omega

section Generic

variable {G H V X Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

theorem sub_smul_mem_of_equiv {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) {τ : Representation ℂ G X}
    (φ : (subQuot S T).Equiv τ) (g : G) (c : ℂ) (hτ : ∀ x, τ g x = c • x) :
    ∀ w ∈ S.toSubmodule, ρ g w - c • w ∈ T.toSubmodule := by
  intro w hw
  let x : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype := Submodule.Quotient.mk ⟨w, hw⟩
  have hq : subQuot S T g x = c • x := by
    apply φ.toLinearEquiv.injective
    have h1 : φ.toLinearEquiv (subQuot S T g x) = τ g (φ.toLinearEquiv x) :=
      Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g x
    rw [h1, hτ]
    exact (φ.toLinearEquiv.map_smul _ _).symm
  have h2 := (Submodule.Quotient.eq _).1 (show
      (Submodule.Quotient.mk (S.toRepresentation g ⟨w, hw⟩) :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) =
        Submodule.Quotient.mk (c • (⟨w, hw⟩ : S.toSubmodule)) from hq)
  exact h2

theorem smul_of_equiv {σ : Representation ℂ G V} {τ : Representation ℂ G X} (φ : σ.Equiv τ) (g : G) (c : ℂ)
    (hτ : ∀ x, τ g x = c • x) : ∀ x, σ g x = c • x := by
  intro x
  apply φ.toLinearEquiv.injective
  have h1 : φ.toLinearEquiv (σ g x) = τ g (φ.toLinearEquiv x) :=
    Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g x
  rw [h1, hτ]
  exact (φ.toLinearEquiv.map_smul _ _).symm

def compEquiv' {ρ : Representation ℂ G V} {σ : Representation ℂ G X} (φ : ρ.Equiv σ) (s : H →* G) :
    Representation.Equiv (ρ.comp s) (σ.comp s) :=
  .mk φ.toLinearEquiv fun h => φ.isIntertwining' (s h)

def pullSub {ρ : Representation ℂ G V} (s : H →* G) (S : Subrepresentation ρ) : Subrepresentation (ρ.comp s) :=
  ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (s h) hv⟩

def pullSubQuotEquiv {ρ : Representation ℂ G V} (s : H →* G) (S T : Subrepresentation ρ) :
    Representation.Equiv (subQuot (pullSub s S) (pullSub s T)) ((subQuot S T).comp s) :=
  .mk (LinearEquiv.refl ℂ _) fun h => LinearMap.ext fun x => by
    induction x using Submodule.Quotient.induction_on
    rfl

theorem assemble (ρ : Representation ℂ G V) (s : H →* G) {N : ℕ} (S : Fin (N + 1) → Subrepresentation ρ)
    (hmono : Monotone S) (h0 : S 0 = ⊥) (htop : S (Fin.last N) = ⊤) (τ : Representation ℂ H X) (z : H) (c : ℂ)
    (t₀ : Fin N) (h1 : Nonempty (Representation.Equiv ((subQuot (S t₀.succ) (S t₀.castSucc)).comp s) τ))
    (h2 : ∀ t, t ≠ t₀ → ∀ x, subQuot (S t.succ) (S t.castSucc) (s z) x = c • x) :
    ∃ S' : Fin (N + 1) → Subrepresentation (ρ.comp s), Monotone S' ∧ S' 0 = ⊥ ∧ S' (Fin.last N) = ⊤ ∧
      ∃ t₀ : Fin N, Nonempty ((subQuot (S' t₀.succ) (S' t₀.castSucc)).Equiv τ) ∧
        ∀ t, t ≠ t₀ → ∀ w ∈ (S' t.succ).toSubmodule, ρ.comp s z w - c • w ∈ (S' t.castSucc).toSubmodule := by
  refine ⟨fun t => pullSub s (S t), fun a b hab x hx => hmono hab hx, ?_, ?_, t₀, ?_, ?_⟩
  · exact Subrepresentation.ext (show (S 0).toSubmodule = _ by rw [h0]; rfl)
  · exact Subrepresentation.ext (show (S (Fin.last N)).toSubmodule = _ by rw [htop]; rfl)
  · obtain ⟨φ⟩ := h1
    exact ⟨(pullSubQuotEquiv s _ _).trans φ⟩
  · intro t ht w hw
    exact sub_smul_mem_of_equiv (pullSub s (S t.succ)) (pullSub s (S t.castSucc))
      (pullSubQuotEquiv s _ _) z c (h2 t ht) w hw

end Generic

end GlobalTheory.DetProdCells
