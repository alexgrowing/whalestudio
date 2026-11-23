import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB (IsFrame)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.TriFrame

def matNorm {C : Type} [NormedField C] {r : ℕ} (M : Matrix (Fin r) (Fin r) C) (i : Fin r) : ℝ :=
  sInf {t | ∃ cf : Fin r → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∀ l, ‖∑ j, cf j * M l j‖ ≤ 1) ∧ t = ‖cf i‖⁻¹}

example {C : Type} [NormedField C] {r : ℕ} (i : Fin r) : matNorm (1 : Matrix (Fin r) (Fin r) C) i = 1 := by
  refine IsLeast.csInf_eq ⟨⟨Pi.single i 1, by simp, fun k hk => by simp [hk.ne'], fun l => ?_, by simp⟩, ?_⟩
  · simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases h : l = i <;> simp [h]
  · rintro _ ⟨cf, h₁, -, h₂, rfl⟩
    have := h₂ i
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    exact (one_le_inv₀ (norm_pos_iff.2 h₁)).2 this

variable {X : Scheme.{0}} {A : X.Opens}

def IsGenOn (A : X.Opens) (L : LB X) (ρ : ∀ k, Γ(X, A ⊓ L.U k)) : Prop :=
  ∀ (k k' : L.ι) (T : X.Opens) (h : T ≤ A ⊓ L.U k) (h' : T ≤ A ⊓ L.U k') (h'' : T ≤ L.U k ⊓ L.U k'),
    resG X h' (ρ k') = resG X h'' (L.g k k').val * resG X h (ρ k)

variable {F : X.Modules} {r : ℕ} {s : Fin r → Γ(F, A)}

def coordIn (hs : IsFrame s) {V : X.Opens} (e : Fin r → Γ(F, V)) (i l : Fin r) : Γ(X, V ⊓ A) :=
  (hs.basis inf_le_right).repr (resM F inf_le_left (e i)) l

def IsTri (hs : IsFrame s) {V : X.Opens} (e : Fin r → Γ(F, V)) : Prop := ∀ i l, i < l → coordIn hs e i l = 0

def Tri (hs : IsFrame s) (L : Fin r → LB X) (ρ : ∀ i k, Γ(X, A ⊓ (L i).U k)) : Prop :=
  ∀ x : X, ∃ (V : X.Opens) (e : Fin r → Γ(F, V)) (k : ∀ i, (L i).ι) (hk : ∀ i, V ≤ (L i).U (k i)),
    x ∈ V ∧ IsFrame e ∧ IsTri hs e ∧
      ∀ i, coordIn hs e i i = resG X (le_inf inf_le_right (inf_le_left.trans (hk i))) (ρ i (k i))

theorem isTri_self (hs : IsFrame s) : IsTri hs s := fun i l h => by
  rw [coordIn, ← hs.basis_apply inf_le_right, Module.Basis.repr_self, Finsupp.single_eq_of_ne h.ne']

def IsRatio {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} (A : B.X.Opens)
    (D : Vert.VertDiv B) (L L' : LB B.X) (ρ : ∀ k, Γ(B.X, A ⊓ L.U k)) (ρ' : ∀ k, Γ(B.X, A ⊓ L'.U k)) : Prop :=
  ∀ x : B.X, ∃ (j : D.M.ι) (k : L.ι) (k' : L'.ι), x ∈ D.M.U j ∧ x ∈ L.U k ∧ x ∈ L'.U k' ∧
    ∀ (T : B.X.Opens) (h₁ : T ≤ B.gen ⊓ D.M.U j) (h₂ : T ≤ A ⊓ L.U k) (h₃ : T ≤ A ⊓ L'.U k'),
      D.eqn j h₁ * resG B.X h₂ (ρ k) = resG B.X h₃ (ρ' k')

end GlobalTheory.TriFrame

end
