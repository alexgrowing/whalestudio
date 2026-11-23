import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

variable {R : Type} [CommRing R] {X : Scheme.{0}}

abbrev ext (s : X ⟶ Sp R) (J : Ideal R) (U : X.Opens) : Ideal Γ(X, U) :=
  J.map (GlobalTheory.SmallExtLift.cst s U)

def tr (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) :
    Γ(X, V a ⊓ V b) :=
  rs X (inf_le_inf (hj a) (hj b)) (M.g (j a) (j b)).val

def trInv (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) :
    Γ(X, V a ⊓ V b) :=
  rs X (inf_le_inf (hj a) (hj b)) (M.g (j a) (j b))⁻¹.val

theorem tr_mul_trInv (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) : tr M V j hj a b * trInv M V j hj a b = 1 := by
  simp only [tr, trInv, ← map_mul, Units.mul_inv, map_one]

section Triple

variable {A : Type} (V : A → X.Opens) (a b d : A)

theorem le₁₂ : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b := inf_le_left

theorem le₂₃ : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d := le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem le₁₃ : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d := le_inf (inf_le_left.trans inf_le_left) inf_le_right

end Triple

theorem tr_cocycle {M : LB X} (hM : M.IsLB) {A : Type} (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (a b d : A) :
    rs X (le₁₂ V a b d) (tr M V j hj a b) * rs X (le₂₃ V a b d) (tr M V j hj b d) =
      rs X (le₁₃ V a b d) (tr M V j hj a d) := by
  have h := congrArg (fun u => rs X (le_inf (le_inf
    ((inf_le_left.trans inf_le_left).trans (hj a)) ((inf_le_left.trans inf_le_right).trans (hj b)))
    (inf_le_right.trans (hj d)) : V a ⊓ V b ⊓ V d ≤ M.U (j a) ⊓ M.U (j b) ⊓ M.U (j d)) u.val)
    (hM.cocycle (j a) (j b) (j d))
  have e : ∀ {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ), ((res h u : Γ(X, W)ˣ) : Γ(X, W)) = rs X h u :=
    fun _ _ => rfl
  simp only [Units.val_mul, map_mul, e, GlobalTheory.AbLaw.rs_rs] at h
  simp only [tr, GlobalTheory.AbLaw.rs_rs]
  exact h

def DepSt : Prop :=
  ∀ (k : Type) [Field k] (Y : Scheme.{0}) (s₀ : Y ⟶ Sp k), Y.IsSeparated → ∀ n r : ℕ,
    Module.Finite k (HO1 s₀) → Module.finrank k (HO1 s₀) ≤ n → n < r →
    ∀ (A : Type) (V : A → Y.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ α : Fin r → ∀ a b, Γ(Y, V a ⊓ V b),
      (∀ i a b d, rs Y (le₁₂ V a b d) (α i a b) + rs Y (le₂₃ V a b d) (α i b d) =
        rs Y (le₁₃ V a b d) (α i a d)) →
      ∃ (c : Fin r → k) (ψ : ∀ a, Γ(Y, V a)), c ≠ 0 ∧ ∀ a b,
        ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * α i a b =
          rs Y inf_le_left (ψ a) - rs Y inf_le_right (ψ b)

end GlobalTheory.CompanionTheory.FewEq
