import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleTwistIffAdmissibleUntwisted

noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def cycM (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : (ZMod M)ˣ :=
  open Classical in
  if h : ∃ y : (ZMod M)ˣ, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val then h.choose else 1

def repM (M : ℕ) (y : (ZMod M)ˣ) : Ω ≃ₐ[ℚ] Ω :=
  Classical.epsilon fun s : Ω ≃ₐ[ℚ] Ω => ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val

def topM (l n r N : ℕ) : ℕ := l ^ (r + n) * N

instance topM.neZero (l n r N : ℕ) [Fact l.Prime] [NeZero N] : NeZero (topM l n r N) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (NeZero.ne N)⟩

def Yk4c (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l)
    (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (s : Ω ≃ₐ[ℚ] Ω)
    (y : (ZMod (topM l n r N))ˣ) : Fin 2 → Qbar l :=
  mat W (repM (topM l n r N) y) *ᵥ
    pr (clsB X l n r N x c d k g ((repM (topM l n r N) y)⁻¹ * s * repM (topM l n r N) (y * (cycM (topM l n r N) s)⁻¹)))

def redM (l n r N : ℕ) (y : (ZMod (topM l n r N))ˣ) : (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) N) (ZMod (l ^ r))).toMonoidHom y

def Yk4r (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l)
    (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) :
    (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l :=
  GlobalTheory.KA.push (redM l n r N) (Yk4c X l pr W n r N x c d k g)

def redL (l r : ℕ) (y : (ZMod (l ^ (r + 1)))ˣ) : (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom y

def IsZeta (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∀ r n : ℕ, ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
    Cv n (Y r s y) (Yk4r X l pr W n r N x c d k g s y +
      (mat W s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

def Adm2 {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l)
    (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) (cf : Coef l) : Prop :=
  admitted ι e gN W X pr N x c d gm ∧
    (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ r₀ : (ZMod l)ˣ, ∃ t : (ZMod l)ˣ,
      (![0, 1] : Fin 2 → ZMod l) ᵥ* ((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
        (t : ZMod l) • ![(r₀ : ZMod l), -1]) ∧
    ∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
      (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
      ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

theorem cycM_spec (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω)
    (h : ∃ y : (ZMod M)ˣ, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val) :
    ∀ z : Ω, z ^ M = 1 → s z = z ^ (cycM M s : ZMod M).val := by
  classical
  unfold cycM
  rw [dif_pos h]
  exact h.choose_spec

theorem repM_spec (M : ℕ) (y : (ZMod M)ˣ)
    (h : ∃ s : Ω ≃ₐ[ℚ] Ω, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val) :
    ∀ z : Ω, z ^ M = 1 → (repM M y : Ω ≃ₐ[ℚ] Ω) z = z ^ (y : ZMod M).val :=
  Classical.epsilon_spec h

example : topM 5 1 1 3 = 75 := rfl
example : cycM (Ω := Ω) 1 AlgEquiv.refl = 1 := Subsingleton.elim _ _
example (l r : ℕ) : redL l r 1 = 1 := map_one _

end GlobalTheory.K4
