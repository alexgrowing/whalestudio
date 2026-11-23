import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective

noncomputable section

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.LeafTerm

variable {C : Type} [Field C]

def KerLe (V : VF C) {σ τ : Type} [Fintype τ] (M : σ → τ → C) (r : ℕ) : Prop :=
  ∀ (N : ℕ) (y : Fin N → τ → C), (∀ ν t, V.Ge 0 (y ν t)) →
    (∀ ν s, V.MM (∑ t, M s t * y ν t)) → IndepMod V y → N ≤ r

def Wt (V : VF C) {σ : Type} (ρ : σ → ℝ) (w : ℝ) (f : MvPowerSeries σ C) : Prop :=
  ∀ α : σ →₀ ℕ, ((w - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤
    V.v (MvPowerSeries.coeff α f)

def lin {ι I : Type} [Fintype ι] (e : ι → I → C) : I → MvPowerSeries ι C :=
  fun x => ∑ c : ι, e c x • (MvPowerSeries.X c : MvPowerSeries ι C)

def psi {I : Fin 2 → Type} (g : Fin 2) {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) : WV I → MvPowerSeries (ι ⊕ ι') C :=
  fun w => (∑ c : ι, toW g (e c) w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
    ∑ b : ι', toW (1 - g) (v' b) w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)

section Chain

variable {Z I J : Type} [Fintype I]

def slots (D : Formalism.BaseCaseIdentities.Data C Z I) (s : ℕ) : Finset I :=
  Finset.univ.filter fun c => D.lev c = s ∧ s < Formalism.BaseCaseIdentities.Kn D.i

def piM (D : Formalism.BaseCaseIdentities.Data C Z I) (s : ℕ) : I → Z → C :=
  Nat.rec (motive := fun _ => I → Z → C) (fun c j => if D.ι j = c then 1 else 0)
    (fun s p e j => ∑ c ∈ slots D s, (D.l : C) * D.al c 2 e * p c j ^ (D.l ^ 2)) s

variable [Fintype J] {V : VF C} {d : ℕ} {X : Cart V d I J}

def phiT (S : Sys X) (D : Formalism.BaseCaseIdentities.Data C Z I) (j : Z) (κ : J) : C :=
  (-1) ^ (Formalism.BaseCaseIdentities.s0 D.i + 1) * ∑ c ∈ slots D (Formalism.BaseCaseIdentities.s0 D.i),
    piM D (Formalism.BaseCaseIdentities.s0 D.i) c j ^ D.l * ((D.l : C) * S.be c 1 κ)

def Adapted (S : Sys X) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ) : Prop :=
  D.v = V.v ∧ D.l = V.l ∧ D.i = i ∧
    (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x) ∧
    (∀ c, D.lev c < Formalism.BaseCaseIdentities.Kn i → X.ty (Sum.inl c) = a + ((2 * D.lev c : ℕ) : ZMod d))

theorem al_zero (S : Sys X) (c x : I) : S.al c 0 x = S.tan c x := by
  simp [Sys.al, (S.curve c).2.1]

theorem tan_int (S : Sys X) (c x : I) : V.Ge 0 (S.tan c x) := by
  rw [← al_zero]
  exact X.t2 _ (S.curve c).1 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) _

variable {S : Sys X} {D : Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d} {i : ℕ}

theorem Adapted.good (h : Adapted S D a i) {c : I} (hc : D.good c) :
    X.Good (X.ty (Sum.inl c)) (S.tan c) (S.cur c) := by
  refine ⟨S.curve c, fun x => ?_⟩
  have := h.2.2.2.1 c 1 x le_rfl
  simpa [D.al_one c hc, Sys.al] using this

end Chain

end GlobalTheory.LeafTerm
