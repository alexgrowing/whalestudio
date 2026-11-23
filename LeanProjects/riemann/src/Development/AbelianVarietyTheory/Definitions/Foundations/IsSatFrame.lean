import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne

namespace GlobalTheory.FGDepth

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C]

def toE (x : WithTop ℝ) : EReal := (WithBot.some x : WithBot (WithTop ℝ))

def mfact {σ : Type} (α : σ →₀ ℕ) : C := α.prod fun _ n => (n.factorial : C)

def derivAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ α ∈ P.support, P.coeff α * mfact α * coeff α g

def content (v : AddValuation C (WithTop ℝ)) {σ : Type} (P : MvPolynomial σ C) : EReal :=
  ⨅ α ∈ P.support, toE (v (P.coeff α * mfact α))

variable {v : AddValuation C (WithTop ℝ)}

def IsExp {d : ℕ} (G : LogFGL v d) (ex : Fin d → MvPowerSeries (Fin d) C) : Prop :=
  (∀ a, constantCoeff (ex a) = 0) ∧ ∀ a, subst ex (G.lg a) = X a

def expOf {d : ℕ} (G : LogFGL v d) : Fin d → MvPowerSeries (Fin d) C :=
  Classical.epsilon (IsExp G)

def expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) :
    (Σ b, Fin (d b)) → MvPowerSeries (Σ b, ι b) C :=
  fun x => subst (fun e : Fin (d x.1) =>
    ∑ a, u x.1 a e • (X ⟨x.1, a⟩ : MvPowerSeries (Σ b, ι b) C)) (expOf (G x.1) x.2)

def depth {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C) : EReal :=
  ⨅ f : {f : MvPowerSeries (Σ b, Fin (d b)) C // MvIsInt v f},
    toE (v (derivAt0 P (subst (expAlong G u) f.1)))

def detPow (C : Type) [Field C] (i c : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) C :=
  (Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C))) ^ c

def IsSatFrame (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (u : Fin i → Fin d → C) : Prop :=
  (∀ a e, IsIntV v (u a e)) ∧
    ∃ r : Fin i → Fin d, v (Matrix.det (Matrix.of fun a b => u a (r b))) = 0

def detDepth {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C) (c : ℕ) : EReal :=
  depth (fun _ : Fin i => G) (fun _ => u) (detPow C i c)

def IsCharLog {d : ℕ} (G : LogFGL v d) (l : Fin d → C) : Prop :=
  ∃ χ : MvPowerSeries (Fin d) C, MvIsInt v χ ∧
    ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => l e ^ n / (n.factorial : C)

end

end GlobalTheory.FGDepth
