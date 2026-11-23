import Mathlib
import Formalism.LocalRingCardinality.DataTheta

noncomputable section
namespace GlobalTheory.FockAlg
open Formalism.BasicNotions.TH

def IsFockIP {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) : Prop :=
  ∀ α β : σ →₀ ℕ, inner ℂ (ι (MvPolynomial.monomial α 1)) (ι (MvPolynomial.monomial β 1)) =
    if α = β then α.prod (fun _ k => (k.factorial : ℂ)) else 0

def harm1 (p q r s : ℕ) : Set (Pol p q r s) :=
  {P | ∀ Z : Mat r s, IsPC Z → minusPart (fockAct2 p q r s Z) P = 0}

def harm2 (p q r s : ℕ) : Set (Pol p q r s) :=
  {P | ∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) P = 0}

def jointHarm (p q r s : ℕ) : Set (Pol p q r s) := harm2 p q r s ∩ harm1 p q r s

def Intw {p q r s : ℕ} (M1 : GKMod p q) (M2 : GKMod r s)
    (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V) : Prop :=
  (∀ X, f ∘ₗ fockAct1 p q r s X = TensorProduct.map (M1.act X) LinearMap.id ∘ₗ f) ∧
  (∀ Y, f ∘ₗ fockAct2 p q r s Y = TensorProduct.map LinearMap.id (M2.act Y) ∘ₗ f)

def genSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (S : Set V) : Submodule ℂ V :=
  sInf {N | S ⊆ N ∧ ∀ Z, ∀ y ∈ N, act Z y ∈ N}

def ConeTypes {p q : ℕ} (M : GKMod p q) (lam : Ix p q → ℚ) : Prop :=
  ∀ (μ : Ix p q → ℚ) v, IsHW M.act μ v →
    ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → lam b < lam a) ∧
      μ = fun c => blattner lam c +
        ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))

theorem J_eq {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) : F.J = jointHarm p q r s := rfl

theorem isIntw_iff {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) (M1 : GKMod p q) (M2 : GKMod r s)
    (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V) : IsIntw F M1 M2 f ↔ Intw M1 M2 f :=
  Iff.rfl

theorem isFockIsometry_of_fockData {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2) : IsFockIP F.ι := by
  intro α β
  exact F.fockIP α β

end GlobalTheory.FockAlg
