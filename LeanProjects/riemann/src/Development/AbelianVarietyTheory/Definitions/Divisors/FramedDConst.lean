import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HoweD

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}

variable (F) in

abbrev TensD (P Q R S : InfinitePlace F → ℕ) : Type := ⨂[ℂ] w : InfinitePlace F, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)

def FramedD (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) : Prop :=
  a * b = Complex.I ∧ (∀ w, IsFrame (a • JA.map (piInf (τ w))) (A w)) ∧ ∀ w, IsFrame (b • JB.map (piInf (τ w))) (C w)

def IsFockMapD (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) : Prop :=
  Function.Injective Φ ∧ ∀ u : Matrix α β (AE F E), At (evI F) u →
    ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      ∀ T, SD (fun t => d.rho ψ (realAd F t • u)) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))

def IsGenD (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)}
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (γ : Multiplicative ℝ →* UG (cA σ) J) (Y : ∀ w : InfinitePlace F, Mat (R w) (S w)) : Prop :=
  ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w =
    C w * NormedSpace.exp (t • Y w)

def ActsByD (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} {r s : InfinitePlace F → ℕ}
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (r w) (s w)) ℂ) (om : UG (cA σ) J →* Module.End ℂ ((κ → AF F) → ℂ))
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (act : ∀ w, Mat (r w) (s w) →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (c : InfinitePlace F → ℂ) : Prop :=
  ∀ γ ∈ RLines σ J, ∀ Y, IsGenD τ C γ Y → ∀ T, SD (fun t => om (γ (Multiplicative.ofAdd t))) (Φ T)
    (Φ (sumPl (fun w => act w (Y w) + (c w * (Y w).trace) • 1) T))

end Adelic

end GlobalTheory.HoweD

end
