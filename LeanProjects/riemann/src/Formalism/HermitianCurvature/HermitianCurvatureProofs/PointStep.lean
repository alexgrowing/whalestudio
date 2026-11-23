import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.StatementU

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def mc {k ρ m : ℕ} (e : ρ + 1 = m) (c : ℂ) (γ : B.Mat k ρ) : B.Mat k m :=
  D.castM e (D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ))

def rn1 {k ρ m : ℕ} (e : ρ + 1 = m) (x : U.RC k 1 ρ) : B.Mat k m :=
  D.castM e (D.castM (Nat.add_comm 1 ρ) (U.Rn k 1 ρ x))

def lev1 {k ρ m : ℕ} (e : ρ + 1 = m) (y : B.Mat k ρ) : B.Mat k m :=
  D.castM e (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y))

def JFStep : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (B1 : B.RealPlaceData k m Wp Wq) (B0 : B.RealPlaceData k ρ Wp Wq),
    B1.z = D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z)) →
    B1.z' = D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z')) →
    (∀ y : B.Mat k ρ, B0.π y = B1.π (lev1 e y)) → (∀ y : B.Mat k ρ, B0.π' y = B1.π' (lev1 e y)) →
    B1.μW Set.univ = 1 → B1.μW' Set.univ = 1 → B0.μW Set.univ = 1 → B0.μW' Set.univ = 1 →
    B1.μN = D.muN k m → B0.μN = D.muN k ρ →
    ∀ (f1 : B.Mat k m → (Wq →L[ℂ] Wp)) (f0 : B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℂ), c ≠ 0 → KB.CptCoef B1 f1 →
    (∀ γ ∈ B.GV k ρ, f0 γ = ∫ xx : U.RC k 1 ρ × U.RC k 1 ρ,
        (psi k m B1.z cStd (rn1 e xx.1) * star (psi k m B1.z' cStd (rn1 e xx.2))) •
          f1 ((rn1 e xx.1)⁻¹ * mc e c γ * rn1 e xx.2) ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))) →
    ∀ γ ∈ B.GV k ρ, γ ∈ Q.OmPlus k ρ B0.z B0.z' →
      B.JF B0 f0 γ = B.JF B1 f1 (mc e c γ)

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def PointStep : Prop :=
  ∀ (k j ρ : ℕ) (σ : Equiv.Perm (Fin j)) (d : Fin j → ℂ), (∀ i, d i ≠ 0) → ∀ (c : ℂ), c ≠ 0 →
    ∀ (zA zA' : Fin (2 * (j + 1 + ρ) + k + 1) → ℂ), inWb k (j + 1 + ρ) zA → inWb k (j + 1 + ρ) zA' →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : B.Mat k (j + 1 + ρ) → E)
      (γ : B.Mat k ρ),
      Integrable (fun ξ : U.Xi k j 1 ρ σ =>
          U.psiStar k ρ σ zA zA' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ)) (U.muXi k j 1 ρ σ) →
      U.PhiFun k ρ σ d zA zA' F (fun _ _ => c) γ =
        ∫ yy : U.RC k 1 ρ × U.RC k 1 ρ,
          (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA)) cStd
              (U.Rn k 1 ρ yy.1) *
            star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA')) cStd
              (U.Rn k 1 ρ yy.2))) •
          U.PhiFun (p := j) (s := 0) k (1 + ρ) σ d (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA)
            (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA') (D.castF (by omega : j + (1 + ρ) = j + 1 + ρ) F)
            (fun a => a.elim0)
            ((U.Rn k 1 ρ yy.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ yy.2)
          ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))

end Formalism.FourierDecayAlt.P.PBH
