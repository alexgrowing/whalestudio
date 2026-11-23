import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudDefs
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def intO (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K] (k : ℕ) (ν : Fin k → ℕ) :
    Submodule O (MvPolynomial (Fin k × Fin k) K) :=
  Submodule.map (mapAlgHom (Algebra.ofId O K)).toLinearMap (dualWeyl O k k ν)

def Row0 {K : Type} [CommRing K] {k : ℕ} (f : MvPolynomial (Fin (k + 1) × Fin (k + 1)) K) (d : ℕ) : Prop :=
  ∀ u, coeff u f ≠ 0 → rowDeg u 0 = d

def ContractionStandardLattice : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (mm : ℕ), 1 ≤ mm → ∀ (a ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ), Antitone lam →
    lam 0 = (P : ℤ) + ccl → lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl) →
    (∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) → 2 * ccl ≤ 8 * a →
    ∃ abelian₂ : MvPolynomial (Bool × (Fin (mm + 1 + 1) × Fin (mm + 1 + 1))) R.Kf →ₗ[R.Kf]
        MvPolynomial (Fin (mm + 1 + 1) × Fin (mm + 1 + 1)) R.Kf,
      (∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
        ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
          abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
            dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)))) ∧
      (∀ g : Matrix (Fin (mm + 1 + 1)) (Fin (mm + 1 + 1)) R.Kf, IsUnit g.det →
        ∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
        ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
          abelian₂ (blockEmb R.Kf true (rowAct R.Kf g v) * blockEmb R.Kf false (rowAct R.Kf g t)) =
            rowAct R.Kf g (abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t))) ∧
      (∀ v ∈ intO R.O (mm + 1 + 1) (nuOf lam),
        ∀ t ∈ intO R.O (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
          abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
            intO R.O (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)))) ∧
      ∃ (nb : ℕ) (s s' : Fin nb → MvPolynomial (Fin (mm + 1 + 1) × Fin (mm + 1 + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim mm (fun j => lam j.castSucc.succ) ∧ (∀ b, ka b ≤ ⌈kappaOneExponent p a (mm + 1)⌉₊) ∧
        (∀ b, s b ∈ intO R.O (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)) ∧ Row0 (s b) (2 * ccl)) ∧
        (∀ a', s' a' ∈ intO R.O (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) ∧ Row0 (s' a') (2 * ccl)) ∧
        ∀ a' b, ∀ F ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) P Q)),
          abelian₂ (blockEmb R.Kf true (F * s b) * blockEmb R.Kf false (s' a')) =
            if a' = b then ((p : R.Kf) ^ ka b) •
              (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl))) * F) else 0

end Formalism.MainNotions.flipOneThree.Pf

end
