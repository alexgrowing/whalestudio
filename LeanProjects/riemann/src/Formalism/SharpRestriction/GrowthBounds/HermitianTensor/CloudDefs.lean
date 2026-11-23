import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsRetractionBasis
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DeltaPsiH

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def dualWt {m : ℕ} (mu : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ := fun i => -mu i.rev

def dualW {n' m : ℕ} (lo : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ := fun s => dualWt (lo s)

def famD (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' k : ℕ}
    (gs : Fin n' → Matrix (Fin k) (Fin k) Kf) (c : Kf) : Fin n' → Submodule O (Fin k → Kf) :=
  fun s => colSpan O (gs s * lb_D k 1 c)

def CloudOne : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (mm : ℕ), 1 ≤ mm → ∀ (a ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ), Antitone lam →
    lam 0 = (P : ℤ) + ccl → lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl) →
    (∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) → 2 * ccl ≤ 8 * a →
    ∃ abelian₂ : MvPolynomial (Bool × (Fin (mm + 1 + 1) × Fin (mm + 1 + 1))) R.Kf →ₗ[R.Kf]
        MvPolynomial (Fin (mm + 1 + 1) × Fin (mm + 1 + 1)) R.Kf,
      (∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
        ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
          abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
            dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)))) ∧
      (∀ Λ : Submodule R.O (Fin (mm + 1 + 1) → R.Kf), IsLattice R.O Λ →
        ∀ v ∈ H0 R.O (mm + 1) lam Λ, ∀ t ∈ H0 R.O (mm + 1) (dualWt (lam - wtPQ (mm + 1) P Q)) Λ,
          abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
            H0 R.O (mm + 1) (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)) Λ) ∧
      ∀ g : Matrix (Fin (mm + 1 + 1)) (Fin (mm + 1 + 1)) R.Kf, IsUnit g.det →
        ∃ (nb : ℕ) (z0 : MvPolynomial (Fin (mm + 1 + 1) × Fin (mm + 1 + 1)) R.Kf)
          (s s' : Fin nb → MvPolynomial (Fin (mm + 1 + 1) × Fin (mm + 1 + 1)) R.Kf) (ka : Fin nb → ℕ),
          (nb : ℚ) = weylDim mm (fun j => lam j.castSucc.succ) ∧ (∀ b, ka b ≤ ⌈kappaOneExponent p a (mm + 1)⌉₊) ∧
          (∀ a' b, ∀ F ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) P Q)),
            abelian₂ (blockEmb R.Kf true (F * s b) * blockEmb R.Kf false (s' a')) =
              if a' = b then ((p : R.Kf) ^ ka b) • (z0 * F) else 0) ∧
          ∀ c : R.Kf, c ≠ 0 →
            (c ^ (2 * ccl)) • z0 ∈ H0 R.O (mm + 1) (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) (colSpan R.O (g * lb_D _ 1 c)) ∧
            (¬ ∃ z' ∈ H0 R.O (mm + 1) (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) (colSpan R.O (g * lb_D _ 1 c)),
              (c ^ (2 * ccl)) • z0 = R.w • z') ∧
            (∀ b, (c ^ ccl) • s b ∈ H0 R.O (mm + 1) (lam - wtPQ (mm + 1) P Q) (colSpan R.O (g * lb_D _ 1 c))) ∧
            (∀ a', (c ^ ccl) • s' a' ∈
              H0 R.O (mm + 1) (dualWt (lam - wtPQ (mm + 1) P Q)) (colSpan R.O (g * lb_D _ 1 c)))

def RestCloudLat : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (mm : ℕ), 1 ≤ mm → ∀ (TT : Finset (Fin n')) (a ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ),
    IsBaseWeight TT aw bw ccl lam0 → IsDominant lam0 → (∀ s, s ∉ TT → lam0 s = 0) →
    (∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) → 2 * ccl ≤ 8 * a →
    ∀ (H Hp ze lo lo' : Fin n' → Fin (mm + 1 + 1) → ℤ), H = flatW (mm + 1) A B →
      Hp = flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl) →
      ze = flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) → lo = lam0 - H → lo' = dualW lo →
    ∃ (mH : Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf ze →ₗ[R.Kf] Vsp R.Kf Hp)
      (mU : Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf lo →ₗ[R.Kf] Vsp R.Kf lam0)
      (abelian₂ : Vsp R.Kf lam0 →ₗ[R.Kf] Vsp R.Kf lo' →ₗ[R.Kf] Vsp R.Kf Hp),
      (∀ M : Fin n' → Submodule R.O (Fin (mm + 1 + 1) → R.Kf), (∀ s, IsLattice R.O (M s)) →
        (∀ F ∈ toV H (Hten R.O H M), ∀ z ∈ toV ze (Hten R.O ze M), mH F z ∈ toV Hp (Hten R.O Hp M)) ∧
        (∀ F ∈ toV H (Hten R.O H M), ∀ z ∈ toV lo (Hten R.O lo M), mU F z ∈ toV lam0 (Hten R.O lam0 M)) ∧
        (∀ v ∈ toV lam0 (Hten R.O lam0 M), ∀ z ∈ toV lo' (Hten R.O lo' M), abelian₂ v z ∈ toV Hp (Hten R.O Hp M))) ∧
      ∀ gs : Fin n' → Matrix (Fin (mm + 1 + 1)) (Fin (mm + 1 + 1)) R.Kf, (∀ s, IsUnit (gs s).det) →
        ∃ (nb : ℕ) (z0 : Vsp R.Kf ze) (s : Fin nb → Vsp R.Kf lo) (s' : Fin nb → Vsp R.Kf lo') (ka : Fin nb → ℕ),
          (nb : ℝ) = dimCl TT lam0 ∧ (∀ b, ka b ≤ TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊) ∧
          (∀ a' b F, abelian₂ (mU F (s b)) (s' a') = if a' = b then ((p : R.Kf) ^ ka b) • mH F z0 else 0) ∧
          ∀ c : R.Kf, c ≠ 0 →
            (c ^ Ar 1 ze) • z0 ∈ toV ze (Hten R.O ze (famD R.O gs c)) ∧
            (∀ b, (c ^ Ar 1 lo) • s b ∈ toV lo (Hten R.O lo (famD R.O gs c))) ∧
            (∀ a', (c ^ Ar 1 lo') • s' a' ∈ toV lo' (Hten R.O lo' (famD R.O gs c))) ∧
            (∀ F, mH F ((c ^ Ar 1 ze) • z0) ∈ toV Hp (Hten R.O Hp (famD R.O gs c)) →
              F ∈ toV H (Hten R.O H (famD R.O gs c)))

end Formalism.MainNotions.flipOneThree.Pf

end
