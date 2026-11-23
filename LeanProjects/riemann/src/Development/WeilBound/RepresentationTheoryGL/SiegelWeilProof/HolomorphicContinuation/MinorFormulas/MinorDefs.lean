import Mathlib

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP.Mi

variable {R : Type} [CommRing R] {ρ : ℕ}

abbrev Pm (R : Type) [CommRing R] (ρ : ℕ) := MvPolynomial (Fin ρ × Fin ρ) R

def Xm (R : Type) [CommRing R] (ρ : ℕ) : Matrix (Fin ρ) (Fin ρ) (Pm R ρ) := fun a d => X (a, d)

def del (p q : Fin ρ) : Derivation R (Pm R ρ) (Pm R ρ) :=
  mkDerivation R fun ad => (X (ad.1, p) * X (q, ad.2) : Pm R ρ)

def opE (α : R) (p q : Fin ρ) : Pm R ρ →ₗ[R] Pm R ρ :=
  LinearMap.mulLeft R (C α * X (q, p)) + (del p q).toLinearMap

def detE (α : R) : Pm R ρ →ₗ[R] Pm R ρ :=
  ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : R) • (List.finRange ρ).foldr (fun k g => opE α k (σ k) ∘ₗ g) LinearMap.id

def ren {r s : ℕ} (I J : Fin r ↪ Fin s) : Pm R r →ₐ[R] Pm R s := rename fun pq => (J pq.1, I pq.2)

def MComm : Prop := ∀ (R : Type) [CommRing R] (ρ : ℕ) (α : R) (p q p' q' : Fin ρ),
  opE α p q ∘ₗ opE α p' q' = opE α p' q' ∘ₗ opE α p q

def DelDet : Prop := ∀ (R : Type) [CommRing R] (ρ : ℕ) (p q : Fin ρ), del p q (Xm R ρ).det = X (q, p) * (Xm R ρ).det

def RenInt : Prop := ∀ (R : Type) [CommRing R] (r s : ℕ) (I J : Fin r ↪ Fin s) (α : R) (p q : Fin r) (f : Pm R r),
  opE α (I p) (J q) (ren I J f) = ren I J (opE α p q f)

def Core : Prop := ∀ (R : Type) [CommRing R] (ρ : ℕ) (α : R),
  detE α (1 : Pm R ρ) = (∏ i ∈ Finset.range ρ, (C α - (i : Pm R ρ))) * (Xm R ρ).det

def Iter : Prop := ∀ (R : Type) [CommRing R] (ρ : ℕ) (α : R) (N : ℕ),
  (detE α)^[N] (1 : Pm R ρ) = (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (C α + (l : Pm R ρ) - (i : Pm R ρ))) * (Xm R ρ).det ^ N

end PositivityTheory.Rg.Sw.SP.Mi
