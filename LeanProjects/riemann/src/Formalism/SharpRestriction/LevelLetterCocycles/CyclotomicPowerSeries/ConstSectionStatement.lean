import Mathlib

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

def RhoExistsStatement : Prop :=
  ∀ (O S : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing S] [Algebra O S]
    (P : Polynomial O), P.IsDistinguishedAt (maximalIdeal O) → ∀ x : PowerSeries S,
    constantCoeff (Polynomial.aeval x P) = 0 → ∃ ρ : PowerSeries O →ₐ[O] PowerSeries S, ρ X = x

def RhoUniqueStatement : Prop :=
  ∀ (O S : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing S] [Algebra O S]
    (P : Polynomial O), P.IsDistinguishedAt (maximalIdeal O) →
    ∀ ρ ρ' : PowerSeries O →ₐ[O] PowerSeries S, ρ X = ρ' X →
    constantCoeff (Polynomial.aeval (ρ X) P) = 0 → ρ = ρ'

def RhoComplStatement : Prop :=
  ∀ (O LL S : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL] [CommRing S] [Algebra LL S] [Algebra O S] [IsScalarTower O LL S]
    (P : Polynomial O), P.IsDistinguishedAt (maximalIdeal O) → ∀ ρ : PowerSeries O →ₐ[O] PowerSeries S,
    (∃ w : (PowerSeries S)ˣ, ρ (P : PowerSeries O) = (w : PowerSeries S) * X) →
    (∀ r : Polynomial LL, Polynomial.aeval (constantCoeff (ρ X)) r = 0 → P.map (algebraMap O LL) ∣ r) →
    ∀ (k : ℕ) (a : PowerSeries O), (X : PowerSeries S) ^ k ∣ ρ a → (P : PowerSeries O) ^ k ∣ a

def RhoDenseStatement : Prop :=
  ∀ (O LL S : Type) [CommRing O] [Field LL] [Algebra O LL] [CommRing S] [Algebra LL S] [Algebra O S]
    [IsScalarTower O LL S] (p : PowerSeries O) (ρ : PowerSeries O →ₐ[O] PowerSeries S),
    (∃ w : (PowerSeries S)ˣ, ρ p = (w : PowerSeries S) * X) →
    Algebra.adjoin LL {constantCoeff (ρ X)} = ⊤ →
    ∀ (k : ℕ) (f : PowerSeries S), ∃ g ∈ Submodule.span LL (Set.range ρ), (X : PowerSeries S) ^ k ∣ f - g

def RhoUnitStatement : Prop :=
  ∀ (O S : Type) [CommRing O] [CommRing S] [Algebra O S] (ρ : PowerSeries O →ₐ[O] PowerSeries S)
    (p a : PowerSeries O) (c : O), constantCoeff (ρ p) = 0 → IsUnit (algebraMap O S c) →
    C c ∈ Ideal.span {p, a} → IsUnit (ρ a)

def PsCoprimeStatement : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ) (φ : PowerSeries O →ₐ[O] PowerSeries O),
    (X * (X + C (l : O)) : PowerSeries O) ∣ φ X →
    (∀ s : ℕ, (C (l : O) : PowerSeries O) ∈ Ideal.span {(⇑φ)^[s] (X + C (l : O)), X}) ∧
    ∀ s s' : ℕ, s ≠ s' →
      (C (l : O) : PowerSeries O) ∈ Ideal.span {(⇑φ)^[s] (X + C (l : O)), (⇑φ)^[s'] (X + C (l : O))}

def CycloDistStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (l s : ℕ), l.Prime → (l : O) ∈ maximalIdeal O →
    ((Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1)).IsDistinguishedAt (maximalIdeal O)

def CycloSimpleStatement : Prop :=
  ∀ (LL S : Type) [Field LL] [CharZero LL] [CommRing S] [Algebra LL S] (m : ℕ), 0 < m → ∀ (ζ : S) (E : PowerSeries S),
    Polynomial.aeval ζ (Polynomial.cyclotomic m LL) = 0 → constantCoeff E = 1 → derivative S E = E →
    ∃ w : (PowerSeries S)ˣ, Polynomial.aeval (C ζ * E) (Polynomial.cyclotomic m LL) = (w : PowerSeries S) * X

def ExpRescaleStatement : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra ℚ S] (E : PowerSeries S), constantCoeff E = 1 → derivative S E = E →
    E = PowerSeries.exp S ∧ ∀ a : ℕ, E ^ a = rescale (a : S) E

def RhoFrobStatement : Prop :=
  ∀ (O S : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing S] [Algebra O S]
    [Algebra ℚ S] (l j m : ℕ), l.Prime → (l : O) ∈ maximalIdeal O →
    ∀ (φ : PowerSeries O →ₐ[O] PowerSeries O), φ X = (1 + X) ^ l - 1 →
    ∀ (ζ : S), ζ ^ (l ^ m) = 1 → ∀ ρ ρ' : PowerSeries O →ₐ[O] PowerSeries S,
    1 + ρ X = C ζ * PowerSeries.exp S → 1 + ρ' X = C (ζ ^ (l ^ j)) * PowerSeries.exp S →
    ∀ a, ρ ((⇑φ)^[j] a) = rescale ((l : S) ^ j) (ρ' a)

def DescendDvdStatement : Prop :=
  ∀ (O : Type) [CommRing O] (ι : PowerSeries O →ₐ[O] PowerSeries O) (m : ℕ), 0 < m →
    (∃ w : (PowerSeries O)ˣ, ι X = (w : PowerSeries O) * X ^ m) →
    Function.Injective ι ∧ ∀ p a : PowerSeries O, ι p ∣ ι a → p ∣ a

def PiSeriesStatement : Prop :=
  ∀ (LL ι : Type) [Field LL],
    (∀ f : ι → PowerSeries LL, ∃! F : PowerSeries (ι → LL), ∀ i, PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F = f i) ∧
    ∀ F : PowerSeries (ι → LL),
      (∀ k : ℕ, (X : PowerSeries (ι → LL)) ^ k ∣ F ↔
        ∀ i, (X : PowerSeries LL) ^ k ∣ PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F) ∧
      (IsUnit F ↔ ∀ i, IsUnit (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F))

def SplitComplStatement : Prop :=
  ∀ (O LL : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Field LL] [CharZero LL] [Algebra O LL] [IsFractionRing O LL] (l s : ℕ), l.Prime → (l : O) ∈ maximalIdeal O →
    (∃ ζ₀ : LL, IsPrimitiveRoot ζ₀ (l ^ (s + 1))) → ∀ ρ : LL → (PowerSeries O →ₐ[O] PowerSeries LL),
    (∀ ζ, IsPrimitiveRoot ζ (l ^ (s + 1)) → 1 + ρ ζ X = C ζ * PowerSeries.exp LL) →
    ∀ (k : ℕ) (a : PowerSeries O), (∀ ζ, IsPrimitiveRoot ζ (l ^ (s + 1)) → (X : PowerSeries LL) ^ k ∣ ρ ζ a) →
    (((Polynomial.cyclotomic (l ^ (s + 1)) O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) ^ k ∣ a

def SplitDenseStatement : Prop :=
  ∀ (O LL : Type) [CommRing O] [IsDomain O] [Field LL] [CharZero LL] [Algebra O LL] [IsFractionRing O LL]
    (R : Finset LL), (∀ ζ ∈ R, ζ ≠ 0) → ∀ ρ : LL → (PowerSeries O →ₐ[O] PowerSeries LL),
    (∀ ζ ∈ R, 1 + ρ ζ X = C ζ * PowerSeries.exp LL) →
    ∀ (k : ℕ) (f : LL → PowerSeries LL), ∃ (c : O) (a : PowerSeries O), c ≠ 0 ∧
      ∀ ζ ∈ R, (X : PowerSeries LL) ^ k ∣ ρ ζ a - C (algebraMap O LL c) * f ζ

def GammaBijStatement : Prop :=
  ∀ (LL : Type) [Field LL] (r : ℕ) (g : PowerSeries LL →ₐ[LL] PowerSeries LL) (w : PowerSeries LL),
    g X = X * w → (∀ k : ℕ, 0 < k → constantCoeff w ^ k ≠ 1) →
    ∀ G : Matrix (Fin r) (Fin r) (PowerSeries LL), G.map constantCoeff = 1 →
    ∀ z : Fin r → PowerSeries LL, (∀ i, constantCoeff (z i) = 0) →
    ∃! v : Fin r → PowerSeries LL, (∀ i, constantCoeff (v i) = 0) ∧ G.mulVec (fun i => g (v i)) - v = z

def HFrameStatement : Prop :=
  ∀ (LL : Type) [Field LL] (r : ℕ) (g : PowerSeries LL →ₐ[LL] PowerSeries LL) (w : PowerSeries LL),
    g X = X * w → (∀ k : ℕ, 0 < k → constantCoeff w ^ k ≠ 1) →
    ∀ G : Matrix (Fin r) (Fin r) (PowerSeries LL), G.map constantCoeff = 1 →
    (∃! H : Matrix (Fin r) (Fin r) (PowerSeries LL), H.map constantCoeff = 1 ∧ G * H.map g = H) ∧
    ∀ H : Matrix (Fin r) (Fin r) (PowerSeries LL), H.map constantCoeff = 1 → G * H.map g = H →
      IsUnit H ∧ ∀ v : Fin r → PowerSeries LL, G.mulVec (fun i => g (v i)) = v →
        v = H.mulVec fun i => C (constantCoeff (v i))

def FrameMapStatement : Prop :=
  ∀ (LL : Type) [Field LL] (r r' : ℕ) (g f : PowerSeries LL →ₐ[LL] PowerSeries LL) (w : PowerSeries LL),
    g X = X * w → (∀ k : ℕ, 0 < k → constantCoeff w ^ k ≠ 1) → constantCoeff (f X) = 0 →
    (∀ a, f (g a) = g (f a)) →
    ∀ (G H : Matrix (Fin r) (Fin r) (PowerSeries LL)) (G' H' : Matrix (Fin r') (Fin r') (PowerSeries LL))
      (F : Matrix (Fin r') (Fin r) (PowerSeries LL)),
    G.map constantCoeff = 1 → G'.map constantCoeff = 1 → H.map constantCoeff = 1 → H'.map constantCoeff = 1 →
    G * H.map g = H → G' * H'.map g = H' → G' * F.map g = F * G.map f →
    F * H.map f = H' * (F.map constantCoeff).map C

def EvExtendStatement : Prop :=
  ∀ (O LL S : Type) [CommRing O] [Field LL] [Algebra O LL] [CommRing S] [Algebra LL S] [Algebra O S]
    [IsScalarTower O LL S] (ψ : PowerSeries O →ₐ[O] PowerSeries S), constantCoeff (ψ X) = 0 →
    ∃! ev : PowerSeries LL →ₐ[LL] PowerSeries S, ∀ a, ev (PowerSeries.map (algebraMap O LL) a) = ψ a

def ConstSectionStatement : Prop :=
  ∀ (LL S : Type) [Field LL] [CommRing S] [Algebra LL S] (r : ℕ) (g : PowerSeries LL →ₐ[LL] PowerSeries LL)
    (τ : PowerSeries S →ₐ[LL] PowerSeries S) (ev : PowerSeries LL →ₐ[LL] PowerSeries S),
    constantCoeff (ev X) = 0 → constantCoeff (g X) = 0 → constantCoeff (τ (ev X)) = 0 → ev (g X) = τ (ev X) →
    ∀ G H : Matrix (Fin r) (Fin r) (PowerSeries LL), H.map constantCoeff = 1 → G * H.map g = H →
    (∀ a, ev (g a) = τ (ev a)) ∧ IsUnit (H.map ev) ∧ (H.map ev).map constantCoeff = 1 ∧
      G.map ev * (H.map ev).map τ = H.map ev

end LevelStatements.Lv
