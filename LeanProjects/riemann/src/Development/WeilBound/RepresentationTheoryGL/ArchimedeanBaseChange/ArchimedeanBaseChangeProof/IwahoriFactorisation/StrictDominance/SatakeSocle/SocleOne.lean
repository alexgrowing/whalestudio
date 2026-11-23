import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.SphericalProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def msOne {n : ℕ} (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i)) : Multiset (Segment k) :=
  Finset.univ.val.map fun i =>
    Segment.single (IrrGL.ofChar (ξ i) (isSmoothChar_of_isUnram (hξ i))) (IrrGL.isCusp_ofChar _ _)

variable (k) in

def atUnif {n : ℕ} (ξ : Fin n → kˣ →* ℂˣ) : Fin n → ℂˣ := fun i => ξ i (Zls.unifU k)

def AbsAnti {n : ℕ} (α : Fin n → ℂˣ) : Prop := Antitone fun i => ‖((α i : ℂˣ) : ℂ)‖

def SocleOne : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i)), AbsAnti (atUnif k ξ) →
    ∀ hd : ∑ a, (IrrGL.ofChar (ξ a) (isSmoothChar_of_isUnram (hξ a))).1 = n,
      (∃ x : IrrGL k, x.1 = n ∧ IsL (msOne ξ hξ) x.rep) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
        IsL (msOne ξ hξ) π → IsSocle π (prodIrr (fun a => IrrGL.ofChar (ξ a) (isSmoothChar_of_isUnram (hξ a))) hd)

def LOneSat : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i))
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
      (IsL (msOne ξ hξ) π ↔ HasSatake π (atUnif k ξ))

def ExpSat : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsAdmissible π → π.IsIrreducible →
    ∀ (ξ : Fin n → kˣ →* ℂˣ), (∀ i, IsUnram (ξ i)) → AbsAnti (atUnif k ξ) →
    (∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), v ≠ 0 ∧
      ∀ t : Levi k (fun _ : Fin n => Fin 1),
        v ∈ Module.End.maxGenEigenspace (jac (stdBlocks (fun _ : Fin n => 1) hd) π t) (PositivityTheory.Lbc.torusChar ξ t)) →
    HasSatake π (atUnif k ξ)

def SatExp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ α : Fin n → ℂˣ, HasSatake π α → AbsAnti α →
    ∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), v ≠ 0 ∧
      ∀ t : Levi k (fun _ : Fin n => Fin 1),
        v ∈ Module.End.maxGenEigenspace (jac (stdBlocks (fun _ : Fin n => 1) hd) π t)
          (PositivityTheory.Lbc.torusChar (fun i => unrChar k (α i)) t)

def ProdSph : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (c N : ℕ) (σ : Fin c → IrrGL k) (hd : ∑ a, (σ a).1 = N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ → τ.IsIrreducible → IsSubquotient τ (prodIrr σ hd) →
    IsSpherical τ →
      (∀ a, IsSpherical (σ a).rep) ∧ (∃ β : Fin N → ℂˣ, HasSatake τ β) ∧
      ∀ α : ∀ a, Fin (σ a).1 → ℂˣ, (∀ a, HasSatake (σ a).rep (α a)) →
        ∀ β : Fin N → ℂˣ, HasSatake τ β → Finset.univ.val.map β = ∑ a, Finset.univ.val.map (α a)

end PositivityTheory.SphericalProduct

end
