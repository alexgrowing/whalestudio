import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

def FlagConcl (v : Valuation C NNReal) (p : ℕ) (M : Submodule R (N → C)) {n : ℕ}
    (b : Module.Basis (Fin n) F N) (σ : MulChar F R) : Prop :=
  ∃ c δ : Fin n → ℕ → R,
    (∀ i s, c i s ≠ 0 ∧
      idealX M (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} ∧
      xIdeal (stepOrderRes M (flagSub b i) (b i)) (σ ^ p ^ s) = Ideal.span {c i s} ∧
      idealD p M (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} ∧
      c i s ^ p = δ i s * c i (s + 1) ∧
      HasLen v R (OmType (stepOrder M (flagSub b i) (b i)) (σ ^ p ^ (s + 1)))
        (v (algebraMap R C (δ i s)))) ∧
    (∀ s, HasLen v R (OmType M (σ ^ p ^ (s + 1))) (∏ i, v (algebraMap R C (δ i s)))) ∧
    ∀ (j s : ℕ), HasLen v R
      (OmType (M.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) (σ ^ p ^ (s + 1)))
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), v (algebraMap R C (δ i s)))

def FlagStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N), FStable F AA.carrier → IsTight v p AA.carrier →
  ∀ (n : ℕ) (b : Module.Basis (Fin n) F N),
    (∀ i : Fin n, GenAF p AA.carrier (flagSub b i).toAddSubgroup) →
  ∀ σ : MulChar F R, IsFund p σ → FlagConcl v p AA.carrier b σ

def PolarisedFlagStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σO : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σO cp → ∀ H : HodgeTateDatum p g v R O σO cp,
    (∀ K : AddSubgroup (Nb p g), GenAF p H.AA.carrier K) →
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p]
      (Nw : Type) [AddCommGroup Nw] [Module F Nw] [Fintype Nw] [DecidableEq Nw]
      (ι : Nw →+ Nb p g) (π : Nb p g →+ Nw), (∀ y, π (ι y) = y) →
      (∀ h ∈ H.AA.carrier, (fun x => h (ι (π x))) ∈ H.AA.carrier) →
      FStable F (H.AA.carrier.map (LinearMap.funLeft R C (ι : Nw → Nb p g))) →
    ∀ (n : ℕ) (b : Module.Basis (Fin n) F Nw) (σ : MulChar F R), IsFund p σ →
      FlagConcl v p (H.AA.carrier.map (LinearMap.funLeft R C (ι : Nw → Nb p g))) b σ

end GlobalTheory.CompanionTheory.Ar.GR
