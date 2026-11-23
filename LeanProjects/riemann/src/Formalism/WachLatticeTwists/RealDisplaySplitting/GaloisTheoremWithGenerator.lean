import Formalism.WachLatticeTwists.RealDisplaySplitting.Statement

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (bcChar PrimHyp AbsIrr BlockDiagonalIrreducibleAt ChainHyp ChainAB blockPoly)

def GenHyp (ℓ : ℕ) (O : Type) [CommRing O] {G : Type} [Group G] (ε : G →* Oˣ) (g₀ : G) (s₀ : ℕ) (y : Oˣ) : Prop :=
  ¬ IsUnit (ℓ : O) ∧ (ℓ : O) ≠ 0 ∧ 1 ≤ s₀ ∧ (ℓ = 2 → 2 ≤ s₀) ∧ ((ε g₀ : Oˣ) : O) - 1 = (ℓ : O) ^ s₀ * (y : O)

def StatGen : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type) [Group G]
    (ε : G →* Oˣ) (g₀ : G) (s₀ : ℕ) (y : Oˣ), GenHyp ℓ O ε g₀ s₀ y →
    (∀ i j : ℕ, (ε g₀) ^ i = (ε g₀) ^ j → i = j) ∧
    ∀ (O' : Type) [CommRing O'] [Algebra O O'],
      ((bcChar O' ε g₀ : O'ˣ) : O') - 1 =
        (ℓ : O') ^ s₀ * ((Units.map (algebraMap O O').toMonoidHom y : O'ˣ) : O')

def StatCycBc : Prop :=
  ∀ (ℓ : ℕ) (Ek Ω O O' : Type) [Field Ek] [Field Ω] [Algebra Ek Ω] [CommRing O] [CommRing O'] [Algebra O O']
    (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ), IsCycG ℓ ε → IsCycG ℓ (bcChar O' ε)

def GaloisTheoremWithGenerator : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Type) [Fintype X] (T : Subalgebra O (X → O))
    (d : Type) [Fintype d] [DecidableEq d] (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω]
    [Algebra Ek Ω] [IsAlgClosure Ek Ω] (r : (Ω ≃ₐ[Ek] Ω) →* (X → Matrix d d O)) (π : X)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1)) (χ₁ ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (g₀ : (Ω ≃ₐ[Ek] Ω))
    (s₀ : ℕ) (y : Oˣ),
    PrimHyp O T r π bl χ₁ ε →
    AbsIrr (fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)) →
    2 ≤ Fintype.card {a // bl a = 0} →
    (∀ x, ∃ (m : ℕ) (c : d → Fin m) (P : Matrix d d (FractionRing O)),
      BlockDiagonalIrreducibleAt (fun g => (r g x).map (algebraMap O (FractionRing O))) m c P) →
    GenHyp ℓ O ε g₀ s₀ y → IsCycG ℓ ε →
    ∀ (L : ℕ) (ϖ : O), ϖ ≠ 0 →
    ∃ eB e₁ s : X → Matrix d d O, ChainAB O T r π bl g₀ (ϖ ^ L) eB e₁ s ∧
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
        (_ : Algebra O O') (_ : Module.Free O O') (_ : Module.Finite O O') (e : ℕ),
        (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
          e * IsDiscreteValuationRing.addVal O y) ∧
        PrimOver ℓ O O' e Ek Ω T r π t ht bl χ₁ ε g₀ eB e₁ s ∧
        IsCycG ℓ (bcChar O' ε) ∧
        ((bcChar O' ε g₀ : O'ˣ) : O') - 1 =
          (ℓ : O') ^ s₀ * ((Units.map (algebraMap O O').toMonoidHom y : O'ˣ) : O')

end Formalism.RepresentationBoundsCohomology.SF
