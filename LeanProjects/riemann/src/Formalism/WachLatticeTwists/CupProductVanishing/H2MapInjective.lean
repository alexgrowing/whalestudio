import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

def StatNatInvFG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ ε : GK p K →* Oˣ, IsCyc p K ε →
    Nonempty (NatInv ε (fun M _ _ _ => IsFGTop O M))

def H2MapInjective : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ε : Γ →* Oˣ),
    Nonempty (NatInv ε (fun M _ _ _ => IsFGTop O M)) →
    ∀ (Y R : Type) [AddCommGroup Y] [Module O Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
      [ContinuousConstSMul O Y] [AddCommGroup R] [Module O R] [TopologicalSpace R]
      [IsTopologicalAddGroup R] [ContinuousConstSMul O R], IsFGTop O Y → IsFGTop O R →
    ∀ i : Y →ₗ[O] R, Continuous i → Function.Injective i →
    ∀ z ∈ characterColumnKernelPairSetVariant (twRep ε Y), Continuous (fun q : Γ × Γ => z q.1 q.2) →
      (∃ f : Γ → R, Continuous f ∧ ∀ g h, i (z g h) = ((ε g : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c : Γ → Y, Continuous c ∧ ∀ g h, z g h = ((ε g : Oˣ) : O) • c h - c (g * h) + c g

def CupClause : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw] (ε : G →* Oˣ),
    IsFGTop O A → Nonempty (NatInv (ε.comp Dw.subtype) (fun M _ _ _ => IsFGTop O M)) →
    ∀ z ∈ characterColumnKernelPairSetVariant (twRep (ε.comp Dw.subtype) (Ymod r χ E)), Continuous (fun q : Dw × Dw => z q.1 q.2) →
      (∃ f : Dw → A, Continuous f ∧ ∀ g h, ((z g h : Ymod r χ E) : A) =
        ((ε (g : G) : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c : Dw → Ymod r χ E, Continuous c ∧ ∀ g h, z g h = ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g

def CupClauseGK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw] (ε : G →* Oˣ),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ e : Dw ≃ₜ* GK p K,
    IsCyc p K ((ε.comp Dw.subtype).comp e.symm.toMulEquiv.toMonoidHom) → IsFGTop O A →
    ∀ z ∈ characterColumnKernelPairSetVariant (twRep (ε.comp Dw.subtype) (Ymod r χ E)), Continuous (fun q : Dw × Dw => z q.1 q.2) →
      (∃ f : Dw → A, Continuous f ∧ ∀ g h, ((z g h : Ymod r χ E) : A) =
        ((ε (g : G) : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c : Dw → Ymod r χ E, Continuous c ∧ ∀ g h, z g h = ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g

def StatCupVanish : Prop :=
  ∀ (O : Type) [CommRing O] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
    (M T₂ P : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul O M] [AddCommGroup T₂] [Module O T₂] [TopologicalSpace T₂]
    [IsTopologicalAddGroup T₂] [ContinuousConstSMul O T₂] [AddCommGroup P] [Module O P]
    [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul O P]
    (ρM : Representation O Γ M) (ρ₂ : Representation O Γ T₂) (ρP : Representation O Γ P)
    (b : M →ₗ[O] T₂ →ₗ[O] P) (hb : Continuous fun q : M × T₂ => b q.1 q.2)
    (hbe : ∀ g x y, b (ρM g x) (ρ₂ g y) = ρP g (b x y)) (h₂ : ContAction ρ₂)
    (x : Z1 ρM) (t : Z1 ρ₂),
    (∃ c : Γ → P, Continuous c ∧ ∀ g h, b (ρM g (x.1 h)) (t.1 g) = ρP g (c h) - c (g * h) + c g) →
    cupProductH1H1 ρM ρ₂ ρP b hb hbe h₂ (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0

end Formalism.RepresentationBoundsCohomology.T2
