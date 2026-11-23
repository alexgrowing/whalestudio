import Formalism.WachLatticeTwists.CharacterSplitJumps.StatPropLocContBK
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

section Defs

variable {O G VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT']

def pairF (D : LatData O G VT VT') : H1 D.ρT →ₗ[O] H1 D.ρT' →ₗ[O] FractionRing O :=
  (cupProductH1H1 D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT D.eqT D.contT').compr₂ D.invF

def withInv (D : LatData O G VT VT') (inv : H2 (twist D.ε (KO O)) →ₗ[O] KO O)
    (invF : H2 (twist D.ε (FractionRing O)) →ₗ[O] FractionRing O) : LatData O G VT VT' :=
  { D with inv := inv, invF := invF }

end Defs

structure RealData {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O (GK p K) VT VT') : Prop where
  cyc : IsCyc p K D.ε
  lat : IsLatticeIn D.T
  perf : PerfectRight D.bT
  contT : ContAction D.ρT
  openT : IsOpen (D.T : Set VT)
  t2 : T2Space VT
  t2' : T2Space VT'
  cs : ContinuousConstSMul (FractionRing O) VT
  cs' : ContinuousConstSMul (FractionRing O) VT'

def StatFinGK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O (GK p K) VT VT'),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → RealData D → Module.Finite O (H1 D.ρTl')

def StatInvGK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O →
    ∀ ε : GK p K →* Oˣ, IsCyc p K ε →
    ∃ (inv : H2 (twist ε (KO O)) ≃ₗ[O] KO O)
      (invF : H2 (twist ε (FractionRing O)) ≃ₗ[O] FractionRing O),
      ∀ z, inv (mapH2 (twist ε (FractionRing O)) (twist ε (KO O)) (toKO O) toKO_cont (toKO_equiv ε) z) =
        toKO O (invF z)

def StatRatGK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O (GK p K) VT VT'),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → RealData D → Function.Injective D.invF →
    ∀ f : H1 D.ρT' →ₗ[O] FractionRing O, ∃ a, ∀ b, pairF D a b = f b

def StatIntGK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O (GK p K) VT VT'),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → RealData D → Function.Injective D.inv →
    ∀ x, (∀ t, D.pr x t = 0) → x = 0

def StatCompat : Prop :=
  ∀ (O G VT VT' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT'), D.InvCompat →
    ∀ a t, D.pr (D.q a) t = Submodule.Quotient.mk (pairF D a (D.j' t))

def StatRealise : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O (GK p K) VT VT'),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → RealData D →
    ∃ (inv : H2 (twist D.ε (KO O)) →ₗ[O] KO O)
      (invF : H2 (twist D.ε (FractionRing O)) →ₗ[O] FractionRing O),
      RealData (withInv D inv invF) ∧ Function.Bijective (withInv D inv invF).inv ∧
        Function.Bijective (withInv D inv invF).invF ∧ (withInv D inv invF).InvCompat

def StatPropLocGK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O (GK p K) VT VT')
    (HfV : Submodule O (H1 D.ρT)) (HfV' : Submodule O (H1 D.ρT'))
    (ℓ e' : ℕ) (ι₁ ι₂ : Type) (P : ι₁ → PushData D) (Q : ι₂ → PushData D),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → RealData D →
    Function.Injective D.inv → Function.Injective D.invF → ∀ hc : D.InvCompat,
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pairF D a b = 0) →
    (∀ (c : O) b, c ≠ 0 → c • b ∈ HfV' → b ∈ HfV') →
    (∀ i, (P i).toDirect.Fun HfV ∧ (P i).toDirect.Lift ℓ e') →
    (∀ i, ((Q i).toDual hc).Fun ∧ ((Q i).toDual hc).Orth ∧
      ((Q i).toDual hc).Lift (HfV'.comap D.j') ℓ e') →
    (∀ i, ∀ y ∈ (P i).HfVY.comap (P i).jY, ((ℓ : O) ^ e') • (P i).φs y ∈ HfV.map D.q) ∧
    (∀ i, ∀ y ∈ (Q i).HfVY.comap (Q i).jY, ((ℓ : O) ^ e') • (Q i).φs y ∈ HfV.map D.q) ∧
    Module.length O
      (((⨆ i, ((P i).HfVY.comap (P i).jY).map (P i).φs) ⊔
          (⨆ i, ((Q i).HfVY.comap (Q i).jY).map (Q i).φs) : Submodule O (H1 D.ρA)) ⧸
        (HfV.map D.q).comap ((⨆ i, ((P i).HfVY.comap (P i).jY).map (P i).φs) ⊔
          (⨆ i, ((Q i).HfVY.comap (Q i).jY).map (Q i).φs) : Submodule O (H1 D.ρA)).subtype) ≤
      ((Module.finrank O ↥(HfV'.comap D.j') + Module.finrank O D.T : ℕ) : ℕ∞) *
        ((e' : ℕ∞) * eO O ℓ)

end Formalism.RepresentationBoundsCohomology.T2
