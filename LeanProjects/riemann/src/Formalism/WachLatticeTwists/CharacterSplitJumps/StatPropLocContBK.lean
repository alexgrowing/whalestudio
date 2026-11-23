import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable

universe u

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.RepresentationBoundsCohomology.LOC

def StatBKbConvO : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A HV HT' HV' : Type u) [AddCommGroup A] [Module O A] [AddCommGroup HV] [Module O HV]
    [AddCommGroup HT'] [Module O HT'] [Module.Finite O HT'] [AddCommGroup HV'] [Module O HV']
    (q : HV →ₗ[O] A) (j' : HT' →ₗ[O] HV') (pr : A →ₗ[O] HT' →ₗ[O] KO O)
    (pair : HV →ₗ[O] HV' →ₗ[O] FractionRing O)
    (HfV : Submodule O HV) (HfV' : Submodule O HV'),
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) →
    (∀ (c : O) b, c ≠ 0 → c • b ∈ HfV' → b ∈ HfV') →
    (∀ f : HV' →ₗ[O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) →
    (∀ x : A, (∀ t, pr x t = 0) → x = 0) →
    HfV.map q = annih pr (HfV'.comap j')

def StatPropLocContBK : Prop :=
  ∀ (O G VT VT' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O G VT VT') (HfV : Submodule O (H1 D.ρT)) (HfV' : Submodule O (H1 D.ρT'))
    (pair : H1 D.ρT →ₗ[O] H1 D.ρT' →ₗ[O] FractionRing O)
    (ℓ e' : ℕ) (ι₁ ι₂ : Type u) (P : ι₁ → PushData D) (Q : ι₂ → PushData D),
    IsLatticeIn D.T → PerfectRight D.bT → Module.Finite O (H1 D.ρTl') → ∀ hc : D.InvCompat,
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) →
    (∀ (c : O) b, c ≠ 0 → c • b ∈ HfV' → b ∈ HfV') →
    (∀ f : H1 D.ρT' →ₗ[O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, D.pr (D.q a) t = Submodule.Quotient.mk (pair a (D.j' t))) →
    (∀ x, (∀ t, D.pr x t = 0) → x = 0) →
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

end Formalism.RepresentationBoundsCohomology.JT
