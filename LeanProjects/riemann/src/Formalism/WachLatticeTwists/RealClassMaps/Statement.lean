import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Statement
import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.StatClause5Row
import Formalism.WachLatticeTwists.CupProductVanishing.StatVhEInChi
import Formalism.WachLatticeTwists.CupProductVanishing.H2MapInjective

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

structure RealLat {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O Γ VT VT') : Prop where
  lat : IsLatticeIn D.T
  perf : PerfectRight D.bT
  contT : ContAction D.ρT
  openT : IsOpen (D.T : Set VT)
  t2 : T2Space VT
  t2' : T2Space VT'
  cs : ContinuousConstSMul (FractionRing O) VT
  cs' : ContinuousConstSMul (FractionRing O) VT'

section Defs
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace A]
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

def InRowReal (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw]
    {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (D : LatData O Dw VT VT') (v : T₂ ≃ₗ[O] D.T') (Fs Im : Submodule O (H1 D.ρTl')) : Prop :=
  ∃ C₁ : (Dw → T₁) → Prop,
    (∀ a, C₁ a → Continuous fun q : Dw × Dw =>
      (inc (a q.1) • (uElt r χ (q.1 : G) • yY r χ E (q.2 : G)) : Ymod r χ E)) ∧
    (∀ a, C₁ a → Continuous fun g : Dw => -(inc (a g) * (uElt r χ (g : G) * E))) ∧
    (∀ (ψ : Ymod r χ E →ₗ[O] KO O) (f : Dw → Ymod r χ E), Continuous f → Continuous fun g => ψ (f g)) ∧
    (∀ a, C₁ a → Continuous fun g => v (π (a g))) ∧
    (∀ x ∈ Im, ∃ a ∈ characterColumnKernelSet (resRep ρ₁ Dw), C₁ a ∧ x = clsRow D v (fun g => π (a g))) ∧
    Im ≤ Fs

end Defs

section Defs2
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def RowTB (ℓ : ℕ) [Fact ℓ.Prime] (M : Type) [AddCommGroup M] [Module A M] [Module O M]
    [SMulCommClass A O M] (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G)
    (F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)))
    (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ) (U : Finset ℤ) : Prop :=
  ∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
    ∀ z : coZ1s (resRep (uRep O (M := M) r χ) Dw),
      (∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : G))) →
      ∃ B : TBBridge ℓ F.toAddSubgroup
          (Submodule.mkQ _ z : H1z (resRep (uRep O (M := M) r χ) Dw)),
        TBFullIn B.D u w s m e d U

end Defs2

def StatRowRhoReal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (Aw : ValuationSubring Ω), Aw.valuation (p : Ω) < 1 →
    ∀ (A T' : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : (Ω ≃ₐ[Ek] Ω) →* A) (χ : (Ω ≃ₐ[Ek] Ω) →* T'ˣ) (E : A) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ)
    (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O (Ω ≃ₐ[Ek] Ω) T₁) (ρ₂ : Representation O (Ω ≃ₐ[Ek] Ω) T₂)
    (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O)
    (D : LatData O (Aw.decompositionSubgroup Ek) VT VT') (u : M ≃ₗ[O] (VT ⧸ D.T))
    (hu : ∀ g m, u (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup Ek) g m) = D.ρA g (u m))
    (v : T₂ ≃ₗ[O] D.T')
    [Module (FractionRing O) (H1 D.ρT)] [IsScalarTower O (FractionRing O) (H1 D.ρT)]
    [Module (FractionRing O) (H1 D.ρT')] [IsScalarTower O (FractionRing O) (H1 D.ρT')]
    (HfV : Submodule (FractionRing O) (H1 D.ρT)) (HfV' : Submodule (FractionRing O) (H1 D.ρT'))
    (Fs Im : Submodule O (H1 D.ρTl')),
    PadicCoeff p O → FracTop O → IsFGTop O A →
    IsCycOn p (Aw.decompositionSubgroup Ek) (ε.comp (Aw.decompositionSubgroup Ek).subtype) →
    (∀ g : Aw.decompositionSubgroup Ek, D.ε g = ε g) → RealLat D → IsEquivMap ρ₁ ρ₂ π →
    (∀ (g : Aw.decompositionSubgroup Ek) t, v (ρ₂ g t) = D.ρTl' g (v t)) →
    (∀ t m, γ t m = pairKO D.bT D.T (u m) (v t)) →

    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', cupFG D a b = 0) →
    Fs = (HfV'.restrictScalars O).comap D.j' →
    InRowReal r χ E (Aw.decompositionSubgroup Ek) ρ₁ inc π D v Fs Im →
    ∀ hk : Function.Injective (kRow D _ u hu),
    ∃ (pr : LinearMap.range (kRow D _ u hu) →ₗ[O] H1 D.ρTl' →ₗ[O] KO O)
      (pair : H1 D.ρT →ₗ[FractionRing O] H1 D.ρT' →ₗ[FractionRing O] FractionRing O),
      BKIn (LinearMap.range (kRow D _ u hu)) (qK D _ hk) D.j' pr pair HfV HfV'
        (((HfV.restrictScalars O).map D.q).map (kRow D _ u hu)) Fs ∧
      InRowRhoNoBK M r χ E (Aw.decompositionSubgroup Ek) ε ρ₁ inc π γ
        (LinearMap.range (kRow D _ u hu)) (clsRow D v) pr Fs Im

def StatRowChiReal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O], Function.Injective (algebraMap ℤ_[p] O) →
    ∀ (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (Aw : ValuationSubring Ω), Aw.valuation (p : Ω) < 1 →
    ∀ pl : HeightOneSpectrum (𝓞 Ek), IsPlaceOver Aw pl →
    ∀ (A T' : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : (Ω ≃ₐ[Ek] Ω) →* A) (χ : (Ω ≃ₐ[Ek] Ω) →* T'ˣ) (E : A) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (e : ℕ),
    IsCycOn p (Aw.decompositionSubgroup Ek) (ε.comp (Aw.decompositionSubgroup Ek).subtype) →
    Nonempty (M ≃ₗ[O] KO O) →
    (∀ g ∈ Aw.decompositionSubgroup Ek, ∀ m : M, uElt r χ g • m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) →
    ∀ F : Submodule O (H1z (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup Ek))),
    (0 < e → F = ⊥) →
    (e = 0 → F = lcH1 (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup Ek)) ⊓
      unrH1 (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup Ek))
        ((Ine (F := Ek) Aw).subgroupOf (Aw.decompositionSubgroup Ek))) →
    ∀ (uu ww : ℤ_[p]ˣ) (s m d : ℕ) (U : Finset ℤ),
    RowTB p M r χ E (Aw.decompositionSubgroup Ek) F uu ww s m e d U →
    RowIn p M r χ E (Aw.decompositionSubgroup Ek)
      (lcH1 (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup Ek))) F uu ww s m e d U (locDeg pl)

end Formalism.RepresentationBoundsCohomology.FIN
