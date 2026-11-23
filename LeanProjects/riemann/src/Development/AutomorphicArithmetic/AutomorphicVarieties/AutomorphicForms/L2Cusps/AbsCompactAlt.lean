import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.L2LocalComponents.Summand

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

section Defs

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

abbrev G1 : Type := Reduction.normOneGL E a

abbrev Γ1 : Subgroup (G1 E a) := Reduction.rationalGLOne E a

variable [IsTotallyComplex E]

def band : Set (GA E a) :=
  {g | a = 0 ∨ (1 ≤ Reduction.detModule E a g ∧
    Reduction.detModule E a g < Reduction.detModule E a (splitCentre E a 1))}

variable {E a} in

def muOne (μ : Measure (GA E a)) : Measure (G1 E a) := Measure.map retractOne (μ.restrict (band E a))

def quotMap (q : Quot (latticeGL E a)) : RightCosetSpace (Γ1 E a) :=
  RightCosetSpace.mk (Γ1 E a) (retractOne q.out)

variable {E a}

abbrev Pres (μ : Measure (GA E a)) (μ₁ : Measure (G1 E a)) : Prop :=
  MeasurePreserving (quotMap E a) (quotMeasure (latticeGL E a) μ) (RightCosetSpace.quotientMeasure (Γ1 E a) μ₁)

def cmp {μ : Measure (GA E a)} {μ₁ : Measure (G1 E a)} [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) :
    CuspL2 μ₁ →ₗᵢ[ℂ] L2 (latticeGL E a) μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (quotMap E a) hp).comp (cuspidalL2 μ₁).subtypeₗᵢ

end Defs

def SplitEq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : ℝ),
    splitCentre E a t =
      Reduction.centralSection E a ⟨Real.exp (a * Module.finrank ℚ E * t), Real.exp_pos _⟩

def QuotMk : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (g : GA E a),
    quotMap E a (mk (latticeGL E a) g) = RightCosetSpace.mk (Γ1 E a) (retractOne g)

def MuHaar : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure],
    (muOne μ).IsHaarMeasure

def BandDom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (D : Set (G1 E a)),
    (∀ x : G1 E a, ∃! γ : Γ1 E a, γ • x ∈ D) →
    ∀ g : GA E a, ∃! γ : latticeGL E a, γ • g ∈ retractOne ⁻¹' D ∩ band E a

def QuotPres : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure],
    Pres μ (muOne μ)

def LiftCmp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (v : CuspL2 μ₁) (Φ : RightCosetSpace (Γ1 E a) → ℂ),
    (toLp μ₁ v : RightCosetSpace (Γ1 E a) → ℂ) =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] Φ →
    lift (latticeGL E a) (cmp hp v) =ᵐ[μ] fun g => Φ (RightCosetSpace.mk (Γ1 E a) (retractOne g))

def CmpEquiv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (g : GA E a) (v : CuspL2 μ₁),
    R (latticeGL E a) μ g (cmp hp v) = cmp hp (cuspRepT μ₁ (retractOne g) v)

def CmpForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (φ : cuspForms E a), φ ∈ centralCuspForms E a →
    lift (latticeGL E a) (cmp hp (cuspVecL μ₁ φ)) =ᵐ[μ] φ.1

def Dense : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ₁ : Measure (G1 K n)) [μ₁.IsHaarMeasure],
    ((centralCuspForms K n).map (cuspVecL μ₁)).topologicalClosure = ⊤

def NeBot : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ₁ : Measure (G1 K n)) [μ₁.IsHaarMeasure]
    (V : Submodule ℂ (CuspL2 μ₁)) [CompleteSpace V] (hV : (cuspRepT μ₁).IsInvariant V),
    ((cuspRepT μ₁).restrict V hV).IsIrreducible → summandCuspForms V ≠ ⊥

def RangeLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (v : CuspL2 μ₁), cmp hp v ∈ L2cusp μ

def ContMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (φ : GA E a → ℂ), φ ∈ cuspCont E a →
    ∀ h : MemL2Quotient (latticeGL E a) μ φ, ∃ v : CuspL2 μ₁, cmp hp v = h.toL2

def KFinTr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (v : CuspL2 μ₁),
    IsKFinL2 μ (cmp hp v) →
    IsOpen {h : AdelicGLn.FiniteAdelicGL E a | cuspRepT μ₁ (retractOne (finEmb E a h)) v = v} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact E a => archRepT μ₁ (k : archGroup E a) v))

def AbsCompact : Prop :=
  ∀ (G G₁ H L : Type) [Group G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [T2Space G₁] [MeasurableSpace G₁] [OpensMeasurableSpace G₁]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (π : UnitaryRep G₁ H) (ν : Measure G₁) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    (ρ : G →* (L →L[ℂ] L)) (W : Submodule ℂ L) (hW : IsSubrep ρ W) (J : H →ₗᵢ[ℂ] L) (r : G → G₁),
    Function.Surjective r → (∀ g v, ρ g (J v) = J (π (r g) v)) → LinearMap.range J.toLinearMap = W →
    (∀ f : CompactlySupportedContinuousMap G₁ ℂ, IsCompactOperator (π.integrated ν (UnitaryRep.ccToL1 ν f))) →
    EnoughCompact hW.rep

def AbsIrr : Prop :=
  ∀ (G G₁ H L : Type) [Group G] [Group G₁] [TopologicalSpace G₁]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (π : UnitaryRep G₁ H) (ρ : G →* (L →L[ℂ] L)) (J : H →ₗᵢ[ℂ] L) (r : G → G₁),
    Function.Surjective r → (∀ g v, ρ g (J v) = J (π (r g) v)) →
    ∀ X : Submodule ℂ L, X ≤ LinearMap.range J.toLinearMap → IsIrredSubrep ρ X →
    ∃ (_ : CompleteSpace (X.comap J.toLinearMap)) (hV : π.IsInvariant (X.comap J.toLinearMap)),
      (π.restrict (X.comap J.toLinearMap) hV).IsIrreducible

def AbsApprox : Prop :=
  ∀ (ι H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : ι → H →L[ℂ] H),
    (∀ i, ∃ j, ContinuousLinearMap.adjoint (A i) = A j) → ∀ (W N : Submodule ℂ H), FiniteDimensional ℂ N →
    (∀ w ∈ W, ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ w ∈ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y) →
    ∀ v ∈ W.topologicalClosure,
      (∀ P : H →L[ℂ] H, (∀ i x, P (A i x) = A i (P x)) → (∀ x, P x ∈ W) → P v ∈ N) → v ∈ W

def HomFin : Prop :=
  ∀ (C M X : Type) [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (σ : Representation ℂ C M) (hσ : CompactRep.IsKFinite σ) (τ : Representation ℂ C X),
    Representation.HasContinuousCoeff τ → ∀ F : Submodule ℂ M,
    (∀ (c : Submodule (MonoidAlgebra ℂ C) σ.asModule) (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ C) σ.asModule),
      FiniteDimensional ℂ (LinearMap.range (CompactRep.kProj hσ hc ∘ₗ F.subtype))) →
    ∃ N : Submodule ℂ M, FiniteDimensional ℂ N ∧
      ∀ f : X →ₗ[ℂ] M, (∀ k x, f (τ k x) = σ k (f x)) → (∀ x, f x ∈ F) → ∀ x, f x ∈ N

def StabFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (M : AdelicGKModule K n V),
    GroundTheory.Automorphic.IsSmooth M.τ → ∀ U : Subgroup (AdelicGLn.FiniteAdelicGL K n),
    IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) → ∀ v : V,
    ∃ Y : Submodule ℂ V, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ (∀ k, ∀ y ∈ Y, M.gk.σ k y ∈ Y) ∧ ∀ u ∈ U, ∀ y ∈ Y, M.τ u y ∈ Y

def PvFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ₁ : Measure (G1 K n)) [μ₁.IsHaarMeasure]
    (π : CuspidalAutomorphicRepresentation K n) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
    IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) → IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) →
    ∀ v : CuspL2 μ₁, (∀ u ∈ U, cuspRepT μ₁ (retractOne (finEmb K n u)) v = v) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact K n => archRepT μ₁ (k : archGroup K n) v)) →
    ∃ N : Submodule ℂ (CuspL2 μ₁), FiniteDimensional ℂ N ∧ ∀ P : CuspL2 μ₁ →L[ℂ] CuspL2 μ₁,
      (∀ (k : archCompact K n) x, P (archRepT μ₁ (k : archGroup K n) x) = archRepT μ₁ (k : archGroup K n) (P x)) →
      (∀ u ∈ U, ∀ x, P (cuspRepT μ₁ (retractOne (finEmb K n u)) x) = cuspRepT μ₁ (retractOne (finEmb K n u)) (P x)) →
      (∀ x, P x ∈ π.carrier.map (cuspVecL μ₁)) → P v ∈ N

def KFinMem : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ₁ : Measure (G1 K n)) [μ₁.IsHaarMeasure]
    (π : CuspidalAutomorphicRepresentation K n) (v : CuspL2 μ₁),
    v ∈ (π.carrier.map (cuspVecL μ₁)).topologicalClosure →
    IsOpen {h : AdelicGLn.FiniteAdelicGL K n | cuspRepT μ₁ (retractOne (finEmb K n h)) v = v} →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact K n => archRepT μ₁ (k : archGroup K n) v)) →
    v ∈ π.carrier.map (cuspVecL μ₁)

def BrCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → φ.1 ∈ cuspForms E a

def BrRep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π₀ : CuspidalAutomorphicRepresentation E a),
    ∃ π : CuspSub E a, π.V.map (Sm E a).subtype = π₀.carrier.map (cuspForms E a).subtype

def BrCpt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (k : archCompact E a),
    ∃ k' : Kinf E a, infEmb E a (k : archGroup E a) = infGL E a (Unitary.toUnits k')

end UpperTheory.V.KernelIndexFullLattice
