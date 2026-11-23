import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartHOfSs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Cj.H

section Conv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}

def cv (ψ : G → ℂ) (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (x : G) : ℂ := ∫ y, GlobalTheory.AutomorphicL2Unitary.lift Γ F y * ψ (y⁻¹ * x) ∂μ

def Comm [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (T : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ →L[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) : Prop :=
  ∀ g F, T (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F) = GlobalTheory.AutomorphicL2Unitary.R Γ μ g (T F)

end Conv

section Fn

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

abbrev HL (μ : Measure (GA E a)) : Type := GlobalTheory.AutomorphicL2Unitary.L2 (latticeGL E a) μ

abbrev InL (μ : Measure (GA E a)) (φ : Sm E a) : Prop := GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ φ.1

abbrev HasLev (φ : Sm E a) : Prop := IsOpen {k | act (.fin k) φ = φ}

def IsTest (ψ : Sm E a) : Prop := HasCompactSupport ψ.1 ∧ HasLev ψ

def gard (μ : Measure (GA E a)) : Submodule ℂ (Sm E a) :=
  Submodule.span ℂ {φ | ∃ (ψ : Sm E a) (F : HL μ), IsTest ψ ∧ φ.1 = cv ψ.1 F}

open Classical in

def cl (μ : Measure (GA E a)) (φ : Sm E a) : HL μ := if h : InL μ φ then h.toL2 else 0

theorem cl_eq {μ : Measure (GA E a)} {φ : Sm E a} (h : InL μ φ) : cl μ φ = h.toL2 := dif_pos h

def Grow (φ : GA E a → ℂ) : Prop := ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N

def Lifts (μ : Measure (GA E a)) (T : HL μ →L[ℂ] HL μ) (T' : Module.End ℂ (Sm E a)) : Prop :=
  ∀ φ ∈ gard μ, T' φ ∈ gard μ ∧ cl μ (T' φ) = T (cl μ φ)

structure IsOp (N : Submodule ℂ (Sm E a)) (T : Module.End ℂ (Sm E a)) : Prop where
  maps : ∀ φ ∈ N, T φ ∈ N
  lie : ∀ X, ∀ φ ∈ N, lie E a X (T φ) = T (lie E a X φ)
  rt : ∀ g, ∀ φ ∈ N, rt E a g (T φ) = T (rt E a g φ)

theorem isOp_one (N : Submodule ℂ (Sm E a)) : IsOp N 1 := ⟨fun _ h => h, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

def LocLim (f : ℕ → Sm E a) (φ : Sm E a) : Prop :=
  ∀ C : Set (GA E a), IsCompact C → TendstoUniformlyOn (fun k => (f k).1) φ.1 atTop C

def casA (r c : ℝ) {n : ℕ} (e : Fin n → Herm E a) : Module.End ℂ (Sm E a) :=
  cas (shift (lie E a) r) e - (c : ℂ) • (1 : Module.End ℂ (Sm E a))

structure IsRes (N : Submodule ℂ (Sm E a)) (A P : Module.End ℂ (Sm E a)) (Q S : ℕ → Module.End ℂ (Sm E a)) : Prop where
  opP : IsOp N P
  opQ : ∀ k, IsOp N (Q k)
  opS : ∀ k, IsOp N (S k)
  res : ∀ k, ∀ φ ∈ N, φ - Q k φ = A (S k φ)
  ker : ∀ φ ∈ N, A (P φ) = 0
  lim : ∀ φ ∈ N, LocLim (fun k => Q k φ) (P φ)

structure Good (r : ℝ) (N : Submodule ℂ (Sm E a)) : Prop where
  lie : ∀ X, ∀ φ ∈ N, lie E a X φ ∈ N
  grow : ∀ φ ∈ N, Grow φ.1
  sq : ∀ φ ∈ N, GlobalTheory.CuspRep.lie E a (oneL E a) φ = -(r : ℂ) • φ → IsSq r φ
  cpt : ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → HasLev φ →
    GlobalTheory.CuspRep.lie E a (oneL E a) φ = -(r : ℂ) • φ → (∃ R : ℝ, ∀ g, R < qht g → φ.1 g = 0) → φ ∈ N

variable {Ξ : AlgRep E a} {q : ℕ}

def app (T : Module.End ℂ (Sm E a)) (ω : Co Ξ q) : Co Ξ q :=
  ((T.rTensor (Fin Ξ.d → ℂ)).restrictScalars ℝ).compAlternatingMap ω

theorem app_apply (T : Module.End ℂ (Sm E a)) (ω : Co Ξ q) (X : Fin q → Herm E a) :
    app T ω X = T.rTensor _ (ω X) := rfl

def Val (N : Submodule ℂ (Sm E a)) (ω : Co Ξ q) : Prop := ∀ X i, cmp i (ω X) ∈ N

def CoLim (ω : ℕ → Co Ξ q) : Prop := ∀ X i, LocLim (fun k => cmp i (ω k X)) 0

def ExactIn (N : Submodule ℂ (Sm E a)) : {q : ℕ} → Co Ξ q → Prop
  | 0, ω => ω = 0
  | _ + 1, ω => ∃ η, Val N η ∧ dCo (smLie Ξ) η = ω

def HasCas (Ξ : AlgRep E a) (r c : ℝ) {n : ℕ} (e : Fin n → Herm E a) : Prop :=
  cas (shift Ξ.dmat (-r)) e = (c : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

structure IsH (r : ℝ) (m : (E →+* ℂ) → Multiset ℂ) (ω : Co Ξ q) : Prop where
  lev : Lev Ξ ω
  closed : dCo (smLie Ξ) ω = 0
  aut : ∀ X i, IsAutForm (cmp i (ω X)) ∧ HasChar m (cmp i (ω X))
  sq : Val (sqSub E a r) ω

end Fn

section Forms

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

def coneOp {q : ℕ} (p : V) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (x : V) : V [⋀^Fin q]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, t ^ q • (w (p + t • (x - p))).curryLeft (x - p)

def FLim {Γ S : Type} [Group Γ] {d : ℕ} (G : Dr.Geo Γ V S d) {q : ℕ} (w : ℕ → G.Om q) : Prop :=
  ∀ s, ∀ K ⊆ G.Y, IsCompact K → TendstoUniformlyOn (fun k => (w k).1 s) 0 atTop K

end Forms

def LocInt : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant], (∀ F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ, LocallyIntegrable (GlobalTheory.AutomorphicL2Unitary.lift Γ F) μ) ∧
    ∀ C : Set G, IsCompact C → ∃ N : ℕ, ∀ g : G, {γ : Γ | (γ : G) * g ∈ C}.encard ≤ N

def CvCount : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ψ : G → ℂ), Continuous ψ → HasCompactSupport ψ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (x : G) (N : ℕ), (∀ g : G, {γ : Γ | ψ (((γ : G) * g)⁻¹ * x) ≠ 0}.encard ≤ N) →
      ∀ F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ, ‖cv ψ F x‖ ≤ B * N * ‖F‖

def CvAlg : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ψ : G → ℂ), Continuous ψ → HasCompactSupport ψ →
    (∀ (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) x, Integrable (fun y => GlobalTheory.AutomorphicL2Unitary.lift Γ F y * ψ (y⁻¹ * x)) μ) ∧
    (∀ (F F' : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (s t : ℂ), cv ψ (s • F + t • F') = s • cv ψ F + t • cv ψ F') ∧
    (∀ F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ, GlobalTheory.AutomorphicL2Unitary.LeftInv Γ (cv ψ F)) ∧
    ∀ C : Set G, IsCompact C → ∃ B : ℝ, ∀ (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ), ∀ x ∈ C, ‖cv ψ F x‖ ≤ B * ‖F‖

def ConvolutionL2Class : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ψ : G → ℂ), Continuous ψ → HasCompactSupport ψ → ∀ F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ,
    ∃ h : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (cv ψ F), h.toL2 = GlobalTheory.AutomorphicL2Unitary.Rop Γ μ (fun y => ψ y⁻¹) F

def RopComm : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (T : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ →L[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 Γ μ), Comm T → ∀ f : G → ℂ, Integrable f μ →
    ∀ F, T (GlobalTheory.AutomorphicL2Unitary.Rop Γ μ f F) = GlobalTheory.AutomorphicL2Unitary.Rop Γ μ f (T F)

def Approx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ), (∀ W ∈ 𝓝 (1 : G), ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧
      (∀ y, ∃ t : ℝ, 0 ≤ t ∧ f y = t) ∧ f 1 ≠ 0 ∧ (∀ y ∉ W, f y = 0) ∧ GlobalTheory.AutomorphicL2Unitary.Rop Γ μ f F = 0) → F = 0

def OrbConv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f f' : G → ℂ), Continuous f → HasCompactSupport f → Continuous f' → HasCompactSupport f' →
    ∃ h : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f), GlobalTheory.AutomorphicL2Unitary.orbitSum Γ (GlobalTheory.AutomorphicL2Unitary.conv μ f f') = cv f' h.toL2

def AbsDense : Prop :=
  ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (R : G →* (H →L[ℂ] H))
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] D) (hD : ∀ g, ∀ v ∈ D, R g v ∈ D), (∀ g v, ‖R g v‖ = ‖v‖) →
    (∀ g (v : D), (A ⟨R g v, hD g v v.2⟩ : H) = R g (A v)) → (∀ v w : D, inner ℂ (A v : H) (w : H) = inner ℂ (v : H) (A w : H)) →
    (∀ W : Submodule ℂ H, GlobalTheory.AutomorphicL2Unitary.IsSubrep R W → W ⊓ D = ⊥ → W = ⊥) → ∀ s : ℝ, s ≠ 0 →
    ∀ w : H, (∀ v : D, inner ℂ w ((A v : H) + (Complex.I * s) • (v : H)) = 0) → w = 0

def AbsInv : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (D : Submodule ℂ H) (A : D →ₗ[ℂ] D),
    (∀ v w : D, inner ℂ (A v : H) (w : H) = inner ℂ (v : H) (A w : H)) → ∀ s : ℝ, s ≠ 0 →
    (∀ w : H, (∀ v : D, inner ℂ w ((A v : H) + (Complex.I * s) • (v : H)) = 0) → w = 0) →
    ∃ T : H →L[ℂ] H, (∀ v : D, T ((A v : H) + (Complex.I * s) • (v : H)) = v) ∧ ∀ w, |s| * ‖T w‖ ≤ ‖w‖

def AbsLim : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (D : Submodule ℂ H) (A : D →ₗ[ℂ] D),
    (∀ v w : D, inner ℂ (A v : H) (w : H) = inner ℂ (v : H) (A w : H)) → ∀ (s : ℕ → ℝ), Tendsto s atTop (𝓝 0) →
    (∀ k (w : H), (∀ v : D, inner ℂ w ((A v : H) + (Complex.I * s k) • (v : H)) = 0) → w = 0) →
    (∀ k (w : H), (∀ v : D, inner ℂ w ((A v : H) - (Complex.I * s k) • (v : H)) = 0) → w = 0) →
    ∀ T : ℕ → H →L[ℂ] H, (∀ k (v : D), T k ((A v : H) + (Complex.I * s k) • (v : H)) = v) → (∀ k w, |s k| * ‖T k w‖ ≤ ‖w‖) →
    ∀ P : H →L[ℂ] H, (∀ w (v : D), inner ℂ (P w) (A v : H) = 0) →
      (∀ w, w - P w ∈ (LinearMap.range (D.subtype ∘ₗ A)).topologicalClosure) →
      ∀ w, Tendsto (fun k => (Complex.I * s k) • T k w) atTop (𝓝 (P w))

def AbsProj : Prop :=
  ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (R : G →* (H →L[ℂ] H))
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] D) (hD : ∀ g, ∀ v ∈ D, R g v ∈ D), (∀ g v, ‖R g v‖ = ‖v‖) →
    (∀ g (v : D), (A ⟨R g v, hD g v v.2⟩ : H) = R g (A v)) → (∀ v w : D, inner ℂ (A v : H) (w : H) = inner ℂ (v : H) (A w : H)) →
    (∀ W : Submodule ℂ H, GlobalTheory.AutomorphicL2Unitary.IsSubrep R W → W ⊓ D = ⊥ → W = ⊥) →
    ∃ (P : H →L[ℂ] H) (Q S : ℕ → H →L[ℂ] H), (∀ g w, P (R g w) = R g (P w)) ∧ (∀ k g w, Q k (R g w) = R g (Q k w)) ∧
      (∀ k g w, S k (R g w) = R g (S k w)) ∧ (∀ k (v : D), (v : H) - Q k v = S k (A v)) ∧
      (∀ w (v : D), inner ℂ (P w) (A v : H) = 0) ∧ ∀ w, Tendsto (fun k => Q k w) atTop (𝓝 (P w))

def TestBump : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (C W : Set (GA E a)), IsCompact C → IsOpen W → C ⊆ W → ∃ ψ : Sm E a, IsTest ψ ∧
    (∀ g, ∃ t : ℝ, 0 ≤ t ∧ ψ.1 g = t) ∧ (∀ g ∈ C, ψ.1 g ≠ 0) ∧ ∀ g ∉ W, ψ.1 g = 0

def TestOps : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), (HasLev ψ → Continuous ψ.1 ∧ (∀ X, HasLev (lie E a X ψ)) ∧ ∀ g, HasLev (rt E a g ψ)) ∧
    (IsTest ψ → (∀ X, IsTest (lie E a X ψ)) ∧ ∀ g, IsTest (rt E a g ψ))

def CvSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ψ : Sm E a), IsTest ψ → ∀ F : HL μ, cv ψ.1 F ∈ Sm E a

def CvLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ψ φ : Sm E a), IsTest ψ → ∀ F : HL μ, φ.1 = cv ψ.1 F →
    ∀ X, (lie E a X φ).1 = cv (lie E a X ψ).1 F

def LatCount : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ S : Set (GA E a), IsCompact S → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ∃ M : ℕ,
    (M : ℝ) ≤ C * GlobalTheory.CuspRep.height y ^ N ∧
      {γ : latticeGL E a | (g * infGL E a y)⁻¹ * γ * (g * infGL E a y) ∈ S}.encard ≤ M

def CvGrow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ψ : GA E a → ℂ), Continuous ψ → HasCompactSupport ψ → ∀ F : HL μ, Grow (cv ψ F)

def OrbSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (u : Sm E a), IsTest u → ∃ w : Sm E a, HasLev w ∧ w.1 = GlobalTheory.AutomorphicL2Unitary.orbitSum (latticeGL E a) u.1

def SmDiv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ u w : Sm E a), (fun g => φ.1 g * u.1 g) ∈ Sm E a ∧
    ∀ Z : Set (GA E a), IsClosed Z → (∀ g ∉ Z, φ.1 g = 0) → (∀ g ∈ Z, w.1 g ≠ 0) → (fun g => φ.1 g / w.1 g) ∈ Sm E a

def OrbLift : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), HasLev φ → GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) φ.1 → ∀ C : Set (GA E a), IsCompact C →
    (∀ g, φ.1 g ≠ 0 → ∃ γ ∈ latticeGL E a, γ * g ∈ C) → ∃ f : Sm E a, IsTest f ∧ φ.1 = GlobalTheory.AutomorphicL2Unitary.orbitSum (latticeGL E a) f.1

def DmTest : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (f : Sm E a), IsTest f → ∃ (k : ℕ) (u v : Fin k → Sm E a),
    (∀ i, IsTest (u i) ∧ IsTest (v i)) ∧ f.1 = ∑ i, GlobalTheory.AutomorphicL2Unitary.conv μ (u i).1 (v i).1

def CptGard : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : Sm E a), HasLev φ → GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) φ.1 →
    ∀ C : Set (GA E a), IsCompact C → (∀ g, φ.1 g ≠ 0 → ∃ γ ∈ latticeGL E a, γ * g ∈ C) → φ ∈ gard μ

def GardFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ φ ∈ gard μ, HasLev φ ∧ InL μ φ ∧ Grow φ.1 ∧
    (∀ X, lie E a X φ ∈ gard μ) ∧ ∀ g, rt E a g φ ∈ gard μ

def ClFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], (∀ (φ ψ : Sm E a) (s t : ℂ), InL μ φ → InL μ ψ → InL μ (s • φ + t • ψ) ∧
      cl μ (s • φ + t • ψ) = s • cl μ φ + t • cl μ ψ) ∧
    (∀ φ : Sm E a, HasLev φ → InL μ φ → cl μ φ = 0 → φ = 0) ∧
    (∀ (φ : Sm E a) g, InL μ φ → cl μ (rt E a g φ) = GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ g (cl μ φ)) ∧
    ∀ (ψ φ : Sm E a) (F : HL μ), IsTest ψ → φ.1 = cv ψ.1 F → cl μ φ = GlobalTheory.AutomorphicL2Unitary.Rop (latticeGL E a) μ (fun y => ψ.1 y⁻¹) F

def OpLift : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (T : HL μ →L[ℂ] HL μ), Comm T → ∃ T', Lifts μ T T'

def LiftCv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (T : HL μ →L[ℂ] HL μ), Comm T → ∀ T', Lifts μ T T' →
    ∀ (ψ φ : Sm E a) (F : HL μ), IsTest ψ → φ.1 = cv ψ.1 F → (T' φ).1 = cv ψ.1 (T F)

def OpComm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (T : HL μ →L[ℂ] HL μ), Comm T → ∀ T', Lifts μ T T' → IsOp (gard μ) T'

def OpLim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (T : ℕ → HL μ →L[ℂ] HL μ) (P : HL μ →L[ℂ] HL μ), (∀ k, Comm (T k)) → Comm P →
    (∀ F, Tendsto (fun k => T k F) atTop (𝓝 (P F))) → ∀ (T' : ℕ → Module.End ℂ (Sm E a)) P', (∀ k, Lifts μ (T k) (T' k)) →
    Lifts μ P P' → ∀ φ ∈ gard μ, LocLim (fun k => T' k φ) (P' φ)

def CasAd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (A : Type) [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (L : Lie E a →ₗ[ℝ] A) (u : A) (y : GL (Fin a) (Cinf E)),
    (∀ X : Matrix (Fin a) (Fin a) (Cinf E), u * L (toL X) = L (toL (y.val * X * (y⁻¹).val)) * u) → Commute u (cas L e)

def CasOp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ r c : ℝ, (∀ X, Commute (lie E a X) (casA r c e)) ∧ (∀ g, Commute (rt E a g) (casA r c e)) ∧
    ∀ N : Submodule ℂ (Sm E a), (∀ X, ∀ φ ∈ N, lie E a X φ ∈ N) → (∀ φ ∈ N, casA r c e φ ∈ N) ∧
      ∀ T, IsOp N T → ∀ φ ∈ N, casA r c e (T φ) = T (casA r c e φ)

def CasSym : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (n : ℕ) (e : Fin n → Herm E a) (c : ℝ), ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ,
    inner ℂ (cl μ (casA 0 c e φ)) (cl μ ψ) = inner ℂ (cl μ φ) (cl μ (casA 0 c e ψ))

def GardSep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (HL μ)), GlobalTheory.AutomorphicL2Unitary.IsSubrep (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ) W →
    (∀ φ ∈ gard μ, cl μ φ ∈ W → cl μ φ = 0) → W = ⊥

def CasimirResolventProjection : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ c : ℝ,
    ∃ (P : HL μ →L[ℂ] HL μ) (Q S : ℕ → HL μ →L[ℂ] HL μ), Comm P ∧ (∀ k, Comm (Q k)) ∧ (∀ k, Comm (S k)) ∧
      (∀ k, ∀ φ ∈ gard μ, cl μ φ - Q k (cl μ φ) = S k (cl μ (casA 0 c e φ))) ∧
      (∀ F, ∀ φ ∈ gard μ, inner ℂ (P F) (cl μ (casA 0 c e φ)) = 0) ∧ ∀ F, Tendsto (fun k => Q k F) atTop (𝓝 (P F))

def FnProj0 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ c : ℝ, ∃ P Q S, IsRes (gard μ) (casA 0 c e) P Q S

def TwRes : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (r : ℝ) (χ : HChar E), IsTw (a := a) r χ → ∀ (N : Submodule ℂ (Sm E a)) (n : ℕ) (e : Fin n → Herm E a) (c : ℝ) P Q S,
    IsRes N (casA 0 c e) P Q S → ∃ P' Q' S', IsRes (N.comap (mulChi a χ).toLinearMap) (casA r c e) P' Q' S'

def ChiGrow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (χ : HChar E) (s : ℝ), χ.IsAbsPow s → ∀ φ : Sm E a, Grow (mulChi a χ φ).1 → Grow φ.1

def TwSq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (r : ℝ) (χ : HChar E), IsTw (a := a) r χ → ∀ φ : Sm E a, mulChi a χ φ ∈ gard μ →
    (∀ X, mulChi a χ (lie E a X φ) ∈ gard μ) ∧ (lie E a (oneL E a) φ = -(r : ℂ) • φ → IsSq r φ)

def TwCpt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (r : ℝ) (χ : HChar E), IsTw (a := a) r χ → ∀ φ : Sm E a,
    (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → HasLev φ → lie E a (oneL E a) φ = -(r : ℂ) • φ →
    (∃ R : ℝ, ∀ g, R < qht g → φ.1 g = 0) → mulChi a χ φ ∈ gard μ

def FnProj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (r : ℝ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ c : ℝ, ∃ N P Q S, Good r N ∧ IsRes N (casA r c e) P Q S

def LevLin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ),
    (∀ (α β : Co Ξ q) (s t : ℂ), IsLev U Ξ α → IsLev U Ξ β → IsLev U Ξ (s • α + t • β)) ∧
    (∀ (α β : Co Ξ q) (s t : ℂ), dCo (smLie Ξ) (s • α + t • β) = s • dCo (smLie Ξ) α + t • dCo (smLie Ξ) β) ∧
    (∀ (α : Co Ξ q), IsLev U Ξ α → ∀ X i, IsLevelFn U Ξ (cmp i (α X))) ∧
    ∀ (T : Module.End ℂ (Sm E a)) (α : Co Ξ q) X i, cmp i (app T α X) = T (cmp i (α X))

def AppFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (r : ℝ), HasOne Ξ r → ∀ N : Submodule ℂ (Sm E a), Good r N → ∀ T, IsOp N T →
    ∀ (q : ℕ) (ω : Co Ξ q), IsLev U Ξ ω → Val N ω →
      IsLev U Ξ (app T ω) ∧ Val N (app T ω) ∧ Val (sqSub E a r) (app T ω) ∧
        dCo (smLie Ξ) (app T ω) = app T (dCo (smLie Ξ) ω)

def CasB : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (Ξ : AlgRep E a) (r : ℝ), ∃ c : ℝ, HasCas Ξ r c e

def SmAB : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a), IsLieHom (smA Ξ) ∧ IsLieHom (smB Ξ) ∧ (∀ X Y, Commute (smA Ξ X) (smB Ξ Y)) ∧
    (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), smK Ξ k * smA Ξ (toL X) = smA Ξ (toL (k.1 * X * star k.1)) * smK Ξ k) ∧
    (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), smK Ξ k * smB Ξ (toL X) = smB Ξ (toL (k.1 * X * star k.1)) * smK Ξ k) ∧
    ∀ (q : ℕ) (ω : Co Ξ q), IsCochain (smK Ξ) ω → InfEq (smLie Ξ) ω

def KugaSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (Ξ : AlgRep E a) (r c : ℝ), HasCas Ξ r c e →
    (∀ ω : Co Ξ 0, IsCochain (smK Ξ) ω → dCo (smLie Ξ) ω = 0 → app (casA r c e) ω = 0) ∧
    ∀ (q : ℕ) (ω : Co Ξ (q + 1)), IsCochain (smK Ξ) ω → dCo (smLie Ξ) ω = 0 →
      app (casA r c e) ω = -dCo (smLie Ξ) (del (smAdj Ξ r) e ω)

def DelLev : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (r : ℝ) (q : ℕ) (ω : Co Ξ (q + 1)),
    (IsLev U Ξ ω → IsLev U Ξ (del (smAdj Ξ r) e ω)) ∧ (Val (sqSub E a r) ω → Val (sqSub E a r) (del (smAdj Ξ r) e ω))

def SqOrth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (Ξ : AlgRep E a) (r : ℝ) (q : ℕ),
    (∀ ω : Co Ξ q, Val (sqSub E a r) ω → Coclosed (smAdj Ξ r) e ω → ExactIn (sqSub E a r) ω → ω = 0) ∧
    ∀ ω : Co Ξ (q + 1), Val (sqSub E a r) ω → Val (sqSub E a r) (del (smAdj Ξ r) e ω) →
      dCo (smLie Ξ) (del (smAdj Ξ r) e ω) = 0 → del (smAdj Ξ r) e ω = 0

def WigHom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (L : Lie E a →ₗ[ℝ] Module.End ℂ M)
    (α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M) (z : Module.End ℂ M),
    (∀ (Y : Matrix (Fin a) (Fin a) (Cinf E)) (f f' : Lie E a →ₗ[ℝ] M),
      (∀ X, L (toL Y) (f (toL X)) = f' (toL X) + f (toL (Y * X - X * Y))) → L (toL Y) (α f) = α f') →
    (∀ (m : M) (f : Lie E a →ₗ[ℝ] M), (∀ X, f X = L X m) → α f = z m) →
    (∀ ω : Herm E a [⋀^Fin 0]→ₗ[ℝ] M, InfEq L ω → dCo L ω = 0 → ∀ Y, z (ω Y) = 0) ∧
    ∀ (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M), InfEq L ω → dCo L ω = 0 →
      ∃ η : Herm E a [⋀^Fin q]→ₗ[ℝ] M, ∀ Y, dCo L η Y = z (ω Y)

def WigAlpha : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (LA LB : Lie E a →ₗ[ℝ] Module.End ℂ M),
    IsLieHom LA → IsLieHom LB → (∀ X Y, Commute (LA X) (LB Y)) → ∀ (τ : E →+* ℂ) (x : ℂ),
    ∃ α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M,
      (∀ (Y : Matrix (Fin a) (Fin a) (Cinf E)) (f f' : Lie E a →ₗ[ℝ] M),
        (∀ X, (LA + LB) (toL Y) (f (toL X)) = f' (toL X) + f (toL (Y * X - X * Y))) → (LA + LB) (toL Y) (α f) = α f') ∧
      ∀ (m : M) (f : Lie E a →ₗ[ℝ] M), (∀ X, f X = (LA + LB) X m) → α f =
        (Formalism.REAL.qdet (eL LA τ) x - (Formalism.REAL.qdet (fun i j => -MulOpposite.op (eL LB τ i j)) x).unop) m

def WigSub : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (LA LB : Lie E a →ₗ[ℝ] Module.End ℂ M),
    IsLieHom LA → IsLieHom LB → (∀ X Y, Commute (LA X) (LB Y)) → ∀ N : Submodule ℂ M, (∀ X, ∀ m ∈ N, LA X m ∈ N) →
    (∀ X, ∀ m ∈ N, LB X m ∈ N) → ∀ (τ : E →+* ℂ) (x : ℂ) (z : Module.End ℂ M),
    z = Formalism.REAL.qdet (eL LA τ) x - (Formalism.REAL.qdet (fun i j => -MulOpposite.op (eL LB τ i j)) x).unop →
    (∀ ω : Herm E a [⋀^Fin 0]→ₗ[ℝ] M, InfEq (LA + LB) ω → dCo (LA + LB) ω = 0 → ∀ Y, z (ω Y) = 0) ∧
    ∀ (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M), InfEq (LA + LB) ω → dCo (LA + LB) ω = 0 → (∀ Y, ω Y ∈ N) →
      ∃ η : Herm E a [⋀^Fin q]→ₗ[ℝ] M, (∀ Y, η Y ∈ N) ∧ ∀ Y, dCo (LA + LB) η Y = z (ω Y)

def CapSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (τ : E →+* ℂ) (u : ℂ),
    Formalism.REAL.qdet (eL (smA Ξ) τ) (u + ((a : ℂ) - 1) / 2) = (cap τ u).rTensor (Fin Ξ.d → ℂ) ∧
    (∀ m : Multiset ℂ, AlgInfChar Ξ τ (m.map Neg.neg) →
      (Formalism.REAL.qdet (fun i j => -MulOpposite.op (eL (smB Ξ) τ i j)) (u + ((a : ℂ) - 1) / 2)).unop = (m.map (u + ·)).prod • 1) ∧
    (∀ X, Commute (lie E a X) (cap τ u)) ∧
    ∀ N : Submodule ℂ (Sm E a), (∀ X, ∀ φ ∈ N, lie E a X φ ∈ N) → ∀ φ ∈ N, cap τ u φ ∈ N

def WigSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (N : Submodule ℂ (Sm E a)), (∀ X, ∀ φ ∈ N, lie E a X φ ∈ N) →
    ∀ (τ : E →+* ℂ) (m : Multiset ℂ), AlgInfChar Ξ τ (m.map Neg.neg) → ∀ (u : ℂ) (q : ℕ) (ω : Co Ξ q),
    IsCochain (smK Ξ) ω → dCo (smLie Ξ) ω = 0 → Val N ω → ExactIn N (app (cap τ u - (m.map (u + ·)).prod • 1) ω)

def CharOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (Ξ : AlgRep E a) (r : ℝ) (m : (E →+* ℂ) → Multiset ℂ),
    (∀ t, AlgInfChar Ξ t ((m t).map Neg.neg)) → ∀ (q : ℕ) (ω : Co Ξ q), IsCochain (smK Ξ) ω → dCo (smLie Ξ) ω = 0 →
    Coclosed (smAdj Ξ r) e ω → Val (sqSub E a r) ω → ∀ X i, HasChar m (cmp i (ω X))

def KType : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
    (ρ : Representation ℂ (Kinf E a) W), GlobalTheory.Published.AutFin.IsContRep ρ ∧ ∀ ω : Co Ξ q, IsCochain (smK Ξ) ω → ∀ X i,
      ∃ (T : W →ₗ[ℂ] Sm E a) (w : W), (∀ k v, T (ρ k v) = cptRep E a k (T v)) ∧ T w = cmp i (ω X)

def AutOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (m : (E →+* ℂ) → Multiset ℂ) (q : ℕ) (ω : Co Ξ q),
    IsLev U Ξ ω → ∀ X i, HasChar m (cmp i (ω X)) → Grow (cmp i (ω X)).1 → IsAutForm (cmp i (ω X))

def AbsSolve : Prop :=
  ∀ (I J : Type) (L : J → I →₀ ℂ) (c : J → ℂ) (cn : ℕ → J → ℂ),
    (∀ k, ∃ b : I → ℂ, ∀ j, (L j).sum (fun i x => x * b i) = cn k j) → (∀ j, Tendsto (fun k => cn k j) atTop (𝓝 (c j))) →
    ∃ b : I → ℂ, ∀ j, (L j).sum (fun i x => x * b i) = c j

def HCobLim : Prop :=
  ∀ (Γ S : Type) [Group Γ] (d : ℕ) (ρ : Representation ℂ Γ (S → Fin d → ℂ)),
    (∀ γ s, ∃ (s' : S) (B : Matrix (Fin d) (Fin d) ℂ), ∀ f, ρ γ f s = B *ᵥ f s') →
    ∀ (q : ℕ) (c : List Γ → S → Fin d → ℂ) (cn : ℕ → List Γ → S → Fin d → ℂ), (∀ k, HCob ρ q (c - cn k)) →
    (∀ x : List Γ, x.length = q + 1 → ∀ s, Tendsto (fun k => cn k x s) atTop (𝓝 0)) → HCob ρ q c

def ConeD : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [CompleteSpace F] (Y : Set V), IsOpen Y → Convex ℝ Y → ∀ p ∈ Y,
    ∀ (q : ℕ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F), ContDiffOn ℝ (⊤ : ℕ∞) w Y → ContDiffOn ℝ (⊤ : ℕ∞) (coneOp p w) Y ∧
      ((∀ x ∈ Y, extDeriv w x = 0) → ∀ x ∈ Y, extDeriv (coneOp p w) x = w x)

def ConeLim : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] (Y : Set V), Convex ℝ Y → ∀ p ∈ Y, ∀ (q : ℕ) (w : ℕ → V → V [⋀^Fin (q + 1)]→L[ℝ] F),
    (∀ K ⊆ Y, IsCompact K → TendstoUniformlyOn w 0 atTop K) →
    ∀ K ⊆ Y, IsCompact K → TendstoUniformlyOn (fun k => coneOp p (w k)) 0 atTop K

def PoinOp : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d), Convex ℝ G.Y → ∀ q : ℕ, ∃ K : V → G.Om (q + 1) → G.Om q,
    (∀ p ∈ G.Y, ∀ w, G.dOm (q + 1) w = 0 → G.dOm q (K p w) = w) ∧
    (∀ γ, ∀ p ∈ G.Y, ∀ w, G.act q γ (K p w) = K (G.ρ γ p) (G.act (q + 1) γ w)) ∧
    ∀ p ∈ G.Y, ∀ w : ℕ → G.Om (q + 1), FLim G w → FLim G fun k => K p (w k)

def HdHd : Prop :=
  ∀ (Γ M : Type) [Group Γ] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Γ M) (k : ℕ) (b : List Γ → M),
    HEquiv ρ k b → HCoc ρ (k + 1) (hd b)

def ZigLim : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d), Convex ℝ G.Y → G.Y.Nonempty → ∀ (q k : ℕ) (u : ℕ → List Γ → G.Om q),
    (∀ j, HCoc (G.act q) k (u j)) → (∀ j (x : List Γ), x.length = k + 1 → G.dOm q (u j x) = 0) →
    (∀ x : List Γ, x.length = k + 1 → FLim G fun j => u j x) →
    ∃ c : ℕ → List Γ → S → Fin d → ℂ, (∀ j, Zig G q k (u j) (c j)) ∧
      ∀ x : List Γ, x.length = k + q + 1 → ∀ s, Tendsto (fun j => c j x s) atTop (𝓝 0)

def ConeCpt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∀ K ⊆ cone E a, IsCompact K →
    ∃ C : Set (GL (Fin a) (Cinf E)), IsCompact C ∧ ∀ p ∈ K, ∃ g ∈ C, sand g (hOne E a) = p

def CorrLim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (ω : ℕ → Co Ξ q) (w : ℕ → (geo ho U Ξ).Om q),
    (∀ k, Corr U Ξ (ω k) (w k).1) → CoLim ω → FLim (geo ho U Ξ) w

def PerLim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (ω : ℕ → Co Ξ q), (∀ k, IsLev U Ξ (ω k)) → (∀ k, dCo (smLie Ξ) (ω k) = 0) →
    CoLim ω → ∃ c : ℕ → List (⊤ : Subgroup (GL (Fin a) E)) → (GL (Fin a) (Af E) ⧸ U) → Fin Ξ.d → ℂ, (∀ k, IsPer U Ξ (ω k) (c k)) ∧
      ∀ x : List (⊤ : Subgroup (GL (Fin a) E)), x.length = q + 1 → ∀ s, Tendsto (fun k => c k x s) atTop (𝓝 0)

def ExactLim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))), IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (β : Co Ξ q) (ω : ℕ → Co Ξ q),
    IsLev U Ξ β → dCo (smLie Ξ) β = 0 → (∀ k, IsLev U Ξ (ω k)) → (∀ k, dCo (smLie Ξ) (ω k) = 0) → CoLim ω →
    (∀ k, IsRelExact U Ξ (β - ω k)) → IsRelExact U Ξ β

def ResExact : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (r c : ℝ), HasCas Ξ r c e → ∀ (q : ℕ) (ω : Co Ξ q),
    IsLev U Ξ ω → dCo (smLie Ξ) ω = 0 → IsRelExact U Ξ (app (casA r c e) ω) ∧
      (Val (sqSub E a r) ω → app (casA r c e) ω = 0 → Coclosed (smAdj Ξ r) e ω)

def HodgeEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ), HasOne Ξ r → ∀ (q : ℕ) (α : Co Ξ q),
    IsLev U Ξ α → dCo (smLie Ξ) α = 0 → CSupp α → ∃ h : Co Ξ q, IsLev U Ξ h ∧ dCo (smLie Ξ) h = 0 ∧
      Coclosed (smAdj Ξ r) e h ∧ Val (sqSub E a r) h ∧ (∀ X i, Grow (cmp i (h X)).1) ∧ IsRelExact U Ξ (α - h)

def AbsSS : Prop :=
  ∀ (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W)
    (M : Submodule ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsPos B M → (∀ g, ∀ v ∈ M, ρ g v ∈ M) →
    (∀ g, ∃ c : ℂ, ∀ v ∈ M, ∀ w ∈ M, B (ρ g v) (ρ g w) = c * B v w) →
    (∀ v ∈ M, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧ ∀ u ∈ U, ρ u v = v) →
    (∀ U : Subgroup G, IsOpen (U : Set G) → FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ M ∧ ∀ u ∈ U, ρ u v = v})) →
    ∀ N ≤ M, (∀ g, ∀ v ∈ N, ρ g v ∈ N) → ∃ N' ≤ M, (∀ g, ∀ v ∈ N', ρ g v ∈ N') ∧ N ⊓ N' = ⊥ ∧ N ⊔ N' = M

def PetInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ r : ℝ, (∀ x (φ : Sm E a), IsSq r φ → IsSq r (act (.fin x) φ)) ∧
    ∃ H : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ, IsPos H (sqSub E a r) ∧ ∀ x, ∃ c : ℂ, ∀ φ ∈ sqSub E a r, ∀ ψ ∈ sqSub E a r,
      H (act (.fin x) φ) (act (.fin x) ψ) = c * H φ ψ

def CoForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (Ξ : AlgRep E a) (r : ℝ) (q : ℕ), ∃ (ρ : Representation ℂ (GL (Fin a) (Af E)) (Co Ξ q))
    (B : Co Ξ q →ₗ⋆[ℂ] Co Ξ q →ₗ[ℂ] ℂ), (∀ x ω, ρ x ω = trans x ω) ∧
    (∀ M : Submodule ℂ (Co Ξ q), (∀ ω ∈ M, Val (sqSub E a r) ω) → IsPos B M) ∧
    ∀ x, ∃ c : ℂ, ∀ ω η : Co Ξ q, Val (sqSub E a r) ω → Val (sqSub E a r) η → B (trans x ω) (trans x η) = c * B ω η

def HarmSub : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (Ξ : AlgRep E a) (r : ℝ) (m : (E →+* ℂ) → Multiset ℂ) (q : ℕ),
    ∃ M : Submodule ℂ (Co Ξ q), (∀ ω, ω ∈ M ↔ IsH r m ω) ∧ ∀ x, ∀ ω ∈ M, trans x ω ∈ M

def HarmFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (m : (E →+* ℂ) → Multiset ℂ) (q : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    FiniteDimensional ℂ (Submodule.span ℂ {ω : Co Ξ q | IsH r m ω ∧ ∀ u ∈ U, trans u ω = ω})

def HarmSS : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (Ξ : AlgRep E a) (r : ℝ) (m : (E →+* ℂ) → Multiset ℂ) (q : ℕ) (M : Submodule ℂ (Co Ξ q)),
    (∀ ω, ω ∈ M ↔ IsH r m ω) → (∀ x, ∀ ω ∈ M, trans x ω ∈ M) →
    ∀ N ≤ M, (∀ x, ∀ ω ∈ N, trans x ω ∈ N) → ∃ N' ≤ M, (∀ x, ∀ ω ∈ N', trans x ω ∈ N') ∧ N ⊓ N' = ⊥ ∧ N ⊔ N' = M

theorem partH_of (h0 : ExactSub) (h1 : FrameEx) (h2 : OneReal) (h3 : HarmSub) (h4 : HarmSS) (h5 : HodgeEx) (h6 : CharOf)
    (h7 : AutOf) : PartH := by
  refine partH_of_ss h0 fun E _ _ _ a ha Ξ m hm q => ?_
  obtain ⟨n, e, he⟩ := h1 E a
  obtain ⟨r, hr⟩ := h2 E a Ξ
  obtain ⟨M, hM, hT⟩ := h3 E a ha Ξ r m q
  refine ⟨M, hT, fun ω h => ⟨((hM ω).1 h).lev, ((hM ω).1 h).closed⟩, fun ω h => ((hM ω).1 h).aut,
    h4 E a ha Ξ r m q M hM hT, ?_⟩
  rintro α ⟨U, hUo, hUc, hα⟩ hd hs
  obtain ⟨h, p1, p2, p3, p4, p5, p6⟩ := h5 E a ha n e he U hUo hUc Ξ r hr q α hα hd hs
  have hc := h6 E a ha n e he Ξ r m hm q h p1.equiv p2 p3 p4
  exact ⟨h, (hM h).2 ⟨⟨U, hUo, hUc, p1⟩, p2, fun X i => ⟨h7 E a U hUo Ξ m q h p1 X i (hc X i) (p5 X i), hc X i⟩, p4⟩,
    U, hUo, hUc, p6⟩

end UpperTheory.V.Cj.H
