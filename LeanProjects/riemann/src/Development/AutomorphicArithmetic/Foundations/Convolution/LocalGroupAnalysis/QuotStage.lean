import Mathlib
import GroundTheory.AutomorphicForms.QuotientMeasure
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc GroundTheory.Automorphic Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

def Uni {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) : Prop :=
  μ.IsHaarMeasure ∧ μ.IsInvInvariant

section

variable {G T : Type} [Group G] [MeasurableSpace G] [Group T] [MeasurableSpace T]

def Pair [TopologicalSpace G] [TopologicalSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T) : Prop :=
  Uni μ ∧ IsClosedEmbedding j ∧ Uni ν

def IsNrm (j : T →* G) (ν : Measure T) (ρ : G → ℝ≥0∞) : Prop := Measurable ρ ∧ ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1

open Classical in

def qI (μ : Measure G) (j : T →* G) (ν : Measure T) (F : G → ℂ) : ℂ :=
  if h : ∃ ρ, IsNrm j ν ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μ else 0

def QInt (μ : Measure G) (j : T →* G) (ν : Measure T) (F : G → ℂ) : Prop :=
  Measurable F ∧ (∀ t g, F (j t * g) = F g) ∧ ∀ ρ, IsNrm j ν ρ → Integrable (fun x => F x * ((ρ x).toReal : ℂ)) μ

end

def NormEx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∃ ρ : G → NNReal, Continuous ρ ∧ IsNrm j ν (fun g => ρ g) ∧
      ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧ ∀ g ∈ Set.range j * C, ρ g ≠ 0 → g ∈ D

def QuotEq : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) → ∀ ρ, IsNrm j ν ρ →
      (QInt μ j ν F ↔ Integrable (fun x => F x * ((ρ x).toReal : ℂ)) μ) ∧ (QInt μ j ν F ↔ ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ ≠ ⊤) ∧
      qI μ j ν F = ∫ x, F x * ((ρ x).toReal : ℂ) ∂μ

def QIntCpt : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ (F : G → ℂ) (C : Set G), Measurable F → (∀ t g, F (j t * g) = F g) → IsCompact C →
      (∀ g, F g ≠ 0 → g ∈ Set.range j * C) → (∃ b, ∀ g ∈ C, ‖F g‖ ≤ b) → QInt μ j ν F

def QuotLin : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    (∀ (ι : Type) (s : Finset ι) (c : ι → ℂ) (F : ι → G → ℂ), (∀ i ∈ s, QInt μ j ν (F i)) →
      QInt μ j ν (fun g => ∑ i ∈ s, c i * F i g) ∧ qI μ j ν (fun g => ∑ i ∈ s, c i * F i g) = ∑ i ∈ s, c i * qI μ j ν (F i)) ∧
    ∀ (a b : NNReal), a ≠ 0 → b ≠ 0 → Pair (a • μ) j (b • ν) ∧ ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) →
      (QInt (a • μ) j (b • ν) F ↔ QInt μ j ν F) ∧ qI (a • μ) j (b • ν) F = ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) * qI μ j ν F

def QuotMap : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (G' : Type) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [LocallyCompactSpace G'] [T2Space G']
    [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (T' : Type) [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [LocallyCompactSpace T'] [T2Space T']
    [SecondCountableTopology T'] [MeasurableSpace T'] [BorelSpace T'] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ (μ' : Measure G') (j' : T' →* G') (ν' : Measure T'), Pair μ' j' ν' → ∀ (e : G ≃ₜ* G') (y : G'), μ.map e = μ' → ν.map (fun t => e (j t)) = ν'.map j' →
      ∀ F : G' → ℂ, Measurable F → (∀ t g, F (j' t * g) = F g) →
        (QInt μ j ν (fun g => F (e g * y)) ↔ QInt μ' j' ν' F) ∧ qI μ j ν (fun g => F (e g * y)) = qI μ' j' ν' F

def QuotConj : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν → ∀ x : G,
    Pair μ ((MulAut.conj x⁻¹).toMonoidHom.comp j) ν ∧ ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) →
      (QInt μ ((MulAut.conj x⁻¹).toMonoidHom.comp j) ν (fun g => F (x * g)) ↔ QInt μ j ν F) ∧
      qI μ ((MulAut.conj x⁻¹).toMonoidHom.comp j) ν (fun g => F (x * g)) = qI μ j ν F

def QuotStage : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ Γ : Subgroup T, DiscreteTopology Γ → ∀ D : Set T, IsFundamentalDomain Γ D ν → ν D ≠ ⊤ →
      Pair μ (j.comp Γ.subtype) Measure.count ∧ ∀ F, QInt μ j ν F →
        QInt μ (j.comp Γ.subtype) Measure.count F ∧
        qI μ (j.comp Γ.subtype) Measure.count F = ((ν D).toReal : ℂ) * qI μ j ν F

def QuotDisc : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    (Γ : Subgroup G) [DiscreteTopology Γ], Pair μ Γ.subtype Measure.count ∧
    ∀ F : G → ℂ, Continuous F → (∀ h ∈ Γ, ∀ g, F (h * g) = F g) →
      (QInt μ Γ.subtype Measure.count F ↔
        Integrable (fun y : RightCosetSpace Γ => F (Quotient.out y)) (RightCosetSpace.quotientMeasure Γ μ)) ∧
      qI μ Γ.subtype Measure.count F = ∫ y : RightCosetSpace Γ, F (Quotient.out y) ∂(RightCosetSpace.quotientMeasure Γ μ)

def Unfold : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), Uni μ → ∀ (Γ : Subgroup G), DiscreteTopology Γ →
    ∀ θ : Monoid.End G, Continuous θ → (∀ γ ∈ Γ, θ γ ∈ Γ) → ∀ f : G → ℂ, Continuous f → HasCompactSupport f →
    ∀ S : Finset G, (∀ s ∈ S, s ∈ Γ) → (∀ s ∈ S, ∀ s' ∈ S, (∃ γ ∈ Γ, s' = twConj θ γ s) → s = s') →
      (∀ δ ∈ Γ, (∃ x, f (twConj θ x δ) ≠ 0) → ∃ s ∈ S, ∃ γ ∈ Γ, δ = twConj θ γ s) →
      (∀ s ∈ S, QInt μ (Γ ⊓ twCent θ s).subtype Measure.count fun g => f (twConj θ g s)) →
      QInt μ Γ.subtype Measure.count (fun x => ∑ᶠ γ : Γ, f (x⁻¹ * γ * θ x)) ∧
      qI μ Γ.subtype Measure.count (fun x => ∑ᶠ γ : Γ, f (x⁻¹ * γ * θ x)) =
        ∑ s ∈ S, qI μ (Γ ⊓ twCent θ s).subtype Measure.count fun g => f (twConj θ g s)

def QuotProd : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (G' : Type) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [LocallyCompactSpace G'] [T2Space G']
    [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (T' : Type) [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [LocallyCompactSpace T'] [T2Space T']
    [SecondCountableTopology T'] [MeasurableSpace T'] [BorelSpace T'] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ (μ' : Measure G') (j' : T' →* G') (ν' : Measure T'), Pair μ' j' ν' → Pair (μ.prod μ') (j.prodMap j') (ν.prod ν') ∧
      ∀ (F : G → ℂ) (F' : G' → ℂ), Measurable F → (∀ t g, F (j t * g) = F g) → Measurable F' → (∀ t g, F' (j' t * g) = F' g) →
        (QInt μ j ν F → QInt μ' j' ν' F' → QInt (μ.prod μ') (j.prodMap j') (ν.prod ν') (fun g => F g.1 * F' g.2)) ∧
        qI (μ.prod μ') (j.prodMap j') (ν.prod ν') (fun g => F g.1 * F' g.2) = qI μ j ν F * qI μ' j' ν' F'

def QuotPi : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)]
    [∀ i, BorelSpace (G i)] (T : ι → Type) [∀ i, Group (T i)] [∀ i, TopologicalSpace (T i)] [∀ i, IsTopologicalGroup (T i)]
    [∀ i, LocallyCompactSpace (T i)] [∀ i, T2Space (T i)] [∀ i, SecondCountableTopology (T i)] [∀ i, MeasurableSpace (T i)]
    [∀ i, BorelSpace (T i)]
    (μ : ∀ i, Measure (G i)) (j : ∀ i, T i →* G i) (ν : ∀ i, Measure (T i)), (∀ i, Pair (μ i) (j i) (ν i)) →
    ∀ J : (∀ i, T i) →* ∀ i, G i, (∀ t i, J t i = j i (t i)) → Pair (Measure.pi μ) J (Measure.pi ν) ∧
      ∀ F : ∀ i, G i → ℂ, (∀ i, Measurable (F i) ∧ ∀ t g, F i (j i t * g) = F i g) →
        ((∀ i, QInt (μ i) (j i) (ν i) (F i)) → QInt (Measure.pi μ) J (Measure.pi ν) (fun g => ∏ i, F i (g i))) ∧
        qI (Measure.pi μ) J (Measure.pi ν) (fun g => ∏ i, F i (g i)) = ∏ i, qI (μ i) (j i) (ν i) (F i)

def QuotOpen : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ U : Subgroup G, IsOpen (U : Set G) → ∀ i : U.comap j →* U, (∀ t, (i t : G) = j t) →
      Pair (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) ∧
      ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) → (∀ g, F g ≠ 0 → g ∈ Set.range j * (U : Set G)) →
        (QInt μ j ν F ↔ QInt (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) fun u => F u) ∧
        qI μ j ν F = qI (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) fun u => F u

def QuotCpt : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] [CompactSpace G] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    QInt μ j ν (fun _ => 1) ∧ qI μ j ν (fun _ => 1) = ((μ Set.univ).toReal : ℂ) / ((ν Set.univ).toReal : ℂ)

def QuotFub : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ (X : Type) [MeasurableSpace X] (m : Measure X) [SFinite m] (F : X → G → ℂ), Measurable (Function.uncurry F) →
      (∀ a t g, F a (j t * g) = F a g) → ∀ ρ, IsNrm j ν ρ → ∫⁻ a, ∫⁻ x, ‖F a x‖ₑ * ρ x ∂μ ∂m ≠ ⊤ →
      QInt μ j ν (fun g => ∫ a, F a g ∂m) ∧ qI μ j ν (fun g => ∫ a, F a g ∂m) = ∫ a, qI μ j ν (F a) ∂m

def QuotLoc : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H), Uni μ → IsClosed (H : Set G) → Uni ν →
    (∀ F : G → ℂ, Measurable F → (∀ h ∈ H, ∀ g, F (h * g) = F g) → quotIntegral μ H ν F = qI μ H.subtype ν F) ∧
    ∀ F : G → ℝ≥0∞, Measurable F → (∀ h ∈ H, ∀ g, F (h * g) = F g) → (∀ g, F g ≠ ⊤) →
      qI μ H.subtype ν (fun g => ((F g).toReal : ℂ)) = ((quotLIntegral μ H ν F).toReal : ℂ)

end UpperTheory.ConvolutionTheory.G
