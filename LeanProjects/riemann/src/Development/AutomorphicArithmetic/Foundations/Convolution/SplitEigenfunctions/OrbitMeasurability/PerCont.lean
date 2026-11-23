import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.CuspRegions.CarrierEq

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

section Objects

variable {E : Type} [Field E] [NumberField E]

abbrev Orb (δ : ℚ) : Type := ↥{ξ : Fin 4 → ℚ | qr δ ξ = qr δ X0}
instance (δ : ℚ) : MeasurableSpace (Orb δ) := ⊤
variable (E) in

abbrev Y (δ : ℚ) : Type := ↥(IdeleGroup.normOneSubgroup E) × G1 E × Orb δ

def mY (δ : ℚ) (N : MeasE E) : Measure (Y E δ) :=
  ((normOneMeasure E).restrict (normOneFundamentalDomain E)).prod ((N.μ.restrict N.D).prod Measure.count)

def el (D : Dat ℚ E) (y : Y E D.δ) : GL (Fin 2) (A E) := gl y.2.1 * sZ D (y.1 : IdeleGroup E)

def pY (D : Dat ℚ E) (y : Y E D.δ) : V4 ℚ := D.act (el D y)⁻¹ (rp y.2.2.1)

end Objects

def AbsUnf : Prop := ∀ (G H ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] [Countable ι] [MeasurableSpace ι]
  [DiscreteMeasurableSpace ι] (μ : Measure G) (ν : Measure H) [μ.IsHaarMeasure] [ν.IsHaarMeasure] [μ.IsMulRightInvariant]
  [ν.IsMulRightInvariant] (j : H →* G) (Γ' : Subgroup G) (Γ : Subgroup H) [Countable Γ'] [Countable Γ] (DG : Set G) (DH : Set H)
  (r : ι → G) (φ c : G → ℂ), Continuous j → Function.Injective j → IsFundamentalDomain Γ' DG μ → IsFundamentalDomain Γ DH ν →
  ν DH < ⊤ → (∀ i, r i ∈ Γ') → (∀ δ ∈ Γ, j δ ∈ Γ') → (∀ γ ∈ Γ', ∃! i, ∃ δ ∈ Γ, γ = r i * j δ) →
  Measurable φ → (∀ γ ∈ Γ', ∀ x, φ (γ * x) = φ x) → (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) → Measurable c → Integrable c μ →
  (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → ∫⁻ p : G × ι, ‖(∫ g, c (j g * ((r p.2)⁻¹ * p.1)) ∂ν) * φ p.1‖ₑ ∂((μ.restrict DG).prod Measure.count) ≤
    ENNReal.ofReal B * ν DH * ∫⁻ y, ‖c y‖ₑ ∂μ) ∧
  ∫ p : G × ι, (∫ g, c (j g * ((r p.2)⁻¹ * p.1)) ∂ν) * φ p.1 ∂((μ.restrict DG).prod Measure.count) =
    ∫ y, c y * ∫ g in DH, φ (j g * y) ∂ν ∂μ

def ZDom : Prop := ∀ (E : Type) [Field E] [NumberField E], normOneMeasure E (normOneFundamentalDomain E) < ⊤ ∧
  MeasurableSet (normOneFundamentalDomain E) ∧ ∃ C : Set (A E)ˣ, IsCompact C ∧ ∀ z ∈ normOneFundamentalDomain E, ((z : IdeleGroup E) : (A E)ˣ) ∈ C

def Reps : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E), ∃ (j : G1 ℚ →* G1 E) (r : Orb D.δ → G1 E),
  (∀ g, gl (j g) = em E (gl g)) ∧ Continuous j ∧ Function.Injective j ∧ (∀ i, r i ∈ Gam E ∧ rp i.1 = D.act (gl (r i)) (rp X0)) ∧
  (∀ δ ∈ Gam ℚ, j δ ∈ Gam E) ∧ ∀ γ ∈ Gam E, ∃! i, ∃ δ ∈ Gam ℚ, γ = r i * j δ

def BddE : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2), ∀ φ ∈ P.V,
  ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ h : G1 E, ∀ k ∈ C, ‖φ.1 (gl h * k)‖ ≤ B

def YInt : Prop := All fun _ _ _ _ D _ _ N P => ∀ φ ∈ P.V, Measurable (pY D) ∧ Measurable (fun y => φ.1 (el D y)) ∧
  ∀ K, IsCompact K → ∃ n, Integrable (fun y => (wt K n (pY D y) : ℂ) * φ.1 (el D y)) (mY D.δ N)

def YEq : Prop := All fun _ _ _ _ D W _ N P => ∀ φ ∈ P.V, ∀ ph ∈ Fock D.δ,
  fOn W N {ξ | qr D.δ ξ = qr D.δ X0} ph φ.1 1 = ∫ y, ph.1 (pY D y) * φ.1 (el D y) ∂mY D.δ N

def ZOne : Prop := All fun E _ _ _ D _ M N P => ∀ φ ∈ P.V, ∀ (j : G1 ℚ →* G1 E), (∀ g, gl (j g) = em E (gl g)) →
  ∀ c : G1 E → ℂ, Continuous c → HasCompactSupport c → ∀ Ψ : V4 ℚ → ℂ,
    (∀ h : G1 E, Ψ (D.act (gl h)⁻¹ (rp X0)) = ∫ g, c (j g * h) ∂M.μ) → ∀ z : ↥(IdeleGroup.normOneSubgroup E),
    (∀ B : ℝ, (∀ h : G1 E, ‖φ.1 (gl h * sZ D (z : IdeleGroup E))‖ ≤ B) →
      ∫⁻ p : G1 E × Orb D.δ, ‖Ψ (pY D (z, p)) * φ.1 (el D (z, p))‖ₑ ∂((N.μ.restrict N.D).prod Measure.count) ≤
        ENNReal.ofReal B * M.μ M.D * ∫⁻ y, ‖c y‖ₑ ∂N.μ) ∧
    ∫ p : G1 E × Orb D.δ, Ψ (pY D (z, p)) * φ.1 (el D (z, p)) ∂((N.μ.restrict N.D).prod Measure.count) =
      ∫ y, c y * (SLP M fun x => φ.1 (x * sZ D (z : IdeleGroup E) * gl y)) ∂N.μ

def ZAll : Prop := All fun E _ _ _ D _ M N P => ∀ φ ∈ P.V, ∀ (j : G1 ℚ →* G1 E), (∀ g, gl (j g) = em E (gl g)) →
  ∀ c : G1 E → ℂ, Continuous c → HasCompactSupport c → ∀ Ψ : V4 ℚ → ℂ, Measurable Ψ →
    (∀ h : G1 E, Ψ (D.act (gl h)⁻¹ (rp X0)) = ∫ g, c (j g * h) ∂M.μ) →
    Integrable (fun y => Ψ (pY D y) * φ.1 (el D y)) (mY D.δ N) ∧
    ∫ y, Ψ (pY D y) * φ.1 (el D y) ∂mY D.δ N = ∫ y, c y * (UPer D M fun x => φ.1 (x * gl y)) ∂N.μ

def PerCont : Prop := All fun E _ _ _ D _ M _ P => ∀ φ ∈ P.V, Continuous fun h : G1 E => UPer D M fun x => φ.1 (x * gl h)

structure Bd (F : GL (Fin 2) (A ℚ) → ℂ) : Prop where
  cont : Continuous F
  left : LRat F
  bdd : ∃ B : ℝ, ∀ x, ‖F x‖ ≤ B
  cen : ∀ s x, F (GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s * x) = F x

def Ext : Prop := ∀ u : G1 ℚ → ℂ, CuspFn u → ∃ F : GL (Fin 2) (A ℚ) → ℂ, Bd F ∧ (∀ g, ∀ t ∈ UU, F (gl g * dM t) = u g) ∧
  ∀ x, ∫ b in fundamentalSet ℚ, F (gl (nU b) * x) ∂(adeleMeasure ℚ) = 0

def PairL : Prop := ∀ (μ : Measure (GroundTheory.Automorphic.Reduction.normOneGL ℚ 2)) [μ.IsHaarMeasure] (F : GL (Fin 2) (A ℚ) → ℂ), Bd F → F ≠ 0 →
  (∀ x, ∫ b in fundamentalSet ℚ, F (gl (nU b) * x) ∂(adeleMeasure ℚ) = 0) →
  ∃ π : TR.CuspSub ℚ 2, PosInv π ∧ ∃ f ∈ π.V,
    ∫ y, f.1 ((Quotient.out y : GroundTheory.Automorphic.Reduction.normOneGL ℚ 2) : GL (Fin 2) (A ℚ)) *
      F ((Quotient.out y : GroundTheory.Automorphic.Reduction.normOneGL ℚ 2) : GL (Fin 2) (A ℚ))
      ∂GroundTheory.Automorphic.RightCosetSpace.quotientMeasure (GroundTheory.Automorphic.Reduction.rationalGLOne ℚ 2) μ ≠ 0

def Fibre : Prop := ∀ (M : Meas ℚ) (μ : Measure (GroundTheory.Automorphic.Reduction.normOneGL ℚ 2)) [μ.IsHaarMeasure] (Φ : GL (Fin 2) (A ℚ) → ℂ),
  Bd Φ → (∀ t ∈ UU, ∫ g in M.D, Φ (gl g * dM t) ∂M.μ = 0) →
    ∫ y, Φ ((Quotient.out y : GroundTheory.Automorphic.Reduction.normOneGL ℚ 2) : GL (Fin 2) (A ℚ))
      ∂GroundTheory.Automorphic.RightCosetSpace.quotientMeasure (GroundTheory.Automorphic.Reduction.rationalGLOne ℚ 2) μ = 0

def FormBd : Prop := ∀ π : TR.CuspSub ℚ 2, PosInv π → ∀ f ∈ π.V, Bd f.1 ∧ ∀ t ∈ UU, ∃ f' ∈ π.V, ∀ x, f'.1 x = f.1 (x * dM t)

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
