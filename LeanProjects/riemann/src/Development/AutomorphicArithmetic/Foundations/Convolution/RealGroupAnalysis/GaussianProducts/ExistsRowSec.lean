import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G

section Base

variable {F : Type} [Field F] [NumberField F]

abbrev Rw (F : Type) [Field F] : Type := {r : Fin 2 → F // r ≠ 0}

abbrev FS2 (F : Type) [Field F] [NumberField F] : Set (Fin 2 → A F) := Set.univ.pi fun _ : Fin 2 => fundamentalSet F

def row (g : G1 F) : Fin 2 → A F := fun j => g 1 j

def pt (ξ : Fin 2 → F) : V4 F := ![0, 1, rt (ξ 0), rt (ξ 1)]

def chi (δ : F) (ξ : Fin 2 → F) (u : Fin 2 → A F) : ℂ := ψ (-(2 * (u 0 * rt (ξ 0) - rt δ * (u 1 * rt (ξ 1)))))

def av (u : G1 F → ℂ) (g : G1 F) : ℂ := ∫ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F)

def abelian₂ (M : Meas F) (u : G1 F → ℂ) : ℝ≥0∞ :=
  _root_.UpperTheory.ConvolutionTheory.R2.M.J0 M fun g => ∫⁻ b in fundamentalSet F, ‖u (nU b * g)‖ₑ ∂(adeleMeasure F)

def NInv (u : G1 F → ℂ) : Prop := Measurable u ∧ ∀ (c : F) g, u (nU (rt c) * g) = u g

def wt4 (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (v : V4 F) : ℝ := ∏ i, GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (v i)

theorem exists_rowSec : ∃ σ : Rw F → Matrix.SpecialLinearGroup (Fin 2) F, M.RowSec σ := by
  have h : ∀ r : Rw F, ∃ γ : Matrix.SpecialLinearGroup (Fin 2) F, γ.1 1 = r.1 := by
    rintro ⟨r, hr⟩
    by_cases h1 : r 1 = 0
    · have h0 : r 0 ≠ 0 := fun h0 => hr (by ext i; fin_cases i <;> simp [h0, h1])
      exact ⟨⟨!![0, -(r 0)⁻¹; r 0, r 1], by simp [Matrix.det_fin_two, h0]⟩, by ext i; fin_cases i <;> simp⟩
    · exact ⟨⟨!![(r 1)⁻¹, 0; r 0, r 1], by simp [Matrix.det_fin_two, h1]⟩, by ext i; fin_cases i <;> simp⟩
  choose σ hσ using h
  exact ⟨σ, hσ⟩

variable [IsTotallyReal F]

def qInf (δ : F) (v : V4 F) : ℝ := ∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w
theorem gauss_eq (δ : F) (v : V4 F) : gauss δ v = Complex.exp (-(Real.pi : ℂ) * (qInf δ v : ℝ)) := rfl

def FockFn (δ : F) : Submodule ℂ (V4 F → ℂ) :=
  Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
    φ = fun v => p v * gauss δ v * g (finPartPi v)}
theorem mem_fock {δ : F} {φ : S4 F} : φ ∈ Fock δ ↔ φ.1 ∈ FockFn δ := Iff.rfl

def polyOn (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ι : Type) : Subalgebra ℂ ((ι → A F) → ℂ) :=
  Algebra.adjoin ℂ {p | ∃ i w, p = fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)}

def sz (r : Fin 2 → A F) : ℝ := ∑ i, ∑ w, |TR.pInf F (r i) w|

end Base

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def nE (D : Dat F E) (u : Fin 2 → A F) : GL (Fin 2) (A E) := gl (nU (D.mkE (u 0) (u 1)))

def al (D : Dat F E) (ξ : Fin 2 → F) : (A E)ˣ :=
  if h : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ = 0 then 1 else IdeleGroup.diagonal E (Units.mk0 _ h)

structure Good (D : Dat F E) (Φ : GL (Fin 2) (A E) → ℂ) : Prop where
  left : ∀ γ h, Φ (ratGL E 2 γ * h) = Φ h
  int0 : ∀ h, IntegrableOn (fun u => Φ (nE D u * h)) (FS2 F) (adeleMeasurePi F)
  int1 : ∀ h, IntegrableOn (fun u => Φ (nE D u * h) * ψ (2 * u 0)) (FS2 F) (adeleMeasurePi F)
  zero : ∀ h, ∫ u in FS2 F, Φ (nE D u * h) ∂(adeleMeasurePi F) = 0
  sum : ∀ h, HasSum (fun ξ : Rw F => WE D Φ (aE (al D ξ.1) * h)) (Φ h)

variable [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (M : Meas F)

def ux (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (ξ : Fin 2 → F) (g : G1 F) : ℂ :=
  f (gl g * dM (nu F h)) * hat (W.Om g (W.L h φ)).1 (pt ξ)

def wx (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (ξ : Fin 2 → F) (g : G1 F) : ℂ :=
  (∫ b in fundamentalSet F, f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) ∂(adeleMeasure F)) *
    hat (W.Om g (W.L h φ)).1 (pt ξ)

def Wx (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (ξ : Fin 2 → F) : ℂ := M.I0 (wx W f φ h ξ)

end Ext

end UpperTheory.ConvolutionTheory.R2.G

end
