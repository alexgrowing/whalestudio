import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.SepPer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def eu {n : ℕ} (y : Fin n → ℂ) : ℝ := Real.sqrt (∑ i, ‖y i‖ ^ 2)

def hsn {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)

section Point

variable (θ : InfFam D) {V : HSp D}

abbrev cmp (τ : D.what₂.Tau) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ := infMat D.sp.cm.sig V.gram (θ τ) g

def nrm (A : Fr V) (x : GA D V) (τ : D.what₂.Tau) (y : Fin V.rank → D.host.E) : ℝ :=
  eu (A.fr τ *ᵥ (cmp θ τ x⁻¹ *ᵥ fun i => tauE D τ (y i)))

def latAt (Λ : Lat V) (x : GA D V) : Lat V :=
  Submodule.span (𝓞 D.host.E) {y | (Lev.finE V x⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
    Formalism.L2.Herm.hatL (F := D.host.F) Λ}

def Long (A : Fr V) (Λ : Lat V) (x : GA D V) (s : ℝ) : Prop :=
  ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ w ∈ 𝔪 • latAt Λ x, w ≠ 0 →
    s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, nrm θ A x τ w

def Lip (A : Fr V) (φ : GA D V → ℂ) (c : ℝ) : Prop :=
  ∀ x τ, ∀ X ∈ lieAt V τ, ∀ s : ℝ, ‖φ (x * oneP θ V τ X s) - φ x‖ ≤ c * |s| * hsn (A.fr τ * X * (A.fr τ)⁻¹)

variable {S : D.what₂.Tau → SPar} (M : DSModel V S)

def coefR (v a : ∀ τ, M.H τ) (g : GA D V) : ℂ := ∏ τ, ⟪v τ, M.rep τ (cmp θ τ g) (a τ)⟫_ℂ

open Classical in

def coef (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ) (g : GA D V) : ℂ :=
  if Lev.finE V g ∈ K then coefR θ M v a g else 0

def poin (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ) (c : GA D V) (a : ∀ τ, M.H τ) (g : GA D V) : ℂ :=
  ∑' γ : GQ V, coef θ M K v a (c * γ * g)

def DecayAt (τ : D.what₂.Tau) (v a : M.H τ) (N : ℕ) : Prop :=
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ‖⟪v, M.rep τ g a⟫_ℂ‖ * (1 + hsn g) ^ N ≤ C

def KDecay (v : ∀ τ, M.H τ) : Prop :=
  ∀ τ, v τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ∧ ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, DecayAt M τ (v τ) a (2 * V.rank ^ 2 + 1)

end Point

section Pack

variable (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1)

def zv : Fin V.rank → D.host.E := fun i => d.a i 0

def Adapted (A : Fr Y) (B : Fr V) : Prop :=
  ∀ τ (y : Fin Y.rank → ℂ) (a : ℂ),
    eu (B.fr τ *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A.fr τ *ᵥ y) ^ 2 + ‖a‖ ^ 2

variable {S S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S') (M : DSModel V S)

structure Pack where

  A : Fr Y

  B : Fr V

  v₀ : ∀ τ, M.H τ

  g₀ : GA D V

  w : M₀.Vec

variable {M₀ M}

def Pack.v (p : Pack M₀ M) : ∀ τ, M.H τ := fun τ => M.rep τ (cmp θ τ p.g₀) (p.v₀ τ)

structure Pack.Base (p : Pack M₀ M) : Prop where

  adapted : Adapted d p.A p.B

  real : p.g₀ ∈ GinfC V

  dec : ∀ τ, p.v₀ τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ∧ DecayAt M τ (p.v₀ τ) (p.v₀ τ) (2 * V.rank ^ 2 + 1)

  ne : ∀ τ, (p.w τ : M₀.H τ) ≠ 0

structure Pack.RealAt (p : Pack M₀ M) (Q : ℝ) (m : Measure (GinfC Y)) (c : ℂ) : Prop where

  ne : c ≠ 0

  act : ∀ b : ∀ τ, M₀.H τ, ∫ h : GinfC Y, coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h) * coefR θ M₀ b (fun τ => p.w τ) h ∂m =
    c * ∏ τ, ⟪b τ, (p.w τ : M₀.H τ)⟫_ℂ

  far : ∀ g : GA D V, Integrable (fun h : GinfC Y => coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d h)) m ∧
    (∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d h)‖ ∂m) * (∏ τ, nrm θ p.B g⁻¹ τ (zv d)) ^ (2 * V.rank + 5) ≤
      Real.exp Q * ‖c‖

  lip : ∀ τ, ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    ∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X s * h)) - coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h)‖ ∂m ≤
      Real.exp Q * ‖c‖ * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)

def Pack.Is (p : Pack M₀ M) (Q : ℝ) : Prop :=
  p.Base d ∧ ∀ m : Measure (GinfC Y), m.IsHaarMeasure → ∃ c, p.RealAt θ d Q m c

structure Pack.AdelicAt (p : Pack M₀ M) (Q : ℝ) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)) (ν : Measure (GA D Y)) (φ : GA D Y → ℂ)
    (c : ℂ) : Prop where

  ne : c ≠ 0

  one : ∀ x, ∫ h, coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h) * φ h ∂ν = c * φ x

  term : ∀ (x : GA D Y) (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z →
    Integrable (fun h => coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h)) ν ∧
    (∫ h, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h)‖ ∂ν) *
      (∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ z) ^ (2 * V.rank + 5) ≤ Real.exp Q * ‖c‖ ∧
    (z - zv d ∉ 𝔪 • latAt Λ (stabilizerEmbedding d x) →
      ∀ h, coef θ M (congLev D.sp.cm V.gram Λ 𝔪) (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h) = 0)

end Pack

def rdisc (D : D7) : ℝ := |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.E)

def loss (D : D7) (C b : ℝ) : ℝ := C * Fintype.card D.what₂.Tau * ((D.R.r : ℝ) + 1) ^ 4 * Real.log b

def Pays (D : D7) (Q N : ℝ) : Prop :=
  ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧
    Real.exp Q * ((D.R.r : ℝ) ^ 2 * Fintype.card D.what₂.Tau * (D.host.g 0 * D.host.g 1 : ℕ) * rdisc D * (2 * s) ^ ((1 : ℝ) / D.R.m)) ≤ 1 / 2 ∧
    2 * Real.exp (Q + (6 * ((D.R.r : ℝ) + 1) + 9) * Fintype.card D.what₂.Tau) ≤ s ^ Fintype.card D.what₂.Tau * Real.sqrt N ∧
    1 < s ^ Fintype.card D.what₂.Tau * Real.sqrt N

def PackEx : Prop := ∃ C : ℝ, 0 ≤ C ∧ Ev fun {D} _ _ {sc} {G} W _ => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), ∃ p : Pack M₀ MP, p.Is W.θ G.sp.dec0 (loss D C sc.b)

def DepthPays : Prop := ∀ C : ℝ, 0 ≤ C → Ev fun {D} _ _ {sc} {G} _ _ => Pays D (loss D C sc.b) (Ideal.absNorm G.modul)

theorem eu_zero {n : ℕ} : eu (0 : Fin n → ℂ) = 0 := by simp [eu]

theorem Long.mono {θ : InfFam D} {V : HSp D} {A : Fr V} {Λ : Lat V} {x : GA D V} {s s' : ℝ} (h : Long θ A Λ x s) (h0 : 0 ≤ s')
    (hs : s' ≤ s) : Long θ A Λ x s' := fun 𝔪 h1 w h2 h3 =>
  (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hs _) (Real.sqrt_nonneg _)).trans (h 𝔪 h1 w h2 h3)

end GlobalTheory.SepPer

end
