import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory GlobalTheory.Doubling
open scoped TensorProduct ENNReal NNReal ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def schwartzA (θ : InfFam D) (m n : ℕ) : Submodule ℂ (Mx D m n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧
      φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))}

variable (A B : HSp D)

def nu0 (μ : Measure (GA D B)) (𝓕 : Set (GA D B)) (φ : WO A B → ℂ) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ∑' x : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ‖φ (actO A B 1 h⁻¹ (ratW B A x))‖ₑ ∂μ

def cols (x y : WO A B) : WO (dblSp A) B := (Matrix.fromCols x y).submatrix id finSumFinEquiv.symm

def fstCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inl j)

def sndCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inr j)

def half (D : D7) : AE D := incA D (1 / 2)

def onX (x : WO A B) : WO (dblSp A) B := cols A B (half D • x) (half D • x)

def onY (y : WO A B) : WO (dblSp A) B := cols A B y (-y)

def xOf (w : WO (dblSp A) B) : WO A B := fstCols A B w + sndCols A B w

def yOf (w : WO (dblSp A) B) : WO A B := half D • (fstCols A B w - sndCols A B w)

def schr (ψ : AddChar (AF D.host.F) ℂ) (w : WO (dblSp A) B) (φ : WO A B → ℂ) : WO A B → ℂ := fun x =>
  ψ (symplO (dblSp A) B (onX A B x) (onY A B (yOf A B w)) +
      symplOH (dblSp A) B (onX A B (xOf A B w)) (onY A B (yOf A B w))) * φ (x + xOf A B w)

def thetaFun (ψ : AddChar (AF D.host.F) ℂ) (φ : WO A B → ℂ) : WO (dblSp A) B → ℂ := fun w =>
  ∑' x : Matrix (Fin B.rank) (Fin A.rank) D.host.E, schr A B ψ w φ (ratW B A x)

def dblBox (f₁ f₂ : WO A B → ℂ) : WO (dblSp A) B → ℂ := fun w => f₁ (fstCols A B w) * conj (f₂ (sndCols A B w))

variable {A B}

def IsDblTranslate (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (F : WO (dblSp A) B → ℂ) (g : GA D (dblSp A))
    (φ' : WO A B → ℂ) : Prop :=
  φ' ∈ schwartzA θ B.rank A.rank ∧ thetaFun A B ψ φ' = omh (g, 1) F

def IsKhatFinite (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
    (F : WO (dblSp A) B → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {F' | ∃ k ∈ Khat A a, F' = omh (k, 1) F})

def IsFockTensor (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (sA : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ) (sB : D.what₂.Tau → Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (bA : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ) (bB : D.what₂.Tau → Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (f : WO A B → ℂ) : Prop :=
  ∃ (f₀ : WO A B → ℂ) (P : MvPolynomial (FVar D B.rank A.rank) ℂ), IsThetaFunO ψ A B f₀ ∧
    (∀ τ, IsFockVacAt (heisO ψ A B) θ τ (cplxO (sA τ) (sB τ)) f₀) ∧ f = pureTensorO ψ θ A B sA sB bA bB f₀ P

def thetaInt (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (μ : Measure (GA D B)) (𝓕 : Set (GA D B))
    (f₁ f₂ : WO A B → ℂ) (g₁ g₂ : GA D A) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ‖thetaKO om g₁ h f₁ * thetaKO om g₂ h f₂‖ₑ ∂μ

abbrev ht (V : HSp D) (g : GA D V) : ℝ≥0 := AdelicU.height D.sp.cm.sig V.gram g

variable (A B)

def DblGrowth : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χB : (AE D)ˣ →* Circle)
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsInfFam θ → IsWeilDatumO ψ (dblSp A) B 1 χB omh →
    ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
    ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
    ∀ φ ∈ schwartzA θ B.rank A.rank, IsKhatFinite omh a (thetaFun A B ψ φ) →
      ∃ (C : ℝ≥0) (N : ℕ), ∀ g : GA D (dblSp A),
        AllSome (IsDblTranslate ψ θ omh (thetaFun A B ψ φ) g) fun φ' =>
          nu0 A B μ 𝓕 φ' ≤ ((C * ht (dblSp A) g ^ N : ℝ≥0) : ℝ≥0∞)

def ThetaIntLe : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ A B χA χB om → IsWeilDatumO ψ (dblSp A) B 1 χB omh →
    ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
    ∀ sA sB bA bB (pA pB : D.what₂.Tau → ℕ), Formalism.IndefR.Fock.Sk.PairSetup ψ θ A B sA sB bA bB pA pB →
    ∀ f₁ f₂, IsFockTensor ψ θ sA sB bA bB f₁ → IsFockTensor ψ θ sA sB bA bB f₂ →
      ∀ g₁ g₂ : GA D A, AllSome (IsDblTranslate ψ θ omh (dblBox A B f₁ f₂) (io A (g₁, g₂))) fun φ' =>
        thetaInt om μ 𝓕 f₁ f₂ g₁ g₂ ≤ nu0 A B μ 𝓕 φ'

def ThetaIntGrowth : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)), IsWeilDatumO ψ A B χA χB om →
    ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
    ∀ sA sB bA bB (pA pB : D.what₂.Tau → ℕ), Formalism.IndefR.Fock.Sk.PairSetup ψ θ A B sA sB bA bB pA pB →
    ∀ f₁ f₂, IsFockTensor ψ θ sA sB bA bB f₁ → IsFockTensor ψ θ sA sB bA bB f₂ →
      ∃ (C : ℝ≥0) (N : ℕ), ∀ g₁ g₂ : GA D A,
        thetaInt om μ 𝓕 f₁ f₂ g₁ g₂ ≤ ((C * (ht A g₁ * ht A g₂) ^ N : ℝ≥0) : ℝ≥0∞)

def PairGrowth : Prop := DblGrowth A B ∧ ThetaIntLe A B ∧ ThetaIntGrowth A B

def InRange : Prop := 1 ≤ A.rank ∧ A.rank < B.rank ∧ (Cusp.wittIndex B = 0 ∨ A.rank + Cusp.wittIndex B < B.rank)

def ModerateGrowthAniso (D : D7) : Prop :=
  ∀ A B : HSp D, 1 ≤ A.rank → A.rank < B.rank → Cusp.wittIndex B = 0 → PairGrowth A B

def ModerateGrowthIso (D : D7) : Prop :=
  ∀ A B : HSp D, 1 ≤ A.rank → 0 < Cusp.wittIndex B → A.rank + Cusp.wittIndex B < B.rank → PairGrowth A B

def ModerateGrowth (D : D7) : Prop := ∀ A B : HSp D, InRange A B → PairGrowth A B

theorem half_add_half : half D + half D = 1 := by
  rw [half, ← map_add, add_halves, map_one]

theorem fstCols_cols (x y : WO A B) : fstCols A B (cols A B x y) = x := by
  ext i j; simp [fstCols, cols]

theorem sndCols_cols (x y : WO A B) : sndCols A B (cols A B x y) = y := by
  ext i j; simp only [sndCols, cols, Matrix.submatrix_apply, Equiv.symm_apply_apply]; rfl

theorem coords (x y : WO A B) : xOf A B (onX A B x) = x ∧ yOf A B (onX A B x) = 0 ∧
    xOf A B (onY A B y) = 0 ∧ yOf A B (onY A B y) = y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [xOf, yOf, onX, onY, fstCols_cols, sndCols_cols]
  · rw [← add_smul, half_add_half, one_smul]
  · simp
  · simp
  · rw [sub_neg_eq_add, smul_add, ← add_smul, half_add_half, one_smul]

end GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

end
