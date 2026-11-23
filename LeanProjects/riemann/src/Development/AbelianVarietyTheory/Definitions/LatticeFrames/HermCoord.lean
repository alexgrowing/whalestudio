import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

noncomputable section

namespace GlobalTheory.SWC

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

def starM {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (g.map (sigR R σ)).transpose

def hermCoord {n : ℕ} (S : HermR R σ n) : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
  (fun a => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S.1 a a), fun p => S.1 p.1.1 p.1.2)

def hermMeas [TopologicalSpace R] [MeasurableSpace R] (lam : Measure (R ⊗[F] E)) (ν : Measure R) (n : ℕ) :
    Measure (HermR R σ n) :=
  Measure.comap (hermCoord R σ) ((Measure.pi fun _ => ν).prod (Measure.pi fun _ => lam))

def blkMat {n : ℕ} (b : R) (u : Fin n → R ⊗[F] E) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E) :=
  Matrix.of (Fin.cons (α := fun _ => Fin (n + 1) → R ⊗[F] E)
    (Fin.cons (α := fun _ => R ⊗[F] E) (algebraMap R (R ⊗[F] E) b) u)
    fun a => Fin.cons (α := fun _ => R ⊗[F] E) (sigR R σ (u a)) (S a))

variable [TopologicalSpace R] {M n : ℕ}

def DensAt (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (κ : Measure (HermR R σ n))
    (S : HermR R σ n) (m : Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ X, 0 ≤ φ X) →
    ∃ (U : Set (HermR R σ n)) (D : HermR R σ n → ℝ), IsOpen U ∧ S ∈ U ∧ ContinuousOn D U ∧ (∀ t ∈ U, 0 ≤ D t) ∧
      (∀ A ⊆ U, MeasurableSet A → ∫⁻ X in gramR R σ J ⁻¹' (Subtype.val '' A), ENNReal.ofReal (φ X) ∂μ =
        ∫⁻ t in A, ENNReal.ofReal (D t) ∂κ) ∧ D S = ∫ X, φ X ∂m

def GF (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (κ : Measure (HermR R σ n))
    (S : HermR R σ n) (m : Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  m {X | gramR R σ J X ≠ S.1} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ DensAt R σ J μ κ S m

def Tube [FiniteDimensional F E] [IsTopologicalRing R] [LocallyCompactSpace R] (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (κ : Measure (HermR R σ n)) (S : HermR R σ n)
    (m : Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  m {X | gramR R σ J X ≠ S.1} = 0 ∧ IsFiniteMeasureOnCompacts m ∧
  ∃ (U : Set (HermR R σ n)) (γ : HermR R σ n → Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsOpen U ∧ S ∈ U ∧
    ContinuousOn γ U ∧ γ S = 1 ∧ (∀ t ∈ U, IsUnit (γ t).det ∧ starM R σ (γ t) * S.1 * γ t = t.1) ∧
    ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞, Measurable φ →
      ∫⁻ X in gramR R σ J ⁻¹' (Subtype.val '' U), φ X ∂μ =
        ∫⁻ t in U, ((modu (R ⊗[F] E) (γ t).det ^ M * (modu (R ⊗[F] E) (γ t).det)⁻¹ ^ n : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ Y, φ (lrAct 1 (γ t) Y) ∂m ∂κ

def consTup (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (g : HA R σ J) (Y : Fin n → Fin M → R ⊗[F] E) :
    Fin (n + 1) → Fin (M + 1) → R ⊗[F] E :=
  Fin.cons (α := fun _ => Fin (M + 1) → R ⊗[F] E) (y 0) fun a =>
    ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix _ _ (R ⊗[F] E)).mulVec ((B.map (inclR R)).mulVec (Y a))

def StepN (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin n → Fin M → R ⊗[F] E))
    (N : Measure (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) : Prop :=
  ∀ f : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable f → ∀ s, IsSec R σ J x s →
    ∫⁻ X, f X ∂N = ∫⁻ y, ∫⁻ Y, f (consTup R σ J B y (s y) Y) ∂m' ∂m

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  {d : ℕ} {b : Module.Basis (Fin d) F E} {M n : ℕ}

def LocT (s : StdMeas b) (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) : Prop :=
  GF (Ainf F) σ J (tupMeas s.lamI n M) (hermMeas (Ainf F) σ s.lamI s.nuI n) (hermOf (Ainf F) σ T hT) mi ∧
    ∀ v, GF (Fv F v) σ J (tupMeas (s.lamV v) n M) (hermMeas (Fv F v) σ (s.lamV v) (s.nuV v) n) (hermOf (Fv F v) σ T hT) (mv v)

def IsStdT (s : StdMeas b) (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) : Prop :=
  ∃ mi mv, LocT σ s J T hT mi mv ∧ IsProd b ν mi mv

def SiegL (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (c : ℝ≥0)
    (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) : Prop :=
  ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), μ.IsHaarMeasure →
    IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ →
      meanL μ 𝓕 (fun h => ∑' X : {X : Fin n → Fin M → E | gramE σ J X = T},
        Φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin n → Fin M → E))) = c * ∫⁻ X, Φ X ∂ν

def kap (cE cF : ℝ≥0) (n M : ℕ) : ℝ≥0 := cE ^ (n * M) / (cF ^ n * cE ^ n.choose 2)

def Ratio (ri ti : ℝ≥0) (r t : HeightOneSpectrum (𝓞 F) → ℝ≥0) (c : ℝ≥0) : Prop :=
  ri ≠ 0 ∧ ti ≠ 0 ∧ (∀ v, r v ≠ 0) ∧ (∀ v, t v ≠ 0) ∧ (Function.mulSupport fun v => r v / t v).Finite ∧
    ri / ti * ∏ᶠ v, r v / t v = c

def SdConst (s : StdMeas b) (cE cF : ℝ≥0) : Prop :=
  cE ≠ 0 ∧ cF ≠ 0 ∧ ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      SdW F E σ M J (Ainf F) (psiInf F ψ) n μi → (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) →
      (∀ (νi : Measure (HermR (Ainf F) σ n)) (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n)),
        SdHerm F E σ (Ainf F) (psiInf F ψ) n νi → (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) →
        ∃ ri ti r t, μi = ri • tupMeas s.lamI n M ∧ νi = ti • hermMeas (Ainf F) σ s.lamI s.nuI n ∧
          (∀ v, μv v = r v • tupMeas (s.lamV v) n M) ∧ (∀ v, νv v = t v • hermMeas (Fv F v) σ (s.lamV v) (s.nuV v) n) ∧
          Ratio ri ti r t (kap cE cF n M)) ∧
      (n = 1 → ∀ (νi : Measure (Ainf F)) (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)),
        SdR (Ainf F) (psiInf F ψ) νi → (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) →
        ∃ ri ti r t, μi = ri • tupMeas s.lamI n M ∧ νi = ti • s.nuI ∧
          (∀ v, μv v = r v • tupMeas (s.lamV v) n M) ∧ (∀ v, νv v = t v • s.nuV v) ∧ Ratio ri ti r t (kap cE cF 1 M))

def OneL (s : StdMeas b) (cE cF : ℝ≥0) : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), 3 ≤ M → IsHermND σ J →
    β ≠ 0 → IsStdX s σ J β ν → SiegL σ J (fun _ _ : Fin 1 => algebraMap F E β) (kap cE cF 1 M) ν

end Global

end GlobalTheory.SWC

end
