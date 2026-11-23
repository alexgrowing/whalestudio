import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Imports

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

def ThetaPt : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ Φ ∈ d.sch, ∀ (x : d.G) (h : UA σ d.A.J),
  thetaSum F (d.om x (d.S h Φ)) = ∑' X : Matrix (Fin d.m) (Fin d.n) E, d.T (d.om x Φ) (mat h⁻¹ * incM F X)

def FPSw : Prop := ∀ (m n : ℕ) (P : PX m n), IsSw (fP P)

def MatCount : Prop := ∀ (E : Type) [Field E] [NumberField E] (m n : ℕ), Countable (Matrix (Fin m) (Fin n) E)

def SplitDom : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w L, R.IsLocOp w L → ∀ Ψ ∈ R.away w, ∀ g : d.G,
  ∃ (y₀ : GR d.n) (Ψ' : Mx F E d.m d.n → ℂ),
    (∀ Φ ∈ d.sch, ∀ f, IsSw f → d.T Φ = R.tens w f Ψ → ∀ y, d.T (d.om (g * R.ι w y) Φ) = R.tens w (L (y₀ * y) f) Ψ') ∧
    ∀ δ : ℝ, 0 < δ → R.tens w (fun u => (Real.exp (-δ * sq u) : ℂ)) Ψ' ∈ d.schM

def DecompW : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w (g : d.G),
  ∃ (x : d.G) (y₀ : GR d.n), g = x * R.ι w y₀ ∧ d.cw w (inFrame d.b x) = 1

def ThetaBdd : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ Fn ∈ d.schM, ∃ K : ℝ, ∀ h : UA σ d.A.J,
  Summable (fun X : Matrix (Fin d.m) (Fin d.n) E => ‖Fn (mat h⁻¹ * incM F X)‖) ∧
    ∑' X : Matrix (Fin d.m) (Fin d.n) E, ‖Fn (mat h⁻¹ * incM F X)‖ ≤ K

def LocFam : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w L, R.IsLocOp w L →
  ∀ (X : Fin d.n → ℝ) (a : ℝ → GR d.n), (∀ t, IsDil X t (a t)) →
    (∀ z ∈ strip X, IsSw (fam d.m X z)) ∧ (∀ (y : GR d.n) (t : ℝ), L y (fam d.m X t) = L (y * a t) (fP 1)) ∧
    (∀ y u, DifferentiableOn ℂ (fun z => L y (fam d.m X z) u) (strip X)) ∧
    (∀ u, ContinuousOn (fun q : GR d.n × ℂ => L q.1 (fam d.m X q.2) u) (Set.univ ×ˢ strip X)) ∧
    ∀ q ∈ (Set.univ : Set (GR d.n)) ×ˢ strip X, ∃ N ∈ 𝓝 q, ∃ C δ : ℝ, 0 < δ ∧ ∀ q' ∈ N, q'.2 ∈ strip X → ∀ u,
      ‖L q'.1 (fam d.m X q'.2) u‖ ≤ C * Real.exp (-δ * sq u)

def LocDerBig : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w L, R.IsLocOp w L →
  ∀ (X : Fin d.n → ℝ) (y : GR d.n), ((mR y).toBlocks₂₂).det ≠ 0 → ∀ (r : ℕ) u,
    iteratedDeriv r (fun z => L y (fam d.m X z) u) 0 = L y (fP ((dil (2 * Real.pi) X ^ r) 1)) u

def LocFamG : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w L, R.IsLocOp w L →
  ∀ (X : Fin d.n → ℝ) (a : ℝ → GR d.n), (∀ t, IsDil X t (a t)) →
    ∃ Gf : GR d.n → ℂ → (Fin d.m → Fin d.n → ℂ) → ℂ, (∀ (y : GR d.n) (t : ℝ), Gf y t = L (y * a t) (fP 1)) ∧
    (∀ y u, DifferentiableOn ℂ (fun z => Gf y z u) (strip X)) ∧
    (∀ u, ContinuousOn (fun q : GR d.n × ℂ => Gf q.1 q.2 u) (Set.univ ×ˢ strip X)) ∧
    (∀ q ∈ (Set.univ : Set (GR d.n)) ×ˢ strip X, ∃ N ∈ 𝓝 q, ∃ C δ : ℝ, 0 < δ ∧ ∀ q' ∈ N, q'.2 ∈ strip X → ∀ u,
      ‖Gf q'.1 q'.2 u‖ ≤ C * Real.exp (-δ * sq u)) ∧
    ∀ y : GR d.n, ((mR y).toBlocks₂₂).det ≠ 0 → ∀ (r : ℕ) u,
      iteratedDeriv r (fun z => Gf y z u) 0 = L y (fP ((dil (2 * Real.pi) X ^ r) 1)) u

def BigDense : Prop := ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0}

def HolMean : Prop := ∀ (P Ω κ : Type) [TopologicalSpace P] [FirstCountableTopology P] [MeasurableSpace Ω] [Countable κ] (μ : Measure Ω) (U : Set ℂ),
  IsOpen U → (∀ z ∈ U, ∃ (t ρ : ℝ), 0 < ρ ∧ z ∈ Metric.ball (t : ℂ) ρ ∧ Metric.ball (t : ℂ) ρ ⊆ U) →
  ∀ F : P → ℂ → Ω → κ → ℂ, (∀ p ω k, DifferentiableOn ℂ (fun z => F p z ω k) U) →
    (∀ ω k, ContinuousOn (fun q : P × ℂ => F q.1 q.2 ω k) (Set.univ ×ˢ U)) →
    (∀ p (t : ℝ), (t : ℂ) ∈ U → AEStronglyMeasurable (fun ω => ∑' k, F p t ω k) μ) →
    (∀ q ∈ (Set.univ : Set P) ×ˢ U, ∃ N ∈ 𝓝 q, ∃ (M : Ω → κ → ℝ) (g : Ω → ℝ), (∀ ω, Summable (M ω)) ∧ Integrable g μ ∧ (∀ ω, ∑' k, M ω k ≤ g ω) ∧
      ∀ q' ∈ N, q'.2 ∈ U → ∀ ω k, ‖F q'.1 q'.2 ω k‖ ≤ M ω k) →
    ContinuousOn (fun q : P × ℂ => ∫ ω, ∑' k, F q.1 q.2 ω k ∂μ) (Set.univ ×ˢ U) ∧
      (∀ p, DifferentiableOn ℂ (fun z => ∫ ω, ∑' k, F p z ω k ∂μ) U) ∧
      ∀ p, ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ ω, ∑' k, F p z ω k ∂μ) z =
        ∫ ω, ∑' k, iteratedDeriv r (fun z => F p z ω k) z ∂μ

def DerCont : Prop := ∀ (P : Type) [TopologicalSpace P] (U : Set ℂ), IsOpen U → ∀ H : P → ℂ → ℂ,
  ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U) → (∀ p, DifferentiableOn ℂ (H p) U) →
    ∀ r : ℕ, ContinuousOn (fun q : P × ℂ => iteratedDeriv r (H q.1) q.2) (Set.univ ×ˢ U)

def StripOK : Prop := ∀ (n : ℕ) (X : Fin n → ℝ), IsOpen (strip X) ∧ (∀ t : ℝ, (t : ℂ) ∈ strip X) ∧
  ∀ z ∈ strip X, ∃ (t ρ : ℝ), 0 < ρ ∧ z ∈ Metric.ball (t : ℂ) ρ ∧ Metric.ball (t : ℂ) ρ ⊆ strip X

end PositivityTheory.SiegelWeilFormula.Kdil

end
