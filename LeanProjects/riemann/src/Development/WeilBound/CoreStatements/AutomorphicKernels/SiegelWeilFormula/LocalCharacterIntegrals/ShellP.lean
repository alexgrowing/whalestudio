import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (E) in

def bA (v : HeightOneSpectrum (𝓞 F)) : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)

def crd (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v ⊗[F] E) : Fin (Module.finrank F E) → Fv F v :=
  (bA E v).equivFun a

def nA (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v ⊗[F] E) : ℝ := ‖crd v a‖

def nV (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : Fin n → Fv F v ⊗[F] E) : ℝ := ‖fun i => crd v (y i)‖

def nM (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ} (x : Fin p → Fin q → Fv F v ⊗[F] E) : ℝ :=
  ‖fun i j => crd v (x i j)‖

structure Hyp (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (g : HermR (Fv F v) σ n → ℂ) (T : HermR (Fv F v) σ n) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  chr : IsCharAF F ψ
  sdW : SdW F E σ M J (Fv F v) (psiV F ψ v) n μv
  sdH : SdHerm F E σ (Fv F v) (psiV F ψ v) n νv
  haar : lam.IsAddHaarMeasure
  co₁ : IsCO L₁
  co₂ : IsCO L₂
  sb : IsSB Φv
  dens : IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} Φv g
  unit : IsUnit (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det

def uu (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (T : HermR (Fv F v) σ n) (b : HermR (Fv F v) σ n) : ℂ :=
  jtR (Fv F v) σ J (psiV F ψ v) μv Φv b * psiV F ψ v (-trPair (Fv F v) T.1 b.1)

def ShellP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) μv νv lam L₁ L₂ Φv g T,
    Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T → ∀ q : ℝ, 1 < q → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ z : ℂ,
      ∫ b in {b : HermR (Fv F v) σ n | R < nM v b.1 ∧ nM v b.1 ≤ q * R},
        whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z b ∂νv = 0

def ConvP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) μv νv lam L₁ L₂ Φv g T,
    Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z) νv

def DualP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) μv νv lam L₁ L₂ Φv g T,
    Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T →
      Tendsto (fun R : ℝ => ∫ b in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R}, uu σ J ψ v μv Φv T b ∂νv) atTop (𝓝 (g T))

end PositivityTheory.SiegelWeilFormula.SwLocFin
