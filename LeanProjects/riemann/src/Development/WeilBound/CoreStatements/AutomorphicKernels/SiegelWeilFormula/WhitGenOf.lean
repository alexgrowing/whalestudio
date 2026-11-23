import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def nu2 {R : Type} [CommRing R] [MeasurableSpace R] {n : ℕ} (lam : Measure (Fin n → R)) (L₁ L₂ : AddSubgroup (Fin n → R))
    (b : Matrix (Fin n) (Fin n) R) : ℝ :=
  (lam {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + b.mulVec y'} / lam L₁).toReal

def IsCO {V : Type} [AddCommGroup V] [TopologicalSpace V] (L : AddSubgroup V) : Prop := IsOpen (L : Set V) ∧ IsCompact (L : Set V)

def matV (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (h : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  h.map (Algebra.TensorProduct.map ((evalV F v).comp (sndA F)) (AlgHom.id F E))

def matInf {n : ℕ} (h : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) :=
  h.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))

structure IsPlaces (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ))
    (l : ι → ℝ) : Prop where
  cont : ∀ i, Continuous (θ i)
  bij : Function.Bijective fun (z : Ainf F ⊗[F] E) i => θ i z
  conj : ∀ i z, θ i (sigR (Ainf F) σ z) = star (θ i z)
  ne : ∀ i, l i ≠ 0
  psi : ∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * θ i (x ⊗ₜ[F] (1 : E)))

def crd {M n : ℕ} (θ : Ainf F ⊗[F] E →+* ℂ) (fr : GL (Fin M) ℂ) (g : GL (Fin n) ℂ) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    Matrix (Fin M) (Fin n) ℂ :=
  (fr⁻¹).1 * Matrix.of (fun a j => θ (X j a)) * g.1

def phiInf {M n : ℕ} {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (fr : ι → GL (Fin M) ℂ)
    (g : ι → GL (Fin n) ℂ) (P : ι → PX M n) (X : Fin n → Fin M → Ainf F ⊗[F] E) : ℂ :=
  ∏ i, evX (P i) (crd (θ i) (fr i) (g i) X) * gs (2 * Real.pi * |l i|) (crd (θ i) (fr i) (g i) X)

def nuInf {n : ℕ} {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (g : ι → GL (Fin n) ℂ)
    (h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) : ℝ :=
  ∏ i, (1 + (((g i)⁻¹).1 * h.map (θ i) * (((g i)⁻¹).1)ᴴ) * (((g i)⁻¹).1 * h.map (θ i) * (((g i)⁻¹).1)ᴴ)).det.re

def IsFrames {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {ι : Type} (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (ε : ι → Fin M → Bool)
    (fr : ι → GL (Fin M) ℂ) : Prop :=
  ∀ i, ((fr i).1)ᴴ * (JR (Ainf F) J).map (θ i) * (fr i).1 = Matrix.diagonal (sgn (ε i))

def whI (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : R → ℂ) (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (ν : Matrix (Fin n) (Fin n) (R ⊗[F] E) → ℝ)
    (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (z : ℂ) (b : HermR R σ n) : ℂ :=
  ((ν b.1 : ℝ) : ℂ) ^ (-(z - ((M : ℂ) - n) / 2)) * jtR R σ J ψR μ φ b * ψR (-trPair R T b.1)

def LocFin2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, n < M →
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)),
    SdW F E σ M J (Fv F v) (psiV F ψ v) n μv → SdHerm F E σ (Fv F v) (psiV F ψ v) n νv → lam.IsAddHaarMeasure →
    IsCO L₁ → IsCO L₂ →
  ∀ (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φv →
  ∀ g : HermR (Fv F v) σ n → ℂ,
    IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} Φv g →
  ∀ T : HermR (Fv F v) σ n, IsUnit (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W (((M : ℂ) - n) / 2) = g T ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z) νv ∧
      W z = ∫ b, whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z b ∂νv

def UnrPoly : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε →
  ∀ ψ, IsLevelChars σ ϖ ψ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ T → ∀ k : ℕ, 1 ≤ k → ∀ t : ℂ,
    ∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (red ϖ k T * B.1)) * t ^ Nat.log (q ^ 2) (nuAt ϖ B.1) =
      ∏ i : Fin n, (1 - t * ((ε : ℂ) * q) ^ (i : ℕ))

def UnrWhit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, n < M →
  ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∃ t : ℝ,
  ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ e : ℤˣ,
    ∀ (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
      (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)),
      SdW F E σ M J (Fv F v) (psiV F ψ v) n μv → SdHerm F E σ (Fv F v) (psiV F ψ v) n νv → lam.IsAddHaarMeasure →
      (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v → ∀ z : ℂ, t < z.re →
        Integrable (whI (Fv F v) σ J (psiV F ψ v) μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z) νv ∧
        ∫ b, whI (Fv F v) σ J (psiV F ψ v) μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z b ∂νv =
          ∏ i : Fin n, (1 - ((e : ℤ) : ℂ) ^ (M + (i : ℕ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * z + n - (i : ℕ))))

def RealWhit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, n < M →
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (ι : Type) [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ),
    IsPlaces σ ψ θ l → ∀ ε fr, IsFrames J θ ε fr → ∀ (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    SdW F E σ M J (Ainf F) (psiInf F ψ) n μ → SdHerm F E σ (Ainf F) (psiInf F ψ) n ν →
    IsSchwartzInf (phiInf θ l fr g P) ∧
  ∀ gi : HermR (Ainf F) σ n → ℂ,
    IsContDensityOn μ (gramR (Ainf F) σ J) Subtype.val ν
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} (phiInf θ l fr g P) gi →
  ∀ T : HermR (Ainf F) σ n, IsUnit (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W (((M : ℂ) - n) / 2) = gi T ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z) ν ∧
      W z = ∫ b, whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z b ∂ν

def nuA {n : ℕ} {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (g : ι → GL (Fin n) ℂ)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (h : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : ℝ :=
  nuInf θ g (matInf h) * ∏ᶠ v, nu2 (lam v) (L₁ v) (L₂ v) (matV v h)

structure Dat (σ : E →ₐ[F] E) {M n d : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E)
    (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)) (ν : Measure (HermR (AF F) σ n)) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  lt : n < M
  hT : ∀ a b, σ (T b a) = T a b
  det : T.det ≠ 0
  chr : IsCharAF F ψ
  places : IsPlaces σ ψ θ l
  frames : IsFrames J θ ε fr
  haar : ∀ v, (lam v).IsAddHaarMeasure
  co : ∀ v, IsCO (L₁ v) ∧ IsCO (L₂ v)
  std : ∀ᶠ v in cofinite, (L₁ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v ∧ (L₂ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v
  pure : IsPureFin bs Φf Φv
  prod : IsProdInfFin Φ (phiInf θ l fr g P) Φf
  sdW : SdW F E σ M J (AF F) ψ n μ
  sdH : SdHerm F E σ (AF F) ψ n ν

def Factor : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) ψ (ι : Type) [Fintype ι]
    θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν, Dat (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν →
    ∀ μi νi (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
      (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n)),
      SdW F E σ M J (Ainf F) (psiInf F ψ) n μi → SdHerm F E σ (Ainf F) (psiInf F ψ) n νi →
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) → (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) →
    ∀ z : ℂ, Integrable (whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z) ν →
      Integrable (whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z) νi →
      (∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z)
        (νv v)) →
      Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) =>
          (∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi) *
          ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b
            ∂(νv v))
        atTop (nhds (∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν))

def WhitGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) ψ (ι : Type) [Fintype ι]
    θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν, Dat (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν →
    (∃ t : ℝ, ∀ z : ℂ, t < z.re → Integrable (whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z) ν) →
    ∀ μH 𝓕, IsHaarH F E σ M J μH → IsFDH F E σ M J μH 𝓕 →
      HolValueAt (fun z => ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν) (((M : ℂ) - n) / 2)
        (meanC μH 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}))

def WhitGenOf : Prop := LocFin2 → UnrWhit → RealWhit → Factor → SiegelDensitiesLow → WhitGen

end PositivityTheory.SiegelWeilFormula.Gen

end
