import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open scoped TensorProduct Matrix Classical Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (E) in

def eSp (v : HeightOneSpectrum (𝓞 F)) : ℂ := if IsField (Fv F v ⊗[F] E) then -1 else 1

structure Dat0 (σ : E →ₐ[F] E) {M n d : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E)
    (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)) (ν : Measure (HermR (AF F) σ n)) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
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

def LocFinX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ,
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

def UnrWhitX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ,
  ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∃ t : ℝ,
  ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    ∀ (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
      (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)),
      SdW F E σ M J (Fv F v) (psiV F ψ v) n μv → SdHerm F E σ (Fv F v) (psiV F ψ v) n νv → lam.IsAddHaarMeasure →
      (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v → ∀ z : ℂ, t < z.re →
        Integrable (whI (Fv F v) σ J (psiV F ψ v) μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z) νv ∧
        ∫ b, whI (Fv F v) σ J (psiV F ψ v) μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z b ∂νv =
          ∏ i : Fin n, (1 - eSp E v ^ (M + (i : ℕ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * z + n - (i : ℕ))))

def RealWhitEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, n ≤ M →
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

def FactorX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) ψ (ι : Type) [Fintype ι]
    θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν, Dat0 (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν →
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

def WROrd : Prop :=
  ∀ (m n : ℕ), m < n → ∀ (b : Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ β : WR.E n, (herm β).det ≠ 0 →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ ∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re →
      Integrable (fun y => ((WR.dP y : ℝ) : ℂ) ^ (-z) * secN (fun _ : Fin m => b) c t 1 (herm y) * WR.chr t β y) ∧
      z ^ (n - m) * W z = ∫ y, ((WR.dP y : ℝ) : ℂ) ^ (-z) * secN (fun _ : Fin m => b) c t 1 (herm y) * WR.chr t β y

def RealLow : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, M < n →
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (ι : Type) [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ),
    IsPlaces σ ψ θ l → ∀ (e : ι → Bool) fr, IsFrames J θ (fun i _ => e i) fr → ∀ (g : ι → GL (Fin n) ℂ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    SdW F E σ M J (Ainf F) (psiInf F ψ) n μ → SdHerm F E σ (Ainf F) (psiInf F ψ) n ν →
  ∀ T : HermR (Ainf F) σ n, IsUnit (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g fun _ => 1) (nuInf θ g) T.1 z) ν ∧
      (z - ((M : ℂ) - n) / 2) ^ (Module.finrank ℚ F * (n - M)) * W z =
        ∫ b, whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g fun _ => 1) (nuInf θ g) T.1 z b ∂ν

def LOrd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (j : ℤ), ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
    (∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} => 1 - eSp E v.1 ^ j * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s)) ∧
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H j ∧ ∀ᶠ s in 𝓝[≠] (j : ℂ), H s =
      (s - j) ^ (if 1 ≤ j then 0 else if j = 0 then S.card + Module.finrank ℚ F - 1 else Module.finrank ℚ F) * Z s

def DensEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ x : Fin M → E, hE σ J x x = 0 → x = 0) →
  ∀ (T : Matrix (Fin M) (Fin M) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin M → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin M → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin M → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin M → Fin M → Fv F v ⊗[F] E) → ℂ),
    IsSchwartzInf Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) M) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) M) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin M → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) M (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ M) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) M (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ M → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ M → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT) / (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) ∧
      ∀ lam : ℂ, Tendsto (fun s : ℝ => ∏' v : HeightOneSpectrum (𝓞 F), (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))))
          (𝓝[>] 1) (𝓝 lam) →
        2 * meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) = ginf (hermOf (Ainf F) σ T hT) * lam *
          ∏' v, gv v (hermOf (Fv F v) σ T hT) / (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))

def WhitGenX (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) ψ (ι : Type) [Fintype ι]
    θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν, Dat0 (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν → ok M n →
    (n + 2 ≤ M ∨ ∀ x : Fin M → E, hE σ J x x = 0 → x = 0) →
    (vac → (∀ i, P i = 1) ∧ ∃ e : ι → Bool, ε = fun i _ => e i) →
    (∃ t : ℝ, ∀ z : ℂ, t < z.re → Integrable (whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z) ν) →
    ∀ μH 𝓕, IsHaarH F E σ M J μH → IsFDH F E σ M J μH 𝓕 →
      HolValueAt (fun z => ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν) (((M : ℂ) - n) / 2)
        (c * meanC μH 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}))

def WhitGenLt : Prop := WhitGenX (fun M n => n < M) False 1

def WhitGenEq : Prop := WhitGenX (fun M n => M = n ∧ 1 ≤ M) False 2

def WhitGenLow : Prop := WhitGenX (fun M n => M < n ∧ 1 ≤ M) True 0

def WhitGenEqOf : Prop := LocFinX → UnrWhitX → RealWhitEq → FactorX → LOrd → DensEq → WhitGenEq

def WhitGenLowOf : Prop := LocFinX → UnrWhitX → RealLow → FactorX → LOrd → WhitGenLow

end PositivityTheory.SiegelWeilFormula.Gen

end
