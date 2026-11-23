import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Rv {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (Fv F v) bs).repr x k ∈ v.adicCompletionIntegers F}

def matS {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E)) {a b : ℕ} (X : Matrix (Fin a) (Fin b) E)
    (hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S) : Matrix (Fin a) (Fin b) S :=
  Matrix.of fun i j => ⟨inclR (F := F) (Fv F v) (X i j), hX i j⟩

structure GoodLoc (σ : E →ₐ[F] E) {M n d : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E))
    (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ) : Prop where
  carrier : (S : Set (Fv F v ⊗[F] E)) = Rv bs v
  sig : ∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x
  fixed : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = x → ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c
  unif_mem : ϖ ∈ v.adicCompletionIntegers F
  unif_ne : ϖ ≠ 0
  unif_lt : ‖ϖ‖ < 1
  unif_S : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S
  quad : IsUnrQuad S σS ⟨_, unif_S⟩ (Ideal.absNorm v.asIdeal) ε
  two : ‖(2 : Fv F v)‖ = 1
  trace_dual : ∀ a : Fv F v ⊗[F] E,
    (∀ b ∈ S, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * b) ∈ v.adicCompletionIntegers F) ↔ a ∈ S
  J_int : ∀ i j, inclR (F := F) (Fv F v) (J i j) ∈ S
  J_unimod : IsUnimod σS (matS S J J_int)
  T_int : ∀ i j, inclR (F := F) (Fv F v) (T i j) ∈ S
  T_unimod : IsUnimod σS (matS S T T_int)
  psi_add : ∀ x y, ψv (x + y) = ψv x * ψv y
  psi_zero : ψv 0 = 1
  psi_cont : Continuous ψv
  psi_cond : ∀ a : Fv F v, (∀ b ∈ v.adicCompletionIntegers F, ψv (a * b) = 1) ↔ a ∈ v.adicCompletionIntegers F

def LocC : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E))
    (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ), GoodLoc σ J T bs v ψv S σS ϖ ε →
  ∀ (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)),
    SdW F E σ M J (Fv F v) ψv n μv → SdHerm F E σ (Fv F v) ψv n νv → lam.IsAddHaarMeasure →
    (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v → ∀ z : ℂ, ((n : ℝ) ^ 2) < z.re →
      Integrable (whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z) νv ∧
      ∫ b, whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z b ∂νv =
        ∏ i : Fin n, (1 - (ε : ℂ) ^ (M + (i : ℕ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * z + n - (i : ℕ))))

def AlmostGood : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E),
    (∀ a b, σ (T b a) = T a b) → T.det ≠ 0 →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ),
    (ε : ℂ) = eSp E v ∧ GoodLoc σ J T bs v (psiV F ψ v) S σS ϖ ε

def UnrWhitAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ,
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

end PositivityTheory.SiegelWeilFormula.Gunr

end
