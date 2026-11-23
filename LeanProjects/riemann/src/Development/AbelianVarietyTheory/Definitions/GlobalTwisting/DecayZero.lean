import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

noncomputable section

namespace GlobalTheory.SWQ

open scoped TensorProduct NNReal ENNReal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

def qd (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F) (u : Fin N → R) : R :=
  ∑ l, algebraMap F R (a l) * u l ^ 2

def Bd (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F) (u u' : Fin N → R) : R :=
  ∑ l, algebraMap F R (2 * a l) * u l * u' l

def rat (ξ : Fin N → F) : Fin N → AF F := fun l => algebraMap F (AF F) (ξ l)

def inf (u : Fin N → AF F) : Fin N → Ainf F := fun l => fstA F (u l)

def fin (u : Fin N → AF F) : Fin N → Af F := fun l => sndA F (u l)

def loc (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → Af F) : Fin N → Fv F v := fun l => evalV F v (u l)

def re (x : Ainf F) (w : InfinitePlace F) : ℝ :=
  (InfinitePlace.Completion.extensionEmbedding w (x w)).re

def sz (u : Fin N → AF F) : ℝ := ∑ l, ∑ w : InfinitePlace F, |re (inf u l) w|

def hf (F : Type) [Field F] [NumberField F] : AF F := pairA F (algebraMap F (Ainf F) (1 / 2)) 1

def intN (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) : Set (Fin N → Fv F v) :=
  {u | ∀ l, u l ∈ v.adicCompletionIntegers F}

def Decay (Φ : (Fin N → AF F) → ℂ) : Prop :=
  Continuous Φ ∧ (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ u, fin u ∉ K → Φ u = 0) ∧
    ∀ k : ℕ, ∃ C : ℝ, ∀ u, ‖Φ u‖ * (1 + sz u) ^ k ≤ C

def IsCov1 (ν : Measure (AF F)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∃ D : Set (AF F), MeasurableSet D ∧
    IsAddFundamentalDomain (algebraMap F (AF F)).range.toAddSubgroup D ν ∧ ν D = 1

def muV (N : ℕ) (ν : Measure (AF F)) : Measure (Fin N → AF F) := Measure.pi fun _ => ν

def IsLam (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) : Prop :=
  (∀ w, lam w ≠ 0) ∧ ∀ x : Ainf F,
    psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, lam w * re x w : ℝ) : ℂ))

def Ctx (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F) : Prop :=
  IsTotallyReal F ∧ IsCharAF F ψ ∧ IsLam ψ lam ∧ IsCov1 ν ∧ ∀ l, a l ≠ 0

variable (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F)

def Ub (b : AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ := fun u => ψ (b * qd (AF F) a u) * Φ u

def Da (t : AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ := fun u => Φ (t • u)

def Fo (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ :=
  fun u => ∫ s, Φ s * ψ (Bd (AF F) a s u) ∂(muV N ν)

def rho (x y : Fin N → AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ :=
  fun u => ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) * Φ (u + x)

def th (Φ : (Fin N → AF F) → ℂ) : ℂ := ∑' ξ : Fin N → F, Φ (rat ξ)

def Fst (Φ : (Fin N → AF F) → ℂ) (b : AF F) : ℂ := ∫ u, Φ u * ψ (b * qd (AF F) a u) ∂(muV N ν)

def dens (Φ : (Fin N → AF F) → ℂ) (y : AF F) : ℂ := ∫ b, Fst ψ ν a Φ b * ψ (-(b * y)) ∂ν

def Eis (Φ : (Fin N → AF F) → ℂ) : ℂ := Φ 0 + ∑' b : F, Fst ψ ν a Φ (algebraMap F (AF F) b)

def gauss (τ : InfinitePlace F → ℂ) (x : Fin N → Ainf F) : ℂ :=
  ∏ w : InfinitePlace F, ∏ l, Complex.exp
    (2 * Real.pi * Complex.I *
        ((lam w * re (algebraMap F (Ainf F) (a l)) w * (τ w).re * re (x l) w ^ 2 : ℝ) : ℂ) -
      ((2 * Real.pi * |lam w * re (algebraMap F (Ainf F) (a l)) w| * (τ w).im * re (x l) w ^ 2 : ℝ) : ℂ))

def GG (τ : InfinitePlace F → ℂ) (Φ : (Fin N → AF F) → ℂ) : Prop :=
  (∀ w, 0 < (τ w).im) ∧ ∃ Φf : (Fin N → Af F) → ℂ, IsSB Φf ∧ ∀ u, Φ u = gauss lam a τ (inf u) * Φf (fin u)

def mob (g : Matrix (Fin 2) (Fin 2) (AF F)) (w : InfinitePlace F) : ℂ :=
  ((re (fstA F (g 0 0)) w : ℂ) * Complex.I + (re (fstA F (g 0 1)) w : ℂ)) /
    ((re (fstA F (g 1 0)) w : ℂ) * Complex.I + (re (fstA F (g 1 1)) w : ℂ))

def Rel (L : AddSubgroup (Fin N → Af F)) (n₀ : ℝ) (g : Matrix (Fin 2) (Fin 2) (AF F))
    (Φ : (Fin N → AF F) → ℂ) : Prop :=
  g.det = 1 ∧ GG lam a (mob g) Φ ∧ ∫ u, ‖Φ u‖ ^ 2 ∂(muV N ν) = n₀ ∧
    ∀ x y : Fin N → AF F, inf x = 0 → inf y = 0 → fin (g 0 0 • x + g 1 0 • y) ∈ L →
      fin (g 0 1 • x + g 1 1 • y) ∈ L → rho ψ a x y Φ = Φ

def Htf (b : Af F) : ℝ := ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖evalV F v b‖

def Ht (b : AF F) : ℝ := (∏ w : InfinitePlace F, max 1 |re (fstA F b) w|) * Htf (sndA F b)

structure IsTheta (M : ℕ) (Θ : Measure (Fin N → AF F)) : Prop where
  ratl : Θ {u | ¬ ∃ β : F, qd (AF F) a u = algebraMap F (AF F) β} = 0
  small : ∀ Ω : Set (Fin N → AF F), IsCompact Ω → ∃ C : ℝ≥0, ∀ j : ℕ,
    Θ ((fun u => hf F ^ j • u) '' Ω) * 2 ^ (Fintype.card (InfinitePlace F) * M * j) ≤ C
  big : ∀ Ω : Set (Fin N → AF F), IsCompact Ω → ∃ C : ℝ≥0, ∀ j : ℕ,
    Θ {u | hf F ^ j • u ∈ Ω} ≤ C * 2 ^ (Fintype.card (InfinitePlace F) * N * j)
  four : ∀ Φ, Decay Φ → Decay (Fo ψ ν a Φ) →
    Fo ψ ν a Φ 0 + ∫ u, Fo ψ ν a Φ u ∂Θ = Φ 0 + ∫ u, Φ u ∂Θ
  dil : ∀ t : F, t ≠ 0 → Θ.map (fun u => algebraMap F (AF F) t • u) = Θ

def Dif (Θ : Measure (Fin N → AF F)) (Φ : (Fin N → AF F) → ℂ) : ℂ :=
  Φ 0 + ∫ u, Φ u ∂Θ - Eis ψ ν a Φ

def PureV (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin N → Fv F v) → ℂ) : Prop :=
  (∀ v, IsSB (Φv v)) ∧ ∀ᶠ v in Filter.cofinite, Φv v = (intN N v).indicator 1

def tens (Φi : (Fin N → Ainf F) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin N → Fv F v) → ℂ) :
    (Fin N → AF F) → ℂ := fun u => Φi (inf u) * ∏ᶠ v, Φv v (loc v (fin u))

def IsPM (μ : Measure (Fin N → AF F)) (μi : Measure (Fin N → Ainf F))
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin N → Fv F v)) : Prop :=
  (∀ᶠ v in Filter.cofinite, μv v (intN N v) = 1) ∧
    ∀ Φi Φv, Integrable Φi μi → PureV Φv → Integrable (tens Φi Φv) μ ∧
      ∫ u, tens Φi Φv u ∂μ = (∫ x, Φi x ∂μi) * ∏ᶠ v, ∫ x, Φv v x ∂(μv v)

def IsPM1 (ν : Measure (AF F)) (νi : Measure (Ainf F))
    (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) : Prop :=
  (∀ᶠ v in Filter.cofinite, νv v (v.adicCompletionIntegers F : Set (Fv F v)) = 1) ∧
    ∀ (Ui : Set (Ainf F)) (Uv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), IsCompact Ui →
      (∀ v, IsCompact (Uv v) ∧ IsOpen (Uv v)) →
      (∀ᶠ v in Filter.cofinite, Uv v = (v.adicCompletionIntegers F : Set (Fv F v))) →
      ν {y | fstA F y ∈ Ui ∧ ∀ v, evalV F v (sndA F y) ∈ Uv v} = νi Ui * ∏ᶠ v, νv v (Uv v)

structure LocData where
  μi : Measure (Fin N → Ainf F)
  νi : Measure (Ainf F)
  μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin N → Fv F v)
  νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)
  fi : Ainf F → Measure (Fin N → Ainf F)
  fv : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → Measure (Fin N → Fv F v)
  sdμi : SelfDual μi fun x y => psiInf F ψ (Bd (Ainf F) a x y)
  sdνi : SdR (Ainf F) (psiInf F ψ) νi
  sdμv : ∀ v, SelfDual (μv v) fun x y => psiV F ψ v (Bd (Fv F v) a x y)
  sdνv : ∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)
  fibi : IsFibreFamily μi (qd (Ainf F) a) id Set.univ νi {c : Ainf F | ∀ w, c w ≠ 0} fi
  fibv : ∀ v, IsFibreFamily (μv v) (qd (Fv F v) a) id Set.univ (νv v) {c | c ≠ 0} (fv v)

variable {ψ a}

def IsXV (T : LocData ψ a) (β : F) (m : Measure (Fin N → AF F)) : Prop :=
  m {u | qd (AF F) a u ≠ algebraMap F (AF F) β} = 0 ∧
    ∀ Φi Φv, Continuous Φi → HasCompactSupport Φi → PureV Φv → Integrable (tens Φi Φv) m ∧
      Multipliable (fun v => ∫ x, Φv v x ∂(T.fv v (algebraMap F (Fv F v) β))) ∧
      ∫ u, tens Φi Φv u ∂m = (∫ x, Φi x ∂(T.fi (algebraMap F (Ainf F) β))) *
        ∏' v, ∫ x, Φv v x ∂(T.fv v (algebraMap F (Fv F v) β))

def Good (ψ : AddChar (AF F) ℂ) (a : Fin N → F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔
    y ∈ v.adicCompletionIntegers F) ∧
  ‖(2 : Fv F v)‖ = 1 ∧ ∀ l, ‖algebraMap F (Fv F v) (a l)‖ = 1

section Herm

variable {E : Type} [Field E] [Algebra F E] {M : ℕ}

def emb (R : Type) [CommRing R] [Algebra F R] (w : Fin N → Fin M → E) (u : Fin N → R) :
    Fin 1 → Fin M → R ⊗[F] E := fun _ i => ∑ l, u l ⊗ₜ[F] w l i

def IsOB (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (a : Fin N → F) (w : Fin N → Fin M → E) : Prop :=
  (∀ l, a l ≠ 0) ∧ LinearIndependent F w ∧ Submodule.span F (Set.range w) = ⊤ ∧
    ∀ ξ : Fin N → F, hE σ J (∑ l, ξ l • w l) (∑ l, ξ l • w l) = algebraMap F E (qd F a ξ)

def orbM (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin 1 → Fin M → E)) : Measure (Fin 1 → Fin M → AF F ⊗[F] E) :=
  Measure.sum fun ξ : S =>
    (μ.restrict 𝓕).map fun h => h⁻¹ • ratTup (F := F) (AF F) (ξ : Fin 1 → Fin M → E)

def thW (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) : Measure (Fin 1 → Fin M → AF F ⊗[F] E) :=
  (μ 𝓕)⁻¹ • orbM σ J μ 𝓕 {ξ | ξ ≠ 0}

end Herm

theorem decay_zero : Decay (fun _ : Fin N → AF F => (0 : ℂ)) :=
  ⟨continuous_const, ⟨∅, isCompact_empty, fun _ _ => rfl⟩, fun _ => ⟨0, fun _ => by simp⟩⟩

end GlobalTheory.SWQ
