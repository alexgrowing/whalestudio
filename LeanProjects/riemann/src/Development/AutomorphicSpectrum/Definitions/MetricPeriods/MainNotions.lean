import Mathlib
import Formalism.MonomialMeanResidues.MonomialMean
import Formalism.MonomialMeanResidues.FilteredDegree
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GoodOver

namespace GlobalTheory.CompanionTheory.Ar.HS

open NumberField Matrix ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GroundTheory.Heights₂.Heights
open scoped ENNReal

noncomputable section

def Claim (C : ℝ) (T D n j0 : ℕ) (Λ β ΛD ΛT J δ h d deg : ℝ) : Prop :=
  let z : ℝ := 1 - ((T - 1).choose D : ℝ) * δ / d
  let lρ : ℝ := Real.log Λ + C * Real.log (n * D * j0 * δ * (2 + |h| + Real.log Λ))
  let g : ℝ := ((D : ℝ) + 1) * (Real.log n + 1) / 2 + 1
  0 ≤ z ∧ z ≤ 1 ∧
    (1 - z) * (T * h - 3 * ((D : ℝ) + 1) * |h| - J - C * (D : ℝ) ^ 2 * (lρ + Real.log T) -
        ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2)) -
      z * (T * (Real.log 2 + lρ + Real.log β / 2) + Real.log ΛD + Real.log ΛT) ≤ deg / d

def bcL {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] {m : ℕ}
    (M : Submodule (𝓞 F) (Fin m → F)) : Submodule (𝓞 K) (Fin m → K) :=
  Submodule.span (𝓞 K) ((fun (x : Fin m → F) (i : Fin m) => algebraMap F K (x i)) '' (M : Set (Fin m → F)))

structure HSData {F : Type} [Field F] [NumberField F] {D N n δ : ℕ} (X : ChowData F D N n δ) (T : ℕ) where

  La : Type
  [grp : AddCommGroup La]

  L : La

  L₂ : La

  n₂ : ℕ

  S : (F →+* ℂ) → Side D N n₂ La L L₂
  good : ∀ σ, GoodOver (S σ).A (S σ).ω (X.eqs σ) fun j => σ (X.θ j)
  bdd : ∀ σ, ∃ C : ℝ, ∀ y, (S σ).A.sqn L₂ (S σ).e₂ y *
    (S σ).A.sqn L (onb (X.H.normAt σ) (S σ).ω) y ^ D ≤ C

  d : ℕ → ℕ

  E : ∀ (σ : F →+* ℂ) (j : ℕ), Fin (d j) → (S σ).ι → (S σ).Y → ℂ
  E_sec : ∀ σ, ∀ j ≤ T, ∀ k, (S σ).A.IsSec ((S σ).mu0 + j • L) (E σ j k)
  E_indep : ∀ σ, ∀ j ≤ T, ∀ c, SecEq (S σ).A (lin (E σ j) c) 0 → c = 0

  μ : ∀ j : ℕ, Fin N → Matrix (Fin (d (j + 1))) (Fin (d j)) F
  μ_real : ∀ σ, ∀ j < T, ∀ a c, SecEq (S σ).A (lin (E σ (j + 1)) (((μ j a).map σ) *ᵥ c))
    ((S σ).ω a * lin (E σ j) c)

  M : ∀ j : ℕ, Submodule (𝓞 F) (Fin (d j) → F)
  M_fg : (M T).FG

  HN : ∀ j : ℕ, ArchData F (d j)

  β : ℝ

  ΛD : ℝ

  ΛT : ℝ
  one_le_β : 1 ≤ β
  one_le_ΛD : 1 ≤ ΛD
  one_le_ΛT : 1 ≤ ΛT
  zero_nat : ∀ σ k, InVnat (S σ).A (S σ).mu0 L (onb (X.H.normAt σ) (S σ).ω) 0 (E σ 0 k)
  nat_le : ∀ σ G, InVnat (S σ).A (S σ).mu0 L (onb (X.H.normAt σ) (S σ).ω) D G →
    ∃ c, SecEq (S σ).A G (lin (E σ D) c)
  mul_int : ∀ j < T, ∀ a : Fin n, ∀ m ∈ M j, (∑ i, X.w a i • μ j i) *ᵥ m ∈ M (j + 1)
  mul_norm : ∀ σ j, D ≤ j → j < T → ∀ (u : Fin N → ℂ) (c : Fin (d j) → ℂ),
    ((HN (j + 1)).normAt σ).norm ((∑ i, u i • (μ j i).map σ) *ᵥ c) ≤
      √β * (X.H.normAt σ).norm u * ((HN j).normAt σ).norm c
  norm_le : ∀ σ c, ENNReal.ofReal (((HN T).normAt σ).norm c ^ 2) ≤
    ENNReal.ofReal (β ^ (D + T + 1) * 2 ^ D) *
      fsInt (S σ).A ((S σ).mu0 + T • L) L L₂ (onb (X.H.normAt σ) (S σ).ω) (S σ).e₂ (D + T) (lin (E σ T) c)
  short_D : ∃ s : Set (Fin (d D) → F), s ⊆ M D ∧ Submodule.span F s = ⊤ ∧
    ∀ m ∈ s, ∀ σ : F →+* ℂ, ((HN D).normAt σ).norm (fun k => σ (m k)) ≤ ΛD
  short_alt : ∃ s : Set (Fin (d T) → F), s ⊆ M T ∧ Submodule.span F s = ⊤ ∧
    ∀ m ∈ s, ∀ σ : F →+* ℂ, ((HN T).normAt σ).norm (fun k => σ (m k)) ≤ ΛT

  t : Fin (D + 1) → Fin N → F

  k₀ : Fin n₂
  rat_b : ∀ k, ∃ (e : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous e ∧ Q.IsHomogeneous e ∧
    Q ∉ X.I ∧ ∀ σ i y, y ∈ ((S σ).A.chart i).source →
      MvPolynomial.eval (fun j => (S σ).ω j i y) (Q.map σ) * (S σ).b k i y =
        MvPolynomial.eval (fun j => (S σ).ω j i y) (P.map σ) * (S σ).b k₀ i y
  rat_E : ∀ k, ∃ (e : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous (e + T) ∧
    Q.IsHomogeneous (e + 1) ∧ Q ∉ X.I ∧ ∀ σ i y, y ∈ ((S σ).A.chart i).source →
      MvPolynomial.eval (fun j => (S σ).ω j i y) (Q.map σ) * E σ T k i y =
        MvPolynomial.eval (fun j => (S σ).ω j i y) (P.map σ) *
          jacF (S σ).A (fun a => lin (S σ).ω fun j => σ (t a j)) i y * (S σ).b k₀ i y

attribute [instance] HSData.grp

namespace HSData
variable {F : Type} [Field F] [NumberField F] {D N n δ T : ℕ} {X : ChowData F D N n δ} (Z : HSData X T)
  {K : Type} [Field K] [NumberField K] [Algebra F K]

abbrev MainNotions (τ : K →+* ℂ) := Z.S (τ.comp (algebraMap F K))

def secL (τ : K →+* ℂ) (u : Fin N → K) : (Z.MainNotions τ).ι → (Z.MainNotions τ).Y → ℂ :=
  lin (Z.MainNotions τ).ω fun j => τ (u j)

def secB (τ : K →+* ℂ) (u : Fin Z.n₂ → K) : (Z.MainNotions τ).ι → (Z.MainNotions τ).Y → ℂ :=
  lin (Z.MainNotions τ).b fun j => τ (u j)

def secE (τ : K →+* ℂ) (j : ℕ) (c : Fin (Z.d j) → ℂ) : (Z.MainNotions τ).ι → (Z.MainNotions τ).Y → ℂ :=
  lin (Z.E (τ.comp (algebraMap F K)) j) c

def IsOver (y : Fin δ → Fin N → K) (xs : ∀ τ : K →+* ℂ, Fin δ → (Z.MainNotions τ).Y) (u : Fin Z.n₂ → K) : Prop :=
  ∀ τ q, (∃ c : ℂ, ptv (Z.MainNotions τ).A (Z.MainNotions τ).ω (xs τ q) = c • fun j => τ (y q j)) ∧
    val (Z.MainNotions τ).A (Z.secB τ u) (xs τ q) ≠ 0

def resLat (x : Fin D → Fin n → 𝓞 K) (xs : ∀ τ : K →+* ℂ, Fin δ → (Z.MainNotions τ).Y) (u : Fin Z.n₂ → K) :
    Submodule (𝓞 K) (Fin δ → K) :=
  Submodule.span (𝓞 K) {ρ | ∃ m ∈ bcL K (Z.M 0), ∀ τ q,
    val (Z.MainNotions τ).A (Z.secE τ 0 fun k => τ (m k)) (xs τ q) =
      τ (ρ q) * dS (Z.MainNotions τ).A (fun i => Z.secL τ (X.sec x i)) ((Z.MainNotions τ).A.pick (xs τ q)) (xs τ q) *
        val (Z.MainNotions τ).A (Z.secB τ u) (xs τ q)}

def c2 (xs : ∀ τ : K →+* ℂ, Fin δ → (Z.MainNotions τ).Y) (u : Fin Z.n₂ → K) (v : InfinitePlace K) (q : Fin δ) : ℝ :=
  √((Z.MainNotions v.embedding).A.sqn Z.L₂ (Z.MainNotions v.embedding).e₂ (xs v.embedding q) /
    (Z.MainNotions v.embedding).A.nsq Z.L₂ (Z.secB v.embedding u) (xs v.embedding q))

def ResBound (J : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra F K] [IsTotallyComplex K]
    (x : Fin D → Fin n → 𝓞 K) (y : Fin δ → Fin N → K), X.SplitsAt x y →
    ∀ (xs : ∀ τ : K →+* ℂ, Fin δ → (Z.MainNotions τ).Y) (u : Fin Z.n₂ → K), Z.IsOver y xs u →
      Submodule.IsLattice K (Z.resLat x xs u) ∧
      -((δ : ℝ) * J) - ((D : ℝ) + 3) * ∑ q, ptHt X.w X.H (y q) ≤
        Formalism.HermiteSiegelSlopes.degT (Pi.basisFun K (Fin δ)) (Formalism.HermiteSiegelSlopes.diagFrame (Z.c2 xs u)) (Z.resLat x xs u)

def frameK (K : Type) [Field K] [NumberField K] [Algebra F K] (j : ℕ) (v : InfinitePlace K) :
    Matrix (Fin (Z.d j)) (Fin (Z.d j)) ℂ :=
  (((Z.HN j).normAt (v.embedding.comp (algebraMap F K))).mat)⁻¹

def degMT [StarRing F] : ℝ :=
  Formalism.HermiteSiegelSlopes.degT (Pi.basisFun F (Fin (Z.d T))) (fun v => (((Z.HN T).normAt v.embedding).mat)⁻¹) (Z.M T)

end HSData

end

end GlobalTheory.CompanionTheory.Ar.HS
