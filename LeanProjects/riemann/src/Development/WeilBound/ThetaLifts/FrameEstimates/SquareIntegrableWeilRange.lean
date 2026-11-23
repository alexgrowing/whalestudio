import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F E) in

abbrev Ten (n d : ℕ) : Type := Matrix (Fin n) (Fin d) (AE F E)

variable (σ) in

def EpsHerm {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop :=
  ((∀ i j, σ (J j i) = J i j) ∨ ∀ i j, σ (J j i) = -J i j) ∧ J.det ≠ 0

variable (F) in

def rId (t : ℝ) : AF F := 1 + realAd F (Real.exp t - 1)

variable (σ) in

structure Frame {n : ℕ} (J : Matrix (Fin n) (Fin n) E) where

  r : ℕ

  x : Fin r → Fin n → E

  y : Fin r → Fin n → E

  a : (Fin r → ℝ) → UA σ J

structure Frame.IsGood {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (fr : Frame σ J) : Prop where
  xx : ∀ i j, form σ J (fr.x i) (fr.x j) = 0
  yy : ∀ i j, form σ J (fr.y i) (fr.y j) = 0
  xy : ∀ i j, form σ J (fr.x i) (fr.y j) = if i = j then 1 else 0
  aniso : ∀ u, (∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0) → form σ J u u = 0 → u = 0
  add : ∀ s t, fr.a (s + t) = fr.a s * fr.a t
  cont : Continuous fr.a
  ax : ∀ t i, mat (fr.a t) *ᵥ incV F (fr.x i) = rId F (t i) • incV F (fr.x i)
  ay : ∀ t i, mat (fr.a t) *ᵥ incV F (fr.y i) = rId F (-t i) • incV F (fr.y i)
  a0 : ∀ t u, (∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0) → mat (fr.a t) *ᵥ incV F u = incV F u

def Cone (r : ℕ) : Set (Fin r → ℝ) := {t | Antitone t ∧ ∀ i, 0 ≤ t i}

def rho2 (n : ℕ) {r : ℕ} (t : Fin r → ℝ) : ℝ := ∑ i : Fin r, ((n : ℝ) - 2 * (i.val : ℝ) - 1) * t i

def psum {r : ℕ} (t : Fin r → ℝ) (i : ℕ) : ℝ := ∑ j : Fin r, if j.val < i then t j else 0

def posWt (n d : ℕ) {q y : ℕ} (s : Fin q → ℝ) (t : Fin y → ℝ) : ℝ :=
  ∑ i, ∑ j, 2 * max (s i) (t j) + ((d : ℝ) - 2 * y) * ∑ i, s i + ((n : ℝ) - 2 * q) * ∑ j, t j

def viol {q y : ℕ} (s : Fin q → ℝ) (t : Fin y → ℝ) : ℝ := ⨆ i : Fin (q + 1), (psum s i.val - psum t i.val)

def SiegelCover {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (fr : Frame σ J) : Prop :=
  ∃ Ω : Set (UA σ J), IsCompact Ω ∧ ∀ g, ∃ γ ∈ ratU σ J, ∃ t ∈ Cone fr.r, ∃ κ ∈ Ω, γ * g = fr.a t * κ

def SiegelInt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (fr : Frame σ J) : Prop :=
  ∀ (μ : Measure (UA σ J)) (D : Set (UA σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ J) D μ →
    ∃ (K : ℝ≥0∞) (Ω : Set (UA σ J)), K < ⊤ ∧ IsCompact Ω ∧ ∀ φ : (Fin fr.r → ℝ) → ℝ≥0∞, Measurable φ →
      ∀ f : UA σ J → ℝ≥0∞, Measurable f → (∀ γ ∈ ratU σ J, ∀ g, f (γ * g) = f g) →
        (∀ t ∈ Cone fr.r, ∀ κ ∈ Ω, f (fr.a t * κ) ≤ φ t) →
        ∫⁻ g in D, f g ∂μ ≤ K * ∫⁻ t in Cone fr.r, φ t * ENNReal.ofReal (Real.exp (-(Module.finrank ℚ E * rho2 n t)))

def TorHt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (fr : Frame σ J) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ t ∈ Cone fr.r, (ht (fr.a t) : ℝ) ≤ C * Real.exp (k * ∑ i, t i) ∧
    ∀ γ ∈ ratU σ J, Real.exp (∑ i, t i) ≤ C * (ht (γ * fr.a t) : ℝ) ^ k

section Pair

variable {n d : ℕ}

def sz (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : Ten F E n d) : ℝ := ∑ w, ∑ i, ∑ j, ‖piInf (τ w) (z i j)‖

open Classical in

def maj (τ : ∀ w : InfinitePlace F, EmbOver E w) (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) : ℝ :=
  if ∃ c ∈ C, At (evI F) (z - c) then ((1 + sz τ z) ^ N)⁻¹ else 0

def latSum (τ : ∀ w : InfinitePlace F, EmbOver E w) (C : Set (Ten F E n d)) (N : ℕ) (S : Set (Matrix (Fin n) (Fin d) E))
    {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E} (g : UA σ J) (h : UA σ J') : ℝ≥0∞ :=
  ∑' x : S, ENNReal.ofReal (maj τ C N (mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ))

def fullRank (E : Type) [Field E] (n d : ℕ) : Set (Matrix (Fin n) (Fin d) E) := {x | x.rank = n}

scoped instance measAdPi {κ : Type} : MeasurableSpace (κ → AF F) := borel _

variable (F) in

def coef {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (μ : Measure (κ → AF F)) (Φ₁ Φ₂ : (κ → AF F) → ℂ)
    (w : (κ → AF F) × (κ → AF F)) : ℂ := ∫ u, schr ψ w Φ₁ u * (starRingEnd ℂ) (Φ₂ u) ∂μ

variable {X : Spc F E n} {W : Spc F E d}

def soFin (B : Base F E) (M : Model σ X W) : Set ((Fin n × Fin d → Af F) → ℂ) :=
  {φ | φ ∈ SB _ ∧ ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ M.So B.ψ B.τ₁}

def SqBound (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (𝓕 : Set ((Fin n × Fin d → Af F) → ℂ))
    (S : Set (Matrix (Fin n) (Fin d) E)) : Prop :=
  ∀ φ ∈ 𝓕, ∀ N : ℕ, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)), Continuous p ∧ IsCompact C ∧
    ∀ (f : SInf F (Fin n × Fin d)) g h, ‖theta om (pureA F f φ) g h‖ₑ ^ 2 ≤ ENNReal.ofReal (p f) ^ 2 * latSum B.emb C N S g h

def Dom (M : Model σ X W) (om : Rep σ X W) (𝓕 : Set ((Fin n × Fin d → Af F) → ℂ)) : Prop :=
  ∀ φ ∈ 𝓕, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (k : ℕ) (G : UA σ X.J → ℝ≥0∞), Continuous p ∧ Measurable G ∧
    ∫⁻ g in M.dom, G g ∂M.μ < ⊤ ∧ ∀ (f : SInf F (Fin n × Fin d)) g h,
      ‖theta om (pureA F f φ) g h‖ₑ ≤ ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * G g

end Pair

def GrpTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), EpsHerm σ J → LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) ∧ Countable (ratU σ J) ∧ DiscreteTopology (ratU σ J) ∧ (Continuous fun g : UA σ J => mat g) ∧ (∀ g h : UA σ J, mat (g * h) = mat g * mat h) ∧ ∀ Ω : Set (UA σ J), IsCompact Ω → ∃ C : ℝ≥0, ∀ g ∈ Ω, ht g ≤ C

def EpsOf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (X : Spc F E n) (r s : ℕ), (X.IsHerm σ B r s ∨ X.IsSkew σ B r s) → EpsHerm σ X.J ∧ r + s = n ∧ ∀ fr : Frame σ X.J, fr.IsGood → fr.r ≤ min r s

def FrameBasis : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), EpsHerm σ J → ∀ fr : Frame σ J, fr.IsGood → ∃ (b : GL (Fin n) E) (lam : Fin n → (Fin fr.r → ℝ) →ₗ[ℝ] ℝ) (ix iy : Fin fr.r ↪ Fin n), (∀ i j, ix i ≠ iy j) ∧ (∀ i t, lam (ix i) t = t i ∧ lam (iy i) t = -t i) ∧ (∀ k, (∀ i, ix i ≠ k ∧ iy i ≠ k) → lam k = 0) ∧ (∀ i, (fun l => b.1 l (ix i)) = fr.x i) ∧ ∀ t, mat (fr.a t) * incM F b.1 = incM F b.1 * Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam k t))

def SiegelAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), EpsHerm σ J → ∃ fr : Frame σ J, fr.IsGood ∧ 2 * fr.r ≤ n ∧ SiegelCover fr ∧ SiegelInt fr ∧ TorHt fr

def FinVolU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), EpsHerm σ J → ∀ (μ : Measure (UA σ J)) (D : Set (UA σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ J) D μ → μ D < ⊤

def ConeExp : Prop :=
  ∀ (r : ℕ) (c : Fin r → ℝ), (∀ i : ℕ, 1 ≤ i → i ≤ r → psum c i < 0) → ∫⁻ t in Cone r, ENNReal.ofReal (Real.exp (∑ i, c i * t i)) < ⊤

def PosWt : Prop :=
  ∀ (n d q y : ℕ) (s : Fin q → ℝ) (t : Fin y → ℝ), s ∈ Cone q → t ∈ Cone y → posWt n d s t ≤ d * ∑ i, s i + n * ∑ j, t j ∧ 0 ≤ viol s t ∧ ∀ i ≤ q, psum s i ≤ psum t i + viol s t

def Major : Prop :=
  ∀ (q : ℕ) (s t : Fin q → ℝ), s ∈ Cone q → t ∈ Cone q → (∀ i ≤ q, psum s i ≤ psum t i) → ∑ i, ∑ j, min (s i) (s j) - ∑ i, ∑ j, min (s i) (t j) ≤ ∑ j : Fin q, ((q : ℝ) - 1 - j.val) * t j

def ExpSo : Prop :=
  ∀ (n d q y Y : ℕ), q ≤ Y → y ≤ Y → 2 * Y + 1 < n → 2 * n ≤ d → ∃ m : ℝ, ∀ s ∈ Cone q, ∀ t ∈ Cone y, posWt n d s t / 2 - rho2 n s - m * viol s t ≤ rho2 d t / 2 - (∑ j, t j) / 4 - (∑ i, s i) / (4 * (q + 1))

def ConeIntegralsFinite : Prop :=
  ∀ (n d q y : ℕ) (D : ℝ), 0 < D → (q = 0 ∨ d + 2 * q < 2 * n) → (y = 0 ∨ n + y < d) → (∫⁻ s in Cone q, ENNReal.ofReal (Real.exp (D * (d / 2 * ∑ i, s i))) * ENNReal.ofReal (Real.exp (-(D * rho2 n s))) < ⊤) ∧ ∫⁻ t in Cone y, ENNReal.ofReal (Real.exp (D * (n * ∑ j, t j))) * ENNReal.ofReal (Real.exp (-(D * rho2 d t))) < ⊤

def FourierInj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ μ : Measure (κ → AF F), μ.IsAddHaarMeasure → ∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ, ∀ Ψ₁ ∈ schA F κ, ∀ Ψ₂ ∈ schA F κ, coef F ψ μ Φ₁ Φ₂ = coef F ψ μ Ψ₁ Ψ₂ → ∀ x u, Φ₁ x * (starRingEnd ℂ) (Φ₂ u) = Ψ₁ x * (starRingEnd ℂ) (Ψ₂ u)

def Parity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∃ (e : UA σ X.J) (c : ℂ), mat e = -1 ∧ ‖c‖ = 1 ∧ ∀ Φ ∈ schA F (Fin n × Fin d), om (e, 1) Φ = c • fun x => Φ (-x)

def CoefSum : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ μ : Measure (κ → AF F), μ.IsAddHaarMeasure → ∃ c : ℝ, 0 < c ∧ ∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ, ‖thetaSum F Φ₁‖ₑ * ‖thetaSum F Φ₂‖ₑ ≤ ENNReal.ofReal c * ∑' w : (κ → F) × (κ → F), ‖coef F ψ μ Φ₁ Φ₂ (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))‖ₑ

def CoefEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ (g : UA σ X.J) (h : UA σ W.J) (z : Ten F E n d), coef F B.ψ μ (om (g, h) Φ₁) (om (g, h) Φ₂) (M.co.e z) = coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * z * (mat h⁻¹)ᵀ))

def CoefReal : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (N : ℕ), ∃ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x y : V), ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)‖ * (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂

def CoefBd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ φ₁ ∈ SB (Fin n × Fin d → Af F), ∀ φ₂ ∈ SB (Fin n × Fin d → Af F), ∀ N : ℕ, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)), Continuous p ∧ IsCompact C ∧ ∀ (f₁ f₂ : SInf F (Fin n × Fin d)) (z : Ten F E n d), ‖coef F B.ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (M.co.e z)‖ ≤ p f₁ * p f₂ * maj B.emb C N z

def SqAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → SqBound B M om {φ | φ ∈ SB _} Set.univ

def SoFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → (∀ Φ ∈ M.So B.ψ B.τ₁, ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ), (∀ i, φ i ∈ soFin B M) ∧ Φ = ∑ i, pureA F (f i) (φ i)) ∧ (∀ Φ ∈ schA F (Fin n × Fin d), ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ), (∀ i, φ i ∈ SB _) ∧ Φ = ∑ i, pureA F (f i) (φ i)) ∧ (∀ Φ ∈ M.So B.ψ B.τ₁, Φ ∈ schA F _) ∧ ∀ φ ∈ soFin B M, ∃ (m : ℕ) (c : Fin m → ℂ) (χ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ i, (∀ v, χ i v ∈ SB _) ∧ (∀ᶠ v in cofinite, χ i v = M.vac v) ∧ χ i B.v₁ ∈ M.SoLoc B.ψ B.τ₁) ∧ ∀ f : SInf F (Fin n × Fin d), pureA F f φ = ∑ i, c i • pure f (χ i)

def SoCut : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ φ ∈ M.SoLoc B.ψ B.τ₁, ∃ (m : ℕ) (χ : Fin m → (Fin n × Fin d → Fv F B.v₁) → ℂ), φ = ∑ i, χ i ∧ ∀ i, χ i ∈ M.SoLoc B.ψ B.τ₁ ∧ ∀ r, Rest (evFin F B.v₁) (χ i) r → ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ z : Ten F E n d, (z.map (piW (B.τ₁.comp σ))).rank ≠ n → coef F B.ψ μ (tens (evFin F B.v₁) (χ i) r) (fun x => tens (evFin F B.v₁) (χ i) r (-x)) (M.co.e z) = 0

def SqSo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → SqBound B M om (soFin B M) (fullRank E n d)

def LatInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E), EpsHerm σ J → EpsHerm σ J' → ∀ C N, ∀ S ∈ ({Set.univ, fullRank E n d} : Set (Set (Matrix (Fin n) (Fin d) E))), ∀ γ ∈ ratU σ J, ∀ δ ∈ ratU σ J', ∀ (g : UA σ J) (h : UA σ J'), latSum τ C N S (γ * g) (δ * h) = latSum τ C N S g h

def LatMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E), EpsHerm σ J → EpsHerm σ J' → ∀ C N S, IsCompact C → ∀ h : UA σ J', Measurable fun g : UA σ J => latSum τ C N S g h

def LatCpt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E), EpsHerm σ J → EpsHerm σ J' → ∀ (Ω : Set (UA σ J)) (Ω' : Set (UA σ J')), IsCompact Ω → IsCompact Ω' → ∀ C N, IsCompact C → ∃ (C' : Set (Ten F E n d)) (K : ℝ≥0), IsCompact C' ∧ ∀ S (g : UA σ J) (h : UA σ J'), ∀ κ ∈ Ω, ∀ κ' ∈ Ω', latSum τ C N S (g * κ) (h * κ') ≤ K * latSum τ C' N S g h

def LatArch : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E), EpsHerm σ J → EpsHerm σ J' → ∀ fr' : Frame σ J', fr'.IsGood → ∀ C N, IsCompact C → ∃ (C' : Set (Ten F E n d)) (K : ℝ≥0), IsCompact C' ∧ ∀ S (g : UA σ J), ∀ t ∈ Cone fr'.r, latSum τ C N S g (fr'.a t) ≤ K * ENNReal.ofReal (Real.exp (N * ∑ j, t j)) * latSum τ C' N S g (1 : UA σ J')

def OneVar : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] (N : ℕ), Module.finrank ℝ V < N → ∃ K : ℝ≥0, ∀ l : ℝ, ∑' x : Λ, ENNReal.ofReal (((1 + Real.exp (-l) * ‖(x : V)‖) ^ N)⁻¹) ≤ K * ENNReal.ofReal (Real.exp (Module.finrank ℝ V * max 0 l))

def LatTor : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E), EpsHerm σ J → EpsHerm σ J' → ∀ (fr : Frame σ J) (fr' : Frame σ J'), fr.IsGood → fr'.IsGood → ∃ N : ℕ, ∀ C, IsCompact C → ∃ K : ℝ≥0, ∀ s ∈ Cone fr.r, ∀ t ∈ Cone fr'.r, latSum τ C N Set.univ (fr.a s) (fr'.a t) ≤ K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * posWt n d s t))

def Minor : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E), EpsHerm σ J → EpsHerm σ J' → ∀ (fr : Frame σ J) (fr' : Frame σ J'), fr.IsGood → fr'.IsGood → ∀ C, IsCompact C → ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Cone fr.r, ∀ t ∈ Cone fr'.r, ∀ x ∈ fullRank E n d, (∃ y ∈ C, At (evI F) (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ - y)) → c * Real.exp (viol s t / (n + 1)) ≤ 1 + sz τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ)

def LatFull : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E), EpsHerm σ J → EpsHerm σ J' → ∀ (fr : Frame σ J) (fr' : Frame σ J'), fr.IsGood → fr'.IsGood → ∀ m : ℕ, ∃ N : ℕ, ∀ C, IsCompact C → ∃ K : ℝ≥0, ∀ s ∈ Cone fr.r, ∀ t ∈ Cone fr'.r, latSum τ C N (fullRank E n d) (fr.a s) (fr'.a t) ≤ K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * posWt n d s t - m * viol s t))

def DomWeil : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → (d + 2 * min r s < 2 * n ∨ min r s = 0) → Dom M om {φ | φ ∈ SB _}

def SoSemi : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ φ ∈ soFin B M, ∀ N : ℕ, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (k : ℕ), Continuous p ∧ ∀ (f : SInf F (Fin n × Fin d)) g h, ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N ≤ p f * (ht h : ℝ) ^ k

def TriplePair : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) ∧ IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) ∧ a + a' + 2 * min (a - G.p) G.p < 2 * a

def SquareIntegrableWeilRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → (d + 2 * min r s < 2 * n ∨ min r s = 0) → (min r' s' = 0 ∨ n + min r' s' < d) → ∀ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 μ → ∀ Φ ∈ schA F (Fin n × Fin d), IntegrableOn (fun h => ‖M.I om Φ h‖ ^ 2) 𝓕 μ

def SquareIntegrableSiegelSet : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → 2 * n ≤ d → (∃ Y, min r s ≤ Y ∧ min r' s' ≤ Y ∧ 2 * Y + 1 < n) → ∀ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 μ → ∀ Φ ∈ M.So B.ψ B.τ₁, IntegrableOn (fun h => ‖M.I om Φ h‖ ^ 2) 𝓕 μ

end PositivityTheory.ThKEst

end
