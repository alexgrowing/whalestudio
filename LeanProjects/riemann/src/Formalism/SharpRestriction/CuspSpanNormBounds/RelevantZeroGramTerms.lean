import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.FormalDegreeBessel.StatementRP
import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.MainNotions.S

abbrev umat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

section Rep

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURepOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Formalism.QuantumDeterminants.IsCRepOn G σ ∧ (∀ g ∈ G, ∀ v : H, ‖σ g v‖ = ‖v‖) ∧
    ∀ v : H, ContinuousOn (fun g => σ g v) G

def IsIrredOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g ∈ G, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤

def coefOn {ε : Fin n → Bool} (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v w : H) :
    Formalism.REAL.UJ ε → ℂ :=
  fun g => ⟪w, σ (umat g) v⟫_ℂ

def IsSqIntOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v w : H, MemLp (coefOn (ε := ε) σ v w) 2 (Formalism.REAL.muG ε)

def IsFdeg {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => coefOn σ v w g * star (coefOn σ v' w' g)) μ ∧
    ∫ g, coefOn σ v w g * star (coefOn σ v' w' g) ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def fdegOf {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (w : H) : ℝ :=
  ‖w‖ ^ 4 / ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ

def IsWtOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ θ : Fin n → ℝ, Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ G →
    σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) v =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v

def CDom (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
    Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b

def IsKStableOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Prop :=
  ∀ g ∈ Formalism.REAL.Kset ε, ∀ v ∈ S, σ g v ∈ S

def IsKTypeOf (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ)
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧
    (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtOn (Formalism.REAL.Kset ε) σ Λ v) ∧
    ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → IsWtOn (Formalism.REAL.Kset ε) σ μ v → CDom ε μ Λ

def vNormSq (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := Formalism.REAL.nsq (μ + (2 : ℝ) • Formalism.REAL.rhoC ε)

def UJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | Formalism.REAL.inUJ ε g}

def IsDS (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ ∧
    (∃ S : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
      vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ vNormSq ε μ

def lowKSub (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Submodule ℂ H :=
  sSup {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}

def IsOrthProjOnto (E : H →L[ℂ] H) (S : Submodule ℂ H) : Prop :=
  E.comp E = E ∧ (∀ x y : H, ⟪E x, y⟫_ℂ = ⟪x, E y⟫_ℂ) ∧ LinearMap.range (E : H →ₗ[ℂ] H) = S

def IsHighestUnit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (w : H) : Prop :=
  ‖w‖ = 1 ∧ w ∈ lowKSub ε lam σ ∧ IsWtOn (Formalism.REAL.Kset ε) σ (Formalism.QuantumDeterminants.lowK ε lam) w

def IsLowUnit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ‖w‖ = 1 ∧ w ∈ lowKSub ε lam σ

def allPos (k : ℕ) : Fin k → Bool := fun _ => true

def IsHCTypeU (k : ℕ) (u : Fin k → ℝ) (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) : Prop :=
  Nontrivial H ∧ FiniteDimensional ℂ H ∧ IsURepOn (UJset (allPos k)) π ∧
    IsKTypeOf (allPos k) π (Formalism.QuantumDeterminants.lowK (allPos k) u) ⊤

end Rep

section Hpk

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCayley (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r

def IsCayleyU (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  IsCayley k r ε P ∧ P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ

def IsDSHpk (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ P, IsCayleyU k r ε P ∧ IsDS ε lam (fun g => σ (P⁻¹ * g * P))

def IsLowUnitH (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ∃ P, IsCayleyU k r ε P ∧ IsLowUnit ε lam (fun g => σ (P⁻¹ * g * P)) w

def IsHighestUnitH (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ∃ P, IsCayleyU k r ε P ∧ IsHighestUnit ε lam (fun g => σ (P⁻¹ * g * P)) w

def blockW (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j =>
    if hi : r ≤ i.val ∧ i.val < r + k then
      (if hj : r ≤ j.val ∧ j.val < r + k then h ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0)
    else (if i = j then 1 else 0)

def IsFrameW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) ∧
      g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) ∧
    g *ᵥ (((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))) = z

def IsHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ g, IsFrameW k r z g ∧ IsHCTypeU k u (fun h => π (g * blockW k r h * g⁻¹))

end Hpk

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (Formalism.QuantumDeterminants.lmulM s) = μ

def hsInner {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A B : Wq →L[ℂ] Wp) : ℂ :=
  ∑ i, ⟪B (stdOrthonormalBasis ℂ Wq i), A (stdOrthonormalBasis ℂ Wq i)⟫_ℂ

def cOfDpsi (s : ℂ) : ℂ := -2 * Complex.I * s

section Params

open Formalism.BasicNotions

theorem dimS_eq (R : Ranks) : 2 * R.rS + R.k + 1 = R.r := by
  obtain ⟨j, hj⟩ := R.m_even
  have h2 := R.two_le_m
  show 2 * (R.m / 2 - 1) + R.k + 1 = R.k + R.m - 1
  omega

def lamS (R : Ranks) (P : HCParam R) : Fin R.r → ℝ := fun i =>
  if h : i.val < R.k - 1 then (P.v ⟨i.val, h⟩ : ℝ)
  else if h' : i.val - (R.k - 1) < R.m then -(P.b ⟨i.val - (R.k - 1), h'⟩ : ℝ) else 0

def epsS (R : Ranks) : Fin R.r → Bool := fun i =>
  if i.val < R.k - 1 then true else decide ((i.val - (R.k - 1)) % 2 = 0)

def lamSH (R : Ranks) (P : HCParam R) : Fin (2 * R.rS + R.k + 1) → ℝ :=
  fun i => lamS R P (Fin.cast (dimS_eq R) i)

def epsSH (R : Ranks) : Fin (2 * R.rS + R.k + 1) → Bool := fun i => epsS R (Fin.cast (dimS_eq R) i)

def IsRowsDS (D : Formalism.BasicNotions.D7) (τ : D.what₂.Tau) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamSH D.R (D.hc τ)) σ

def IsColsType (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (π : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  IsHCTypeW D.R.k D.R.rS z (fun i => ((D.hcW u τ).u i : ℝ)) π

end Params

section Bessel

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsSmoothVec (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  Formalism.QuantumDeterminants.SmoothOnH (Formalism.QuantumDeterminants.Hpk k r) (fun g => σ g v)

def smoothVecs (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Set H :=
  {v | IsSmoothVec (k := k) (r := r) σ v}

def ellA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
  else (g *ᵥ z) (Formalism.QuantumDeterminants.eI k r a)

def psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, c a * ellA k r z g a).re : ℂ))

def IsQuotMeas (μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  ∀ f : Formalism.QuantumDeterminants.Mt k r → ENNReal, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν

def IsSPsiEquiv {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) : Prop :=
  ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
    W (h * m * g) = ψ m • π h (W g)

def l2SG {Wp : Type*} [NormedAddCommGroup Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) : ENNReal :=
  ∫⁻ x, (‖W (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂ν

def rconv {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (e : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp :=
  fun x => ∫ g, e (Matrix.of g) • W (x * Matrix.of g) ∂μG

end Bessel

section Points

def ptHead {K : Type*} [Zero K] (bs : List (K × ℕ)) : List (K × ℕ) := bs.dropLast

def leadMinor {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (l : ℕ) (hl : l ≤ N) : ℂ :=
  (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def Ml (k r l : ℕ) : ℕ := 2 * (r + 1 - l) + k + 1

def ptWeightFrom (k r : ℕ) (T T' : ℝ) : ℕ → List (ℂ × ℕ) → ℝ
  | _, [] => 1
  | a, (t, s) :: bs =>
    (if s = 1 ∧ a + 1 = r + 1 then (Complex.normSq t - T * T') ^ (k - 1)
      else ‖t‖ ^ (2 * s * (Ml k r (a + s) + s - 3))) * ptWeightFrom k r T T' (a + s) bs

def ptWeight (k r : ℕ) (T T' : ℝ) {i : ℕ} (p : Point ℂ i) : ℝ := ptWeightFrom k r T T' 0 p.1

def PtLastOk (r : ℕ) (T T' : ℝ) (p : Point ℂ (r + 1)) : Prop :=
  ∀ t : ℂ, p.1.getLast? = some (t, 1) → T * T' < Complex.normSq t

def beS {n k : ℕ} (κ : ℝ) (r : ℕ) (lam : Fin n → ℝ) (T T' : ℝ) (u u' : Fin k → ℝ) (Y : ℝ) : ℝ :=
  κ ^ (-(1 + 2 * (r : ℤ))) *
    Real.sqrt ‖Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (Y : ℂ) * Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) ((Y : ℂ) + 1) /
      Formalism.QuantumDeterminants.qPoly T T' u u' (Y : ℂ)‖

def InterlaceS {k n : ℕ} (hkn : k ≤ n) (u : Fin k → ℝ) (lam : Fin n → ℝ) : Prop :=
  (∀ (i : ℕ) (hi : i + 1 < k),
    lam ⟨i, by omega⟩ < u ⟨i, by omega⟩ ∧ u ⟨i + 1, hi⟩ < lam ⟨i, by omega⟩) ∧
    ∀ (h : 0 < k), lam ⟨k - 1, by omega⟩ < u ⟨k - 1, by omega⟩

def vand {k : ℕ} (x : Fin k → ℝ) : ℝ := ∏ a : Fin k, ∏ b ∈ univ.filter (fun b : Fin k => a < b), (x a - x b)

end Points

section Smooth

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def InLieHpk (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0

def dsig (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

def IsBesselMapSm {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (B : H → Wp) : Prop :=
  (∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ w ∈ smoothVecs (k := k) (r := r) σ, B (v + w) = B v + B w) ∧
    (∀ (c : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) σ, B (c • v) = c • B v) ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
      B (σ (h * m) v) = ψ m • π h (B v)) ∧
    IsCWCont (k := k) (r := r) σ B

def eucl {N : ℕ} (v : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, Complex.normSq (v i))

def lA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a : Fin (r + 1)) : ℝ :=
  sInf {t | ∃ y ∈ Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} =>
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1)),
    t = eucl (g⁻¹ *ᵥ (Formalism.QuantumDeterminants.fvec k r z a - y))}

end Smooth

section Cells

variable {K : Type*} [CommRing K]

def IsLoUni {N : ℕ} (L : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1)

def IsUpUni {N : ℕ} (U : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1)

def IsInCell {N : ℕ} (Z : Matrix (Fin N) (Fin N) K) (p : Point K N) : Prop :=
  ∃ L U : Matrix (Fin N) (Fin N) K, IsLoUni L ∧ IsUpUni U ∧ Z = L * ptMat p * U

end Cells

def dimPiU (k : ℕ) (u : Fin k → ℝ) : ℕ :=
  sInf {d | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π ∧ Module.finrank ℂ H = d}

def hsNormSq {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : ℝ := (hsInner A A).re

section Kernel

open Formalism.BasicNotions

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {Word Tau : Type} [Fintype Tau]
  {hc : Word → Tau → HCParam R} (s : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc)

def dimPi (u : Word) : ℝ := ∏ τ, ((dimPiU R.k (fun i => ((hc u τ).u i : ℝ)) : ℕ) : ℝ)

def c0 (u : Word) : ℝ := s.volN u * s.volH u / dimPi (hc := hc) u

def Kmat (u u' : Word) : s.Cu u' →L[ℂ] s.Cu u :=
  haveI := FiniteDimensional.complete ℂ (s.Cu u)
  haveI := FiniteDimensional.complete ℂ (s.Cu u')
  haveI := FiniteDimensional.complete ℂ s.HH
  (((c0 s u * c0 s u') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((ContinuousLinearMap.adjoint (s.Pu u)).comp (s.Pu u'))

def KExpansion (u u' : Word) : Prop := HasSum (fun t => s.aTerm u u' t) (Kmat s u u')

def KAbsConv (u u' : Word) : Prop := Summable (fun t => ‖s.aTerm u u' t‖)

def KOf (u u' : Word) (Φ : Set (s.Term u u')) : s.Cu u' →L[ℂ] s.Cu u := ∑' t : Φ, s.aTerm u u' t.1

def RelevantZeroGramTerms {u u' : Word} : Set (s.Term u u') := {t | s.relevant t ∧ s.Gterm t = 0 ∧ ¬ s.FeqF t}

def famNG {u u' : Word} : Set (s.Term u u') := {t | ¬ s.isId t ∧ s.Gterm t ≠ 0 ∧ ¬ s.generic t}

def famG {u u' : Word} : Set (s.Term u u') := {t | ¬ s.isId t ∧ s.Gterm t ≠ 0 ∧ s.generic t}

def loopP {u u' : Word} (p : s.Pair u u') : Prop :=
  s.Gterm (s.pfst p) ≠ 0 ∧ s.Gterm (s.psnd p) ≠ 0 ∧
    (2 ≤ s.s0 p ∨ (s.generic (s.pfst p) ∧ s.generic (s.psnd p) ∧ s.s0 p = 1 ∧ ¬ s.scalarPair p))

def scalarP {u u' : Word} (p : s.Pair u u') : Prop :=
  s.generic (s.pfst p) ∧ s.generic (s.psnd p) ∧ s.s0 p = 1 ∧ s.scalarPair p

def pairsIn {u u' : Word} (Φ : Set (s.Term u u')) : Set (s.Pair u u') := {p | s.pfst p ∈ Φ ∧ s.psnd p ∈ Φ}

def K2 (u u' : Word) : s.Cu u' →L[ℂ] s.Cu u := KOf s u u' (RelevantZeroGramTerms s)

def Kgs (u u' : Word) (w w' : Point E (R.rS + 1)) : ℂ :=
  ∑' p : {p : s.Pair u u' // scalarP s p ∧ s.ptOf (s.pfst p) = w ∧ s.ptOf (s.psnd p) = w'},
    (s.massPair p.1 : ℂ) * s.cTerm (s.pfst p.1) * star (s.cTerm (s.psnd p.1))

def IdCellDiag (u : Word) : Prop :=
  HasSum (fun t : {t : s.Term u u // s.isId t} => s.aTerm u u t.1) (ContinuousLinearMap.id ℂ (s.Cu u))

def IdCellOff (u u' : Word) : Prop :=
  HasSum (fun t : {t : s.Term u u' // s.isId t} => s.aTerm u u' t.1) 0

end Kernel

section Pinned

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

def haarLie {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (κ : ENNReal) :
    Measure (Formalism.QuantumDeterminants.Mt k r) :=
  κ • Measure.map (fun x : lieE S => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) volume

def Rset (k r : ℕ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ Formalism.QuantumDeterminants.Nset k r ∧ γ * g * γ⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r}

def psiS (D : Formalism.BasicNotions.D7) (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ℂ :=
  Formalism.QuantumDeterminants.psi D.R.k D.R.rS z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)

end Pinned

section Amp

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def ampJ {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (c : ℝ)
    (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp)
    (Φ' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  (c : ℂ)⁻¹ • ∫ x, (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x)) ∂ν

def fdegH (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : ℝ :=
  ‖w‖ ^ 4 / ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG

def eFun (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  (fdegH μG σ w : ℂ) * star ⟪w, σ g w⟫_ℂ

def IsKFinHpk (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, σ g x ∈ S

def IsKFin {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ IsKStableOn ε σ S

def rdM {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (X : Matrix (Fin m) (Fin m) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ → V) : Matrix (Fin m) (Fin m) ℂ → V :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

def ldM {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (X : Matrix (Fin m) (Fin m) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ → V) : Matrix (Fin m) (Fin m) ℂ → V :=
  fun g => deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) 0

def rdWord {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Matrix (Fin m) (Fin m) ℂ) → (Matrix (Fin m) (Fin m) ℂ → V) → Matrix (Fin m) (Fin m) ℂ → V
  | [], f => f
  | X :: w, f => rdM X (rdWord w f)

def ldWord {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Matrix (Fin m) (Fin m) ℂ) → (Matrix (Fin m) (Fin m) ℂ → V) → Matrix (Fin m) (Fin m) ℂ → V
  | [], f => f
  | X :: w, f => ldM X (ldWord w f)

end Amp

def IsCutS {k : ℕ} (u u' : Fin k → ℝ) (I : Set ℝ) : Prop :=
  ∃ (l : Fin k) (a b : ℝ), u l ≠ u' l ∧ a ≤ b ∧ I = Set.Icc a b ∧
    min (-u l) (-u' l) < a ∧ b < max (-u l) (-u' l) ∧
    ∀ y ∈ I, 2 ≤ |y + u l| ∧ 2 ≤ |y + u' l|

structure LocBessel (k r : ℕ) where
  ε : Fin (2 * r + k + 1) → Bool
  lam : Fin (2 * r + k + 1) → ℝ
  hlam : Formalism.QuantumDeterminants.IsHCParam lam
  z : Fin (2 * r + k + 1) → ℂ
  z' : Fin (2 * r + k + 1) → ℂ
  hz : Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z
  hz' : Formalism.QuantumDeterminants.inWb k r z' ∧ 0 < Formalism.QuantumDeterminants.Tz k r z'
  u : Fin k → ℝ
  u' : Fin k → ℝ
  Hs : Type
  [hsN : NormedAddCommGroup Hs]
  [hsI : InnerProductSpace ℂ Hs]
  [hsC : CompleteSpace Hs]
  σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)
  hσ : IsDSHpk k r ε lam σ
  Wp : Type
  [wpN : NormedAddCommGroup Wp]
  [wpI : InnerProductSpace ℂ Wp]
  [wpF : FiniteDimensional ℂ Wp]
  π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)
  hπ : IsHCTypeW k r z u π
  Wq : Type
  [wqN : NormedAddCommGroup Wq]
  [wqI : InnerProductSpace ℂ Wq]
  [wqF : FiniteDimensional ℂ Wq]
  π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq)
  hπ' : IsHCTypeW k r z' u' π'
  c : ℂ
  μW : Measure (Formalism.QuantumDeterminants.Mt k r)
  μW' : Measure (Formalism.QuantumDeterminants.Mt k r)
  hμW : IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW ∧ μW Set.univ = 1
  hμW' : IsHaarOn (Formalism.QuantumDeterminants.UWset k r z') μW' ∧ μW' Set.univ = 1
  κN : ENNReal

attribute [instance] LocBessel.hsN LocBessel.hsI LocBessel.hsC LocBessel.wpN LocBessel.wpI LocBessel.wpF
  LocBessel.wqN LocBessel.wqI LocBessel.wqF

def LocBessel.μN {k r : ℕ} (L : LocBessel k r) : Measure (Formalism.QuantumDeterminants.Mt k r) := haarLie (Formalism.QuantumDeterminants.Nset k r) L.κN

def LocBessel.J {k r : ℕ} (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.Wq →L[ℂ] L.Wp :=
  Formalism.QuantumDeterminants.besselJ k r L.z L.z' L.c L.π L.π' L.μW L.μN L.μW' F g

section KernelD

variable (D : Formalism.BasicNotions.D7)

def KD (u u' : D.what₂.Word) : D.s.Cu u' →L[ℂ] D.s.Cu u := Kmat D.s u u'

def ramCu (u : D.what₂.Word) : Submodule ℂ (D.s.Cu u) :=
  Submodule.comap ((D.s_Cu u : D.s.Cu u →ₗ[ℂ] (D.mem u).A.Mu0))
    (Submodule.comap (D.mem u).A.Mu0.subtype (D.mem u).A.Mram)

def PiU (u : D.what₂.Word) : D.s.Cu u →L[ℂ] D.s.Cu u :=
  haveI := FiniteDimensional.complete ℂ (ramCu D u)
  (ramCu D u).subtypeL.comp (ramCu D u).orthogonalProjectionOnto

def hsSqD (u u' : D.what₂.Word) : ℝ := hsNormSq (KD D u u')

def hsDiagD (u : D.what₂.Word) : ℝ :=
  hsNormSq ((PiU D u).comp ((KD D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)).comp (PiU D u)))

end KernelD

def LocBessel.beta {k r : ℕ} (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (F F' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) : ℂ :=
  ∫ p : (Fin r → ℂ) × ℂ, (Formalism.QuantumDeterminants.bcWeight k r (Formalism.QuantumDeterminants.Tz k r L.z) (Formalism.QuantumDeterminants.Tz k r L.z') p : ℂ) *
    hsInner (L.J F (Formalism.QuantumDeterminants.bigCell k r p.1 (μsec p.2))) (L.J F' (Formalism.QuantumDeterminants.bigCell k r p.1 (μsec p.2)))

def capC {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : ℂ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V :=
  Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk k r) (Y + ((2 * r + k : ℕ) : ℂ) / 2) F

def capW {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (sgn : ℝ) :
    List ℂ → (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V) →
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V
  | [], F => F
  | Y :: w, F => fun g => (sgn : ℂ) • capC (k := k) (r := r) Y (capW sgn w F) g

def brkW {n : ℕ} (lam : Fin n → ℝ) (Ys : List ℝ) : ℝ :=
  (Ys.map fun Y => ‖Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) (Y : ℂ)‖).prod

def IsCutoff (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ≤ 1 / 2, χ x = 0) ∧ ∀ x, 1 ≤ x → χ x = 1

theorem isCutoff_exists : ∃ χ : ℝ → ℝ, IsCutoff χ := by
  refine ⟨fun x => Real.smoothTransition (2 * x - 1), ?_, ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x hx
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · intro x hx
    exact Real.smoothTransition.one_of_one_le (by linarith)

def IsCC {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (k r : ℕ) (A : ℝ) (mm : ℕ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V) : Prop :=
  Formalism.QuantumDeterminants.SmoothOnH (Formalism.QuantumDeterminants.Hpk k r) F ∧
    ∀ w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), w.length ≤ mm →
      (∀ X ∈ w, InLieHpk k r X) → ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        ‖rdWord w F g‖ ≤ C * (1 + Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j))) ^ (-A)

def IsKFinCoefH {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (P : H →L[ℂ] Wp) (Q : Wq →L[ℂ] H), (∀ w, IsKFinHpk (k := k) (r := r) σ (Q w)) ∧
    (∀ x, IsKFinHpk (k := k) (r := r) σ (ContinuousLinearMap.adjoint P x)) ∧ ∀ g, f g = P.comp ((σ g).comp Q)

end Formalism.MainNotions.S
