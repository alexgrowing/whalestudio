import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

open MeasureTheory Matrix Finset Filter Topology
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.BasicNotions Formalism.QuantumDeterminants

abbrev MatKR (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

section Local

variable {k r : ℕ}

def muS (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map (fun p => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)

def DminN (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (l : ℕ) : ℂ :=
  if h : l < r + 2 then Dmin k r z z' γ ⟨l, h⟩ else 0

def ptBlockEnds {i : ℕ} (p : Point ℂ i) : List ℕ := ((p.1.map Prod.snd).scanl (· + ·) 0).tail

def sizeV (scalePowQuadraticExponent : ℝ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) : ℝ :=
  ∏ l : Fin (r + 2), max 1 (‖Dmin k r z z' γ l‖ / scalePowQuadraticExponent)

def lossV (b C : ℝ) (m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (p : Point ℂ (r + 1)) : ℝ :=
  b ^ (C * (m : ℝ) ^ 4) * (max (Gf k r z z' γ) (Gf k r z z' γ)⁻¹) ^ (C * (m : ℝ) ^ 2) *
    ((ptBlockEnds p).map fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (C * (m : ℝ))).prod

def lossP (b C : ℝ) (m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (p : Point ℂ (r + 1)) : ℝ :=
  (b ^ (C * (m : ℝ)) * ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹).foldr max 1) ^ (C * (r : ℝ) ^ 3)

def chV (T T' : ℝ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) : ℝ :=
  ‖zeta k r z z' γ‖ / Real.sqrt (T * T')

def shV (T T' : ℝ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) : ℝ :=
  Real.sqrt (chV T T' z z' γ ^ 2 - 1)

def chRatio (T T' : ℝ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) : ℝ :=
  if DminN z z' γ r = 0 then 1 else (1 + chV T T' z z' γ) / shV T T' z z' γ

def nuV (T : ℝ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) : ℝ :=
  Gf k r z z' γ / (T * ‖DminN z z' γ r‖ ^ 2)

def epsI {N : ℕ} (I : Finset (Fin N)) : Fin N → ℝ := fun i => if i ∈ I then 1 else 0

def l1dist {N : ℕ} (x y : Fin N → ℝ) : ℝ := ∑ i, |x i - y i|

end Local

structure LocW (k r : ℕ) where
  Wp : Type
  [p1 : NormedAddCommGroup Wp]
  [p2 : InnerProductSpace ℂ Wp]
  [p3 : FiniteDimensional ℂ Wp]
  Wq : Type
  [q1 : NormedAddCommGroup Wq]
  [q2 : InnerProductSpace ℂ Wq]
  [q3 : FiniteDimensional ℂ Wq]
  π : MatKR k r → (Wp →L[ℂ] Wp)
  π' : MatKR k r → (Wq →L[ℂ] Wq)
  z : Fin (2 * r + k + 1) → ℂ
  z' : Fin (2 * r + k + 1) → ℂ
  μG : Measure (Mt k r)
  μW : Measure (Mt k r)
  μW' : Measure (Mt k r)
  μN : Measure (Mt k r)
  νS : Measure (Mt k r)
  νS' : Measure (Mt k r)

attribute [instance] LocW.p1 LocW.p2 LocW.p3 LocW.q1 LocW.q2 LocW.q3

structure LocS {k r : ℕ} (W : LocW k r) where
  H : Type
  [h1 : NormedAddCommGroup H]
  [h2 : InnerProductSpace ℂ H]
  [h3 : CompleteSpace H]
  σ : MatKR k r → (H →L[ℂ] H)
  B : H → W.Wp
  B' : H → W.Wq
  v0 : H
  cN : ℝ
  deg : ℝ

attribute [instance] LocS.h1 LocS.h2 LocS.h3

namespace LocS

variable {k r : ℕ} {W : LocW k r}

def Φ (A : LocS W) (g : MatKR k r) : W.Wp := A.B (A.σ g A.v0)

def Φ' (A : LocS W) (g : MatKR k r) : W.Wq := A.B' (A.σ g A.v0)

def J (A : LocS W) (ν : Measure (Mt k r)) (γ : MatKR k r) : W.Wq →L[ℂ] W.Wp :=
  ampJ ν A.cN A.Φ A.Φ' γ

end LocS

section Scalars

variable (D : D7)

def scalePowQuadraticExponent (large₂ : SizeData₂ D) (C0 : ℝ) : ℝ := large₂.sc.b ^ (C0 * (D.R.m : ℝ) ^ 2)

def GamS (large₂ : SizeData₂ D) : ℝ := Real.exp (large₂.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)

def normalizedLocalScale (w : D.what₂.Word) : ℝ :=
  (Real.exp 1 * Real.pi * gg D ^ (-(D.R.m : ℝ)) / (Tr D w * D.R.k * D.host.v)) ^ D.R.k

def tvPr (τ : D.what₂.Tau) (w' : D.what₂.Word) : ℝ := Tcrit D w' τ / Tr D w'

def lamD (τ : D.what₂.Tau) : Fin (2 * D.R.rS + D.R.k + 1) → ℝ := lamSH D.R (D.hc τ)

def kapN (θ : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ)

end Scalars

section Good

variable (D : D7)

def GoodW (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) : Prop :=
  IsColsType D w τ W.z W.π ∧ IsColsType D w' τ W.z' W.π' ∧
  inWb D.R.k D.R.rS W.z ∧ inWb D.R.k D.R.rS W.z' ∧
  Tz D.R.k D.R.rS W.z = Tr D w ∧ Tz D.R.k D.R.rS W.z' = Tr D w' ∧
  IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG ∧
  IsHaarOn (UWset D.R.k D.R.rS W.z) W.μW ∧ W.μW Set.univ = 1 ∧
  IsHaarOn (UWset D.R.k D.R.rS W.z') W.μW' ∧ W.μW' Set.univ = 1 ∧
  W.μN = haarLie (Nset D.R.k D.R.rS) (kapN D θ) ∧
  IsQuotMeas W.μG (muS W.μW W.μN) W.νS ∧ IsQuotMeas W.μG (muS W.μW' W.μN) W.νS'

def GoodS {W : LocW D.R.k D.R.rS} (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) : Prop :=
  IsHCParam lam ∧ IsDSHpk D.R.k D.R.rS (epsSH D.R) lam A.σ ∧
  IsBesselMapSm W.z (psiS D W.z) A.σ W.π A.B ∧ IsBesselMapSm W.z' (psiS D W.z') A.σ W.π' A.B' ∧
  A.v0 ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ ∧ A.v0 ≠ 0 ∧
  (∃ P, IsCayleyU D.R.k D.R.rS (epsSH D.R) P ∧ A.v0 ∈ lowKSub (epsSH D.R) lam (fun g => A.σ (P⁻¹ * g * P))) ∧
  0 < A.cN ∧
  l2SG W.νS A.Φ = ENNReal.ofReal (A.cN * Module.finrank ℂ W.Wp) ∧
  l2SG W.νS' A.Φ' = ENNReal.ofReal (A.cN * Module.finrank ℂ W.Wq) ∧
  ∃ P, IsCayley D.R.k D.R.rS (epsSH D.R) P ∧
    IsFdeg (((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
      (fun g => A.σ (P⁻¹ * g * P)) A.deg

def RelPt (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : MatKR D.R.k D.R.rS)
    (p : Point ℂ (D.R.rS + 1)) : Prop :=
  γ ∈ UH (Hpk D.R.k D.R.rS) ∧ IsInCell (ZhatO D.R.k D.R.rS z z' γ) p ∧ Gf D.R.k D.R.rS z z' γ ≠ 0

def IsRootMeasR (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : Point ℂ (D.R.rS + 1)) (γ : MatKR D.R.k D.R.rS)
    (μR : Measure (Mt D.R.k D.R.rS)) : Prop :=
  ∃ n ∈ Nset D.R.k D.R.rS, ∃ n' ∈ Nset D.R.k D.R.rS, ∃ g₀ : MatKR D.R.k D.R.rS,
    γ = n * g₀ * n' ∧ ZhatO D.R.k D.R.rS z z' g₀ = ptMat p ∧
    ∃ μ₀ : Measure (Mt D.R.k D.R.rS),
      μ₀ {x | Matrix.of x ∉ Rset D.R.k D.R.rS g₀} = 0 ∧
      μ₀.map (rootCoords D.R.k D.R.rS z' p) =
        ENNReal.ofReal ((2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) • volume ∧
      μR = μ₀.map (fun x => fun i j => (n'⁻¹ * Matrix.of x * n') i j)

def RMeas (W : LocW D.R.k D.R.rS) (γ : MatKR D.R.k D.R.rS) (θ' : ℝ) (νR : Measure (Mt D.R.k D.R.rS)) :
    Prop :=
  ∃ (p : Point ℂ (D.R.rS + 1)) (μR : Measure (Mt D.R.k D.R.rS)), IsRootMeasR D W.z W.z' p γ μR ∧
    IsQuotMeas W.μG (ENNReal.ofReal θ' • μR) νR

def HypTT (w w' : D.what₂.Word) : Prop :=
  Nat.Prime (D.mem w).A.T ∧ Nat.Prime (D.mem w').A.T ∧ 3 ≤ (D.mem w).A.T ∧ 3 ≤ (D.mem w').A.T ∧
    ((D.mem w).A.T : ℤ) ≡ (D.mem w').A.T [ZMOD ((D.host.g 0 * D.host.g 1 : ℕ) : ℤ)]

def normWin (large₂ : SizeData₂ D) (C1 θ : ℝ) : Prop :=
  large₂.sc.b ^ (-(C1 * (D.R.m : ℝ) ^ 2)) ≤ θ ∧ θ ≤ large₂.sc.b ^ (C1 * (D.R.m : ℝ) ^ 2)

end Good

section Shared

variable (D : D7) (large₂ : SizeData₂ D)

def ForAmp (C1 : ℝ)
    (Q : (τ : D.what₂.Tau) → (w w' : D.what₂.Word) → (W : LocW D.R.k D.R.rS) → LocS W →
      MatKR D.R.k D.R.rS → Point ℂ (D.R.rS + 1) → Measure (Mt D.R.k D.R.rS) → Prop) : Prop :=
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ A : LocS W, GoodS D (lamD D τ) A → A.deg = D.dsig τ → ∀ γ p, RelPt D W.z W.z' γ p →
      ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR → Q τ w w' W A γ p νR

def MMv {W : LocW D.R.k D.R.rS} (w w' : D.what₂.Word) (A : LocS W)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : ℝ≥0∞ :=
  ∫⁻ q : (Fin D.R.rS → ℂ) × ℂ,
    ENNReal.ofReal (bcWeight D.R.k D.R.rS (Tr D w) (Tr D w') q *
      hsNormSq (A.J W.μG (bigCell D.R.k D.R.rS q.1 (μsec q.2))))

def TermPts (w w' : D.what₂.Word) (zs zs' : D.what₂.Tau → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (γs : D.what₂.Tau → MatKR D.R.k D.R.rS) (ps : D.what₂.Tau → Point ℂ (D.R.rS + 1)) : Prop :=
  (∀ τ, inWb D.R.k D.R.rS (zs τ) ∧ inWb D.R.k D.R.rS (zs' τ) ∧ Tz D.R.k D.R.rS (zs τ) = Tr D w ∧
    Tz D.R.k D.R.rS (zs' τ) = Tr D w' ∧ RelPt D (zs τ) (zs' τ) (γs τ) (ps τ)) ∧
  (∀ τ τ', ptBlockEnds (ps τ) = ptBlockEnds (ps τ')) ∧
  1 ≤ ∏ τ, Gf D.R.k D.R.rS (zs τ) (zs' τ) (γs τ) ∧
  ∀ τ₀, ∀ l ∈ ptBlockEnds (ps τ₀), 1 ≤ ∏ τ, ‖DminN (zs τ) (zs' τ) (γs τ) l‖ ^ 2

def ampMinF (C δ : ℝ) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (γ : MatKR D.R.k D.R.rS) : ℝ :=
  if DminN z z' γ D.R.rS = 0 then 1
  else min 1 (nuV (Tr D w) z z' γ * tvPr D τ w' * gg D ^ (-(D.R.m : ℝ)) *
    (C / D.R.k) ^ (2 * (D.R.rS : ℝ) * (1 - δ)))

def jhUnit {W : LocW D.R.k D.R.rS} (w w' : D.what₂.Word) (A : LocS W)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (νR : Measure (Mt D.R.k D.R.rS))
    (γ : MatKR D.R.k D.R.rS) : W.Wq →L[ℂ] W.Wp :=
  (((MMv D w w' A μsec).toReal ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • A.J νR γ

end Shared

def toBessel (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS)
    (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') : LocBessel D.R.k D.R.rS where
  ε := epsSH D.R
  lam := lam
  hlam := hA.1
  z := W.z
  z' := W.z'
  hz := by obtain ⟨_, _, h3, _, h5, _⟩ := hW; exact ⟨h3, by rw [h5]; exact hT⟩
  hz' := by obtain ⟨_, _, _, h4, _, h6, _⟩ := hW; exact ⟨h4, by rw [h6]; exact hT'⟩
  u := fun i => ((D.hcW w τ).u i : ℝ)
  u' := fun i => ((D.hcW w' τ).u i : ℝ)
  Hs := A.H
  σ := A.σ
  hσ := hA.2.1
  Wp := W.Wp
  π := W.π
  hπ := hW.1
  Wq := W.Wq
  π' := W.π'
  hπ' := hW.2.1
  c := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)
  μW := W.μW
  μW' := W.μW'
  hμW := by obtain ⟨_, _, _, _, _, _, _, h8, h9, _⟩ := hW; exact ⟨h8, h9⟩
  hμW' := by obtain ⟨_, _, _, _, _, _, _, _, _, h10, h11, _⟩ := hW; exact ⟨h10, h11⟩
  κN := kapN D θ

end Formalism.MainNotions.S
