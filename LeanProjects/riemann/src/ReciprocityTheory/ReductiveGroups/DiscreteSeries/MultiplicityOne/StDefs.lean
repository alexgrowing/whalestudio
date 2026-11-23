import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

structure SigData (k r : ℕ) where
  Hs : Type
  [hN : NormedAddCommGroup Hs]
  [hI : InnerProductSpace ℂ Hs]
  [hC : CompleteSpace Hs]
  σ : Mat k r → (Hs →L[ℂ] Hs)
  rep : Formalism.MainNotions.S.IsURepOn (GV k r) σ
  irr : Formalism.MainNotions.S.IsIrredOn (GV k r) σ
  w : Hs
  w_norm : ‖w‖ = 1
  a : ℝ
  Cw : ℝ
  dec : ∀ x ∈ GV k r, ‖⟪w, σ x w⟫_ℂ‖ ≤ Cw * gN x ^ (-a)

attribute [instance] SigData.hN SigData.hI SigData.hC

variable {k r : ℕ}

def nR (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

def aM (k r : ℕ) : ℝ := 4 * nR k r ^ 3

def AG (k r : ℕ) : ℝ := nR k r ^ 2

def AS (k r : ℕ) : ℝ := nR k r ^ 3

def mc (X : SigData k r) (u v : X.Hs) (g : Mat k r) : ℂ := ⟪v, X.σ g u⟫_ℂ

def VflA (X : SigData k r) (b : ℝ) : Set X.Hs :=
  {u | ∃ C : ℝ, ∀ x ∈ GV k r, ‖mc X u X.w x‖ ≤ C * gN x ^ (-b)}

def Vfl (X : SigData k r) : Set X.Hs := VflA X X.a

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

structure IsDiag (D : RealPlaceData k r Wp Wp) : Prop where
  z_eq : D.z' = D.z
  π_eq : D.π' = D.π
  μW_eq : D.μW' = D.μW
  mass : D.μW Set.univ = 1
  irr : Formalism.MainNotions.S.IsIrredOn (UWset k r D.z) D.π

def psiD (D : RealPlaceData k r Wp Wq) (m : Mat k r) : ℂ := psi k r D.z cStd m

def SqIntG (D : RealPlaceData k r Wp Wq) (X : SigData k r) : Prop :=
  ∀ v w : X.Hs, MemLp (fun g : Mt k r => mc X v w (Matrix.of g)) 2 D.μG

def IsFdegG (D : RealPlaceData k r Wp Wq) (X : SigData k r) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : X.Hs,
    Integrable (fun g : Mt k r => mc X v w (Matrix.of g) * star (mc X v' w' (Matrix.of g))) D.μG ∧
    ∫ g : Mt k r, mc X v w (Matrix.of g) * star (mc X v' w' (Matrix.of g)) ∂D.μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def beInt (D : RealPlaceData k r Wp Wq) (X : SigData k r) (u u' : X.Hs) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (mc X u u' (Matrix.of p.2 * Matrix.of p.1) * star (psiD D (Matrix.of p.2))) • D.π (Matrix.of p.1)⁻¹

def beOp (D : RealPlaceData k r Wp Wq) (X : SigData k r) (u u' : X.Hs) : Wp →L[ℂ] Wp :=
  ∫ p, beInt D X u u' p ∂(D.μW.prod D.μN)

def rk1 (a b : Wp) : Wp →L[ℂ] Wp := (innerSL ℂ b).smulRight a

def IsSMapOn (D : RealPlaceData k r Wp Wq) (X : SigData k r) (E : Set X.Hs) (l : X.Hs → Wp) : Prop :=
  (∀ u ∈ E, ∀ v ∈ E, l (u + v) = l u + l v) ∧ (∀ (c : ℂ), ∀ u ∈ E, l (c • u) = c • l u) ∧
    ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ u ∈ E, l (X.σ (m * h) u) = psiD D m • D.π h (l u)

def IsMultOneMap (D : RealPlaceData k r Wp Wq) (X : SigData k r) (l : X.Hs → Wp) : Prop :=
  IsSMapOn D X (Vfl X) l ∧ ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, beOp D X u u' = rk1 (l u) (l u')

def IsTestG (φ : Mat k r → ℂ) : Prop :=
  CkOn ⊤ (GV k r) φ ∧ ∃ K : Set (Mat k r), IsCompact K ∧ ∀ g ∈ GV k r, g ∉ K → φ g = 0

def sigInt (D : RealPlaceData k r Wp Wq) (X : SigData k r) (φ : Mat k r → ℂ) (v : X.Hs) : X.Hs :=
  ∫ g : Mt k r, φ (Matrix.of g) • X.σ (Matrix.of g) v ∂D.μG

def DDinf (D : RealPlaceData k r Wp Wq) (X : SigData k r) : Set X.Hs :=
  {v | ∃ φ, IsTestG φ ∧ v = sigInt D X φ X.w}

def IsZFrame (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  γᴴ * Hb k * γ = Hb k ∧
    embWb k r γ *ᵥ bvec (wI k r (Fin.last k)) = (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z

def gbar (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (g : Mat k r) : Mat k r :=
  embWb k r γ * ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) * (embWb k r γ)⁻¹

def th (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (g : Mat k r) : Mat k r := (gbar k r γ g)⁻¹

def w1 (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin (2 * r + k + 1) → ℂ :=
  embWb k r γ *ᵥ bvec (wI k r 0)

def UUset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Set (Mat k r) :=
  {u | u ∈ UWset k r z ∧ u *ᵥ w1 k r γ = w1 k r γ}

def mud (k : ℕ) (d : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j =>
  if i = 0 ∧ j = 0 then -(starRingEnd ℂ d)
  else if i = Fin.last k ∧ j = 0 then -((Real.sqrt (Complex.normSq d - 1) : ℝ) : ℂ)
  else if i = 0 ∧ j = Fin.last k then ((Real.sqrt (Complex.normSq d - 1) : ℝ) : ℂ)
  else if i = Fin.last k ∧ j = Fin.last k then d
  else if i = j then 1 else 0

def g0 (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (c : Fin r → ℂ) (d : ℂ) : Mat k r :=
  bigCell k r c (γ * mud k d * γ⁻¹)

def scalF (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (f : Mat k r → ℂ) :
    Mat k r → (Wp →L[ℂ] Wp) := fun g => f g • ContinuousLinearMap.id ℂ Wp

def Ef (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (q : (Fin r → ℂ) × ℂ) : ℝ≥0∞ :=
  ∫⁻ p, ‖rho D p F (gq D q)‖ₑ ∂D.μSS

def muS (D : RealPlaceData k r Wp Wq) : Measure (Mt k r) :=
  (D.μW.prod D.μN).map fun p => ((Matrix.of p.2 * Matrix.of p.1 : Mat k r) : Mt k r)

end ReciprocityTheory.ChartRestriction.DS.Mult1
