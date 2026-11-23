import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.LemmaJ
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

set_option linter.dupNamespace false

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDD

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def pairMaj {k r : ℕ} (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (p : PairSp k r) : ℝ :=
  Formalism.FourierDecayAlt.B.gN ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1) ^ (-b)

def coefF {k r : ℕ} (L : LocBessel k r) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.Wq →L[ℂ] L.Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, L.σ g v'⟫_ℂ • ξ)

def CellData {k r : ℕ} (L : LocBessel k r) (μG : Measure (Mt k r))
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) : Prop :=
  γ ∈ UH (Hpk k r) ∧ 0 < Gf k r L.z L.z' γ ∧ Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ) ∧
    IsRelStab L γ ∧ IsHaarOn (RStab k r γ) μR ∧ IsOrbQuot L γ μR ν ∧
    PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR

def OnePlace {k r : ℕ} (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp)
    (l' : L.Hs → L.Wq) : Prop :=
  GapAtLeast L.ε L.lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h ∧ L.c ≠ 0 ∧ PI.UpqRep.IsLowUnitH k r L.ε L.lam L.σ w0 ∧
    IsHaarOn (UH (Hpk k r)) μG ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def AmpDD : Prop :=
  Formalism.FourierDecayAlt.ThreeDimData.Inputs →
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlace L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - b → Integrable (pairMaj γ b) ν →
    ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v' ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

def RStabInv : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r)),
    1 ≤ k → γ ∈ UH (Hpk k r) → 0 < Gf k r L.z L.z' γ → IsRelStab L γ →
    Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ) → IsHaarOn (RStab k r γ) μR →
    μR.map (fun x => fun i j => (Matrix.of x)⁻¹ i j) = μR

def OnePlaceKF {k r : ℕ} (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp)
    (l' : L.Hs → L.Wq) : Prop :=
  OnePlace L h μG w0 l l' ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v →
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v →
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def AmpKF : Prop :=
  Formalism.FourierDecayAlt.ThreeDimData.Inputs →
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

def AmpKFOfSteps : Prop :=
  Formalism.FourierDecayAlt.ThreeDimData.SchurH → Formalism.FourierDecayAlt.ThreeDimData.NormInv → Formalism.FourierDecayAlt.ThreeDimData.GrowthG → Formalism.FourierDecayAlt.ThreeDimData.DecDD →
    Formalism.FourierDecayAlt.ThreeDimData.BeConv → RStabInv → AmpKF

def KDense : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)),
      (∀ w ∈ Ws, ∀ X ∈ w, PI.UpqRep.InLieHpk k r X) →
      ∀ e : ℝ, 0 < e → ∃ v' : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v' ∧
        (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - v')‖).sum < e

def NzKF : Prop :=
  KDense → PI.KFinSmooth →
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 : H)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → PI.UpqRep.IsLowUnitH k r ε lam σ w0 →
    ∀ l : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) σ π l →
      (∃ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0, l x ≠ 0) →
      ∃ v : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v ∧ l v ≠ 0

def GapCell (k r : ℕ) (h : ℝ) : Prop :=
  10 * ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) + 2 * Formalism.FourierDecayAlt.ThreeDimData.AG k r + 4 ≤
    Formalism.FourierDecayAlt.ThreeDimData.aOf r h

def CellConv : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r))
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)),
    L.κN ≠ ⊤ → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → CellData L μG γ μR νR ν →
    Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ) →
    ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ Integrable (pairMaj γ b) ν

def AmpDDOfSteps : Prop :=
  Formalism.FourierDecayAlt.ThreeDimData.SchurH → Formalism.FourierDecayAlt.ThreeDimData.NormInv → Formalism.FourierDecayAlt.ThreeDimData.GrowthG → Formalism.FourierDecayAlt.ThreeDimData.DecDD → RStabInv → AmpDD

def GapOfHyp0 (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    ∃ h : ℝ, GapAtLeast (epsSH D.R) lam' h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GapCell D.R.k D.R.rS h

def NVHyp (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
    (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    ∀ (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w') (w0 : A.H),
      PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 →
      (∃ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, ∃ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0,
        Formalism.FourierDecayAlt.ThreeDimData.be W.z (toBessel D τ w w' θ W lam' A hW hA hT hT').c W.π A.σ W.μW
          (toBessel D τ w w' θ W lam' A hW hA hT hT').μN x y ≠ 0) ∧
      (∃ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, ∃ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0,
        Formalism.FourierDecayAlt.ThreeDimData.be W.z' (toBessel D τ w w' θ W lam' A hW hA hT hT').c W.π' A.σ W.μW'
          (toBessel D τ w w' θ W lam' A hW hA hT hT').μN x y ≠ 0)

def AmpOrbOfAmpDD (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Formalism.FourierDecayAlt.ThreeDimData.Inputs → Formalism.FourierDecayAlt.ThreeDimData.DDFormOne → Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOne → KDense → NzKF → AmpKF → CellConv →
    (1000 ≤ Cl → Cn ≤ Cl → GapOfHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 Cn) → NVHyp D large₂ C' Cl Cg cb Cu cT CT C0 Cn →
    Formalism.MainNotions.S.Pv.LemmaJ.AmpOrb D large₂ C' Cl Cg cb Cu cT CT C0 Cn

end Formalism.MainNotions.S.Pv.AmpDD
