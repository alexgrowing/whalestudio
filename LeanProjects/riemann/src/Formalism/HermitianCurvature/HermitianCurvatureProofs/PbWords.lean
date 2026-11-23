import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightAverageSmoothComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VLetZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartIntegralLocal

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section defs

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Proper (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n) (Cs : Set (B.Mat k n))
    (U : Set (B.Mat k n)) : Prop :=
  ∀ y ∈ U, ∃ V ∈ 𝓝 y, ∃ K : Set (PBQ.XP k p ρ), IsCompact K ∧ ∀ g ∈ V, g ∈ B.GV k n → ∀ x, PBQ.GoodP Bj x → x ∉ K →
    ∀ ξ, PBG.InR B0 ξ → D.castM e (PBQ.sP Bj x) * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∉ Cs

end defs

def PbWords : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (i : ℕ) (hi : i ≤ n) (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    (∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g) →
    IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → (∀ g ∈ U, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0) →
    Proper Bj B0 e Cs U →
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)), ∀ y ∈ U, y ∈ B.GV k n →
      D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w ew y =
        PBQ.pbF Bj B0 e (D.uwG k n B0.z B0.z' H i hi w ew) y

def PbLoc : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    B.CkOn ⊤ (B.GV k n) H → IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → Proper Bj B0 e Cs U →
    ∀ y ∈ U, y ∈ B.GV k n → CapelliWordSumExpansion.Loc ⊤ (PBQ.pbF Bj B0 e H) y

end Formalism.FourierDecayAlt.P.PartialBesselProperness
