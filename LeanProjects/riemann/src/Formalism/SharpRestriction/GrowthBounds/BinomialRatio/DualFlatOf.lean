import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def kapTen (p : ℕ) {n' : ℕ} (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : ℕ :=
  ∑ x : TT × Bool, m * Nat.log p (hhDeg aT bT x.1.val x.2)

def DualLatAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    ∃ Ψ : Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT),
      (∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L →
        (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O) ≤
                  HHL ι σ TT aT bT (latDual L) ∧
        scale ((p : Kf) ^ (kapTen p m TT aT bT : ℤ)) (HHL (O := O) ι σ TT aT bT (latDual L)) ≤
          (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O)) ∧
      ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e →
        (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O) ≤ ReHH p ι σ w TT aT bT e.dual ∧
        scale ((p : Kf) ^ (kapTen p m TT aT bT : ℤ)) (ReHH p ι σ w TT aT bT e.dual) ≤
          (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O)

def DualFlatAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    (∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e → IsEdge p n' 1 e.dual ∧ e.dual.dual = e) ∧
    ∃ Ψ : Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT),
      (∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L →
        (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O) ≤
                  HHL ι σ TT aT bT (latDual L) ∧
        scale ((p : Kf) ^ (kapTen p m TT aT bT : ℤ)) (HHL (O := O) ι σ TT aT bT (latDual L)) ≤
          (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O)) ∧
      ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e →
        (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O) ≤ ReHH p ι σ w TT aT bT e.dual ∧
        scale ((p : Kf) ^ (kapTen p m TT aT bT : ℤ)) (ReHH p ι σ w TT aT bT e.dual) ≤
          (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O)

end Formalism.MainNotions.ColumnSystems.Pf
