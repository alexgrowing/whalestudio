import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualFlatOf
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

def PosCoreLetterAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m d : ℕ) (vec : Bool), 1 ≤ m →
      ∃ β : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec))) ≃ₗ[Kf]
          Module.Dual Kf ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec))),
        PosCore O Kf p m (letterWt m d vec) (m * Nat.log p d) β

theorem letterWt_anti (m d : ℕ) (vec : Bool) : Antitone (letterWt m d vec) := by
  intro i j hij
  have hl : i = Fin.last m → j = Fin.last m := fun hi => le_antisymm (Fin.le_last j) (hi ▸ hij)
  have h0 : j = 0 → i = 0 := fun hj => le_antisymm (hj ▸ hij) (Fin.zero_le i)
  unfold letterWt
  cases vec
  · simp only [Bool.false_eq_true, if_false]
    by_cases hj : j = Fin.last m
    · by_cases hi : i = Fin.last m
      · simp [hi, hj]
      · simp [hi, hj]
    · have hi : i ≠ Fin.last m := fun hi => hj (hl hi)
      simp [hi, hj]
  · simp only [if_true]
    by_cases hj : j = 0
    · simp [hj, h0 hj]
    · by_cases hi : i = 0
      · simp [hi, hj]
      · simp [hi, hj]

def kapTenW (p : ℕ) {n' : ℕ} (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : ℕ :=
  ∑ x : TT × Bool, expN p m (hhWt m TT aT bT x)

def DualLatWAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    ∃ Ψ : Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT),
      (∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L →
        (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O) ≤
                  HHL ι σ TT aT bT (latDual L) ∧
        scale ((p : Kf) ^ (kapTenW p m TT aT bT : ℤ)) (HHL (O := O) ι σ TT aT bT (latDual L)) ≤
          (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL (O := O) ι σ TT aT bT L)).map (Ψ.toLinearMap.restrictScalars O)) ∧
      ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e →
        (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O) ≤ ReHH p ι σ w TT aT bT e.dual ∧
        scale ((p : Kf) ^ (kapTenW p m TT aT bT : ℤ)) (ReHH p ι σ w TT aT bT e.dual) ≤
          (ReHH' p ι σ w TT aT bT e).map (Ψ.toLinearMap.restrictScalars O)

end Formalism.MainNotions.ColumnSystems.Pf
