import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.VeluIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormClosed
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
import Formalism.FormalGroupLog.Statement

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def VeluIntegralX : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (A g : PowerSeries K) (ι : Type) [Fintype ι]
    (xs : ι → PowerSeries K) (xP : ι → K) (al r : K),
    IsOneUnit R A → (∀ P, IntPS R (xs P)) → (∀ P, xP P ∈ R) → r ∈ R → al ∈ R → al ≠ 0 →
    (2 : K)⁻¹ ∈ R → PowerSeries.constantCoeff g = 1 →
    PowerSeries.C (al ^ 2) * PowerSeries.subst (PowerSeries.C al * PowerSeries.X * g) A
        * PowerSeries.X ^ 2 =
      (PowerSeries.C al * PowerSeries.X * g) ^ 2 * veluXs A xs xP r →
    IntPS R g

def IsEndoR {K : Type} [Field K] (R : Subring K) (e l : PowerSeries K) (c0 : K) {ι : Type}
    [Fintype ι] (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al albar : K) : Prop :=
  IsEndoZ e neg (fun P => xP P + c0) w al ∧ al * albar = (Fintype.card ι : K) + 1 ∧
  (∀ P, PowerSeries.subst l (w P) = xs P + PowerSeries.C c0) ∧ (∀ P, IntPS R (xs P)) ∧
  (∀ P, xP P ∈ R) ∧ al ∈ R ∧ al⁻¹ ∈ R ∧ (al ^ 2 - 1) * c0 ∈ R

def EndIntFromDatum : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (e l linv A : PowerSeries K) (c0 : K)
    (ι : Type) [Fintype ι] (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al albar : K),
    IsLogPair l linv → XIsWp e l A c0 → IsOneUnit R A → (2 : K)⁻¹ ∈ R →
    IsEndoR R e l c0 neg xP w xs al albar → EndInt R l linv al

def PhNormFromDatum : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (e : PowerSeries K) (s2 : K)
    (l linv ph A : PowerSeries K) (c0 : K)
    (ι : Type) [Fintype ι] (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al albar : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 → IsOneUnit R A → (2 : K)⁻¹ ∈ R →
    IsEndoR R e l c0 neg xP w xs al albar →
    al * (al - albar) * s2 = ∑ P, (xP P + c0) →
    PhNormAt R l linv ph al albar

def EndoAllFromData : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ (e : PowerSeries K) (s2 : K) (l linv ph A : PowerSeries K) (c0 : K),
    Frame R l linv ph → F1 R l linv ph → IsPh e s2 l ph → XIsWp e l A c0 → IsOneUnit R A →
    ∀ (O : Type) [CommRing O] [StarRing O] [TopologicalSpace O] (τ : O →+* K),
    Continuous τ → Continuous (star : O → O) →
    (∀ z : O, star z = z → τ z ∈ closure (Set.range (fun n : ℤ => (n : K)))) →
    (2 : K)⁻¹ ∈ R → IsUnit (2 : O) → (∀ α : O, ∃ u v : Oˣ, α = u + v) →
    ∀ Dn : Set O, (∀ α : Oˣ, (α : O) ∈ closure Dn) →
    (∀ α ∈ Dn, ∃ (ι : Type) (_ : Fintype ι) (neg : ι → ι) (xP : ι → K)
        (w xs : ι → PowerSeries K),
      IsEndoR R e l c0 neg xP w xs (τ α) (τ (star α)) ∧
      τ α * (τ α - τ (star α)) * s2 = ∑ P, (xP P + c0)) →
    ∀ α : O, EndInt R l linv (τ α) ∧ PhNormAt R l linv ph (τ α) (τ (star α)) ∧
      AdjAt R l linv ph (τ α) (τ (star α))

def SimeqIffCong : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (f g : MvPowerSeries ι K),
    Formalism.InvariantFactorPaths.G7.Simeq f g ↔ Cong (Formalism.G.unitBall K) f g

def UnitBallClosed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K], IsClosed ((Formalism.G.unitBall K : Subring K) : Set K)

def PhOIsPh : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e l : PowerSeries K) (s2 : K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    Formalism.L2.Th1.B.sgStar s2 e = sgStar e s2 ∧ IsPh e s2 l (Formalism.L2.Th1.B.phO s2 e l)

def FirstLevelFromUniversal : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l linv ph : PowerSeries K), IsLogPair l linv → Formalism.L2.Th1.B.LawLog F l →
    PowerSeries.constantCoeff ph = 0 →
    Formalism.InvariantFactorPaths.G7.Simeq (Formalism.InvariantFactorPaths.G7.d1 F (Formalism.InvariantFactorPaths.G7.cob F ph)) 0 →
    F = fadd l linv (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∧ FGInt (Formalism.G.unitBall K) l linv ∧
      F1 (Formalism.G.unitBall K) l linv ph

def AdjUniversal : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l linv ph : PowerSeries K) (a b : K), IsLogPair l linv → Formalism.L2.Th1.B.LawLog F l →
    PowerSeries.constantCoeff ph = 0 →
    EndInt (Formalism.G.unitBall K) l linv a → EndInt (Formalism.G.unitBall K) l linv b →
    AdjAt (Formalism.G.unitBall K) l linv ph a b →
    Formalism.InvariantFactorPaths.G7.Simeq
      (MvPowerSeries.subst ![Formalism.InvariantFactorPaths.G7.at1 (0 : Fin 2) (mulBy l linv a), MvPowerSeries.X 1]
        (Formalism.InvariantFactorPaths.G7.cob F ph))
      (MvPowerSeries.subst ![MvPowerSeries.X 0, Formalism.InvariantFactorPaths.G7.at1 (1 : Fin 2) (mulBy l linv b)]
        (Formalism.InvariantFactorPaths.G7.cob F ph))

end Formalism.L2.Th1.C
