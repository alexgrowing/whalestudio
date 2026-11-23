import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def IsogenyReduce : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (c : ι → K) (al : K), al ≠ 0 →
    (IsogenyFormula e s2 c al ↔
      mvExp ((2 * ((Fintype.card ι : K) + 1)) • lam e s2 - (2 : K) • PowerSeries.rescale al (lam e s2))
        = ∏ P, wpShift e (c P))

def IsogenyIff : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (c : ι → K) (w : ι → PowerSeries K) (al : K), al ≠ 0 →
    IsEndoZ e neg c w al →
    (IsogenyFormula e s2 c al ↔ (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2 = ∑ P, c P)

def IsogenyIffBar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP : ι → K) (c0 : K) (w : ι → PowerSeries K) (al albar : K), al ≠ 0 →
    al * albar = (Fintype.card ι : K) + 1 →
    IsEndoZ e neg (fun P => xP P + c0) w al →
    (IsogenyFormula e s2 (fun P => xP P + c0) al ↔
      al * (al - albar) * s2 = ∑ P, (xP P + c0))

def s2Of {K : Type} [Field K] {ι : Type} [Fintype ι] (c : ι → K) (al : K) : K :=
  (∑ P, c P) / (al ^ 2 - ((Fintype.card ι : K) + 1))

def SecondCoeffDetermined : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (c : ι → K) (w : ι → PowerSeries K) (al : K), al ≠ 0 →
    al ^ 2 ≠ (Fintype.card ι : K) + 1 → IsEndoZ e neg c w al →
    (∀ s2 : K, IsogenyFormula e s2 c al ↔ s2 = s2Of c al) ∧
    ∀ R : Subring K, (∀ P, c P ∈ R) →
      ((al ^ 2 - ((Fintype.card ι : K) + 1)) * s2Of c al ∈ R) ∧
      ((al ^ 2 - ((Fintype.card ι : K) + 1))⁻¹ ∈ R → s2Of c al ∈ R)

def SecondCoeffConsistency : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (fa fb : G →+ G) (wp : G → K) (al be : K),
    (∀ Q, fb Q = 0 ↔ ∃ T, fa T = Q) → (∀ Q, fa Q = 0 ↔ ∃ T, fb T = Q) →
    (∀ T, fa T ≠ 0 → al ^ 2 * wp (fa T) =
      wp T + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), (wp (T + P) - wp P)) →
    (∀ T, fb T ≠ 0 → be ^ 2 * wp (fb T) =
      wp T + ∑ P ∈ Finset.univ.filter (fun P => fb P = 0 ∧ P ≠ 0), (wp (T + P) - wp P)) →
    (be ^ 2 - ((Finset.univ.filter (fun P => fb P = 0)).card : K)) *
        (∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), wp P) =
      (al ^ 2 - ((Finset.univ.filter (fun P => fa P = 0)).card : K)) *
        (∑ P ∈ Finset.univ.filter (fun P => fb P = 0 ∧ P ≠ 0), wp P)

def ChordSecondLogDeriv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (g2 g3 c d : K) (wplus wminus : PowerSeries K),
    (-2 + PowerSeries.X ^ 3 * PowerSeries.derivative K e) ^ 2 =
      4 * (wpShift e 0) ^ 3 - PowerSeries.C g2 * PowerSeries.X ^ 4 * wpShift e 0
        - PowerSeries.C g3 * PowerSeries.X ^ 6 →
    d ^ 2 = 4 * c ^ 3 - g2 * c - g3 →
    4 * PowerSeries.X ^ 2 * (wpShift e c) ^ 2 * wplus =
      ((-2 + PowerSeries.X ^ 3 * PowerSeries.derivative K e) - PowerSeries.C d * PowerSeries.X ^ 3) ^ 2
        - 4 * (wpShift e c) ^ 2 * wpShift e 0
        - 4 * PowerSeries.C c * PowerSeries.X ^ 2 * (wpShift e c) ^ 2 →
    4 * PowerSeries.X ^ 2 * (wpShift e c) ^ 2 * wminus =
      ((-2 + PowerSeries.X ^ 3 * PowerSeries.derivative K e) + PowerSeries.C d * PowerSeries.X ^ 3) ^ 2
        - 4 * (wpShift e c) ^ 2 * wpShift e 0
        - 4 * PowerSeries.C c * PowerSeries.X ^ 2 * (wpShift e c) ^ 2 →
    HasSecondLogDeriv (wpShift e c) (2 * e - wplus - wminus)

end Formalism.L2.Th1.C
