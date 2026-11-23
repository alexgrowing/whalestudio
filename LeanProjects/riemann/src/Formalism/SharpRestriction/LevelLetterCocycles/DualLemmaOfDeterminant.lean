import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
import Formalism.SharpRestriction.LevelLetterCocycles.LengthCokerLe
import Formalism.SharpRestriction.LevelLetterCocycles.LemmaDN0OfAdmits
import Formalism.SharpRestriction.LevelLetterCocycles.WachQuotientCyclicDecomposition

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem hasSubst_π₀ (hz : PowerSeries.constantCoeff W.π₀₁ = 0) : PowerSeries.HasSubst W.π₀₁ := by
  exact PowerSeries.HasSubst.of_constantCoeff_zero' hz

theorem evaluation_add (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f + g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f + Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  exact PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero' hz) f g

theorem evalZero_mul (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f * g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  exact PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hz) f g

theorem evalZero_X_eq_pi0 (hz : PowerSeries.constantCoeff W.π₀₁ = 0) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W PowerSeries.X = W.π₀ := by
  funext i
  show PowerSeries.subst W.π₀₁ PowerSeries.X = W.π₀ i
  rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hz)]
  rfl

theorem evalZero_C (c : O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C c) = algebraMap O (LetA O n) c := by
  funext i
  show PowerSeries.subst W.π₀₁ (PowerSeries.C c) = _
  rw [PowerSeries.subst_C]
  rfl

def AdaptData (T : LocLat G Qp LL O) (i : ZMod n) (h η m : ℕ) (e' : Fin (finrank LL T.V) → W.DD T)
    (m' : ℕ) (u : Fin m' → ℤ) : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T (i - 1) e' ∧ m' ≤ m ∧ ∃ hmr : m' ≤ finrank LL T.V,
    (∀ j, -(η : ℤ) ≤ u j ∧ u j ≤ η) ∧
    (∀ j (hj : e' (Fin.castLE hmr j) ∈ W.N T),
      ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (W.cmp T ⟨_, hj⟩)) ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (u j)) ∧
    ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i →
      Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum (PD := PD) T τ h η ≤ ∑ j, ((h : ℤ) + u j)

def AdaptBas : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ),
        AdaptData W T₂ i (b i + S) η m e' m' u

def DetCondition : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∀ (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ),
        AdaptData W T₂ i (b i + S) η m e' m' u →
      ∀ (r : ℕ) (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O)), IsRed W T₂ i red →
      ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → W.DD T₂) (_ : ∀ j, g j ∈ NDl W T₂ i)
        (cols : Fin r → ↥(NDl W T₂ i)),
        (∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
          ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j) ∧
        ∃ V : ℕ, V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m ∧
          (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB
