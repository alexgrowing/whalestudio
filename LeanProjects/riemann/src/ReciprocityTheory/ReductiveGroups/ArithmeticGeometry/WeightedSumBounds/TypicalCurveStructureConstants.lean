import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.NsmulCoprimeBijectiveCurves
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtBasisMapGood

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

def addMv {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    {τ : Type} (x y : Fin d → MvPowerSeries τ C) : Fin d → MvPowerSeries τ C :=
  fun a => subst (Sum.elim x y) (G.F a)

def sumMvList {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    {τ : Type} : List (Fin d → MvPowerSeries τ C) → (Fin d → MvPowerSeries τ C)
  | [] => 0
  | x :: l => addMv G x (sumMvList G l)

def basisMap {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    (γ : Fin d → Fin d → PowerSeries C) : Fin d → MvPowerSeries (Fin d) C :=
  sumMvList G (List.ofFn fun a => fun b => PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (γ a b))

def IsBasis {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    (p : ℕ) {h : ℕ} (ty : Fin d → ZMod h) (γ : Fin d → Fin d → PowerSeries C) : Prop :=
  (∀ a, IsCurve v (γ a)) ∧ (∀ a, G.IsOfType p ty (ty a) (γ a)) ∧
    v (Matrix.det (Matrix.of fun a b => tangent (γ a) b)) = 0

def CoprimeMultiplicationBijective : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d : ℕ) (G : LogFGL v d) (n : ℕ), ¬ p ∣ n →
      ∀ gb : Fin d → PowerSeries C, IsCurve v gb →
        ∃! ga : Fin d → PowerSeries C, IsCurve v ga ∧ G.nsmulF n ga = gb

def TypicalCurveEigenspace : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d),
      MuAction G p h ty → ∀ (i : ZMod h) (u : Fin d → C), (∀ a, IsIntV v (u a)) →
        (∀ a, ty a ≠ i → u a = 0) →
          ∃ γ : Fin d → PowerSeries C, IsCurve v γ ∧ G.IsOfType p ty i γ ∧ tangent γ = u

def TypicalCurveBasisExists : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d),
      MuAction G p h ty →
        (∃ γ, IsBasis G p ty γ) ∧
        ∀ γ, IsBasis G p ty γ →
          (∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧
            (∀ a, constantCoeff (Ψ a) = 0) ∧
            (∀ a, subst Ψ (basisMap G γ a) = X a) ∧ (∀ a, subst (basisMap G γ) (Ψ a) = X a)) ∧
          ∀ b, subst (basisMap G γ) (G.lg b) =
            ∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) b)

def TypicalCurveTangentBasis : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d) γ,
      IsBasis G p ty γ → ∀ ga : Fin d → PowerSeries C, IsCurve v ga → G.IsPTypical p ga →
        ∃ x : ℕ → Fin d → C, (∀ s b, IsIntV v (x s b)) ∧ ∀ n,
          G.lc p ga n = ∑ s ∈ Finset.range (n + 1), ∑ b,
            (x s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)

def TypicalCurveStructureConstants : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d) γ,
      IsBasis G p ty γ →
        ∃ sc : ℕ → Fin d → Fin d → C, (∀ s b a, IsIntV v (sc s b a)) ∧
          (∀ s b a, sc s b a ≠ 0 → ty b = ty a + (s : ZMod h) + 1) ∧
          ∀ a n, (p : C) • G.lc p (γ a) (n + 1) = ∑ m ∈ Finset.range (n + 1), ∑ b,
            (sc (n - m) b a) ^ (p ^ m) • G.lc p (γ b) m

def TypicalCurveValuationBounds : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d) γ,
      IsBasis G p ty γ → ∀ a,
        (∀ (n : ℕ) c, (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ v (G.lc p (γ a) n c)) ∧
        (G.lc p (γ a) 1 = 0 → ∀ (n : ℕ) c, 1 ≤ n →
          (((1 - (n : ℝ)) : ℝ) : WithTop ℝ) ≤ v (G.lc p (γ a) n c))

def TypicalCurveRebasing : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d m : ℕ) (G : LogFGL v d) (γ : Fin m → Fin d → PowerSeries C)
      (x : Fin m → C), (∀ u, IsCurve v (γ u)) → (∀ u, IsIntV v (x u)) →
        let γ' := G.sumF fun u => rescaleCurve (x u) (γ u)
        IsCurve v γ' ∧ tangent γ' = ∑ u, x u • tangent (γ u) ∧
          (∀ n, G.lc p γ' n = ∑ u, (x u) ^ (p ^ n) • G.lc p (γ u) n) ∧
          ((∀ u, G.IsPTypical p (γ u)) → G.IsPTypical p γ')

theorem pt1 : CoprimeMultiplicationBijective := by
  intro C _ _ _ v p hp hvp d G n hn gb hgb
  exact nsmul_coprime_bijective_curves G hp hvp n hn gb hgb

end

end ReciprocityTheory.ChartRestriction.G.Sh
