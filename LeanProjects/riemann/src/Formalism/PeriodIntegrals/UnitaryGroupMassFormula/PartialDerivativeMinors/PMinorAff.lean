import Mathlib
import Formalism.PeriodIntegrals.EntAtD

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

abbrev ZV (H : Type) (N0 N1 : ℕ) : Type := (Bool × H) × Fin N0 × Fin N1

abbrev XV (H : Type) (N0 : ℕ) : Type := (Bool × H) × ℕ × Fin N0

abbrev PolyXZ (H : Type) (N0 N1 : ℕ) : Type := MvPolynomial (XZ (Bool × H) N0 N1) ℤ

def ShapeH (H : Type) [Fintype H] (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ}
    (Th : MvPowerSeries (ZV H N0 N1) ℂ_[p]) : Prop :=
  ∃ S : ℂ_[p], ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) ∧ ∃ ut : H → ℂ_[p], (∀ t, ‖ut t‖ ≤ 1) ∧
    ∃ sg' : MvPowerSeries (ZV H N0 N1) ℂ_[p],
      (∀ m, ‖(m.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff m sg'‖ ≤ 1) ∧
      Th = expS ℂ_[p] (-(S • ∑ t : H, ut t • ∑ a : Fin N0, ∑ b : Fin N1,
        (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
          MvPowerSeries (ZV H N0 N1) ℂ_[p]))) * sg'

def cPr (α β : YoungDiagram) : ℕ := (α.cells.card - α.rowLen 0) + min (α.rowLen 0) (β.rowLen 0)

def CoreBound : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 p : ℕ) [Fact p.Prime] (nu : Bool × H → YoungDiagram)
    (Th : MvPowerSeries (ZV H N0 N1) ℂ_[p]),
    ShapeH H p Th → KvalGe N0 N1 p nu Th (-((∑ t : H, (cPr (nu (false, t)) (nu (true, t)) : ℝ)) / 2))

abbrev xpart {H : Type} {N0 N1 : ℕ} (μ : XZ (Bool × H) N0 N1 →₀ ℕ) : XV H N0 →₀ ℕ :=
  (Finsupp.sumFinsuppEquivProdFinsupp μ).1

abbrev zpart {H : Type} {N0 N1 : ℕ} (μ : XZ (Bool × H) N0 N1 →₀ ℕ) : ZV H N0 N1 →₀ ℕ :=
  (Finsupp.sumFinsuppEquivProdFinsupp μ).2

def Bal {H : Type} [Fintype H] (N0 N1 : ℕ) (n : H → ℕ) (κ : ZV H N0 N1 →₀ ℕ) : Prop :=
  (∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b)) ∧
    ∀ t, ∑ a : Fin N0, ∑ b : Fin N1, κ ((true, t), a, b) = n t

def binomF {H : Type} {N0 N1 : ℕ} (κ κ' : ZV H N0 N1 →₀ ℕ) : ℕ :=
  ∏ v ∈ κ.support, (κ v).choose (κ' v)

def Acon {H : Type} [Fintype H] {N0 N1 : ℕ} (P : PolyXZ H N0 N1) (m : XV H N0 →₀ ℕ)
    (κ2 : ZV H N0 N1 →₀ ℕ) (n : H → ℕ) : ℤ :=
  ∑ μ ∈ P.support,
    if xpart μ = m ∧ κ2 ≤ zpart μ ∧ Bal N0 N1 n (zpart μ - κ2) then
      MvPolynomial.coeff μ P * (binomF (zpart μ) κ2 : ℤ) *
        ∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1, (((zpart μ - κ2) ((true, t), a, b)).factorial : ℤ)
    else 0

def PExpand : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 p : ℕ) [Fact p.Prime] (S : ℂ_[p]) (ut : H → ℂ_[p])
    (sg : MvPowerSeries (ZV H N0 N1) ℂ_[p]) (P : PolyXZ H N0 N1) (m : XV H N0 →₀ ℕ),
    MvPolynomial.coeff m (applyAt0 N0 N1 p (expS ℂ_[p] (-(S • ∑ t : H, ut t • ∑ a : Fin N0, ∑ b : Fin N1,
        (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
          MvPowerSeries (ZV H N0 N1) ℂ_[p]))) * sg) P) =
      ∑ κ2 ∈ P.support.biUnion (fun μ => Finset.Iic (zpart μ)),
        ∑ n ∈ Fintype.piFinset (fun _ : H => Finset.range (P.totalDegree + 1)),
          ((κ2.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ2 sg) *
            (∏ t : H, (-(S * ut t)) ^ n t) * ((Acon P m κ2 n : ℤ) : ℂ_[p])

def PVanish : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (nu : Bool × H → YoungDiagram) (I : ColChoice N1 nu)
    (m : XV H N0 →₀ ℕ) (κ2 : ZV H N0 N1 →₀ ℕ) (n : H → ℕ) (t : H),
    cPr (nu (false, t)) (nu (true, t)) < n t → Acon (Gxz N0 N1 nu I) m κ2 n = 0

def pd {H : Type} {N0 N1 : ℕ} (v : XZ (Bool × H) N0 N1) : Module.End ℤ (PolyXZ H N0 N1) :=
  (MvPolynomial.pderiv (R := ℤ) v).toLinearMap

def lapT {H : Type} (N0 N1 : ℕ) (t : H) : Module.End ℤ (PolyXZ H N0 N1) :=
  ∑ a : Fin N0, ∑ b : Fin N1,
    pd (H := H) (N0 := N0) (N1 := N1) (Sum.inr ((false, t), a, b)) * pd (Sum.inr ((true, t), a, b))

def lapAll {H : Type} [Fintype H] (N0 N1 : ℕ) (n : H → ℕ) : Module.End ℤ (PolyXZ H N0 N1) :=
  ((Finset.univ : Finset H).toList.map fun t => lapT N0 N1 t ^ n t).prod

def PBridge : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (P : PolyXZ H N0 N1) (m : XV H N0 →₀ ℕ)
    (κ2 : ZV H N0 N1 →₀ ℕ) (n : H → ℕ),
    (∏ t : H, ((n t).factorial : ℤ)) * Acon P m κ2 n =
      MvPolynomial.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (m, κ2)) (lapAll N0 N1 n P)

def PLapComm : Prop :=
  ∀ (H : Type) (N0 N1 : ℕ) (t t' : H), Commute (lapT (H := H) N0 N1 t) (lapT N0 N1 t')

def PLapZero : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (nu : Bool × H → YoungDiagram) (I : ColChoice N1 nu)
    (t : H) (n : ℕ), cPr (nu (false, t)) (nu (true, t)) < n → (lapT N0 N1 t ^ n) (Gxz N0 N1 nu I) = 0

def dRow {H : Type} {N0 N1 : ℕ} (t : H) (r : ℕ) (b : Fin N1) :
    Derivation ℤ (PolyXZ H N0 N1) (PolyXZ H N0 N1) :=
  ∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((false, t), r, a)) : PolyXZ H N0 N1) •
    MvPolynomial.pderiv (R := ℤ) (Sum.inr ((true, t), a, b))

def PMinorAff : Prop :=
  ∀ (H : Type) (N0 N1 : ℕ) (t : H) (k : ℕ) (I : Fin k ↪o Fin N1) (b b' : Fin N1),
    dRow (N0 := N0) t 0 b (dRow (N0 := N0) t 0 b' (minorXZ (Lt := Bool × H) N0 N1 (true, t) k I)) = 0

def SDegD {A : Type} [CommRing A] {ι : Type} (d : ι → Derivation ℤ A A) : ℕ → A → Prop
  | 0, h => ∀ j, d j h = 0
  | k + 1, h => ∀ j, SDegD d k (d j h)

def PSDegMul : Prop :=
  ∀ (A : Type) [CommRing A] (ι : Type) (d : ι → Derivation ℤ A A) (f g : A) (k l : ℕ),
    SDegD d k f → SDegD d l g → SDegD d (k + l) (f * g)

def PLapForms : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (α : YoungDiagram)
    (I : ∀ c : Fin (α.rowLen 0), Fin (α.colLen c) ↪o Fin N1) (t : H) (g : PolyXZ H N0 N1) (d n : ℕ),
    (∀ (a : Fin N0) (b : Fin N1), pd (Sum.inr ((false, t), a, b)) g = 0) →
    SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) d g →
    (α.cells.card - α.rowLen 0) + min (α.rowLen 0) d < n →
    (lapT N0 N1 t ^ n) ((∏ c : Fin (α.rowLen 0),
      minorXZ (Lt := Bool × H) N0 N1 (false, t) (α.colLen c) (I c)) * g) = 0

def PExpCoeff : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 p : ℕ) [Fact p.Prime] (S : ℂ_[p]) (ut : H → ℂ_[p])
    (κ : ZV H N0 N1 →₀ ℕ),
    (κ.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff κ (expS ℂ_[p] (-(S • ∑ t : H, ut t •
        ∑ a : Fin N0, ∑ b : Fin N1, (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
          MvPowerSeries (ZV H N0 N1) ℂ_[p])))) =
      if ∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b) then
        ∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          ((κ ((true, t), a, b)).factorial : ℂ_[p]) * (-(S * ut t)) ^ κ ((true, t), a, b)
      else 0

end PI.EntAtD.W
