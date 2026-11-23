import Formalism.MahlerMeasure.IsFrozenInv

namespace Formalism.GM.M

open MvPolynomial Finset

def HasOrder {σ : Type} {p : ℕ} [Fact p.Prime] (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) : Prop :=
  (∀ m ∈ f.support, e ≤ m v) ∧ ∃ m ∈ f.support, m v = e

noncomputable def initPart {σ : Type} {p : ℕ} [Fact p.Prime] (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) :
    MvPolynomial σ ℚ_[p] :=
  ∑ m ∈ f.support, if m v = e then monomial m (f.coeff m) else 0

noncomputable def tieGam (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) : ℚ_[p] :=
  (((LL.deg (Fin.last N) + n + r + z - 1).choose (LL.deg (Fin.last N)) : ℕ) : ℚ_[p]) *
    fock p (tiePhiAt p (LL.snoc n) (Fin.castSucc (Fin.last N)) (Fin.last (N + 1)) z (freeze p LL ρ n f))
      (freeze p LL ρ n f') /
    ((((n - LL.total).factorial * LL.total.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p]))

def GamDeg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z e e' : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ Pol p r LL → f' ∈ Pol p r LL →
    HasOrder (Fin.last N, ρ) e f → HasOrder (Fin.last N, ρ) e' f' →
    ∃ P : Polynomial ℚ_[p], P.natDegree ≤ LL.total + LL.deg (Fin.last N) - max e e' ∧
      ∀ n, LL.total ≤ n → tieGam p LL ρ z n f f' = P.eval (n : ℚ_[p])

def GamLead : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z e : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (P : Polynomial ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ Pol p r LL → f' ∈ Pol p r LL →
    HasOrder (Fin.last N, ρ) e f → HasOrder (Fin.last N, ρ) e f' →
    (∀ n, LL.total ≤ n → tieGam p LL ρ z n f f' = P.eval (n : ℚ_[p])) →
    P.coeff (LL.total + LL.deg (Fin.last N) - e) =
      ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) *
        fock p (initPart (Fin.last N, ρ) e f) (initPart (Fin.last N, ρ) e f') /
        ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℚ_[p]) *
          ∏ i, ((LL.deg i).factorial : ℚ_[p]))

end Formalism.GM.M
