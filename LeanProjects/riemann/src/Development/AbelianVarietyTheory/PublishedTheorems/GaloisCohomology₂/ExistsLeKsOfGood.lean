import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Cyc

namespace GlobalTheory.Published

def FontaineEtale : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), GlobalTheory.Per.IsStd P AI →
    ∀ (K : FinExt l) (s : ℕ) (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l), IsIo (AI.εroot s) io →
      (∀ (LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
        ∃ (n : ℕ) (d : Fin n → TW (RW LL) T),
          (∀ i, d i ∈ FonD AI K LL io T) ∧
          (∀ z ∈ FonD AI K LL io T, ∃ w : Fin n → WCb l,
            (∀ i, w i ∈ Eur io ∧ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.actWCbHom (g : GQ l) (w i) = w i) ∧
            z = ∑ i, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w i : RW LL) • d i) ∧
          (∀ z ∈ EurT LL io T, ∃ w : Fin n → WCb l, (∀ i, w i ∈ Eur io) ∧
            z = ∑ i, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w i : RW LL) • d i) ∧
          Function.Bijective fun w : Fin n → WCb l =>
            ∑ i, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w i : RW LL) • d i) ∧
      ((∃ m : ℕ, K.1 ≤ Ks K m) → ∀ x : WCb l,
        (x ∈ Eur io ∧ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.actWCbHom (g : GQ l) x = x) ↔
          ∃ (n : ℕ) (a : Fin n → WCb l) (xb : Fin n → OCb l), (∀ i, a i ∈ E0 io) ∧
            (∀ i, ∃ (c : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ (c : Om l) ^ m = 1 ∧
              IsTiltOf (c : Om l) m (xb i)) ∧
            x = ∑ i, a i * inclW l (WittVector.teichmuller l (xb i)))

end GlobalTheory.Published
