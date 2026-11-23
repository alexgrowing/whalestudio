import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.PZ

variable {l : ℕ} [Fact l.Prime]

def resCard (K : FinExt l) : ℕ := l ^ Module.finrank ℚ_[l] ↥(K0 K)

def ltSeries (K : FinExt l) (π : ↥(OL K)) : PowerSeries ↥(OL K) :=
  PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ resCard K

def IsLTEndo (K : FinExt l) (π a : ↥(OL K)) (φ : PowerSeries ↥(OL K)) : Prop :=
  PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
    PowerSeries.C π * φ + φ ^ resCard K = PowerSeries.subst (ltSeries K π) φ

def LTData (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l) : Prop :=
  Irreducible π ∧ z 0 = 0 ∧ z 1 ≠ 0 ∧
    (∀ n, ((π : ↥K.1) : Om l) * z (n + 1) + z (n + 1) ^ resCard K = z n) ∧
    ∀ g : ↥(GK K), ∃ a : ↥(OL K), ((a : ↥K.1) = (χ g : ↥K.1)) ∧
      ∃ φ : PowerSeries ↥(OL K), IsLTEndo K π a φ ∧ ∀ n,
        HasSum (fun k => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k) ((g : GQ l) (z n))

def lineRep {K : FinExt l} {LL : FinExt l} (χ : ↥(GK K) →* (↥LL.1)ˣ) :
    Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) where
  toFun g := ((χ g : (↥LL.1)ˣ) : ↥LL.1) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp; ring

end GlobalTheory.PZ

end
