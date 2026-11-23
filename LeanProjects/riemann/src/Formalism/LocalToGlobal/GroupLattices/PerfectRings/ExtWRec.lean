import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWEx

noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions NumberField IsDedekindDomain

variable (D : D7)

theorem val_nonneg_iff (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hv : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    rw [D.val_eq w x hx, vAdd, ← WithTop.coe_zero, WithTop.coe_le_coe, neg_nonneg]
    conv_rhs => rw [← WithZero.exp_log hv]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]

theorem resChar_mem (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL)]
  suffices hs : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 by
    first | exact_mod_cast hs | simpa using hs
  have hp : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have hv : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hp
  have h1 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hp, vAdd] at h1
  have h2 : -WithZero.log ((D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) =
      ((D.what₂.places.ramIdx w : ℕ) : ℤ) := WithTop.coe_inj.1 h1
  have hpos := D.what₂.places.ramIdx_pos w
  rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

variable (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime] (n : ℕ)

def tauRec : D.what₂.LL →+* Om (D.what₂.places.resChar w) n :=
  tauAt (D.what₂.places.resChar w) n (D.plEq w) (resChar_mem D w)

abbrev KfRec : Type := Lt (tauRec D w n)

abbrev ORec : Type := Ot (tauRec D w n)

def embRec : D.what₂.LL →+* KfRec D w n := embL (tauRec D w n)

def extRec : ExtOf (OO (D.what₂.places.resChar w) n) (KO (D.what₂.places.resChar w) n) (ORec D w n) (KfRec D w n) :=
  extOt (tauRec D w n)

theorem embRec_int (x : D.what₂.LL) :
    (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
      embRec D w n x ∈ Set.range (algebraMap (ORec D w n) (KfRec D w n)) := by
  rw [val_nonneg_iff]
  exact induces_tauAt (D.plEq w) (resChar_mem D w) x

end Formalism.L2.G
