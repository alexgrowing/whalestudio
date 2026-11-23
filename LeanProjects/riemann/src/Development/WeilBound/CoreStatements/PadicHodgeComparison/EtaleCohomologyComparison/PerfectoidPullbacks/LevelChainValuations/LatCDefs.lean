import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ToBSurj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
import GroundTheory.PAdicHodge.UntiltFrobeniusEquivSymmEpsilonNeOne
import GroundTheory.PAdicHodge.BdRAlgCl
import GroundTheory.PAdicHodge.BdRGalois
import GroundTheory.PAdicHodge.BdRField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.Pb.Lat

variable (l : ℕ) [Fact l.Prime]

abbrev Bk (k : ℕ) : Type := BdRp l ⧸ Ideal.span {tBdR l ^ k}

def fk (k : ℕ) : Ainf l →+* Bk l k := (Ideal.Quotient.mk _).comp (wittToBDeRhamPlus (normInteger ℂ_[l]) l)

def dk (k : ℕ) : Bk l (k + 1) →+* Bk l k :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ k)))

def pk (k : ℕ) : BdRp l →+* Bk l k := Ideal.Quotient.mk _

def pInv : ↥(algebraMap (BdRp l) (BdR l)).range →+* BdRp l :=
  (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm.toRingHom

def kP (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : K →+* BdRp l := (algClToBdR l).toRingHom.comp K.val.toRingHom

def gP {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (g : K.fixingSubgroup) : BdRp l →+* BdRp l := galBdRHom (toBot g.1)

structure LevHyp (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : ℕ) : Prop where
  ok : ∀ (k : ℕ) (a : OK l K), pk l k (kP l K a) ∈ sub (fk l k) (xi0 l) l M
  cris : ∀ (k : ℕ) (c : Acris l), pk l k (ACris.iota ℂ_[l] l c) ∈ sub (fk l k) (xi0 l) l M
  hc : ∀ k : ℕ, DPClosed (ι (fk l k) (xi0 l) l M) (γB (fk l k) (xi0 l))
  galT : ∀ (k : ℕ) (g : K.fixingSubgroup), Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (gP l g)
  gal : ∀ (k : ℕ) (g : K.fixingSubgroup), ∀ x ∈ sub (fk l k) (xi0 l) l M,
    Ideal.quotientMap _ (gP l g) (galT k g) x ∈ sub (fk l k) (xi0 l) l M
  dIn : ∀ k : ℕ, ∀ x ∈ sub (fk l (k + 1)) (xi0 l) l M, dk l k x ∈ sub (fk l k) (xi0 l) l M

variable {l} {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

def okA (h : LevHyp l K M) (k : ℕ) : OK l K →+* A (fk l k) (xi0 l) l M :=
  ((pk l k).comp ((kP l K).comp (OK l K).subtype)).codRestrict (sub (fk l k) (xi0 l) l M) (h.ok k)

def lamA (h : LevHyp l K M) (k : ℕ) : Acris l →+* A (fk l k) (xi0 l) l M :=
  ((pk l k).comp (ACris.iota ℂ_[l] l)).codRestrict (sub (fk l k) (xi0 l) l M) (h.cris k)

def gB (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) : Bk l k →+* Bk l k :=
  Ideal.quotientMap _ (gP l g) (h.galT k g)

def lev (h : LevHyp l K M) (k : ℕ) : Kap.Lev (per l K) k where
  B := Bk l k
  balg := ((pk l k).comp (kP l K)).toAlgebra
  toB := (pk l k).comp (pInv l)
  IB := IB (fk l k) (xi0 l)
  γB := γB (fk l k) (xi0 l)
  A := A (fk l k) (xi0 l) l M
  aalg := (okA h k).toAlgebra
  I := I (fk l k) (xi0 l) l M
  γ := γ (fk l k) (xi0 l) l M (h.hc k)
  ι := ι (fk l k) (xi0 l) l M
  lam := lamA h k
  σA g := map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g)
  σB g := gB h k g

def levSys (h : LevHyp l K M) : Kap.LevSys (per l K) where
  L m := lev h (m + 1)
  dA m := map (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1)) (h.dIn (m + 1))
  dB m := dk l (m + 1)

end CrystallineSemistableComparison.Pb.Lat
