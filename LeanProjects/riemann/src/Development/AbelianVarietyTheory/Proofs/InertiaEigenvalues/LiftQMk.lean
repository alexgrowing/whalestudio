import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UseLoc

section Gen
variable {l : ℕ} [Fact l.Prime]

def incO {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥(OL LL) →+* ↥(OL LL') where
  toFun x := ⟨IntermediateField.inclusion h x, by
    have := x.2
    exact IsIntegral.map ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) this⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def incV {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) : (Fin k → ↥LL.1) →+ (Fin k → ↥LL'.1) :=
  (AddMonoidHom.compLeft (IntermediateField.inclusion h).toRingHom.toAddMonoidHom (Fin k))

def liftQ {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) :
    (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k →+ (Fin k → ↥LL'.1) ⧸ stdG ↥(OL LL') ↥LL'.1 k :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' (stdG ↥(OL LL') ↥LL'.1 k).toAddSubgroup).comp (incV h k)) (by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨fun j => incO h (u j), rfl⟩)

theorem liftQ_mk {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) (v : Fin k → ↥LL.1) :
    liftQ h k (Submodule.Quotient.mk v) = Submodule.Quotient.mk (incV h k v) := rfl

end Gen
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

def locOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL) :=
  mapM (incO C.le) (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)))

def chiOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  (Units.map ((incO C.le).comp (D.nbr i w hw).eO.toRingHom).toMonoidHom).comp
    ((χ.comp (decS D.nd w)).comp (Br.iota D.nbr i w hw))

abbrev repV (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Representation ↥C.LL.1 (Br.G D.nbr i w hw) (Fin k → ↥C.LL.1) :=
  matRep (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) N)

def latC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Lattice (O := ↥(OL C.LL)) (repV C N) :=
  stdLatG Subtype.val_injective N

def chiT (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) :
    Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) * θ

def embC (HW : HWOf D.loc) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) :=
  ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hA.2.2).emb

end AtW
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

open Module in

def SetC (HW : HWOf D.loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
    (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
    (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ) : Prop :=
  tableLineDegreeTwo.TopHyp (Br.PD D.loc D.nbr i w hw) (embC HW C hA) D.R.t h w' η typ U
                     (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) ∧
    ∀ x, tableLineDegreeTwo.IsFull (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t)
      (repV C (twistM (locOC C (rTwO D.nd i r x)) θ))

end AtW
end GlobalTheory.UseLoc
