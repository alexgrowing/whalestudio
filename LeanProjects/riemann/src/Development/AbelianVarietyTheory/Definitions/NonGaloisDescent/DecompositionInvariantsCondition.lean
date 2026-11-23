import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.HubX

def epJ (D : D7) : Bool := if h : AdmissibleParameterJ.ConclusionJa D then Exists.choose h else true

theorem epJ_eq {D : D7} (h : AdmissibleParameterJ.ConclusionJa D) : epJ D = Exists.choose h := dif_pos h

def dcOf (D : D7) (i : D.nd.Loc) : TruncatedSeriesCountingIdentities.Decl D i :=
  if h : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) ∧ ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc (epJ D) then
    Exists.choose h.2 else KillingConditions.allRows i

variable {D : D7}

def cBof (L : SizeData₂ D) (i : D.nd.Loc) : ℕ :=
  GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV)

def hOf (L : SizeData₂ D) : ℕ := ⌊2 * L.sc.b⌋₊ + 1

def c0of (L : SizeData₂ D) (i : D.nd.Loc) (_u : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  5 + Nat.log (D.nd.l i) (2 * hOf L) + (4 * D.R.n * D.R.nV) * (4 + 2 * Nat.log (D.nd.l i) (2 * hOf L))

def ourX (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D)
    (e' : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : Finset ℕ) (I : TwIn D) : KillingConditions.HubData D :=
  KillingConditions.canon L HW R r ρ (dcOf D) e' (cBof L) (c0of L) exc ⌊L.etaSz⌋₊ I

structure Canon (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D) : Prop where
  fam : GlobalTheory.PtCore.PtFam D X.r X.ρ
  data : KillingConditions.DataAD L HW X R
  dc : ∀ i, ¬ TwistedPlaces.InertK D (D.nd.l i) → X.dc i = dcOf D i
  cB : X.cB = cBof L
  c0 : X.c0 = c0of L
  eta : X.eta = ⌊L.etaSz⌋₊

theorem canon_ourX (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D)
    (e' : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : Finset ℕ) (I : TwIn D)
    (h : GlobalTheory.PtCore.PtFam D r ρ) : Canon L HW R (ourX L HW R r ρ e' exc I) := by
  have hs : ∀ l, TwistedPlaces.SplitK D l → ¬ TwistedPlaces.InertK D l := by
    intro l h1 h2
    unfold TwistedPlaces.SplitK at h1
    unfold TwistedPlaces.InertK at h2
    rw [h1] at h2
    rcases h2 with h2 | h2 <;> cases h2
  refine ⟨h, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl, rfl, rfl⟩
  · intro i hi; simp only [ourX, KillingConditions.canon, if_pos hi]; rfl
  · intro i _ hb; simp only [ourX, KillingConditions.canon, if_pos hb]
  · intro i _ hb; simp only [ourX, KillingConditions.canon, if_neg hb]
  · intro i hi π lam; simp only [ourX, KillingConditions.canon, if_pos hi]
  · intro i hi π; simp only [ourX, KillingConditions.canon, if_pos hi]
  · intro i _; rfl
  · intro i hi π lam; simp only [ourX, KillingConditions.canon, if_neg (hs _ hi)]
  · intro i hi π; simp only [ourX, KillingConditions.canon, if_neg (hs _ hi)]
  · intro i lam; exact Iff.rfl
  · intro i hi; simp only [ourX, KillingConditions.canon, if_neg hi]

def CondCB (L : SizeData₂ D) (X : KillingConditions.HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) →
    (X.cB i : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L

section H0

variable (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (l : ℕ) [Fact l.Prime]
  (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)

def invariantsCountConstant (M0 h0 : ℕ) (T : LocLat (LocalSituation.sit LT HW l (AI l) K s LL h).G (LocalSituation.sit LT HW l (AI l) K s LL h).Qp
    (LocalSituation.sit LT HW l (AI l) K s LL h).LL (LocalSituation.sit LT HW l (AI l) K s LL h).O) : ℕ :=
  LocalSituation.cLL l (LocalSituation.mN l s (M0 + h0)) (padicValNat l ((LocalSituation.sit LT HW l (AI l) K s LL h).degKj (LocalSituation.mN l s (M0 + h0))) -
    padicValNat l (LocalSituation.sit LT HW l (AI l) K s LL h).degK) (LocalSituation.Jset (LocalSituation.sit LT HW l (AI l) K s LL h) T) 0 1

end H0

def wLat (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i))
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) :
    LocLat ↥(GK (D.nbr i u hu).Kw) ℚ_[D.nd.l i] (Br.LLw (D.nbr i u hu)) (Br.Ow (D.nbr i u hu)) :=
  { V := Fin D.R.r → Br.LLw (D.nbr i u hu)
    ρ := matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)))
    cont := hc
    L := Br.lat (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)) }

def JointCond_H0Wall (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) (X : Formalism.MainNotions.N.KillingConditions.HubData D) (M0 h0 : ℕ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) →
    ∀ u ∈ (X.dc i).col, ∀ π ∈ D.nd.Zgood i, ∃ (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
      (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
      (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i (X.ρ i) π).comp (decS D.nd u))) g v),
      IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i u hu).Kw) (wLat D i (X.ρ i) π u hu hc).ρ ∧
      (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s
        (D.nbr i u hu).LL hs) (wLat D i (X.ρ i) π u hu hc), -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      (∀ τ, ¬ IsJumpV ((D.loc (D.nd.l i)).PD (D.nbr i u hu).Kw) (wLat D i (X.ρ i) π u hu hc).ρ τ 0) ∧
        invariantsCountConstant D.loc HW D.locA (D.nd.l i) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs M0 h0
          (wLat D i (X.ρ i) π u hu hc) ≤ X.c0 i u

section T2

variable (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def tTwoLocalLattice {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) g v)
    (L2 : Lattice (O := ↥(OL C.LL)) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)))) :
    LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
  { V := Fin D.R.r → ↥C.LL.1, ρ := matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)), cont := hc, L := L2 }

def DecompositionInvariantsCondition (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (M0 h0 : ℕ) : Prop :=
  D.nd.l i ≠ 2 ∧ ∀ u ∈ dc.col, ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    IsConjPl D.host u w → (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
      ∀ (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hs : Good (D.nbr i w hw).Kw 1 C.LL)
      (hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) g v)
      (L2 : Lattice (O := ↥(OL C.LL)) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)))),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) ∧
      (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs)
        (tTwoLocalLattice D i ρ π C hc L2), -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      (∀ τ, ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) τ 0) ∧
      invariantsCountConstant D.loc HW D.locA (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hs M0 h0 (tTwoLocalLattice D i ρ π C hc L2) ≤ c0 u

end T2

def MuUnr (D : D7) : Prop :=
  ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ w ∈ placesOver D.host.E (D.nd.l i),
    D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)

def DepthZeroG (D : D7) : Prop :=
  ∀ i : D.nd.Loc, ∀ w ∈ D.nd.S i, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) →
    ∀ P : D.naut.AV i, ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w),
      D.naut.inePol (D.naut.locV i P w) σ = (Polynomial.X - 1) ^ D.R.nV

def LgcG (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ w ∈ D.nd.S i, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → ∀ x, ∃ P, D.naut.ptV i P = some x ∧
      D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w =
        D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)

end GlobalTheory.HubX

end
