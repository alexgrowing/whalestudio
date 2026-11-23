import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.RhoFam
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LocalErrorBoundPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

open NumberField IsDedekindDomain

def CommutingEndomorphismCondition (D : D7) : Prop :=
  ∀ i : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D →
    ∃ α : Module.End (D.nd.O i) (D.nd.Mt i),
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      (∀ x ∈ D.nd.Zgood i, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (KK D.nd i) u = ((D.what₂.restRowsFiniteGroupCard : ℤ) : KK D.nd i) • u) ∧
      (∀ x ∈ D.nd.Z i, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (KK D.nd i) u = 0)

def LocalisationUniqueness (D : D7) : Prop :=
  ∀ i i' : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' →
    ∀ σ, D.nd.goodRow σ → AtM D.nd D.naut i σ → AtM D.nd D.naut i' σ → i = i'

section Kill

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

abbrev psiW (C : NChoice D) (w : D.what₂.places.Pl) : GE D.nd →* (D.ntw.Ok (C.twI w) (C.k' w))ˣ :=
  (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)).comp (D.ntw.art (C.twI w) (C.Q w))

def SignatureChoiceCondition (C : NChoice D) : Prop :=
  ∀ i : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i →
    (∀ π ∈ D.nd.Zgood i, ∃ s : D.ntw.Sig (C.twI (D.nd.w i)),
      Formalism.MainNotions.BlochKatoReduction.Gen.goodS (Formalism.MainNotions.BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s ∧
      (Formalism.MainNotions.BlochKatoReduction.Gen.sLen (Formalism.MainNotions.BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s (C.k' (D.nd.w i)) (C.Q (D.nd.w i))
                (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt (D.ntw.side _ s) (psiW C (D.nd.w i))) ≠ ⊤ → Br.sFin D.loc D.nbr i (ρ i) π) ∧
      ENNReal.ofReal (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) ≤
        Formalism.MainNotions.BlochKatoReduction.Gen.sLen (Formalism.MainNotions.BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s (C.k' (D.nd.w i)) (C.Q (D.nd.w i))
          (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt (D.ntw.side _ s) (psiW C (D.nd.w i)))) ∧
    ((∑ v ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) ≤
      ∑ P ∈ C.Q (D.nd.w i), Formalism.MainNotions.BlochKatoReduction.Gen.tameVal (D.ntw.l (C.twI (D.nd.w i))) (psiW C (D.nd.w i)) (D.nd.plOm.1 P)

def KillAt : Prop :=
  ∀ i : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i →
    (∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i (ρ i) π ∧
      (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.nuL D (D.nd.l i) + Formalism.MainNotions.TwistedPlaces.epsL (D.nd.l i)) ∧
    (D.R.t : ℝ) * ((∑ v ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) ≤
        Formalism.MainNotions.TwistedPlaces.epsL (D.nd.l i)

end Kill

section Star

open Classical

variable {D : D7}
  (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

def localErrorBoundDecomposition (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (cB : ℕ) : ℚ :=
  (D.R.t : ℚ) * (∑ w ∈ dc.row, ((locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
    4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
    (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col

end Star

section Wit

open Classical

variable {D : D7}

def RangeAD (L : SizeData₂ D) (exc : Finset ℕ) (l : ℕ) : Prop :=
  ¬ (l ∈ D.host.small ∨ l = 3) ∧ ¬ (l = D.host.q ∨ l = D.host.d) ∧ ¬ (Formalism.MainNotions.TwistedPlaces.lStar L < (l : ℝ) ∧ l ∉ exc)

variable (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (C' A constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ)
    (lenR : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℝ) (BBR : D.nd.Loc → ℝ)
    (band : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → Prop) (exc : Finset ℕ) (gcost gs : ℕ → ℕ → ℝ)

end Wit

section Sup

open Classical

variable {D : D7}

def supZ (i : D.nd.Loc) (f : D.nd.X i → ℝ) : ℝ :=
  if h : (D.nd.Zgood i).Nonempty then (D.nd.Zgood i).sup' h f else 0

variable (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

def lenR (i : D.nd.Loc) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ := supZ i fun π => len0 i π lam

end Sup

section Asm

variable {D : D7}

structure HubData (D : D7) where
  r : FamilyRepresentationConstants.RFam D
  ρ : FamilyRepresentationConstants.RhoFam D
  len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ
  errorBoundHub : ∀ i : D.nd.Loc, D.nd.X i → ℝ
  dc : ∀ i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i
  lenRow : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℚ
  e' : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ
  cB : D.nd.Loc → ℕ
  eS : D.nd.Loc → ℕ
  c0 : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ
  band : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → Prop
  exc : Finset ℕ
  eta : ℕ
  I : TwIn D

structure HubK where
  C' : ℝ
  A : ℝ
  Ct0 : ℝ
  CV : ℝ
  constantFirstHub : ℝ
  Q : MvPolynomial (Fin 3) ℕ
  constantSecondHub : ℝ
  CT : ℕ
  C1 : ℝ
  C5 : ℝ

def StarAD (L : SizeData₂ D) (X : HubData D) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) → ∀ π ∈ D.nd.Zgood i,
    (D.nd.vcc i π : ℝ) ≤ (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) + Formalism.MainNotions.TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) +
      Formalism.MainNotions.TwistedPlaces.VVr D (D.nd.l i) + Formalism.MainNotions.TwistedPlaces.vhE D (D.nd.l i) + X.errorBoundHub i π + Formalism.MainNotions.TwistedPlaces.epsL (D.nd.l i)

def BBLe (L : SizeData₂ D) (X : HubData D) (C5 : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) → ∀ π ∈ D.nd.Zgood i,
    X.errorBoundHub i π ≤ C5 * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (Formalism.MainNotions.TwistedPlaces.large₂ L) ^ 2

def HubK.Le (K : HubK) (C : ℝ) : Prop :=
  0 ≤ K.constantSecondHub ∧ 0 ≤ K.C5 ∧ K.C5 ≤ C ∧ FamilyRepresentationConstants.CG K.constantFirstHub K.Q ≤ C ∧ FamilyRepresentationConstants.CF K.C' K.A K.CV K.C1 ≤ C ∧
    FamilyRepresentationConstants.CH K.constantSecondHub K.C1 ≤ C

end Asm

section Rows

open Classical

variable {D : D7}

structure RowK where
  C₂ : ℝ
  CB : ℝ
  CC : ℝ
  CA : ℝ
  CB' : ℝ
  CK : ℝ

def RowK.K₁ (R : RowK) : ℝ := R.CB + 48
def RowK.K₂ (R : RowK) : ℝ := 6 * R.CB + (12 + 6 * R.CC)
def RowK.K₃ (R : RowK) : ℝ := 3 * R.CA * R.CB + (12 * R.CA + 9)

def IsRowB (L : SizeData₂ D) (l : ℕ) : Prop := (l : ℝ) < Formalism.MainNotions.TwistedPlaces.lA L ∧ 4 * D.host.Lw < Formalism.MainNotions.TwistedPlaces.ordH D l

structure DataAD (L : SizeData₂ D) (HW : HWOf D.loc) (X : HubData D) (R : RowK) : Prop where
  col : ∀ i, Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) → (X.dc i).col = ∅
  rowB : ∀ i, Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) → IsRowB L (D.nd.l i) → X.lenRow i = lenRowB L R.C₂ (D.nd.l i)
  rowCD : ∀ i, Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) → ¬ IsRowB L (D.nd.l i) →
    X.lenRow i = lenRowCD L (X.band i) R.K₁ R.K₂ R.K₃ (D.nd.l i)
  len0I : ∀ i, Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) → ∀ π lam, X.len0 i π lam = (X.lenRow i lam : ℝ)
  error_bound_inert_eq : ∀ i, Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) → ∀ π, X.errorBoundHub i π = (localErrorBoundDecomposition i (X.dc i) (X.cB i) : ℝ)
  eS : ∀ i, Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → X.eS i = eA L R.CA (D.nd.l i)
  len0S : ∀ i, Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∀ π lam, X.len0 i π lam = (lenA i (X.dc i) (X.eS i) lam : ℝ)
  error_bound_split_eq : ∀ i, Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∀ π,
    X.errorBoundHub i π = (localErrorBoundPlaces i (X.ρ i) π (X.dc i) (X.c0 i) (X.cB i) : ℝ)
  band : ∀ i lam, X.band i lam ↔ bandOf L HW R.CB i (X.r i) (X.ρ i) lam

def RowK.Le (R : RowK) (C : ℝ) : Prop :=
  1 ≤ R.C₂ ∧ 0 ≤ R.CB ∧ 0 ≤ R.CC ∧ 0 ≤ R.CA ∧ 1 ≤ C ∧ 3 * R.C₂ + 1 ≤ C ∧ R.K₁ ≤ C ∧ R.K₂ + 1 ≤ C ∧ R.K₃ ≤ C ∧
    6 * R.CB + 1 ≤ C ∧ 2 * (3 * R.CA + 1) ≤ C

def JointParametersHubConditions (L : SizeData₂ D) (HW : HWOf D.loc) (X : HubData D) (R : RowK) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i,
    (IsRowB L (D.nd.l i) → LocalRepresentationBoundCondition L HW R.C₂ i (X.r i) (X.ρ i) π) ∧
    (¬ IsRowB L (D.nd.l i) → LocalRepresentationCongruenceCondition L HW i (X.r i) (X.ρ i) π)

structure StepAD (L : SizeData₂ D) (X : HubData D) : Prop where
  a09 : ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i,
      Formalism.MainNotions.TruncatedSeriesCountingIdentities.admitted i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i)
  a78 : ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∃ ep, Formalism.MainNotions.EmbeddingTypes.hypDecl i (X.dc i) ep ∧
      (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧
      ∀ π ∈ D.nd.Zgood i, Formalism.MainNotions.EmbeddingTypes.admitted i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i)

  goodR : ∀ i, GoodR D.nd i (X.r i)

def InvariantsBoundConditions (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    (X.cB i : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L ∧
    (h0 D.nd i (X.dc i).col : ℝ) ≤ c * D.R.t ∧
    (Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∀ u ∈ (X.dc i).col,
      (X.c0 i u : ℝ) ≤ c * D.R.r * Formalism.MainNotions.TwistedPlaces.large₂ L ∧
      ∀ π ∈ D.nd.Zgood i, (Br.h0W i u (X.ρ i) π : ℝ) ≤ c * (D.R.r : ℝ) ^ 2 * Formalism.MainNotions.TwistedPlaces.large₂ L)

end Rows

section CanonData

open Classical

variable {D : D7}

def ConstantColumnBound (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∀ u ∈ (X.dc i).col, (X.c0 i u : ℝ) ≤ c * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L

def InvariantsBoundsWithCoarseColumnConstant (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    (X.cB i : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L ∧
    (h0 D.nd i (X.dc i).col : ℝ) ≤ c * D.R.t ∧
    (Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∀ u ∈ (X.dc i).col,
      (X.c0 i u : ℝ) ≤ c * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L ∧
      ∀ π ∈ D.nd.Zgood i, (Br.h0W i u (X.ρ i) π : ℝ) ≤ c * D.R.r * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L)

def allRows (i : D.nd.Loc) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i where
  row := (FamilyRepresentationConstants.placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).toFinset
  col := ∅
  disj := Finset.disjoint_empty_right _
  cover v := by simp

def canon (L : SizeData₂ D) (HW : HWOf D.loc) (R : RowK) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (dcS : ∀ i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)
    (e' : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : D.nd.Loc → ℕ)
    (c0 : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : Finset ℕ) (eta : ℕ) (I : TwIn D) : HubData D where
  r := r
  ρ := ρ
  len0 i _ lam :=
    if Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) then
      (((if IsRowB L (D.nd.l i) then lenRowB L R.C₂ (D.nd.l i)
        else lenRowCD L (fun lam => bandOf L HW R.CB i (r i) (ρ i) lam) R.K₁ R.K₂ R.K₃ (D.nd.l i)) lam : ℚ) : ℝ)
    else (lenA i (if Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) then allRows i else dcS i) (eA L R.CA (D.nd.l i)) lam : ℝ)
  errorBoundHub i π :=
    if Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) then
      (localErrorBoundDecomposition i (if Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) then allRows i else dcS i) (cB i) : ℝ)
    else (localErrorBoundPlaces i (ρ i) π (if Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) then allRows i else dcS i) (c0 i) (cB i) : ℝ)
  dc i := if Formalism.MainNotions.TwistedPlaces.InertK D (D.nd.l i) then allRows i else dcS i
  lenRow i := if IsRowB L (D.nd.l i) then lenRowB L R.C₂ (D.nd.l i)
    else lenRowCD L (fun lam => bandOf L HW R.CB i (r i) (ρ i) lam) R.K₁ R.K₂ R.K₃ (D.nd.l i)
  e' := e'
  cB := cB
  eS i := eA L R.CA (D.nd.l i)
  c0 := c0
  band i lam := bandOf L HW R.CB i (r i) (ρ i) lam
  exc := exc
  eta := eta
  I := I

end CanonData

end Formalism.MainNotions.N.KillingConditions

end
