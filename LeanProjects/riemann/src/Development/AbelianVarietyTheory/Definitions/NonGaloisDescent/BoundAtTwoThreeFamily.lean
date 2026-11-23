import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open Classical

namespace GlobalTheory.NLink

variable {D : D7}

def Bd (ρ : FamilyRepresentationConstants.RhoFam D) (i : D.nd.Loc) (π : D.nd.X i) (b : ℝ) : Prop :=
  (D.nd.vcc i π : ℝ) ≤ (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) + b + TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) +
    TwistedPlaces.epsL (D.nd.l i)

def StarE (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ) : Prop :=
  ∀ i, TwistedPlaces.TwLoc D i → TwistedPlaces.lStar L < (D.nd.l i : ℝ) → D.nd.l i ∉ TwistedPlaces.gset D → D.nd.l i ∉ exc →
    ∀ π ∈ D.nd.Zgood i, Bd ρ i π 0

def ExcOK (L : SizeData₂ D) (exc : Finset ℕ) : Prop :=
  (exc.card : ℝ) ≤ ((D.host.TT.card : ℝ) + 2) * (L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / TwistedPlaces.lStar L + 9) ∧
    ∀ l ∈ exc, (l : ℝ) ≤ 3 * L.sc.b

def StarF (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (C : ℝ) : Prop :=
  ∃ tf : TwistedPlaces.Tab L, TwistedPlaces.SmallPrimeLengthBound L tf C ∧ ∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) →
    ∀ π ∈ D.nd.Zgood i, Bd ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)

def midF (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * D.R.f * D.R.m * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * (TwistedPlaces.large₂ L) ^ 2

theorem midF_mono (L : SizeData₂ D) {C C' : ℝ} (h : C ≤ C') (h0 : 0 ≤ C') : midF L C ≤ midF L C' := by
  have hx : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hxp : 0 < L.sc.x := lt_of_lt_of_le one_pos hx
  have hCx : C * L.sc.x ^ C ≤ C' * L.sc.x ^ C' := by
    rcases le_or_gt 0 C with hC | hC
    · exact mul_le_mul h (Real.rpow_le_rpow_of_exponent_le hx h) (Real.rpow_nonneg hxp.le _) h0
    · have : C * L.sc.x ^ C ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC.le (Real.rpow_nonneg hxp.le _)
      exact this.trans (mul_nonneg h0 (Real.rpow_nonneg hxp.le _))
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hk : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x := by positivity
  have h1 := mul_le_mul_of_nonneg_right h hk
  have h2 := mul_le_mul_of_nonneg_right hCx (sq_nonneg (TwistedPlaces.large₂ L))
  unfold midF
  nlinarith

def BoundAtTwoThree (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (C : ℝ) : Prop :=
  ∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i = 2 ∨ (D.nd.l i = 3 ∧ D.nd.l i ∉ D.host.small)) → ∀ π ∈ D.nd.Zgood i, Bd ρ i π (midF L C)

def StarS (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (C : ℝ) : Prop :=
  ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∈ D.host.small → D.nd.l i ≠ 2 → ∀ π ∈ D.nd.Zgood i, Bd ρ i π (midF L C)

theorem starF_of (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (C : ℝ) (h23 : BoundAtTwoThree L ρ C) (hS : StarS L ρ C) : StarF L ρ C := by
  have h0 : ∀ l, TwistedPlaces.sumOver D l (fun _ => (0 : ℝ)) = 0 := fun l => by simp [TwistedPlaces.sumOver]
  refine ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ => midF L C, fun _ _ => False, ∅, fun _ _ => 0, fun _ _ => 0⟩, ?_, ?_⟩
  · intro i _ _
    show TwistedPlaces.sumOver D _ (fun _ => (0 : ℝ)) + midF L C ≤ midF L C
    rw [h0, zero_add]
  · intro i hi hl π hπ
    show Bd ρ i π (TwistedPlaces.sumOver D _ (fun _ => (0 : ℝ)) + midF L C)
    rw [h0, zero_add]
    by_cases h2 : D.nd.l i = 2
    · exact h23 i hi (Or.inl h2) π hπ
    · by_cases hs : D.nd.l i ∈ D.host.small
      · exact hS i hi hs h2 π hπ
      · exact h23 i hi (Or.inr ⟨hl.resolve_left hs, hs⟩) π hπ

def At23 (L : SizeData₂ D) (C : ℝ) : Prop :=
  TwistedPlaces.ShaFinOdd D → ∀ (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D), GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → BoundAtTwoThree L ρ C

def BoundAtTwoThreeFamily {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, At23 (Fm.L x i) C

def StarG (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (C : ℝ) : Prop :=
  ∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ π ∈ D.nd.Zgood i, Bd ρ i π (TwistedPlaces.midG L C (D.nd.l i))

def StarH (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ l ∈ TwistedPlaces.gset D,
    TwistedPlaces.etaAt L j l ≤ Real.log l * (L.dZ0 j : ℝ) *
      (C * L.sc.x ^ C * L.etaSz + TwistedPlaces.epsL l + TwistedPlaces.VVr D l + TwistedPlaces.vhE D l + TwistedPlaces.epsL l)

def MultLe (L : SizeData₂ D) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, TwistedPlaces.TwPl D w →
    (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤ (L.zeroSpaceRankAtPlace j w : ℝ)

def Small (L : SizeData₂ D) (C : ℝ) : Prop :=
  3 ≤ TwistedPlaces.lStar L ∧ (D.host.q : ℝ) ≤ TwistedPlaces.lStar L ∧ (D.host.d : ℝ) ≤ TwistedPlaces.lStar L ∧ ¬ TwistedPlaces.InertK D 3 ∧
    (∀ l, (l = D.host.q ∨ l = D.host.d) → TwistedPlaces.midG L C l ≤ 2 * C * D.R.f * D.R.m * L.sc.b) ∧
    ∀ l ∈ D.host.small, (l : ℝ) ≤ TwistedPlaces.lStar L

def tabX (L : SizeData₂ D) (X : KillingConditions.HubData D) : TwistedPlaces.Tab L where
  s i π := (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ)
  len := KillingConditions.lenR X.len0
  BB i := KillingConditions.supZ i (X.errorBoundHub i)
  band := X.band
  exc := X.exc
  gcost _ _ := 0
  gs _ l := TwistedPlaces.epsL l

def tab (L : SizeData₂ D) (X : KillingConditions.HubData D) (tf : TwistedPlaces.Tab L) (C : ℝ) : TwistedPlaces.Tab L where
  s i π := (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ)
  len i lam :=
    if D.nd.l i ∈ D.host.small then 0
    else if D.nd.l i = 3 then (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ)
    else if KillingConditions.RangeAD L X.exc (D.nd.l i) then KillingConditions.lenR X.len0 i lam else 0
  BB i :=
    if D.nd.l i ∈ D.host.small then TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i
    else if D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d then TwistedPlaces.midG L C (D.nd.l i)
    else if KillingConditions.RangeAD L X.exc (D.nd.l i) then KillingConditions.supZ i (X.errorBoundHub i) else 0
  band := X.band
  exc := X.exc
  gcost _ _ := C * L.sc.x ^ C * L.etaSz
  gs _ l := TwistedPlaces.epsL l

def RowNum (L : SizeData₂ D) (X : KillingConditions.HubData D) (C : ℝ) : Prop :=
  TwistedPlaces.admA L (tabX L X) C ∧ TwistedPlaces.admB L (tabX L X) C ∧ TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C ∧
    TwistedPlaces.BandPlaceWeightApproximation L (tabX L X) C

structure Concl (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) : Prop where
  pos : 0 ≤ C
  pass : TwistedPlaces.adm1 D
  mult : MultLe L
  rank : TwistedPlaces.adm3 L
  kill : KillingConditions.KillAt X.ρ
  num : RowNum L X C
  mid : KillingConditions.StarAD L X
  bb : KillingConditions.BBLe L X C
  large : StarE L X.ρ X.exc
  exc : ExcOK L X.exc
  two : StarF L X.ρ C
  ram : StarG L X.ρ C
  typ : StarH L C
  par : TwistedPlaces.ParametersPolynomiallyBounded L C P
  small : Small L C

def ConclF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) →
    ∃ X : KillingConditions.HubData (Fm.D x i), Concl (Fm.L x i) (Fm.params x hx i) X C

end GlobalTheory.NLink

end
