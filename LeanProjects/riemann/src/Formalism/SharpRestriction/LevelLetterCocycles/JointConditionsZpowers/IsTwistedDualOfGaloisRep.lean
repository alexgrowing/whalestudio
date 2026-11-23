import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

variable {D : D7}

section Glue

variable (L : SizeData₂ D) (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

def HLen : Prop :=
  ∀ i lam, D.nd.l i ≠ 2 → D.nd.l i ≠ 3 →
    ((∃ π ∈ D.nd.Zgood i, tb.len i lam = len0 i π lam) ∨ tb.len i lam = 0)

def coreB (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  ((Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) +
    (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L)

end Glue

section Row

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)

abbrev LatW : Type 1 := LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥Cx.LL.1 ↥(OL Cx.LL)

def IsTwistedDualOfGaloisRep (T₂ : LatW i w hw Cx) : Prop :=
  IsMatLat (ρ := T₂.ρ) T₂.L.T ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π))

def IsSubOfTwistedDualSums (T₁ : LatW i w hw Cx) : Prop :=
  IsSubOfSums T₁.ρ (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)))

def RowL (x : ℝ) : Prop :=
  ∀ (T₁ T₂ : LatW i w hw Cx) (F : LatHom T₁.L T₂.L), IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ → IsSubOfTwistedDualSums i r w hw Cx T₁ →
    F.Onto → Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR (Br.PD D.loc D.nbr i w hw) F x

abbrev nLet : ℕ := finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)

theorem nLet_neZero : NeZero (nLet i w hw) := by
  have := (D.nbr i w hw).Kw.2
  have h0 : K0 (D.nbr i w hw).Kw ≤ (D.nbr i w hw).Kw.1 := inf_le_left
  have : FiniteDimensional ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) :=
    Module.Finite.of_injective (IntermediateField.inclusion h0).toLinearMap
      (IntermediateField.inclusion h0).injective
  exact ⟨(finrank_pos).ne'⟩

end Row

structure WordDat (n : ℕ) where
  b : ℕ
  w : ℕ
  S : ℕ
  η : ℕ
  m : ℕ
  up : ZMod n → Bool
  sz : ZMod n → ℕ
  Mi : ZMod n → ℕ
  hi : ZMod n → ℕ

def WordDat.win {n : ℕ} (Wd : WordDat n) (a : ZMod n) : Set ℤ :=
  if Wd.up a then Set.Icc (Wd.sz a : ℤ) ((Wd.sz a : ℤ) + Wd.S) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η
  else Set.Icc (-(Wd.sz a : ℤ) - Wd.S) (-(Wd.sz a : ℤ)) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η

section Word

variable (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL)

abbrev WW := (HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG

structure WordBase (Wd : WordDat (nLet i w hw)) : Prop where
  unram : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i)
  deg : Br.DegW D.nbr i w hw
  split : ∀ _ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    Splits (K := ↥(D.nbr i w hw).Kw.1) (Qp := ℚ_[D.nd.l i]) ↥Cx.LL.1
  dvr : ∃ hO : IsDomain ↥(OL Cx.LL), @IsDiscreteValuationRing ↥(OL Cx.LL) _ hO ∧
    IsFractionRing ↥(OL Cx.LL) ↥Cx.LL.1
  t1 : ∀ T₁ : LatW i w hw Cx, IsSubOfTwistedDualSums i r w hw Cx T₁ →
    IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₁.ρ ∧
    (∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt (WW HW i w hw Cx hG) T₁ a (Wd.win a)) ∧
    Formalism.MainNotions.LiftingTheory.JumpsLet (WW HW i w hw Cx hG) T₁ Wd.Mi Wd.hi
  t2 : ∀ T₂ : LatW i w hw Cx, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ →
    IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ ∧
    ∀ (_ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1)) (a : ZMod (nLet i w hw)),
      Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount (WW HW i w hw Cx hG) T₂ a Wd.η ≤ Wd.m
  thick_or : ∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a ∨ Wd.sz a ≤ Wd.w
  h_le : (Wd.b : ℝ) + Wd.η + Wd.S ≤ Formalism.MainNotions.TwistedPlaces.hB L
  w_le : (Wd.w : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.wP L
  S_le : (Wd.S : ℝ) ≤ L.Sc
  η_le : (Wd.η : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eta₃ L
  m_eq : Wd.m = D.R.m

variable {L HW i r ρ π w hw Cx hG}

structure WordsB (L : SizeData₂ D) (C₂ : ℝ) (l : ℕ) {n : ℕ} (Wd : WordDat n) : Prop where
  j_lt : Formalism.MainNotions.TwistedPlaces.jA L l + 1 ≤ n
  par : C₂ * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) * (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) ≤ Wd.b
  clusters : Formalism.MainNotions.TruncatedSeriesCountingBounds.Clusters (Formalism.MainNotions.TwistedPlaces.jA L l) (Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz)

end Word

def ratIn (x y : ℝ) : ℚ := if h : x < y then (exists_rat_btwn h).choose else 0

section RowB

variable (L : SizeData₂ D)

def lenRowB (C₂ : ℝ) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  ratIn (3 * C₂ * coreB L l lam) ((3 * C₂ + 1) * coreB L l lam)

def LocalRepresentationBoundCondition (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL),
      ∃ Wd : WordDat (nLet i w hw), WordBase L HW i r ρ π w hw Cx hG Wd ∧ WordsB L C₂ (D.nd.l i) Wd

end RowB

end Formalism.MainNotions.N

end
