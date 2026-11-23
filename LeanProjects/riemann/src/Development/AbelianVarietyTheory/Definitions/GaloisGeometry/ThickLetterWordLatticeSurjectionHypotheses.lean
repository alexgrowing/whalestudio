import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN

noncomputable section

namespace GlobalTheory.HTW.RecS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.HTW.Rec

variable {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL)

abbrev nLet : ℕ := Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)

abbrev WW : Wach (D.loc (D.nd.l i)) (D.nbr i w hw).Kw Cx.LL := (HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG

def IsSubOfTwistedDualSums (T : Lat (D.nbr i w hw).Kw Cx.LL) : Prop :=
  IsSubOfSums T.ρ fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x))

def IsTwistedDualOfGaloisRep (T : Lat (D.nbr i w hw).Kw Cx.LL) : Prop := IsMatRep T (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π))

variable (Wd : NWord (nLet i w hw))

structure WordBase : Prop where
  unram : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i)
  deg : Br.DegW D.nbr i w hw
  split : ∀ _ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    Splits (Qp := ℚ_[D.nd.l i]) (K := ↥(D.nbr i w hw).Kw.1) ↥Cx.LL.1
  t1 : ∀ T₁, IsSubOfTwistedDualSums i r w hw Cx T₁ → IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₁.ρ ∧
    (∀ a, TruncatedSeriesCountingBounds.JumpsAt (WW HW i w hw Cx hG) T₁ a (Wd.win a)) ∧ LiftingTheory.JumpsLet (WW HW i w hw Cx hG) T₁ Wd.Mi Wd.hi
  t2 : ∀ T₂, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ → IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ ∧
    ∀ (_ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1)) (a),
      TruncatedSeriesCountingBounds.lowCount (WW HW i w hw Cx hG) T₂ a Wd.η ≤ (Wd.m : ℤ)
  t2win : ∀ T₂, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ →
    (∀ a, TruncatedSeriesCountingBounds.JumpsAt (WW HW i w hw Cx hG) T₂ a (Wd.win a)) ∧ LiftingTheory.JumpsLet (WW HW i w hw Cx hG) T₂ Wd.Mi Wd.hi
  num : WordNum L Wd
  small : Small Wd ∧ 1 ≤ Wd.S ∧ 1 ≤ Wd.η

def ThickLetterWordLatticeSurjectionHypotheses : Prop :=
  ∀ (_ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1)) T₁ T₂ (F : LatHom T₁.L T₂.L),
    IsSubOfTwistedDualSums i r w hw Cx T₁ → IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ → F.Onto →
      TruncatedSeriesCountingBounds.HidaSetting ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) (WW HW i w hw Cx hG) T₁ T₂ F
        Wd.b Wd.w Wd.S Wd.η Wd.m Wd.up Wd.sz Wd.Mi Wd.hi

def AlternatingWordLatticeSurjectionHypotheses (d : ℕ) : Prop :=
  ∀ (_nz : NeZero (nLet i w hw)) T₁ T₂ (F : LatHom T₁.L T₂.L),
    IsSubOfTwistedDualSums i r w hw Cx T₁ → IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ → F.Onto →
      RamifiedCoefficientChains.SetCS (WW HW i w hw Cx hG) d T₁ T₂ F Wd.sz Wd.S Wd.η Wd.m

structure PtIn : Prop where
  good : GoodR D.nd i r
  cont : TruncatedSeriesCountingIdentities.FamilyContinuous i r
  mem : π ∈ D.nd.Z i
  dec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π
  contρ : Continuous fun g => rhoO D.nd i ρ π g
  crys : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) x,
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)))

def JointB (C₂ : ℝ) : Prop :=
  ∀ i, InertUnr D (D.nd.l i) → IsRowB L (D.nd.l i) → ∀ r ρ π, PtIn i r ρ π → ∀ w hw,
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), ∃ Wd : NWord (nLet i w hw),
      WordBase L HW i r ρ π w hw Cx hG Wd ∧ ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd ∧ 11 ≤ D.nd.l i ∧
      jA L (D.nd.l i) + 1 ≤ nLet i w hw ∧
      C₂ * ((jA L (D.nd.l i) : ℝ) + 1) * (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) ≤ (Wd.b : ℝ) ∧
      TruncatedSeriesCountingBounds.Clusters (jA L (D.nd.l i)) (TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz)

def JointCD : Prop :=
  ∀ i, InertUnr D (D.nd.l i) → ∀ r ρ π, PtIn i r ρ π → ∀ w hw,
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), ∃ Wd : NWord (nLet i w hw),
      WordBase L HW i r ρ π w hw Cx hG Wd ∧ ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd ∧ 11 ≤ D.nd.l i ∧ WordBox L Wd ∧
      (WordsNT Wd ∨ ∃ d, WordsAT (D.nd.l i) Wd d ∧ AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d)

end GlobalTheory.HTW.RecS
