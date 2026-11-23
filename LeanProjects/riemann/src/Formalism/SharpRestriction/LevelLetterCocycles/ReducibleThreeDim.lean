import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.FrobeniusOrbits.Statement
import Formalism.GaloisCohomology.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

noncomputable section

namespace Formalism.MainNotions.ReducibleThreeDim

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.BasicNotions

section PartB

open Real

open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Real

def BD (s q d e : ℕ) : ℝ :=
  (2 : ℝ) ^ (s + 1) * (((e : ℝ) + 2) * logb 2 ((2 : ℝ) ^ (s + 2) * q * d) +
    ((e : ℝ) + 1) * logb 2 5 + 1 +
    logb 2 (((e : ℝ) + 1) * ((e + 1).factorial : ℝ) * ((e + 2).factorial : ℝ)))

section Field

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def ShaLengthBoundAt (LD : Formalism.GaloisCohomology.LData E Ω 2) (s q d : ℕ) : Prop :=
  ∀ e : ℕ, 1 ≤ e → Formalism.GaloisCohomology.shaLen LD (e : ℤ) ≠ ⊤ ∧
    ((Formalism.GaloisCohomology.shaLen LD (e : ℤ)).toNat : ℝ) ≤
      5 * BD s q d e + 2 * ((s : ℝ) + 2 + (padicValNat 2 e : ℝ))

def rd (E : Type) [Field E] [NumberField E] : ℝ :=
  |(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))

def CorAt (LD : Formalism.GaloisCohomology.LData E Ω 2) (s q d : ℕ) (C : ℝ) : Prop :=
  (∀ t : ℕ, (∀ e ∈ Finset.Ioo 0 t, Formalism.GaloisCohomology.shaLen LD (e : ℤ) ≠ ⊤) ∧
    ∑ e ∈ Finset.Ioo 0 t, ((Formalism.GaloisCohomology.shaLen LD (e : ℤ)).toNat : ℝ) ≤
      C * (2 : ℝ) ^ (s + 1) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (2 : ℝ) ^ s * q * d)) ∧
  (padicValNat 2 (classNumber E) : ℝ) ≤ C * (2 : ℝ) ^ (s + 1) * Real.log (rd E)

end Field

def ShaLengthVersionTwo : Prop :=
  ∀ (s q d : ℕ), HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (s + 2) q d ζ a b →
  ∀ (Ω : Type) [Field Ω] [Algebra (hostE ζ a b) Ω] [IsAlgClosure (hostE ζ a b) Ω]
    (LD : Formalism.GaloisCohomology.LData (hostE ζ a b) Ω 2), ShaLengthBoundAt LD s q d

def CyclotomicCorollaryBound (C : ℝ) : Prop :=
  ∀ (s q d : ℕ), HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (s + 2) q d ζ a b →
  ∀ (Ω : Type) [Field Ω] [Algebra (hostE ζ a b) Ω] [IsAlgClosure (hostE ζ a b) Ω]
    (LD : Formalism.GaloisCohomology.LData (hostE ζ a b) Ω 2), CorAt LD s q d C

end PartB

def Conclusion1 (_D : D7) : Prop := ShaLengthVersionTwo

def Conclusion2 (_D : D7) (C : ℝ) : Prop := CyclotomicCorollaryBound C

def PointsLemma (D : D7) : Prop := D.nd.ShaFinTwo

def ShaBoundTheoremB (D : D7) (C : ℝ) : Prop := Conclusion1 D ∧ Conclusion2 D C ∧ PointsLemma D

def corVV2 (D : D7) (C : ℝ) : Prop :=
  (D.what₂.VV 2 : ℝ) ≤ C * (D.R.f : ℝ) * (D.R.t : ℝ) ^ 2 *
    Real.log ((D.R.t : ℝ) * (D.R.n : ℝ) * D.host.q * D.host.d)

def Kq (D : D7) : IntermediateField ℚ D.host.E := IntermediateField.adjoin ℚ {D.host.sqq}

def LogSigmaOnePullbackCocycle (D : D7) : IntermediateField ℚ D.host.E :=
  IntermediateField.fixedField
    (D.R.hH.comp ((MonoidHom.snd _ _).comp D.host.gal.toMonoidHom)).ker

def epsL (l : ℕ) : ℝ := 1 / (l : ℝ) ^ 2

def TwLoc (D : D7) (i : D.nd.Loc) : Prop := D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0

section PartA

open Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.TruncatedSeriesCountingIdentities Formalism.BasicNotions.Loc ReciprocityTheory.Gal

variable {D : D7}

def Over (w : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = v.asIdeal

def EpsAt (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ z : ℤ_[D.nd.l i], ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * z

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

section AtW

variable {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
  (Cx : CoefExt D i w hw)

def jumpsR (x : D.nd.X i) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1) : Set ℤ :=
  {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (locC Cx (rTwO D.nd i r x))) τ a}

def jumpsRd (x : D.nd.X i) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1) : Set ℤ :=
  {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (locC Cx (rDuO D.nd i r x))) τ a}

end AtW

def JumpLe (h : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : CoefExt D i w hw) (x : D.nd.X i) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    ∀ a ∈ jumpsR i r Cx x τ, |a| ≤ (h : ℤ)

open Classical in
def JumpHost (large₂ : SizeData₂ D) (vplus : HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : CoefExt D i w hw) (x : D.nd.X i) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    {a ∈ jumpsR i r Cx x τ | |(a : ℝ) - ((D.R.t : ℝ) - 1) / 2| ≤ large₂.etaSz ∧ ¬ (0 ≤ a ∧ a < D.R.t)}.ncard ≤ D.R.m ∧
    {a ∈ jumpsR i r Cx x τ | (large₂.Sc + large₂.etaSz + D.R.t : ℝ) < (if Over w vplus then (1 : ℝ) else -1) * a}.ncard =
      D.R.r - D.R.m ∧
    (∀ a : ℤ, 0 ≤ a → a < D.R.t → a ∈ jumpsR i r Cx x τ) ∧ (-1 : ℤ) ∉ jumpsR i r Cx x τ ∧
    (D.R.t : ℤ) ∉ jumpsR i r Cx x τ ∧
    ∀ a ∈ jumpsR i r Cx x τ, |(a : ℝ) - ((D.R.t : ℝ) - 1) / 2| ≤ large₂.etaSz ∨ (0 ≤ a ∧ a < D.R.t) ∨
      (large₂.Sc + large₂.etaSz + D.R.t : ℝ) < (if Over w vplus then (1 : ℝ) else -1) * a

def JumpTop (large₂ : SizeData₂ D) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : CoefExt D i w hw) (x : D.nd.X i) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    ∀ a ∈ jumpsR i r Cx x τ, |(a : ℝ)| ≤ large₂.sc.b + large₂.Sc + large₂.etaSz + D.R.t + 2

def ColRow (dc : Decl D i) (vplus : HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  (∀ w, w ∈ dc.col ↔ w ∈ placesOver D.host.E (D.nd.l i) ∧ Over w vplus) ∧
  (∀ w, w ∈ dc.row ↔ ∃ w' ∈ dc.col, IsConjPl D.host w' w)

def expo {X : Type} [AddCommGroup X] [Module (D.nd.O i) X] (M : Submodule (D.nd.O i) X) : ℕ :=
  sInf {c : ℕ | ∀ m ∈ M, ((D.nd.l i : D.nd.O i) ^ c) • m = 0}

def H0WeightInvariants (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (D.nd.O i) (KOG (D.nd.O i) D.R.r) :=
  Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w))

def H0DualInvariants (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (D.nd.O i) (KOG (D.nd.O i) D.R.r) :=
  Representation.invariants ((WKG (T2O D.nd i ρ π)).comp (decS D.nd w))

def c0 (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  max (max (expo i (H0WeightInvariants i ρ π w)) (expo i (H0DualInvariants i ρ π w)))
    (sSup {c : ℕ | ∃ w', IsConjPl D.host w w' ∧ c = expo i (H0DualInvariants i ρ π w')})

def Polar (π : D.nd.X i) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (w' : HeightOneSpectrum (𝓞 D.host.E)) (hw' : w' ∈ placesOver D.host.E (D.nd.l i)),
    IsConjPl D.host w w' → ∀ (Cx : CoefExt D i w hw) (Cx' : CoefExt D i w' hw'),
    (∀ (x : D.nd.X i) (b : ℤ), (∃ τ', b ∈ jumpsRd i r Cx' x τ') ↔ ∃ τ, b + D.R.t ∈ jumpsR i r Cx x τ) ∧
    ∀ b : ℤ, ∑ τ', multV (Br.PD D.loc D.nbr i w' hw') (matRep (locC Cx' (T2O D.nd i ρ π))) τ' b =
      ∑ τ, multV (Br.PD D.loc D.nbr i w hw) (matRep (locC Cx (WpO D.nd i ρ π))) τ (b + D.R.t)

def LiftTw (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (e' : ℕ) : Prop :=
  ∀ Cx : CoefExt D i w hw, Cx.IsGood →
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL Cx.LL)) (fun x : D.nd.X i => ⇑(locC Cx (rTwO D.nd i r x))) e'

def LiftDu (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (e' : ℕ) : Prop :=
  ∀ Cx : CoefExt D i w hw, Cx.IsGood →
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL Cx.LL)) (fun x : D.nd.X i => ⇑(locC Cx (rDuO D.nd i r x))) e'

def liftRows (dc : Decl D i) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) : Prop :=
  ∀ w ∈ dc.col, ∀ (w' : HeightOneSpectrum (𝓞 D.host.E)) (hw' : w' ∈ placesOver D.host.E (D.nd.l i)),
    IsConjPl D.host w w' → LiftDu i r w' hw' (e' w)

def qTerm : ℚ :=
  (D.R.t : ℚ) * ∑ v ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1})

open Classical in
def jCol (π : D.nd.X i) (dc : Decl D i) (w : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  if h : w ∈ dc.col then Br.jW D.loc D.nbr i w ((dc.cover w).1 (Or.inr h)) ρ π else 0

end PartA

end Formalism.MainNotions.ReducibleThreeDim
