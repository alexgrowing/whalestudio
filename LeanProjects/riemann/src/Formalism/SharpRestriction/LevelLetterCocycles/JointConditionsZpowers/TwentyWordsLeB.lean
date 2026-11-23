import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IsTwistedDualOfGaloisRep

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

variable {D : D7}

section Cores

variable (L : SizeData₂ D)

def coreE (l : ℕ) : ℝ := 1 + Formalism.MainNotions.TwistedPlaces.hB L / l + Real.logb l (Formalism.MainNotions.TwistedPlaces.hB L)

def coreH (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  ((Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (Formalism.MainNotions.TwistedPlaces.hB L / (l : ℝ) ^ 2)

open Classical in
def flat (bd : Prop) (l : ℕ) : ℝ :=
  (Formalism.MainNotions.TwistedPlaces.wP L + Formalism.MainNotions.TwistedPlaces.eta₃ L) / l + L.Sc + Formalism.MainNotions.TwistedPlaces.large₂ L +
    Formalism.MainNotions.TwistedPlaces.eta₃ L * (if bd then 1 else 0)

def coreF (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  ((Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * flat L bd l

def coreM (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) * D.R.m * coreE L l

def bdCD (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) (K₁ K₂ K₃ : ℝ) : ℝ :=
  K₁ * coreH L l lam + K₂ * coreF L bd l lam + K₃ * coreM L l lam

end Cores

structure WordBox (L : SizeData₂ D) {n : ℕ} (Wd : WordDat n) : Prop where
  box_le : ∀ a, ((Wd.Mi a + Wd.hi a : ℕ) : ℝ) ≤ 2 * Formalism.MainNotions.TwistedPlaces.hB L
  nt : ∀ a, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a →
    ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ Formalism.MainNotions.TwistedPlaces.wB L ∧ |(Wd.sz a : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2
  b_lo : L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ Wd.b
  b_hi : (Wd.b : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1

structure WordsNT {n : ℕ} (Wd : WordDat n) : Prop where
  eta_lt : ∀ a, Wd.η < Wd.sz a
  w20 : 20 * Wd.w ≤ Wd.b
  η20 : 20 * Wd.η ≤ Wd.b
  twenty_words_le_b : 20 * Wd.S ≤ Wd.b
  some_nt : ∃ a, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a
  alt : ∀ a, Wd.up (a + 1) ≠ Wd.up a ∧
    ¬ (Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a ∧ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz (a + 1) ∧
      Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz (a + 2))

structure WordsAT (l : ℕ) {n : ℕ} [NeZero n] (Wd : WordDat n) (d : ℕ) : Prop where
  even : Even n
  typ : ∀ a : ZMod n, Wd.up a = true ↔ (a.val + d) % 2 ≠ 0
  thick : ∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a
  big1 : ∀ a, 2 * Formalism.MainNotions.RamifiedCoefficientChains.aR l (Formalism.MainNotions.RamifiedCoefficientChains.hpar n Wd.sz Wd.S + Wd.η) + (Wd.η : ℝ) + 1 ≤ (Wd.sz a : ℝ)
  big2 : ∀ a, ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n Wd.sz Wd.S : ℕ) : ℝ) / 2 ≤ (Wd.sz a : ℝ)

section Word2

variable {L : SizeData₂ D} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}

def WordDat.band {n : ℕ} (Wd : WordDat n) (l : ℕ) (CB : ℝ) : Prop :=
  Formalism.MainNotions.TruncatedSeriesCountingBounds.Band l Wd.b Wd.S Wd.η Wd.sz
    (Real.logb l (2 * ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ))) CB

end Word2

attribute [local instance] nLet_neZero

section Word3

variable {L : SizeData₂ D} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}

variable (ρ π hG) in

structure WordBaseC (Wd : WordDat (nLet i w hw)) : Prop where
  zeta : ∃ ζ : ↥Cx.LL.1, IsPrimitiveRoot ζ (D.nd.l i)
  mult : ∀ T₂ : LatW i w hw Cx, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ →
    ∀ (a : ZMod (nLet i w hw)) (τ : ↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
      Formalism.MainNotions.LiftingTheory.Over (WW HW i w hw Cx hG) τ a →
      ∑ x ∈ Finset.Icc (-(Wd.η : ℤ)) (Wd.η : ℤ),
        multV ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ τ x ≤ (Wd.m : ℤ)

end Word3

section RowCD

variable (L : SizeData₂ D)

def LocalRepresentationCongruenceCondition (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL),
      ∃ Wd : WordDat (nLet i w hw), WordBase L HW i r ρ π w hw Cx hG Wd ∧ WordBox L Wd ∧
        (WordsNT Wd ∨ (WordBaseC (HW := HW) ρ π hG Wd ∧ ∃ d, WordsAT (D.nd.l i) Wd d))

def bandOf (HW : HWOf D.loc) (CB : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (lam : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  11 ≤ D.nd.l i ∧ ∃ π ∈ D.nd.Zgood i, ∃ (hw : lam ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i lam hw) (hG : Good (D.nbr i lam hw).Kw 1 Cx.LL)
    (Wd : WordDat (nLet i lam hw)), WordBase L HW i r ρ π lam hw Cx hG Wd ∧ WordBox L Wd ∧ WordsNT Wd ∧
      Wd.band (D.nd.l i) CB

def lenRowCD (bd : HeightOneSpectrum (𝓞 D.host.E) → Prop) (K₁ K₂ K₃ : ℝ) (l : ℕ)
    (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  ratIn (bdCD L (bd lam) l lam K₁ K₂ K₃) (bdCD L (bd lam) l lam K₁ (K₂ + 1) K₃)

variable (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

end RowCD

end Formalism.MainNotions.N

end
