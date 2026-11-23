import Mathlib
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.DataParams

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Exceptional

variable {D : D7} (L : SizeData₂ D)

def sigmaPlus : ℤ := ⌊2 * L.sc.b / LevelStarExponents.lStar L⌋

def baseSizes : Set ℝ :=
  {W | W = L.sc.b ∨ W = L.sc.w'' D.R.n ∨
    ∃ τ : D.host.TT, W = (L.bT τ : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ)}

def window (W₀ : ℝ) : Set ℤ :=
  {n | W₀ + (-L.etaSz - 2 * (sigmaPlus L : ℝ) - 3) ≤ (n : ℝ) ∧
    (n : ℝ) ≤ W₀ + (L.Sc + L.etaSz + L.etaSz + 2 * (sigmaPlus L : ℝ) + 4)}

def excPrimes : Set ℕ :=
  {l | l.Prime ∧ LevelStarExponents.lStar L < (l : ℝ) ∧ ∃ W₀ ∈ baseSizes L, ∃ n ∈ window L W₀, (l : ℤ) ∣ n}

end Exceptional

section Terms

variable (D : D7) (i : D.nd.Loc)

def ramLen : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)})

def ccLen (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)

def selLen (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i (fun _ => ρ) π)

def shaSum : ℕ∞ :=
  ∑ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

def zetaP (P : HeightOneSpectrum (𝓞 D.host.E)) : D.nd.O i :=
  ((D.ntw.psiL i (D.nd.gam0 i P) : (D.nd.O i)ˣ) : D.nd.O i)

def twistLen : ℕ∞ :=
  (D.R.t : ℕ∞) * ∑ P ∈ D.nd.Q i,
    Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {zetaP D i P - 1})

def IsBlockSplit (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) :
    Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
  ∃ φ : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ g u, φ ((((r g : GL (Fin D.R.nV) (D.nd.O i)) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (toK D.nd i)).mulVec u) =
      ((((ρ g : GL (Fin D.R.r) (D.nd.O i)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (toK D.nd i)).mulVec (φ u).1,
        fun c : Fin D.R.t =>
          toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (φ u).2 c)

end Terms

def LargePrimeBound_at (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ i : D.nd.Loc,
    LevelStarExponents.lStar L < (D.nd.l i : ℝ) → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    D.nd.l i ∉ excPrimes L →
    HG D.nd D.naut i →
    ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, ∀ ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i), IsBlockSplit D i (r π) ρ →
      ccLen D i π ≤ selLen D i ρ π + ramLen D i * shaSum D i +
        ramLen D i * (padicValNat (D.nd.l i) (hE D.host) : ℕ∞) + twistLen D i

def LargePrimeBoundF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LargePrimeBound_at (Fm.D x i) (Fm.L x i)

def LargePrimeBound (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => LargePrimeBoundF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

end
