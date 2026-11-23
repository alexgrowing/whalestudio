import Mathlib
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

section At

variable (D : D7) (i : D.nd.Loc)

def NoLevelPrime : Prop := ∀ k : Fin 2, D.nd.l i ≠ D.host.g k

def chiRatio (c : ℕ) : GE D.nd →* (D.nd.O i)ˣ := chiU D.nd i c * (chiU D.nd i 1)⁻¹

def IsConstituent {n : ℕ} (χ : GE D.nd →* (D.nd.O i)ˣ)
    (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i)) : Prop :=
  ∃ v : Fin n → KK D.nd i, v ≠ 0 ∧
    ∀ g, (mapM (toK D.nd i) M g).mulVec v = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • v

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def CharCrysAt (χ : GE D.nd →* (D.nd.O i)ˣ) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (charRep (Br.locChi D.nbr i w hw χ))

def MatCrysAt {n : ℕ} (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i)) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw M))

def ChiOneInvCrysAt : Prop := CharCrysAt D i w hw (chiU D.nd i 1)⁻¹

def ChiRatioCrysAt : Prop :=
  ∀ c : ℕ, 1 ≤ c → c ≤ D.R.t →
    chiRatio D i c = (epsU D.nd i) ^ (-((c : ℤ) - 1)) ∧ CharCrysAt D i w hw (chiRatio D i c)

def BlockCrysAt : Prop := ChiOneInvCrysAt D i w hw ∧ ChiRatioCrysAt D i w hw

end At

def BlockCrys_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, NoLevelPrime D i → (D.nd.Z i).Nonempty →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), BlockCrysAt D i w hw

def BlockCrysF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ a : Fm.Ix x, BlockCrys_at (Fm.D x a)

def BlockCrysClosed (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm _ => BlockCrysF Fm)

def BlockCharactersCrystalline : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → NoLevelPrime D i →
    ∀ π ∈ D.nd.Z i, IsConstituent D i (chiU D.nd i 1) (rO D.nd i r π) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      (∀ x, MatCrysAt D i w hw (rO D.nd i r x)) → BlockCrysAt D i w hw

def Inputs_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, NoLevelPrime D i →
    ∃ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r ∧
      (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i),
        MatCrysAt D i w hw (rO D.nd i r x)) ∧
      ∀ π ∈ D.nd.Z i, IsConstituent D i (chiU D.nd i 1) (rO D.nd i r π)

theorem chiRatio_eq (D : D7) (i : D.nd.Loc) (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) :
    chiRatio D i c = (epsU D.nd i) ^ (-((c : ℤ) - 1)) := by
  unfold chiRatio chiU
  rw [D.nd.chi_def i c h1 h2, mul_inv_cancel_comm]
  rfl

theorem chiRatO_apply (D : D7) (i : D.nd.Loc) (c : ℕ) (g : GE D.nd) :
    chiRatO D.nd i c g 0 0 = ((chiRatio D i c g : (D.nd.O i)ˣ) : D.nd.O i) := by
  simp [chiRatO, twistM, chiRatio]

end GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps
