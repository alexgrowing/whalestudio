import Mathlib
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineWindowLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTW

variable (D : D7)

def liftIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def UnramifiedInE (l : ℕ) : Prop :=
  ∀ v ∈ placesOver D.host.E l, v.asIdeal.ramificationIdx ℤ = 1

def InertInK (l : ℕ) : Prop := D.host.cls l = .signal ∨ D.host.cls l = .inertClass

def IsFrobAt (w : HeightOneSpectrum (𝓞 D.host.E)) (φ : D.R.GG) : Prop :=
  IsArithFrobAt ℤ (D.host.sigmaOf φ) w.asIdeal

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

def Matches (θ : Emb D i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, θ (Br.cEw D.nbr i w hw x) =
    Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def CrystallineInput : Prop :=
  (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) ∧
    IsCrys (Br.PD D.loc D.nbr i w hw) (charRep (Br.locChi D.nbr i w hw (chiU D.nd i 1)))

def JumpInput (ε : ℤˣ) : Prop :=
  ∀ (θ : Emb D i w hw) (g : D.R.GG), Matches D i w hw θ g → ∀ (x : D.nd.X i) (a : ℤ),
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) θ a ↔
      a ∈ jR (hcAt D g) (liftIdx D i) (pos ε g)

def IsNumbering {n : ℕ} (θ : ZMod n → Emb D i w hw) : Prop :=
  n = Module.finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) ∧ Function.Bijective θ ∧
    ∀ (k : ZMod n) (c : Br.K0 D.nbr i w hw),
      θ (k + 1) (algebraMap (Br.K0 D.nbr i w hw) (Br.Kw D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).σ c)) =
        θ k (algebraMap (Br.K0 D.nbr i w hw) (Br.Kw D.nbr i w hw) c)

end Place

def window {n : ℕ} (W : WordData n) (k : ZMod n) : Set ℤ :=
  (if W.up k then Set.Icc (W.sz k) (W.sz k + W.S) else Set.Icc (-(W.sz k + W.S)) (-W.sz k)) ∪
    Set.Icc (-(W.η : ℤ)) W.η

section Concl

variable (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def WordJumpsAt : Prop :=
  ∃ (φ τ : D.R.GG) (θ : ZMod (orderOf φ⁻¹) → Emb D i w hw),
    IsFrobAt D w φ ∧ IsNumbering D i w hw θ ∧
    (∀ k, Matches D i w hw (θ k) (letter τ φ⁻¹ k)) ∧
    (InertInK D (D.nd.l i) →
      Even (orderOf φ⁻¹) ∧ Alternates (pageWord L (liftIdx D i) ε τ φ⁻¹).up ∧
        ∀ k, (pageWord L (liftIdx D i) ε τ φ⁻¹).up k = false ↔ Even k.val) ∧
    ∀ T : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
      IsSubOfSums T.ρ (fun (x : D.nd.X i) (g : Br.G D.nbr i w hw) =>
        Br.loc D.nbr i w hw (rDuO D.nd i r x) g) →
      IsCrys (Br.PD D.loc D.nbr i w hw) T.ρ ∧
        ∀ k,
          JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (θ k) ((pageWord L (liftIdx D i) ε τ φ⁻¹).J1 k) ∧
          JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (θ k) (window (pageWord L (liftIdx D i) ε τ φ⁻¹) k) ∧
          JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (θ k)
            (Set.Icc (-((pageWord L (liftIdx D i) ε τ φ⁻¹).Mi k : ℤ))
              ((pageWord L (liftIdx D i) ε τ φ⁻¹).hi k : ℤ))

end Concl

def JumpsAlongWord : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    UnramifiedInE D (D.nd.l i) → (∀ k, D.nd.l i ≠ D.host.g k) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrystallineInput D i w hw r → JumpInput D i w hw r ε → WordJumpsAt D L ε i w hw r

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineWindowLifts
