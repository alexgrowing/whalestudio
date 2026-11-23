import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCrystallineInputs

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW

def window {n : ℕ} (W : WordData n) (a : ZMod n) : Set ℤ :=
  (if W.up a then Set.Icc (W.sz a) (W.sz a + W.S) else Set.Icc (-(W.sz a + W.S)) (-W.sz a)) ∪
    Set.Icc (-(W.η : ℤ)) W.η

def range {n : ℕ} (W : WordData n) (a : ZMod n) : Set ℤ :=
  Set.Icc (-(W.Mi a : ℤ)) (W.hi a : ℤ)

def UnramifiedIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ v ∈ placesOver E p, v.asIdeal.ramificationIdx ℤ = 1

def InertInK {R : Ranks} (H : Host R) (p : ℕ) : Prop :=
  H.cls p = .signal ∨ H.cls p = .inertClass

def IsFrobAt {R : Ranks} (H : Host R) (w : HeightOneSpectrum (𝓞 H.E)) (φ : R.GG) : Prop :=
  IsArithFrobAt ℤ (H.sigmaOf φ) w.asIdeal

section Place

variable (D : D7) (i : D.nd.Loc)

def liftIdx : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def ChiConstituent (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∃ π ∈ D.nd.Z i, ∃ v : Fin D.R.nV → KK D.nd i, v ≠ 0 ∧
    ∀ g : GE D.nd, repK D.nd i r π g v = toK D.nd i ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) • v

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

abbrev Lat : Type 1 :=
  LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)

def IsLetter (τ : Emb D i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) =
    Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))

def IsNumbering {n : ℕ} (emb : ZMod n → Emb D i w hw) : Prop :=
  n = Module.finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) ∧ Function.Bijective emb ∧
    ∀ (a : ZMod n) (c : Br.K0 D.nbr i w hw),
      emb (a + 1) (algebraMap (Br.K0 D.nbr i w hw) (Br.Kw D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).σ c)) =
        emb a (algebraMap (Br.K0 D.nbr i w hw) (Br.Kw D.nbr i w hw) c)

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def CrysInput : Prop :=
  ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))

def JumpInput (ε : ℤˣ) : Prop :=
  ∀ (x : D.nd.X i) (τ : Emb D i w hw) (g : D.R.GG), IsLetter D i w hw τ g → ∀ u : ℤ,
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) τ u ↔
      u ∈ jR (hcAt D g) (liftIdx D i) (pos ε g)

def InTwistedDuals (T : Lat D i w hw) : Prop :=
  IsSubOfSums T.ρ fun (x : D.nd.X i) (g : Br.G D.nbr i w hw) => Br.loc D.nbr i w hw (rDuO D.nd i r x) g

def FitsWord {n : ℕ} (W : WordData n) (emb : ZMod n → Emb D i w hw) (T : Lat D i w hw) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) T.ρ ∧
    ∀ a : ZMod n,
      JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (emb a) (W.J1 a) ∧
      JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (emb a) (window W a) ∧
      JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ (emb a) (range W a)

def WordAt (L : SizeData₂ D) (ε : ℤˣ) : Prop :=
  ∃ τ ψ : D.R.GG, IsFrobAt D.host w ψ⁻¹ ∧
    ∃ emb : ZMod (orderOf ψ) → Emb D i w hw,
      IsNumbering D i w hw emb ∧
      (∀ a, IsLetter D i w hw (emb a) (letter τ ψ a)) ∧
      (InertInK D.host (D.nd.l i) →
        Even (orderOf ψ) ∧ Alternates (pageWord L (liftIdx D i) ε τ ψ).up ∧
          ∀ a, (pageWord L (liftIdx D i) ε τ ψ).up a = false ↔ Even a.val) ∧
      ∀ T : Lat D i w hw, InTwistedDuals D i w hw r T →
        FitsWord D i w hw (pageWord L (liftIdx D i) ε τ ψ) emb T

end Place

def JumpsAlongWord : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    UnramifiedIn D.host.E (D.nd.l i) → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    ChiConstituent D i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrysInput D i w hw r → JumpInput D i w hw r ε → WordAt D i w hw r L ε

def Inputs (D : D7) (ε : ℤˣ) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    (D.nd.Z i).Nonempty → ChiConstituent D i r ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
        JumpInput D i w hw r ε ∧
          (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → CrysInput D i w hw r)

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCrystallineInputs
