import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits NumberField IsDedekindDomain GlobalTheory.HTW

variable (D : D7)

def liftIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def Splits (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i]
      ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ g u, e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) =
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1,
        fun c : Fin D.R.t =>
          toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def Reads (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) =
    Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))

def CrysAt {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw M))

def mult {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ) : ℤ :=
  multV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw M)) τ a

def countIn {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (n : ℕ) : ℤ :=
  ∑ a ∈ Finset.Icc (-(n : ℤ)) n, mult D i w hw M τ a

def HasJumps {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (J : Multiset ℤ) : Prop :=
  ∀ a : ℤ, mult D i w hw M τ a = (J.count a : ℤ)

def CrysInput (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ x, CrysAt D i w hw (rO D.nd i r x)

def JumpInput (ε : ℤˣ) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ x τ g, Reads D i w hw τ g →
    HasJumps D i w hw (rTwO D.nd i r x) τ (jR (hcAt D g) (liftIdx D i) (pos ε g))

variable {D} (L : SizeData₂ D) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def ExactlyAt : Prop :=
  CrysAt D i w hw (T2O D.nd i ρ π) ∧
    ∀ τ, countIn D i w hw (T2O D.nd i ρ π) τ (etaHat L) = D.R.m

def AtMostAt : Prop :=
  CrysAt D i w hw (T2O D.nd i ρ π) ∧
    ∀ τ, countIn D i w hw (T2O D.nd i ρ π) τ (etaHat L) ≤ D.R.m

end Place

def HidaSetting (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  (∀ v ∈ placesOver D.host.E (D.nd.l i), eWL D.host.E v = 1) ∧
  (∀ k, D.nd.l i ≠ D.host.g k) ∧ GoodR D.nd i r ∧ π ∈ D.nd.Z i ∧ Splits D i r ρ π

variable {D}

def JumpsByLetter (L : SizeData₂ D) : Prop :=
  ∀ (ε : ℤˣ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    HidaSetting D i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrysInput D i w hw r → JumpInput D i w hw ε r →
      CrysAt D i w hw (T2O D.nd i ρ π) ∧
      ∀ τ g, Reads D i w hw τ g →
        HasJumps D i w hw (T2O D.nd i ρ π) τ (jT2 (hcAt D g) (liftIdx D i) (pos ε g)) ∧
        ((etaHat L : ℤ) < szT (hcAt D g) (liftIdx D i) (pos ε g) →
          countIn D i w hw (T2O D.nd i ρ π) τ (etaHat L) = D.R.m)

def SmallJumps (L : SizeData₂ D) : Prop :=
  ∀ C : ℝ, Roomy L C →
  ∀ (ε : ℤˣ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    HidaSetting D i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrysInput D i w hw r → JumpInput D i w hw ε r → ExactlyAt i w hw L ρ π

def SmallJumpsAll : Prop := ∀ (D : D7) (L : SizeData₂ D), SmallJumps L

theorem embLL_sigmaOf (g : D.R.GG) (x : D.host.E) :
    D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x := by
  have := RingHom.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)
  simpa [Host.emb] using this

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces
