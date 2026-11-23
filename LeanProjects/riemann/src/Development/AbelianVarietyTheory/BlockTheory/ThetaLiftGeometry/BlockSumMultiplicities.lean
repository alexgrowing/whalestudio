import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockSumMultiplicities

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW

variable (D : D7)

abbrev Fam (i : D.nd.Loc) (k : ℕ) : Type := D.nd.X i → (GE D.nd →* GL (Fin k) (D.nd.O i))

def BlockSum (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i) : Prop :=
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ (g : GE D.nd) (u : Fin D.R.nV → KK D.nd i),
      e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) =
        ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

def UnramIn (p : ℕ) : Prop :=
  ∀ v ∈ placesOver D.host.E p, Algebra.IsUnramifiedAt ℤ v.asIdeal

def OffTypes (p : ℕ) : Prop := ∀ k : Fin 2, p ≠ D.host.g k

def SizesLarge {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ (g : D.R.GG) (j : Fin D.R.m) (s : Bool), (etaHat L : ℤ) < szT (hcAt D g) j s

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

abbrev locRep {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Representation (Br.LL D.nbr i w hw) (Br.G D.nbr i w hw) (Fin k → Br.LL D.nbr i w hw) :=
  matRep (Br.loc D.nbr i w hw M)

def CrysAt {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (locRep D i w hw M)

def mult {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (τ : Emb D i w hw) (a : ℤ) : ℤ :=
  multV (Br.PD D.loc D.nbr i w hw) (locRep D i w hw M) τ a

def FinDR {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (τ : Emb D i w hw) : Prop :=
  FiniteDimensional (Br.LL D.nbr i w hw) ↥(DdRE (Br.PD D.loc D.nbr i w hw) (locRep D i w hw M) τ)

def smallCount {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (τ : Emb D i w hw) (h : ℕ) : ℤ :=
  ∑ a ∈ Finset.Icc (-(h : ℤ)) (h : ℤ), mult D i w hw M τ a

def Over (τ : Emb D i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, ∃ y : D.what₂.LL,
    Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ (Br.cEw D.nbr i w hw x) ∧
      D.what₂.embLL y = D.host.emb g x

end Place

def jIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def HidaSetting (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i) : Prop :=
  GoodR D.nd i r ∧ π ∈ D.nd.Z i ∧ BlockSum D i r ρ π ∧ UnramIn D (D.nd.l i) ∧ OffTypes D (D.nd.l i)

variable {D}

def SecondTwistCrystallineSmall (L : SizeData₂ D) : Prop :=
  SizesLarge L →
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i), HidaSetting D i r ρ π →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    CrysAt D i w hw (T2O D.nd i ρ π) ∧
    ∀ τ : Emb D i w hw, FinDR D i w hw (T2O D.nd i ρ π) τ ∧
      smallCount D i w hw (T2O D.nd i ρ π) τ (etaHat L) = D.R.m

def SecondTwistCrystallineAtMost (L : SizeData₂ D) : Prop :=
  SizesLarge L →
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i), HidaSetting D i r ρ π →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    CrysAt D i w hw (T2O D.nd i ρ π) ∧
    ∀ τ : Emb D i w hw, FinDR D i w hw (T2O D.nd i ρ π) τ ∧
      smallCount D i w hw (T2O D.nd i ρ π) τ (etaHat L) ≤ D.R.m

theorem SecondTwistCrystallineSmall.le {L : SizeData₂ D} (h : SecondTwistCrystallineSmall L) : SecondTwistCrystallineAtMost L :=
  fun hs i r ρ π hS w hw =>
    ⟨(h hs i r ρ π hS w hw).1, fun τ => ⟨((h hs i r ρ π hS w hw).2 τ).1, ((h hs i r ρ π hS w hw).2 τ).2.le⟩⟩

variable (D)

def SecondTwistJumps (ε : ℤˣ) : Prop :=
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV) (ρ : Fam D i D.R.r) (π : D.nd.X i), HidaSetting D i r ρ π →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Emb D i w hw) (g : D.R.GG), Over D i w hw τ g →
    ∀ a : ℤ, mult D i w hw (T2O D.nd i ρ π) τ a =
      ((jT2 (hcAt D g) (jIdx D i) (pos ε g)).count a : ℤ)

def PointsCrys : Prop :=
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV), GoodR D.nd i r → OffTypes D (D.nd.l i) →
  ∀ (x : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    CrysAt D i w hw (rO D.nd i r x)

def PointsJumps (ε : ℤˣ) : Prop :=
  ∀ (i : D.nd.Loc) (r : Fam D i D.R.nV), GoodR D.nd i r →
  ∀ (x : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Emb D i w hw) (g : D.R.GG), Over D i w hw τ g →
    ∀ a : ℤ, mult D i w hw (rTwO D.nd i r x) τ a =
      ((jR (hcAt D g) (jIdx D i) (pos ε g)).count a : ℤ)

def FromInputs : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (ε : ℤˣ), PointsCrys D → PointsJumps D ε → SecondTwistJumps D ε ∧ SecondTwistCrystallineSmall L

example {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) : (jT2 P j s).card = R.k - 1 + R.m := by
  cases s <;> simp [jT2, GlobalTheory.HTW.jW, cloud, lows]

end GlobalTheory.IndefiniteRowSideFullHecke.BlockSumMultiplicities
