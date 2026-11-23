import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff

noncomputable section

namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def matKO {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (A : Matrix (Fin k) (Fin k) O) :
    KOG O k →ₗ[O] KOG O k :=
  (stdG O (FractionRing O) k).mapQ (stdG O (FractionRing O) k)
    (((A.map (algebraMap O (FractionRing O))).mulVecLin).restrictScalars O) (by
      rintro _ ⟨u, rfl⟩
      refine ⟨A.mulVec u, ?_⟩
      funext j
      exact RingHom.map_mulVec (algebraMap O (FractionRing O)) A u j)

variable {D : D7} (i : D.nd.Loc)

def ccOff (Xs : Set (D.nd.X i)) (π : D.nd.X i) : Ideal (D.nd.O i) :=
  Ideal.span {a | ∃ f ∈ D.nd.T i, (∀ x ∈ Xs, x ∉ D.nd.Z i → f x = 0) ∧ a = f π}

def vccOff (Xs : Set (D.nd.X i)) (π : D.nd.X i) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccOff i Xs π)

def lenQ (a : D.nd.O i) : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {a})

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i) (Xs : Set (D.nd.X i))

def cocW {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k) :=
  Submodule.span (D.nd.O i)
    {c | ∃ φ : (S.X' → MatN D.nd i) →ₗ[D.nd.O i] KOG (D.nd.O i) k,
      (∀ a, InR' D.nd r S a → ∀ y, InY D.nd r S y → φ (a * y) = matKO (ψ a) (φ y)) ∧
      (∀ y, InY D.nd r S y → (∀ x', S.p x' ∈ Xs → y x' = 0) → φ y = 0) ∧
      c = fun γ => φ (yg D.nd r S γ)}

def cocRho : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r) := cocW i r S Xs S.ψρ

def cocChi (c : Fin D.R.t) : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1) :=
  cocW i r S Xs fun a => S.ψχ c a • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i))

def locFun {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : GE D.nd → KOG (D.nd.O i) k) :
    Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T :=
  fun g => Br.phi (D.nbr i w hw) k (c ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))

def IsFinL {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (c : GE D.nd → KOG (D.nd.O i) k) : Prop :=
  ∀ w hw, locFun i M w hw c ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)

def resIne {k : ℕ} (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (D.nd.O i) (↥(Ine (F := D.host.E) (D.nd.plOm.1 v)) → KOG (D.nd.O i) k) :=
  C.map (LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) k) Subtype.val)

def QuadAt (v : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ x ∈ Xs, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    (rO D.nd i r x γ - 1) *
      (rO D.nd i r x γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) = 0

def PolyAt (π : D.nd.X i) (v : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ P : Polynomial (D.nd.T i),
    (∀ x ∈ Xs, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
      Polynomial.aeval (rO D.nd i r x (D.nd.gam0 i v)) (P.map (evT D.nd i x)) *
        (rO D.nd i r x γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) = 0) ∧
    IsUnit ((P.map (evT D.nd i π)).eval (D.nd.zeta i v))

def NoChiOff : Prop :=
  ∀ x ∈ Xs, x ∉ D.nd.Z i → ∀ u : Fin D.R.nV → KK D.nd i,
    (∀ g, (mapM (toK D.nd i) (rTwO D.nd i r x) g).mulVec u = u) → u = 0

def UnrOut : Prop :=
  ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i →
    ∀ x ∈ Xs, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), rTwO D.nd i r x γ = 1

def GlobalCore : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (eρ eχ : ℕ)
    (S : IdempotentChoiceData D.nd i),
    GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ D.nd.Z i → π ∈ Xs →
    NoChiOff i r Xs → UnrOut i r Xs →
    (∀ v ∈ D.nd.S i, (QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Xs π v) →
    (∀ v ∈ D.nd.Q i, QuadAt i r Xs v ∧ D.nd.zeta i v ≠ 1) →
    (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), GlobalTheory.Pass.HfChar i w hw ∧
      GlobalTheory.Pass.LocBound i w hw r Xs (WpO D.nd i ρ π) eρ ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, GlobalTheory.Pass.LocBound i w hw r Xs (chiRatO D.nd i c) eχ) →
    Br.sFin D.loc D.nbr i ρ π →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    vccOff i Xs π ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * (eρ + D.R.t * eχ) : ℕ) : ℚ) +
      Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) +
      (padicValNat (D.nd.l i) (hE D.host) : ℚ) + 4 * (D.R.nV : ℚ) * D.nd.vdel i +
      (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i,
        lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})

end GlobalTheory.Cut

end
