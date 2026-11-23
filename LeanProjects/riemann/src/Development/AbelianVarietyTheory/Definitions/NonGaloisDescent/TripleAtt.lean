import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

noncomputable section

namespace GlobalTheory.TripleGal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def rd (i : X.Tw) (ι : FractionRing (X.O0 i) →+* ℂ) : X.O0 i →+* ℂ :=
  ι.comp (algebraMap (X.O0 i) (FractionRing (X.O0 i)))

def cj (D : Formalism.BasicNotions.D7) : D.host.E →+* D.host.E :=
  (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom

def UnrRho (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v, v ∉ placesOver D.host.E (X.l i) → (∀ k, v ∉ placesOver D.host.E (D.host.g k)) →
    ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, X.rhoS i s σ = 1

def HodgeL (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v (hv : v ∈ placesOver D.host.E (X.l i)), ∀ r ∈ ({X.rhoS i s, Tgl i s} : Set _),
    (bkP.br i v hv).IsdRW (D.loc (X.l i)) (r.comp (DecV N v).subtype) ∧
    ((∀ k, X.l i ≠ D.host.g k) → (bkP.br i v hv).IsCrysW (D.loc (X.l i)) (r.comp (DecV N v).subtype)) ∧
    (bkP.br i v hv).IsPotCrysW (D.loc (X.l i)) (r.comp (DecV N v).subtype)

def NoInv (i : X.Tw) (M : GE N → Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) (v : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ x : Fin D.R.r → FractionRing (X.O0 i), (∀ g ∈ Dec (F := D.host.E) A,
      ((M g).map (algebraMap (X.O0 i) (FractionRing (X.O0 i)))).mulVec x = x) → x = 0

def NegCount (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ v v' (hv : v ∈ placesOver D.host.E (X.l i)) (hv' : v' ∈ placesOver D.host.E (X.l i))
    (τ : EmbV bkP i v hv) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' →
    dimD bkP i v hv (Tgl i s) τ + dimD bkP i v' hv' (Tgl i s) τ' =
      dimFil0 bkP i v hv (Tgl i s) τ + dimFil0 bkP i v' hv' (Tgl i s) τ' + D.R.r

def Pure (i : X.Tw) (s : X.Sig i) (ι : FractionRing (X.O0 i) →+* ℂ) : Prop :=
  ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl (X := X) i → ∀ A : ValuationSubring N.Om, IsPlaceOver (F := D.host.E) A v →
    ∀ σ : GE N, IsFrob (F := D.host.E) A (normV v) σ → ∀ z : ℂ,
      ((Tmat i s σ).charpoly.map (rd i ι)).IsRoot z → ‖z‖ = ((normV v : ℕ) : ℝ) ^ ((1 - (D.R.t : ℝ)) / 2)

def ReadEmb (bkP : BKPh X) (i : X.Tw) (ι : FractionRing (X.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∈ placesOver D.host.E (X.l i)) (τ : EmbV bkP i v hv) (τc : D.host.E →+* ℂ) : Prop :=
  ∀ (x : D.host.E) (n d : X.O0 i), IsFrac bkP i v hv (τ (cE bkP i v hv x)) n d → rd i ι d * τc x = rd i ι n

def JumpsAre (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (ι : FractionRing (X.O0 i) →+* ℂ)
    (J : (D.host.E →+* ℂ) → Multiset ℤ) : Prop :=
  ∀ v (hv : v ∈ placesOver D.host.E (X.l i)) (τ : EmbV bkP i v hv) (τc : D.host.E →+* ℂ), ReadEmb bkP i ι v hv τ τc →
    ∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = ((J τc).count a : ℤ)

def GoodJ (D : Formalism.BasicNotions.D7) (J : (D.host.E →+* ℂ) → Multiset ℤ) : Prop :=
  ∀ τc, Multiset.card (J τc) = D.R.r ∧ J (τc.comp (cj D)) = (J τc).map (fun a => (D.R.t : ℤ) - 1 - a) ∧
    ∀ a ∈ J τc, a < -1 ∨ (D.R.t : ℤ) < a

def CharDual (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ g g' : GE N, (∀ x, g' x = X.cc (g (X.cc.symm x))) →
    (Tdual i s g').charpoly = ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g).charpoly

def FrobDual (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → (∀ P', IsConjPl D.host P P' → P' ∉ X.S0 i) →
    ∀ A : ValuationSubring N.Om, IsPlaceOver (F := D.host.E) A P →
    ∀ g g' : GE N, IsFrob (F := D.host.E) A (normV P) g → (∀ x, g' x = X.cc (g (X.cc.symm x))) →
    (Tdual i s g').charpoly = ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g).charpoly

def HkFrob (i : X.Tw) (s : X.Sig i) : Prop :=
  ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → ∀ σ : GE N, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ⁻¹ →
    ∀ k, k ≤ D.R.r → (-1 : X.O i) ^ k * ((normV P : ℕ) : X.O i) ^ (k * (k - 1) / 2) * X.hEig i s k P =
      algebraMap (X.O0 i) (X.O i)
        ((((((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s σ).charpolyRev).coeff k)

open Classical in

structure Att (A : NAut N) (bkP : BKPh X) (i : X.Tw) (ι : FractionRing (X.O0 i) →+* ℂ)
    (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (π : A.CG D.R.r) (sh : ℝ) : Prop where
  unr : ∀ w, w ∉ placesOver D.host.E (X.l i) → A.unr (A.locG π w) → ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 w), ρ σ = 1
  frob : ∀ w, w ∉ placesOver D.host.E (X.l i) → A.unr (A.locG π w) → ∀ (B : ValuationSubring N.Om) (σ : GE N),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).charpoly.map (rd i ι) =
      ((A.frobEig (A.lpTw (A.locG π w) sh)).map fun α => Polynomial.X - C α).prod
  temp : ∀ w, w ∉ placesOver D.host.E (X.l i) → A.tempered (A.locG π w)
  hodge : ∀ v (hv : v ∈ placesOver D.host.E (X.l i)),
    (bkP.br i v hv).IsdRW (D.loc (X.l i)) (ρ.comp (DecV N v).subtype) ∧
    (A.unr (A.locG π v) → (bkP.br i v hv).IsCrysW (D.loc (X.l i)) (ρ.comp (DecV N v).subtype)) ∧
    (A.mono0 (A.locG π v) → (bkP.br i v hv).IsPotCrysW (D.loc (X.l i)) (ρ.comp (DecV N v).subtype))
  jumps : ∀ v (hv : v ∈ placesOver D.host.E (X.l i)) (τ : EmbV bkP i v hv) (τc : D.host.E →+* ℂ),
    ReadEmb bkP i ι v hv τ τc → ∀ a : ℤ,
    Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv ρ) τ a =
      ((((A.infG π τc).map fun z => -z - (sh : ℂ)).count (a : ℂ) : ℕ) : ℤ)

def HkSat (A : NAut N) (i : X.Tw) (s : X.Sig i) (ι : FractionRing (X.O0 i) →+* ℂ) (π : A.CG D.R.r) : Prop :=
  ∀ P, P ∉ X.S0 i → Formalism.BasicNotions.IsSplitPl D.host P → ∀ k, k ≤ D.R.r → ∃ h : X.O0 i,
    X.hEig i s k P = algebraMap (X.O0 i) (X.O i) h ∧
    rd i ι h = ((normV P : ℕ) : ℂ) ^ (((k : ℂ) * ((D.R.r : ℂ) - k)) / 2) *
      ((A.frobEig (A.locG π P)).map fun a => a⁻¹ * ((normV P : ℕ) : ℂ) ^ (-((D.R.r : ℂ) + D.R.t) / 2)).esymm k

structure RowFacts (A : NAut N) (i : X.Tw) (π₁ π : A.CG D.R.r) : Prop where
  unr₁ : ∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → A.unr (A.locG π₁ w)
  mono₁ : ∀ w, A.mono0 (A.locG π₁ w)
  unr : ∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ X.pD i → A.unr (A.locG π w)
  mono : ∀ w, A.mono0 (A.locG π w)
  csd : A.csd π
  ralg : A.ralg π
  anti : ∀ τc, A.infG π (τc.comp (cj D)) = (A.infG π τc).map fun z => -z
  window : ∀ τc, ∀ z ∈ A.infG π τc, ∀ a : ℤ, (a : ℂ) = -z + ((D.R.t : ℂ) - 1) / 2 → a < -1 ∨ (D.R.t : ℤ) < a

def TripleAtt (A : NAut N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) : Prop :=
  ∃ (ι : FractionRing (X.O0 i) →+* ℂ) (π₁ π : A.CG D.R.r),
    Att A bkP i ι (X.rhoS i s) π₁ ((1 - ((D.R.r : ℝ) + D.R.t)) / 2) ∧
    Att A bkP i ι (Tgl i s) π ((1 - (D.R.t : ℝ)) / 2) ∧ RowFacts A i π₁ π ∧ HkSat A i s ι π

end GlobalTheory.TripleGal

end
