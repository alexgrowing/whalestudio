import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt

abbrev SigFam : Type 1 :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), IrrGL (w.adicCompletion E) → WD h

abbrev BCRel : Type 1 :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)),
    IrrGL (v.adicCompletion K) → IrrGL (u.adicCompletion L) → Prop

section Cyc

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def CycAt (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) : Prop :=
  IsGalois K L ∧ (Module.finrank K L).Prime ∧ u.under (𝓞 K) = v ∧
    ∀ u' : HeightOneSpectrum (𝓞 L), u'.under (𝓞 K) = v → u' = u

def Conj {u : HeightOneSpectrum (𝓞 L)} (s : L ≃ₐ[K] L) (Y Y' : IrrGL (u.adicCompletion L)) : Prop :=
  ∃ i : u.adicCompletion L ≃+* u.adicCompletion L, Continuous i ∧
    (∀ x : L, i (algebraMap L _ x) = algebraMap L _ (s x)) ∧ RepRel i Y Y'

variable (L) in

def KillsNorms {v : HeightOneSpectrum (𝓞 K)} (η : (v.adicCompletion K)ˣ →* ℂˣ) : Prop :=
  ∀ (z : L) (y : (v.adicCompletion K)ˣ), (y : v.adicCompletion K) = algebraMap K _ (Algebra.norm K z) → η y = 1

variable (K) in

def IsOrbitProd {u : HeightOneSpectrum (𝓞 L)} (Y : (L ≃ₐ[K] L) → IrrGL (u.adicCompletion L))
    (X : IrrGL (u.adicCompletion L)) : Prop :=
  (∀ s, (Y s).IsCusp ∧ Conj s (Y 1) (Y s)) ∧ Function.Injective Y ∧
    ∃ (g : ℕ) (e : Fin g ≃ (L ≃ₐ[K] L)) (hd : ∑ i, (Y (e i)).1 = X.1), Nonempty (X.rep.Equiv (prodIrr (fun i => Y (e i)) hd))

end Cyc

section Loc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

structure LocLaws (h : IsPlaceOver A w) (r : IrrGL (w.adicCompletion E) → WD h) : Prop where

  dim : ∀ x, (r x).lpDim = x.1

  mono : ∀ x, (r x).mono0

  one : ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) χ hχ,
    r (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)

  ind : ∀ (t : ℕ) (y : Fin t → IrrGL (w.adicCompletion E)) (x : IrrGL (w.adicCompletion E)) (hd : ∑ i, (y i).1 = x.1),
    IsSubquotient x.rep (prodIrr y hd) → r x = sumList (List.ofFn fun i => r (y i))

  twist : ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) x χ hχ,
    r (x.tw χ hχ) = (r x).lpTwist (χ.comp a) (ha.smooth hχ)

  iw : ∀ x, (r x).unr → fixed x.rep (iwahori (w.adicCompletion E) (Fin x.1)) ≠ ⊥

def BijDeg (h : IsPlaceOver A w) (r : IrrGL (w.adicCompletion E) → WD h) (n : ℕ) : Prop :=
  Set.BijOn r {x | x.IsCusp ∧ x.1 = n} {y | IsIrrWD y ∧ y.lpDim = n}

variable (h : IsPlaceOver A w) in

def UnrOn (U : Subgroup (Weil h)) (y : WD h) : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = y ∧ ∀ σ : Ine (F := E) A, ineIncl h σ ∈ U → a.ρ (ineIncl h σ) = 1

variable (h : IsPlaceOver A w) in

def IsLevel (U : Subgroup (Weil h)) (N : ℕ) : Prop :=
  U.Normal ∧ U.index = N ∧ 0 < N ∧ IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ U}

end Loc

structure FunctExt (BC : BCRel) (σ : SigFam) : Prop where

  loc : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), LocLaws h (σ E Ω A w h)

  nat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω')
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E')
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i →
    ∀ x x', RepRel i x x' → WDRel φ (σ E Ω A w h x) (σ E' Ω' A' w' h' x')

  bc : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A u),
    CycAt v u → ∀ x X, x.IsCusp → BC K L v u x X → GlobalTheory.AboveL.Restricts (σ K Ω A v h x) (σ L Ω A u h' X)

structure LocalBCAt {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {u : HeightOneSpectrum (𝓞 L)}
    (B : IrrGL (v.adicCompletion K) → IrrGL (u.adicCompletion L) → Prop) : Prop where

  ex : ∀ x, x.IsCusp → ∃! X, B x X

  shape : ∀ x X, x.IsCusp → B x X → X.IsCusp ∨ ((∃ Y, IsOrbitProd K Y X) ∧ ∀ η hη, KillsNorms L η → x.tw η hη = x)

  desc : ∀ X, X.IsCusp → (∀ s : L ≃ₐ[K] L, Conj s X X) → ∃ x, x.IsCusp ∧ B x X

  ind : ∀ Y : (L ≃ₐ[K] L) → IrrGL (u.adicCompletion L), (∀ s, (Y s).IsCusp ∧ Conj s (Y 1) (Y s)) → Function.Injective Y →
    ∃ x X, x.IsCusp ∧ B x X ∧ IsOrbitProd K Y X

  fib : ∀ x x' X, x.IsCusp → x'.IsCusp → B x X → B x' X → ∃ η hη, KillsNorms L η ∧ x' = x.tw η hη

def LocalBC (BC : BCRel) : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)), CycAt v u → LocalBCAt (BC K L v u)

abbrev clS {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a : ℕ}
    (τ : SmIrr (GL (Fin a) k)) : IrrGL k := IrrGL.of τ.ρ τ.smooth τ.irred

def StrongBC (BC : BCRel) : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)), CycAt v u →
    ∀ (n c : ℕ) (π : CuspSub K n) (m : Fin c → ℕ) (P : ∀ i, CuspSub L (m i)), 1 ≤ n → (∀ i, 1 ≤ m i) →
    UpperTheory.V.Published.WeakBC (CG.mk π).HasSat
      (fun w B => ∃ B' : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (B' i)) ∧ B = ∑ i, B' i) →
    ∀ (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (T : ∀ i, SmIrr (GL (Fin (m i)) (u.adicCompletion L))),
    π.IsLocComp v τ → (∀ i, (P i).IsLocComp u (T i)) →
    ∀ (t : ℕ) (x : Fin t → IrrGL (v.adicCompletion K)) (X : Fin t → IrrGL (u.adicCompletion L))
      (S : Fin t → Multiset (IrrGL (u.adicCompletion L))) (S' : Fin c → Multiset (IrrGL (u.adicCompletion L))),
    HasSupport τ.ρ (Finset.univ.val.map x) → (∀ j, BC K L v u (x j) (X j) ∧ HasSupport (X j).rep (S j)) →
    (∀ i, HasSupport (T i).ρ (S' i)) → ∑ i, S' i = ∑ j, S j

def GoodCM (E : Type) [Field E] [NumberField E] : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E))

def GlobalRep (σ : SigFam) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → GoodCM E →
    ∀ π : CuspSub E n, GlobalTheory.ContraPair.DualIsConj π → (CG.mk π).IsRegAlg →
    (∃ (x : HeightOneSpectrum (𝓞 E)) (τ : SmIrr (GL (Fin n) (x.adicCompletion E))),
      GlobalTheory.UnitaryBC.IsSplitAt x ∧ π.IsLocComp x τ ∧ IsCuspidal τ.ρ) →
    ∃ (a : ℕ) (j : ℤ) (R : G E Ω →* GL (Fin (a * n)) (Qbar l)), 1 ≤ a ∧ Continuous R ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (τ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w τ → ∀ g : Weil h,
        ι (R (g : G E Ω)).val.trace =
          (a : ℂ) * GlobalTheory.DelEps.trW ((σ E Ω A w h (clS τ)).lpTw ((1 - (n : ℝ)) / 2 + j)) g

section Ind

variable (K : Type) {L Ω : Type} [Field K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]

open Classical in

def wval (χ : HChar L) (A : ValuationSubring Ω) (γ : G K Ω) : ℂ :=
  if hx : ∃ z : ℂˣ, ∃ (u : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A u) (a : Weil h →* (u.adicCompletion L)ˣ)
      (τ : Weil h), IsLocalArtin h a ∧ GlobalTheory.DelGlob.resG K L Ω τ = γ ∧
        z = χ.1 (localIdele L u (a τ)) then (hx.choose : ℂ) else 0

def indTr (χ : HChar L) (A : ValuationSubring Ω) (g : G K Ω) : ℂ :=
  ∑ᶠ q : G K Ω ⧸ (GlobalTheory.DelGlob.resG K L Ω).range,
    wval K χ (A.comap (q.out : Ω →+* Ω)) (q.out⁻¹ * g * q.out)

end Ind

def Assoc (σ : SigFam) {K L : Type} (Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] {n : ℕ}
    (π : CuspSub K n) (χ : HChar L) : Prop :=
  ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w)
    (τ : SmIrr (GL (Fin n) (w.adicCompletion K))), π.IsLocComp w τ → ∀ g : Weil h,
    GlobalTheory.DelEps.trW (σ K Ω A w h (clS τ)) g = indTr K χ A g

structure IndData (K L M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [IsCMField L]
    [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L Ω] [IsScalarTower K M Ω]
    (χ : HChar L) (p : (L →+* ℂ) → ℤ) : Prop where

  good : GoodCM K

  tower : ∀ z : L, algebraMap M Ω (algebraMap L M z) = algebraMap L Ω z

  gal : IsGalois K M

  solv : IsSolvable (M ≃ₐ[K] M)

  csd : GlobalTheory.ContraPair.DualIsConj ((CuspSub.triv L (le_refl 1)).twist χ)

  inf : ∀ τ, (CG.ofChar χ).HasInfChar τ {(p τ : ℂ)}

  reg : ∀ τ τ' : L →+* ℂ, τ.comp (algebraMap K L) = τ'.comp (algebraMap K L) → p τ = p τ' → τ = τ'

  place : ∃ (A : ValuationSubring Ω) (x : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A x) (y : HeightOneSpectrum (𝓞 M))
    (h' : IsPlaceOver A y), GlobalTheory.UnitaryBC.IsSplitAt x ∧ IsLocalExt M h ∧ ∀ g : Weil h,
      (∀ τ : Weil h', wval K χ A ((g : G K Ω)⁻¹ * GlobalTheory.DelGlob.resG K M Ω τ * g) = wval K χ A (GlobalTheory.DelGlob.resG K M Ω τ)) →
      (g : G K Ω) ∈ (GlobalTheory.DelGlob.resG K L Ω).range

end GlobalTheory.FunExt

end
