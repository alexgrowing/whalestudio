import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def eG (i : X.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (X.O i)) (Y.Fm i j b) :=
  MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)) (Y.eAlg i b)

def eO (i : X.Tw) (j : ℕ) (b : Bool) : Module.End (X.O i) (Y.Fm i j b) :=
  (eG Y i j b).restrictScalars (X.O i)

def AO (i : X.Tw) (j : ℕ) (b : Bool) : Module.End (X.O i) (Y.Fm i j b) :=
  ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eO Y i j b

def zO (i : X.Tw) (j : ℕ) (b : Bool) (z : MonoidAlgebra (X.O i) (G0g N)) :
    Module.End (X.O i) (Y.Fm i j b) :=
  (MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b))
    (MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom z)).restrictScalars (X.O i)

def Fm0 (i : X.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  ⨅ u : Y.U, LinearMap.ker ((Y.actG i j b u).toLinearMap -
    ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • LinearMap.id)

def V0 (i : X.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  (Fm0 Y i j b).map (eG Y i j b)

structure ExpDat where
  Dat0 : ∀ i j b, Set (Y.Dat i j b)
  theta_base_equivariant : ∀ i j b, ∀ a ∈ Dat0 i j b, ∀ u : Y.U, Y.actG i j b u (Y.th i j b a) =
    ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • Y.th i j b a

def Th (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) : Submodule (X.O i) (Y.Fm i j b) :=
  Submodule.span (X.O i) (Y.th i j b '' Sg)

def ThPsi (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) (Sg : Set (Y.Dat i j b)) :
    Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  Submodule.span (X.Ok i k) (⋃ a ∈ Sg, Y.thPsi i j b k Q ψ a)

def eTh (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) : Submodule (X.O i) (Y.Fm i j b) :=
  (Th Y i j b Sg).map (eO Y i j b)

def eThPsi (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) (Sg : Set (Y.Dat i j b)) :
    Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  (ThPsi Y i j b k Q ψ Sg).map ((eO Y i j b).baseChange (X.Ok i k))

def eThPMt (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  ((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ)).map ((eO Y i j b).baseChange (X.Ok i k))

def lenR (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (M : Type)
    [AddCommGroup M] [Module R M] : ℝ :=
  ((Module.length R M).toNat : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ)

def sIdx {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W]
    [Module R W] (l : ℕ) (M N' : Submodule R W) : ℝ :=
  lenR R l (M ⧸ N'.comap M.subtype) - lenR R l (N' ⧸ M.comap N'.subtype)

def IsLatIn {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (M V : Submodule R W) : Prop :=
  M.FG ∧ M ≤ V ∧ ∀ x ∈ V, ∃ c : R, c ≠ 0 ∧ c • x ∈ M

def HkIdx (i : X.Tw) (k : ℕ) (P : PlE D.host) : Prop :=
  1 ≤ k ∧ k ≤ D.R.r ∧ Formalism.BasicNotions.IsSplitPl D.host P ∧ P ∉ X.S0 i

def hkO (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) : Module.End (X.O i) (Y.Fm i j b) :=
  (Y.hkF i j b k P).restrictScalars (X.O i)

def TwOK (i : X.Tw) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) : Prop :=
  (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) ∧ Disjoint Q (X.S0 i) ∧ IsOpen (ψ.ker : Set (G D.host.E N.Om)) ∧
    AntiHom X.cc ψ ∧ (∀ g, ψ g ∈ Subgroup.zpowers (X.zk i k)) ∧ RamExactly ψ ↑Q ∧
    Formalism.MainNotions.BlochKatoReduction.Gen.TrivAbove ψ (X.l i)

def UnrG {A : Type} [Group A] (ψ : G D.host.E N.Om →* A) : Prop :=
  ∀ k, ∀ v ∈ placesOver D.host.E (D.host.g k), ∀ A' : ValuationSubring N.Om, IsPlaceOver A' v →
    ∀ σ ∈ Ine (F := D.host.E) A', ψ σ = 1

def specU (i : X.Tw) (j : ℕ) (b : Bool) (Q : Finset (PlE D.host)) (M k : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    (Y.Fm i j b ⊗[X.O i] AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)) →ₗ[X.O i]
      (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  (TensorProduct.comm (X.O i) (Y.Fm i j b) (X.Ok i k)).toLinearMap ∘ₗ
    ((AddMonoidAlgebra.lift (X.O i) (X.Ok i k) (DelQM D.host (X.l i) Q M)
      ((Units.coeHom (X.Ok i k)).comp χ)).toLinearMap.lTensor (Y.Fm i j b))

structure RFam (i : X.Tw) where
  Ball : ∀ j b, Submodule (X.O i) (Y.Fm i j b)
  z : ℕ → Bool → MonoidAlgebra (X.O i) (G0g N)
  B : ∀ j b, Submodule (X.O i) (Y.Fm i j b)
  S : ∀ j b, Finset (Y.Dat i j b)

variable {Y}

def RFam.A {i : X.Tw} (F : RFam Y i) (j : ℕ) (b : Bool) : Module.End (X.O i) (Y.Fm i j b) :=
  zO Y i j b (F.z j b)

def RFam.Th {i : X.Tw} (F : RFam Y i) (j : ℕ) (b : Bool) : Submodule (X.O i) (Y.Fm i j b) :=
  Submodule.span (X.O i) ((fun a => F.A j b (Y.th i j b a)) '' ↑(F.S j b))

variable (Y)

def T3 (i : X.Tw) (j : ℕ) (b : Bool) (B : Submodule (X.O i) (Y.Fm i j b)) : Prop :=
  ∀ x ∈ B, x ∉ (IsLocalRing.maximalIdeal (X.O i)) • B →
    ∀ ev : ℕ → PlE D.host → X.O i,
    (∀ k P, HkIdx i k P →
      hkO Y i j b k P x - ev k P • x ∈ (IsLocalRing.maximalIdeal (X.O i)) • B) →
    ∃ s : X.Sig i, X.jS i s = j ∧ X.side i s = b ∧
      ∀ k P, HkIdx i k P → ev k P - X.hEig i s k P ∈ IsLocalRing.maximalIdeal (X.O i)

def ClsQ (Q : Finset (PlE D.host)) : Prop :=
  ∀ P ∈ Q, ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal)

def ABHyp (i : X.Tw) (F : RFam Y i) (j : ℕ) (b : Bool) : Prop :=

  (F.Ball j b).FG ∧
  (∀ k P, HkIdx i k P → (F.Ball j b).map (hkO Y i j b k P) ≤ F.Ball j b) ∧

  (F.Ball j b).map (F.A j b) ≤ F.Ball j b ∧

  IsLatIn (F.B j b) ((Submodule.span (FractionRing (X.O i))
    (((F.Ball j b).map (F.A j b) : Submodule (X.O i) (Y.Fm i j b)) : Set (Y.Fm i j b))).restrictScalars (X.O i)) ∧
  (F.Ball j b).map (F.A j b) ≤ F.B j b ∧
  (∀ k P, HkIdx i k P → (F.B j b).map (hkO Y i j b k P) ≤ F.B j b) ∧

  LinearIndependent (X.O i) (fun a : ↥(F.S j b) => F.A j b (Y.th i j b a)) ∧
  Submodule.span (FractionRing (X.O i)) ((fun a => F.A j b (Y.th i j b a)) '' ↑(F.S j b)) =
    Submodule.span (FractionRing (X.O i)) (F.B j b : Set (Y.Fm i j b)) ∧

  (∀ x, F.z j b * x = x * F.z j b) ∧
  (∀ k P, HkIdx i k P → F.A j b ∘ₗ hkO Y i j b k P = hkO Y i j b k P ∘ₗ F.A j b) ∧

  (∃ c : ℕ, ∀ Q M, (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (X.S0 i) →
    ∀ a ∈ F.S j b, Disjoint Q (Y.lev i j b a) →
    ((X.l i : X.O i) ^ c) • Y.thU i j b Q M a ∈ LinearMap.range ((F.Ball j b).subtype.rTensor _)) ∧

  T3 Y i j b (F.B j b)

def partAB (i : X.Tw) (F : RFam Y i) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) : Prop :=
  ∃ (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k')ˣ),
    ψ'.comp (X.art i Q) = χ.comp (Y.delU i Q M) ∧
    ∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧
      ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
      ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
        ∀ Tψ : Submodule (X.Ok i k') (X.Ok i k' ⊗[X.O i] Y.Fm i j b),
          IsLatIn Tψ (((Submodule.span (FractionRing (X.O i)) (F.B j b : Set (Y.Fm i j b))).restrictScalars
            (X.O i)).baseChange (X.Ok i k')) →
          (∀ a ∈ F.S j b, ((F.A j b).baseChange (X.Ok i k'))
            (specU Y i j b Q M k' (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b χ) (Y.thU i j b Q M a)) ∈ Tψ) →
          sIdx (X.l i) ((F.B j b).baseChange (X.Ok i k')) Tψ ≤ sIdx (X.l i) (F.B j b) (F.Th j b) + epsB j b

variable (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)

def TwistingCharacterExistence (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ABHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
      Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i A0 Q k' ψ' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partAT bkP i Q k' ψ' eps' ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.partC N0 i Q k' ψ' eps' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partD i Q k' ψ' eps' ∧
      partAB Y i F Q k' ψ' eps'

variable (E : ExpDat Y)

def FullRk (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) : Prop :=
  Sg ⊆ E.Dat0 i j b ∧
  (∀ x ∈ (Th Y i j b Sg).map (AO Y i j b), x ∈ V0 Y i j b) ∧
  Submodule.span (FractionRing (X.O i))
      (((Th Y i j b Sg).map (AO Y i j b) : Submodule (X.O i) (Y.Fm i j b)) : Set (Y.Fm i j b)) =
    V0 Y i j b

def BasisOf (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) (S : Finset (Y.Dat i j b)) : Prop :=
  (↑S ⊆ Sg) ∧ LinearIndependent (X.O i) (fun a : ↥S => AO Y i j b (Y.th i j b a)) ∧
  Submodule.span (X.O i) ((fun a => AO Y i j b (Y.th i j b a)) '' ↑S) = (Th Y i j b Sg).map (AO Y i j b)

open Classical in

def levs (i : X.Tw) (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) : Finset (PlE D.host) :=
  (Finset.Icc 1 D.R.m).biUnion fun j =>
    (Finset.univ : Finset Bool).biUnion fun b => (S j b).biUnion (Y.lev i j b)

def SgJ (i : X.Tw) (j : ℕ) (b : Bool) : Set (Y.Dat i j b) := E.Dat0 i j b

def ThJ (i : X.Tw) (j : ℕ) (b : Bool) : Submodule (X.O i) (Y.Fm i j b) := Th Y i j b (SgJ Y E i j b)

def ThSub (Sg0 : ∀ (i : X.Tw) (j : ℕ) (b : Bool), Set (Y.Dat i j b)) : Prop :=
  ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, Th Y i j b (Sg0 i j b) ≤ ThJ Y E i j b

def IdxAt (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) (e : ℝ) : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.Ok i k) O']
    [Algebra (X.O i) O'] [IsScalarTower (X.O i) (X.Ok i k) O'],
    Function.Injective (algebraMap (X.Ok i k) O') → Module.Finite (X.Ok i k) O' →
    ∀ M : Submodule O' (O' ⊗[X.O i] Y.Fm i j b),
      IsLatIn M (((V0 Y i j b).restrictScalars (X.O i)).baseChange O') →
      sIdx (X.l i) M (Submodule.span O'
          ((LinearMap.rTensor (Y.Fm i j b) (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O').toLinearMap) ''
            (eThPsi Y i j b k Q ψ Sg : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)))) ≤
        sIdx (X.l i) M ((eTh Y i j b Sg).baseChange O') + e

def InclAt (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) : Prop :=
  eThPsi Y i j b k Q ψ Sg ≤ eThPMt Y i j b k Q ψ

open Classical in

def GoodTw (N0 : X.Tw → ℕ) (i : X.Tw) (eps' : ℝ)
    (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) (A : Finset (PlE D.host)) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i (levs Y i S ∪ A) Q k' ψ' ∧
    (∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧
      ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
      ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
        IdxAt Y i j b (SgJ Y E i j b) k' Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ'.comp (X.art i Q))) (epsB j b)) ∧
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IsLatIn (eThPsi Y i j b k' Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ'.comp (X.art i Q))) (SgJ Y E i j b))
        (((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k')) ∧
      InclAt Y i j b (SgJ Y E i j b) k' Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ'.comp (X.art i Q)))) ∧
    Formalism.MainNotions.BlochKatoReduction.Gen.partAT bkP i Q k' ψ' eps' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partC N0 i Q k' ψ' eps' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partD i Q k' ψ' eps'

def TwistTheoremAtIndex (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    GoodTw Y bkP E N0 i eps' S A Q k' ψ'

def Mall (i : X.Tw) (j : ℕ) (b : Bool) : Submodule (X.O i) (Y.Fm i j b) :=
  Y.Bsup i j b ⊓ (Fm0 Y i j b).restrictScalars (X.O i)

def IsotypicPartsInternalDirectSum : Prop :=
  ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool),
    (∀ g, (Y.Bsup i j b).map ((Y.actG i j b g).toLinearMap.restrictScalars (X.O i)) ≤ Y.Bsup i j b) ∧
    (Mall Y i j b).FG ∧
    Submodule.span (FractionRing (X.O i)) (Mall Y i j b : Set (Y.Fm i j b)) = Fm0 Y i j b ∧
    (∀ k P, HkIdx i k P → (Mall Y i j b).map (hkO Y i j b k P) ≤ Mall Y i j b) ∧
    (∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M, (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q →
      Disjoint Q (X.S0 i) → Disjoint Q (Y.lev i j b a) →
      ((X.l i : X.O i) ^ c) • Y.thU i j b Q M a ∈ LinearMap.range ((Mall Y i j b).subtype.rTensor _)) ∧
    (∀ k Q (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ →
      ∀ a ∈ E.Dat0 i j b,
      Y.thPsi i j b k Q ψ a ⊆
        ((((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) :
          Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)))

def Eigsp (i : X.Tw) (j : ℕ) (b : Bool) (ev : ℕ → PlE D.host → FractionRing (X.O i)) :
    Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  ⨅ k, ⨅ P, ⨅ (_ : HkIdx i k P), LinearMap.ker (Y.hkF i j b k P - ev k P • LinearMap.id)

def GStable (i : X.Tw) (j : ℕ) (b : Bool) (W : Submodule (FractionRing (X.O i)) (Y.Fm i j b)) : Prop :=
  ∀ g x, x ∈ W → Y.actG i j b g x ∈ W

def GIrred (i : X.Tw) (j : ℕ) (b : Bool) (W : Submodule (FractionRing (X.O i)) (Y.Fm i j b)) : Prop :=
  W ≠ ⊥ ∧ GStable Y i j b W ∧ ∀ W' ≤ W, GStable Y i j b W' → W' = ⊥ ∨ W' = W

def GroupAlgebraIntegrality : Prop :=
  ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ (b : Bool),
    (∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b) ∧
    ∀ j ∈ Finset.Icc 1 D.R.m,
      (∀ g k P, HkIdx i k P →
        (Y.actG i j b g).toLinearMap ∘ₗ Y.hkF i j b k P = Y.hkF i j b k P ∘ₗ (Y.actG i j b g).toLinearMap) ∧
      (∀ ev W, W ≤ Eigsp Y i j b ev → GIrred Y i j b W →
        (∀ x ∈ W, eG Y i j b x = x) ∨ (∀ x ∈ W, eG Y i j b x = 0))

def admT4 : Prop :=
  ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), TwOK i k Q ψ →
    ∀ Sg : Set (Y.Dat i j b), Sg ⊆ E.Dat0 i j b →
      ThPsi Y i j b k Q ψ Sg ≤ (Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ)

def GoodLatticePoints : Prop :=
  ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    T3 Y i j b (Mall Y i j b ⊓ (V0 Y i j b).restrictScalars (X.O i))

def TwistedSeriesSpecialisation : Prop :=
  ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → ∀ a : Y.Dat i j b, Disjoint Q (Y.lev i j b a) →
      specU Y i j b Q M k χ (Y.thU i j b Q M a) ∈ ThPsi Y i j b k Q (χ.comp (Y.delU i Q M)) {a}

abbrev XD (D : Formalism.BasicNotions.D7) : Type := ExpDat D.nexp

def aux₃ (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → TwistTheoremAtIndex D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) E N0 i

def adm1 (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.aux₃ D bkP N0

def adm2 (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  TwistingCharacterExistence D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0

def adm3 (D : Formalism.BasicNotions.D7) (E : XD D) : Prop := IsotypicPartsInternalDirectSum D.nexp E

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.ArithmeticCylinders.PointsLemma D

def adm5 (D : Formalism.BasicNotions.D7) : Prop := GroupAlgebraIntegrality D.nexp

def adm7 (D : Formalism.BasicNotions.D7) (E : XD D) : Prop := admT4 D.nexp E

def adm8 (D : Formalism.BasicNotions.D7) (N0 : D.ntw.Tw → ℕ) : Prop := Formalism.MainNotions.BlochKatoReduction.adm9 D N0

def adm9 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.BlochKatoReduction.adm10 D

def adm10 (D : Formalism.BasicNotions.D7) : Prop := TwistedSeriesSpecialisation D.nexp

def adm11 (D : Formalism.BasicNotions.D7) : Prop := GoodLatticePoints D.nexp

def admitted (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : XD D)
    (N0 : D.ntw.Tw → ℕ) : Prop :=
  adm1 D bkP N0 ∧ adm2 D bkP N0 ∧ adm3 D E ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm7 D E ∧
    adm8 D N0 ∧ adm9 D ∧ adm10 D ∧ adm11 D

def Stmt (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : XD D) :
    Prop :=
  ∀ N0 : D.ntw.Tw → ℕ, admitted D bkP E N0 → aux₃ D bkP E N0

end Formalism.MainNotions.IntegralHeckeForms

end
