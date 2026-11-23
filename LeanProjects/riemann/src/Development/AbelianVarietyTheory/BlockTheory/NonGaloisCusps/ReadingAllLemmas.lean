import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LemmaAtAllGoodPlaces

section Gen

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)
  (bkP : BlochKatoReduction.Gen.BKPh X) (E : IntegralHeckeForms.ExpDat Y)

def GoodAll (N0 : X.Tw → ℕ) (i : X.Tw) (eps' : ℝ)
    (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) (A Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, IsCoprime a (X.l i : ℤ) → IntegralHeckeForms.GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

def LemmaAllAt (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk Y E i j b (IntegralHeckeForms.SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf Y i j b (IntegralHeckeForms.SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    GoodAll Y bkP E N0 i eps' S A Q k' ψ'

abbrev Reading (i : X.Tw) : Type :=
  ∀ (j : ℕ) (b : Bool) (k : ℕ) (_ : Finset (PlE D.host)) (_ : G D.host.E N.Om →* (X.Ok i k)ˣ),
    Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) × Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)

def ownReading (i : X.Tw) : Reading Y i := fun j b k Q ψ =>
  (IntegralHeckeForms.ThPsi Y i j b k Q ψ (IntegralHeckeForms.SgJ Y E i j b), (Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ))

def PartBFor (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ)
    (L : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) ×
      Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) (e : ℝ) : Prop :=
  (∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.Ok i k) O']
    [Algebra (X.O i) O'] [IsScalarTower (X.O i) (X.Ok i k) O'],
    Function.Injective (algebraMap (X.Ok i k) O') → Module.Finite (X.Ok i k) O' →
    ∀ M : Submodule O' (O' ⊗[X.O i] Y.Fm i j b),
      IntegralHeckeForms.IsLatIn M (((IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).baseChange O') →
      IntegralHeckeForms.sIdx (X.l i) M (Submodule.span O'
                         ((LinearMap.rTensor (Y.Fm i j b) (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O').toLinearMap) ''
                           (L.1.map ((IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)))) ≤
        IntegralHeckeForms.sIdx (X.l i) M ((IntegralHeckeForms.eTh Y i j b (IntegralHeckeForms.SgJ Y E i j b)).baseChange O') + e) ∧
  IntegralHeckeForms.IsLatIn (L.1.map ((IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k)))
    (((IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)) ∧
  L.1.map ((IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k)) ≤ L.2.map ((IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k))

def GoodAllRead (N0 : X.Tw → ℕ) (i : X.Tw) (Rd : Set (Reading Y i)) (eps' : ℝ)
    (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) (A Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  GoodAll Y bkP E N0 i eps' S A Q k' ψ' ∧
  ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
    ∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧
      ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
      ∀ ρ ∈ insert (ownReading Y E i) Rd, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
        PartBFor Y E i j b k' (ρ j b k' Q (BlochKatoReduction.Gen.psiAt b ((ψ' ^ a).comp (X.art i Q)))) (epsB j b)

def LemmaAllReadAt (N0 : X.Tw → ℕ) (i : X.Tw) (Rd : Set (Reading Y i)) : Prop :=
  BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk Y E i j b (IntegralHeckeForms.SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf Y i j b (IntegralHeckeForms.SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    GoodAllRead Y bkP E N0 i Rd eps' S A Q k' ψ'

variable {Y bkP E}

theorem GoodAll.goodTw {N0 : X.Tw → ℕ} {i : X.Tw} {eps' : ℝ}
    {S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)} {A Q : Finset (PlE D.host)} {k' : ℕ}
    {ψ' : X.RCG i Q →* (X.Ok i k')ˣ} (h : GoodAll Y bkP E N0 i eps' S A Q k' ψ') :
    IntegralHeckeForms.GoodTw Y bkP E N0 i eps' S A Q k' ψ' := by
  have := h 1 isCoprime_one_left
  rwa [zpow_one] at this

end Gen

def LemmaAll (D : Formalism.BasicNotions.D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → LemmaAllAt D.nexp (BlochKatoReduction.pin bkP) E N0 i

def LemmaAllCM (D : Formalism.BasicNotions.D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) : Prop :=
  ∀ N0 : D.ntw.Tw → ℕ, BlochKatoReduction.adm9 D N0 → LemmaAll D bkP E N0

def LemmaAllRead (D : Formalism.BasicNotions.D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ)
    (Rd : ∀ i, Set (Reading D.nexp i)) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → LemmaAllReadAt D.nexp (BlochKatoReduction.pin bkP) E N0 i (Rd i)

theorem LemmaAll.aux₃ {D : Formalism.BasicNotions.D7} {bkP : BlochKatoReduction.BK D} {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ}
    (h : LemmaAll D bkP E N0) : IntegralHeckeForms.aux₃ D bkP E N0 := by
  intro i hi hs eps' he hF S hS A
  obtain ⟨Q, k', ψ', hg⟩ := h i hi hs eps' he hF S hS A
  exact ⟨Q, k', ψ', hg.goodTw⟩

end GlobalTheory.IndefiniteRowSideFullHecke.LemmaAtAllGoodPlaces

end
