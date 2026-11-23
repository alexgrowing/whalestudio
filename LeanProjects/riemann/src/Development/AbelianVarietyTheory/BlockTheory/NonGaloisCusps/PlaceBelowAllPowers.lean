import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlaceBelowAllPowers

open Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def placeBelow (i : X.Tw) (b : Bool) : Set (𝓞 ↥D.LL0) :=
  {x | ∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i),
    algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = (if b then X.emb0 i else X.emb0b i) (x : ↥D.LL0)}

def SamePlace (i : X.Tw) (b : Bool) (i' : X.Tw) (b' : Bool) : Prop :=
  X.l i' = X.l i ∧ placeBelow i' b' = placeBelow i b

def IsReading (i i' : X.Tw) (k : ℕ) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (φ : G D.host.E N.Om →* (X.Ok i' k)ˣ) : Prop :=
  ∃ a : ℤ, IsCoprime a (X.l i : ℤ) ∧
    ∀ g, ∃ n : ℤ, ψ g = X.zk i k ^ n ∧ φ g = X.zk i' k ^ (a * n)

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X) (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (E : ExpDat Y)

def PartBAt (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (φ : G D.host.E N.Om →* (X.Ok i k)ˣ) (e : ℝ) : Prop :=
  IsLatIn (eThPsi Y i j b k Q φ (SgJ Y E i j b)) (((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)) ∧
    IdxAt Y i j b (SgJ Y E i j b) k Q φ e ∧ InclAt Y i j b (SgJ Y E i j b) k Q φ

def AllPowersGood (N0 : X.Tw → ℕ) (i : X.Tw) (eps' : ℝ) (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b))
    (A Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, IsCoprime a (X.l i : ℤ) → GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

def PartBAbove (i : X.Tw) (eps' : ℝ) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  ∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧
    ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
    ∀ (b : Bool) (i' : X.Tw) (b' : Bool), SamePlace i b i' b' → Disjoint Q (X.S0 i') →
      ∀ φ : G D.host.E N.Om →* (X.Ok i' k')ˣ, IsReading i i' k' (ψ'.comp (X.art i Q)) φ →
        ∀ j ∈ Finset.Icc 1 D.R.m,
          IsLatIn (eTh Y i' j b' (SgJ Y E i' j b')) ((V0 Y i' j b').restrictScalars (X.O i')) →
          PartBAt Y E i' j b' k' Q φ (epsB j b)

def AllAt (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    AllPowersGood Y bkP E N0 i eps' S A Q k' ψ' ∧ PartBAbove Y E i eps' Q k' ψ'

def AllPowersAt (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    AllPowersGood Y bkP E N0 i eps' S A Q k' ψ'

def AllConjugatesGood (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → AllAt D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) E N0 i

def AllPowers (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → AllPowersAt D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) E N0 i

theorem samePlace_refl (i : X.Tw) (b : Bool) : SamePlace i b i b := ⟨rfl, rfl⟩

theorem isReading_zpow (i : X.Tw) (k : ℕ) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (hψ : ∀ g, ψ g ∈ Subgroup.zpowers (X.zk i k)) (a : ℤ) (ha : IsCoprime a (X.l i : ℤ)) :
    IsReading i i k ψ (ψ ^ a) := by
  refine ⟨a, ha, fun g => ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hψ g)
  refine ⟨n, hn.symm, ?_⟩
  rw [mul_comm, zpow_mul, hn]
  rfl

variable {Y bkP E}

theorem AllPowersGood.self_inv {N0 : X.Tw → ℕ} {i : X.Tw} {eps' : ℝ}
    {S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)} {A Q : Finset (PlE D.host)} {k' : ℕ}
    {ψ' : X.RCG i Q →* (X.Ok i k')ˣ} (h : AllPowersGood Y bkP E N0 i eps' S A Q k' ψ') :
    GoodTw Y bkP E N0 i eps' S A Q k' ψ' ∧ GoodTw Y bkP E N0 i eps' S A Q k' ψ'⁻¹ := by
  refine ⟨?_, ?_⟩
  · simpa using h 1 isCoprime_one_left
  · simpa using h (-1) isCoprime_one_left.neg_left

theorem AllConjugatesGood.allPowers {D : Formalism.BasicNotions.D7} {bkP : Formalism.MainNotions.BlochKatoReduction.BK D} {E : XD D} {N0 : D.ntw.Tw → ℕ}
    (h : AllConjugatesGood D bkP E N0) : AllPowers D bkP E N0 := by
  intro i hi hs eps' he hF S hS A
  obtain ⟨Q, k', ψ', h1, -⟩ := h i hi hs eps' he hF S hS A
  exact ⟨Q, k', ψ', h1⟩

theorem AllPowers.aux₃ {D : Formalism.BasicNotions.D7} {bkP : Formalism.MainNotions.BlochKatoReduction.BK D} {E : XD D} {N0 : D.ntw.Tw → ℕ}
    (h : AllPowers D bkP E N0) : Formalism.MainNotions.IntegralHeckeForms.aux₃ D bkP E N0 := by
  intro i hi hs eps' he hF S hS A
  obtain ⟨Q, k', ψ', h1⟩ := h i hi hs eps' he hF S hS A
  exact ⟨Q, k', ψ', h1.self_inv.1⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PlaceBelowAllPowers

end
