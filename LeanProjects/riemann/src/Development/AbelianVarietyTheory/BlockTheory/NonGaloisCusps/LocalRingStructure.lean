import Mathlib
import Formalism.CoboundaryTransfers.Statement
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def IsOver (i : ZMod n) (τ : K →ₐ[Qp] LL) : Prop :=
  ∀ c : K₀, τ (algebraMap K₀ K c) = W.emb i c

def JumpsBounded (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), IsOver W i τ →
    JumpsInV PD T.ρ τ (Set.Icc (-(M i : ℤ)) (h i : ℤ))

def phiStar (T : LocLat G Qp LL O) (i : ZMod n) : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (W.Nl T (i - 1) : Set (W.DD T)))

def PartA (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ i : ZMod n,
    (∀ y ∈ phiStar W T i, W.Q ^ M i • y ∈ W.Nl T i) ∧
    (∀ y ∈ W.Nl T i, W.Q ^ h i • y ∈ phiStar W T i)

def LocRing (_W : LocWach PD LL O v n) (_i : ZMod n) (_ζ : LL) : Type := PowerSeries LL

instance (i : ZMod n) (ζ : LL) : CommRing (LocRing W i ζ) :=
  inferInstanceAs (CommRing (PowerSeries LL))

instance (i : ZMod n) (ζ : LL) : Algebra (LetA O n) (LocRing W i ζ) :=
  RingHom.toAlgebra (R := LetA O n) (S := LocRing W i ζ) (W.lev i ζ).toRingHom

abbrev Nloc (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) : Type :=
  LocRing W i ζ ⊗[LetA O n] ↥(W.Nl T i)

def MemInv (T : LocLat G Qp LL O) (i : ZMod n) (y : W.DD T) : Prop :=
  ∃ k : ℕ, W.Q ^ k • y ∈ W.Nl T i

def MemLoc (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (y : W.DD T) : Prop :=
  ∃ (k : ℕ) (hk : W.Q ^ k • y ∈ W.Nl T i) (z : Nloc W T i ζ),
    (1 : LocRing W i ζ) ⊗ₜ[LetA O n] (⟨W.Q ^ k • y, hk⟩ : ↥(W.Nl T i)) =
      (algebraMap (LetA O n) (LocRing W i ζ) (W.Q ^ k)) • z

def PartB (T : LocLat G Qp LL O) : Prop :=
  ∀ (i : ZMod n) (y : W.DD T), MemInv W T i y →
    (y ∈ W.Nl T i ↔ ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ W.s) → MemLoc W T i ζ y)

example (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (y : W.DD T) (hy : y ∈ W.Nl T i) :
    MemLoc W T i ζ y :=
  ⟨0, by simpa using hy, (1 : LocRing W i ζ) ⊗ₜ[LetA O n] (⟨y, hy⟩ : ↥(W.Nl T i)), by simp⟩

variable {W} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
  (E : EtTie W RA RW inclR φR gR πA)

def latAinf (_E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  LinearMap.range (TWincl inclR T)

def wachAinf (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  Submodule.span O {w | ∃ (a : RA) (x : W.DD T), x ∈ W.N T ∧ w = inclR a • E.jD T x}

def PartC (T : LocLat G Qp LL O) (M h : ℕ) : Prop :=
  (∀ w ∈ latAinf E T, inclR (E.io W.X) ^ h • w ∈ wachAinf E T) ∧
  (∀ w ∈ wachAinf E T, inclR (E.io W.X) ^ M • w ∈ latAinf E T)

end Generic

open TensorProduct in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure.letters_neZero {l : ℕ} [Fact l.Prime] (K : _root_.Formalism.BasicNotions.Loc.FinExt l) :
    NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := by
  haveI : FiniteDimensional ℚ_[l] ↥(K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := K.2
  have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ (K : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) := inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  exact ⟨Module.finrank_pos.ne'⟩

def letterMax {l : ℕ} [Fact l.Prime] (K : FinExt l)
    (m : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) : ℕ :=
  haveI := letters_neZero K
  Finset.univ.sup m

example {l : ℕ} [Fact l.Prime] (K : FinExt l) (m : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) :
    IsGreatest (Set.range m) (letterMax K m) := by
  haveI := letters_neZero K
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty m
    exact ⟨i, hi.symm⟩
  · rintro _ ⟨i, rfl⟩
    exact Finset.le_sup (f := m) (Finset.mem_univ i)

def HeightsFromJumps (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (_C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (hg : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ M h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ, JumpsBounded (H.W K s LL hg) T M h →
      PartA (H.W K s LL hg) T M h ∧ PartB (H.W K s LL hg) T ∧
        PartC (F.E K s LL hg).tie T (letterMax K M) (letterMax K h)

end GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure
