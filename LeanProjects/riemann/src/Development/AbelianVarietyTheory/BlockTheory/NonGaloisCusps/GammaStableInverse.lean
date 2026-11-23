import Mathlib
import Formalism.CoboundaryTransfers.Statement
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Inv

variable {A D : Type} [CommRing A] [AddCommGroup D] [Module A D]

def invSub (a : A) (M : Submodule A D) : Submodule A D where
  carrier := {x | ∃ k : ℕ, a ^ k • x ∈ M}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨j, hj⟩ ⟨k, hk⟩
    refine ⟨j + k, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact M.smul_mem _ hj
    · rw [pow_add, mul_smul]
      exact M.smul_mem _ hk
  smul_mem' := by
    rintro c x ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [smul_comm]
    exact M.smul_mem _ hk

theorem invSub_le {a : A} {M M' : Submodule A D} (h : M ≤ invSub a M') :
    invSub a M ≤ invSub a M' := by
  rintro x ⟨k, hk⟩
  obtain ⟨j, hj⟩ := h hk
  exact ⟨j + k, by rwa [pow_add, mul_smul]⟩

end Inv

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N₁ : Submodule (LetA O n) (W.DD T))

def HasCommonBasis : Prop :=
  ∃ (ι : Type) (b : Module.Basis ι (LetA O n) ↥N₁) (b' : Module.Basis ι W.EE (W.DD T)),
    ∀ j, b' j = (b j : W.DD T)

def GammaStable : Prop := W.γ T '' (N₁ : Set (W.DD T)) = (N₁ : Set (W.DD T))

def GammaTrivialModPi : Prop :=
  ∀ x ∈ N₁, ∃ y ∈ N₁, W.γ T x - x = (letπ : LetA O n) • y

def phiSpan : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (N₁ : Set (W.DD T)))

def FrobeniusIsoAwayQ : Prop := invSub W.Q (phiSpan W T N₁) = invSub W.Q N₁

def WachUniqueAt : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ N₁ : Submodule (LetA O n) (W.DD T),
    HasCommonBasis W T N₁ → GammaStable W T N₁ → GammaTrivialModPi W T N₁ →
      FrobeniusIsoAwayQ W T N₁ → N₁ = W.N T

end Generic

def WachUnique (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), WachUniqueAt (H.W K s LL h)

def WachUniqueOfJumps (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (M hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ),
    IsCrys (P.PD K) T.ρ →
    (∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
      (∀ c : ↥(K0 K), τ (algebraMap ↥(K0 K) ↥K.1 c) = (H.W K s LL h).emb i c) →
        JumpsInV (P.PD K) T.ρ τ (Set.Icc (-(M i : ℤ)) (hi i : ℤ))) →
    ∀ N₁ : Submodule (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ((H.W K s LL h).DD T),
      HasCommonBasis (H.W K s LL h) T N₁ → GammaStable (H.W K s LL h) T N₁ →
        GammaTrivialModPi (H.W K s LL h) T N₁ → FrobeniusIsoAwayQ (H.W K s LL h) T N₁ →
          N₁ = (H.W K s LL h).N T

end GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse
