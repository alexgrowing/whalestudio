import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.CoboundaryTransfers.Statement

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

abbrev rk : ℕ := finrank O ↥T.L.T

abbrev letterModule (i : ZMod n) : Module (PowerSeries O) ↥(W.Nl T i) :=
  Module.compHom _ (Pi.constRingHom (ZMod n) (PowerSeries O))

attribute [local instance] letterModule

open Module in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul (i : ZMod n) (c : PowerSeries O)
    (x : ↥(W.Nl T i)) :
    ((c • x : ↥(W.Nl T i)) : W.DD T) = (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • (x : W.DD T) := by
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ Submodule.map (_root_.Formalism.BasicNotions.letE i • LinearMap.id) (W.N T) := hx
  obtain ⟨y, -, rfl⟩ := Submodule.mem_map.mp hx'
  change (Pi.constRingHom (ZMod n) (PowerSeries O) c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y) =
    (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y)
  rw [smul_smul, smul_smul]
  congr 1
  unfold _root_.Formalism.BasicNotions.letE
  ext j : 1
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

abbrev LetterBasis (i : ZMod n) : Type := Basis (Fin (rk T)) (PowerSeries O) ↥(W.Nl T i)

def LettersDecompose : Prop := iSupIndep (W.Nl T) ∧ ⨆ i, W.Nl T i = W.N T

def LettersFree : Prop := ∀ i : ZMod n, Nonempty (LetterBasis W T i)

def GlobalBasis : Prop :=
  ∃ b : Basis (Fin (rk T)) (LetA O n) ↥(W.N T),
    LinearIndependent W.EE (fun j => (b j : W.DD T)) ∧
      Submodule.span W.EE (Set.range fun j => (b j : W.DD T)) = ⊤

def phiPullLetter (i : ZMod n) : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (W.Nl T (i - 1) : Set (W.DD T)))

def LetterSandwich (M₀ h₀ : ℕ) : Prop :=
  ∀ i : ZMod n, (∀ y ∈ W.Nl T i, W.Q ^ h₀ • y ∈ phiPullLetter W T i) ∧
    (∀ z ∈ phiPullLetter W T i, W.Q ^ M₀ • z ∈ W.Nl T i)

def Sandwich (M₀ h₀ : ℕ) : Prop :=
  (∀ x ∈ W.N T, W.Q ^ M₀ • W.φD T x ∈ W.N T) ∧ (∀ y ∈ W.N T, W.Q ^ h₀ • y ∈ W.φpull T)

variable {W T}

def rowMul {i : ZMod n} (b : LetterBasis W T i)
    (R : Matrix (Fin (rk T)) (Fin (rk T)) (PowerSeries O)) (k : Fin (rk T)) : W.DD T :=
  ((∑ j, R j k • b j : ↥(W.Nl T i)) : W.DD T)

def FrobMatrices (b : ∀ i, LetterBasis W T i) (M₀ h₀ : ℕ) : Prop :=
  ∀ i : ZMod n, ∃ R R' : Matrix (Fin (rk T)) (Fin (rk T)) (PowerSeries O),
    (∀ k, W.Q ^ M₀ • W.φD T (b (i - 1) k : W.DD T) = rowMul (b i) R k) ∧
      R * R' = (W.Q i ^ (M₀ + h₀)) • (1 : Matrix _ _ _) ∧
      R' * R = (W.Q i ^ (M₀ + h₀)) • (1 : Matrix _ _ _)

def GammaMatrices (b : ∀ i, LetterBasis W T i) : Prop :=
  ∀ (g : W.Gam) (i : ZMod n), ∃ Gm : GL (Fin (rk T)) (PowerSeries O),
    ∀ k, W.γD T g (b i k : W.DD T) = rowMul (b i) (Gm : Matrix _ _ _) k

variable (W T)

def Matrices : Prop :=
  ∀ b : ∀ i, LetterBasis W T i,
    GammaMatrices b ∧ (∃ M₀ h₀, FrobMatrices b M₀ h₀) ∧
      ∀ M₀ h₀, FrobMatrices b M₀ h₀ → LetterSandwich W T M₀ h₀

def FreeAt : Prop :=
  LettersDecompose W T ∧ LettersFree W T ∧ GlobalBasis W T ∧
    (∃ M₀ h₀, Sandwich W T M₀ h₀) ∧ Matrices W T

theorem phi_letE (i : ZMod n) : W.φA (letE (i - 1)) = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [LocWach.φA, letφ, letE]
  · have h' : j - 1 ≠ i - 1 := fun e => h (sub_left_injective e)
    simp [LocWach.φA, letφ, letE, h, h']

end Generic

def LettersFreeOfRank (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → FreeAt (H.W K s LL h) T

end GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
