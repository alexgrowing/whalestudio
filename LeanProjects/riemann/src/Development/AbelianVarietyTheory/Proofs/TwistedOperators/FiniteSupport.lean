import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KerLe {A B Z₁ Z₂ : Type} [AddCommMonoid Z₁] [AddCommMonoid Z₂] (q₁ : A → B → Z₁) (q₂ : A → B → Z₂) : Prop :=
  ∀ (n : ℕ) (a : Fin n → A) (b : Fin n → B), ∑ i, q₁ (a i) (b i) = 0 → ∑ i, q₂ (a i) (b i) = 0

def AbsIrr {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) : Prop :=
  (∀ N : Submodule ℂ K, (∀ g, ∀ x ∈ N, a g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
    ∀ T : Module.End ℂ K, (∀ g, T ∘ₗ a g = a g ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id

def intersection_update_fsHerm_neg_one {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι) (f : Module.End ℂ (K i)) :
    Module.End ℂ (⨂[ℂ] j, K j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) i f)

theorem position_tprod {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι)
    (f : Module.End ℂ (K i)) (v : ∀ j, K j) :
    intersection_update_fsHerm_neg_one i f (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v i (f (v i))) := by
  unfold intersection_update_fsHerm_neg_one
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simp [hji]

section Cover

variable {p q r s : ℕ}

def AdjRule {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (X : Mat p q) P P' y y', ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ = ⟪B P y, B (fockAct1 p q r s (adjZ X) P') y'⟫_ℂ

def InvRule (N : GKMod r s) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (Y : Mat r s) P y, B (fockAct2 p q r s Y P) y = B P (N.act (adjZ Y) y)

variable (p q r s) in

def UnitaryImage : Prop :=
  ∀ (Y Z : Type) [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z), AdjRule B →
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧ Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (fockAct1 p q r s X P) y = A.M.act X (B' P y)

def contr {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (y : V) : A ⊗[ℂ] V →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ LinearMap.lTensor A (innerₛₗ ℂ (ι y) ∘ₗ ι)

variable (p q) in

def FiniteSupport {T : GrpData r s} (R : DSRep T) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (B : Pol p q r s →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] A), InvRule R.HK B →
    ∀ P, ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪R.ι y, R.ι e⟫_ℂ = 0) → B P y = 0

def TensorForm : Prop :=
  ∀ (U A V H : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    (∀ t : A ⊗[ℂ] V, (∀ y, contr ι y t = 0) → t = 0) ∧
    ∀ B : U →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] A,
      (∀ P, ∃ E : Submodule ℂ V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → B P y = 0) →
      ∃ f : U →ₗ[ℂ] A ⊗[ℂ] V, ∀ P y, contr ι y (f P) = B P y

structure IsCoverPair (N : GKMod r s) {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop where
  skew : ∀ X ∈ upq p q, ∀ P P' y y',
    ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ + ⟪B P y, B (fockAct1 p q r s X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ upq r s, ∀ P y, B (fockAct2 p q r s Y P) y + B P (N.act Y y) = 0

variable (p q) in

def CoverKer (N : GKMod r s) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₁) (B₂ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₂),
    IsCoverPair N B₁ → IsCoverPair N B₂ → B₁ ≠ 0 → KerLe (fun P y => B₁ P y) fun P y => B₂ P y

end Cover

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure IsKAct (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) : Prop where
  der : ∀ X ∈ lieAt V τ, ∀ v : kFin M τ,
    HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (a X v : M.H τ) 0
  skew : ∀ X ∈ lieAt V τ, ∀ v w : kFin M τ, ⟪a X v, w⟫_ℂ + ⟪v, a X w⟫_ℂ = 0

def KSm : Prop := ∀ τ, kFin M τ ≤ M.sm τ

abbrev KT : Type := ⨂[ℂ] τ, kFin M τ

variable {M} in

def inclK (h : KSm M) : KT M →ₗ[ℂ] SmT M := PiTensorProduct.map fun τ => Submodule.inclusion (h τ)

def kOp (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ maxCpt M τ) : Module.End ℂ (kFin M τ) :=
  (M.rep τ k : M.H τ →ₗ[ℂ] M.H τ).restrict fun _ hv => rep_mem_kFin M τ hk hv

def sOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure IsLocPair (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ))
    {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z) :
    Prop where
  skew : ∀ X ∈ lieAt V τ, ∀ P P' y y', ⟪B (sOp M M' τ aT X P) y, B P' y'⟫_ℂ + ⟪B P y, B (sOp M M' τ aT X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ lieAt W τ, ∀ P y, B (tOp M M' τ aS Y P) y + B P (a' Y y) = 0

def LocKer (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₁) (B₂ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₂),
    IsLocPair M M' τ aS aT a' B₁ → IsLocPair M M' τ aS aT a' B₂ → B₁ ≠ 0 →
      KerLe (fun P y => B₁ P y) fun P y => B₂ P y

def IsCuspGrow (θ : InfFam D) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  IsAutFun V φ ∧ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ IsCuspFun V φ ∧ GlobalTheory.Grow.UnifModGrowth V θ φ

def kMean (τ : D.what₂.Tau) (e : Formalism.REAL.KG (M.ε τ) → ℂ) (w : M.H τ) : M.H τ :=
  ∫ k, e k • M.σ τ (Formalism.REAL.toMK k) w ∂(Formalism.REAL.muK (M.ε τ))

def IsCoefFam {G : Type} [Group G] [TopologicalSpace G] {n : ℕ} (c : Fin n → G → ℂ) : Prop :=
  (∀ i, Continuous (c i)) ∧ ∀ (k₀ : G) (i : Fin n), ∃ d : Fin n → ℂ, ∀ k, c i (k₀ * k) = ∑ j, d j * c j k

end GlobalTheory.Chain.IoLift

end
