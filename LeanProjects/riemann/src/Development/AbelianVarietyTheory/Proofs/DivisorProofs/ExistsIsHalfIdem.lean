import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut

open GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.SplitScalar

variable {D : D7}

def IsHalfIdem (D : D7) (ε : AE D) : Prop :=
  ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧
    (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧
    ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0

theorem exists_isHalfIdem (D : D7) : ∃ ε, IsHalfIdem D ε := GlobalTheory.T.exists_splitPlaces_selecting_adelicIdempotent D

theorem finRat_eq (S T : HSp D) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T x = (1 - realIdem D) • (ratW T S x : WO S T) := by
  funext i j
  refine adele_ext ?_ ?_
  · exact (congrFun (congrFun (finRat_inf S T x) i) j).trans (congrFun (congrFun (fin_smul_fin (ratW T S x)) i) j).symm
  · show finPart D (ratW T S x i j) = finPart D ((1 - realIdem D) * ratW T S x i j)
    rw [RingHom.map_mul, RingHom.map_sub, finPart_realIdem, RingHom.map_one, sub_zero, one_mul]

theorem finRat_smul (S T : HSp D) (c : D.host.E) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T (c • x) = incA D c • finRat S T x := by
  rw [finRat_eq, finRat_eq, smul_comm]
  congr 1
  funext i j
  exact (incA D).map_mul c (x i j)

def latQ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E) where
  carrier := {x | finRat S T x ∈ latO S T LS LT fun _ => True}
  add_mem' {x y} hx hy := by
    show finRat S T (x + y) ∈ latO S T LS LT fun _ => True
    rw [map_add]
    exact add_mem hx hy
  zero_mem' := by
    show finRat S T 0 ∈ latO S T LS LT fun _ => True
    rw [map_zero]
    exact zero_mem _
  smul_mem' r x hx := by
    show finRat S T ((r : D.host.E) • x) ∈ latO S T LS LT fun _ => True
    rw [finRat_smul]
    exact GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ _ (finPart_intA r) _ hx

theorem mem_latQ {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {x : Matrix (Fin T.rank) (Fin S.rank) D.host.E} :
    x ∈ latQ S T LS LT ↔ finRat S T x ∈ latO S T LS LT fun _ => True := Iff.rfl

def gamQ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℂ :=
  ψ (symplO S T (finRat S T x) (finRat S T y))

open Classical in

def chiLat (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (x : WO S T) : ℂ :=
  if (1 - realIdem D) • x ∈ latO S T LS LT (fun _ => True) then
    ψ (symplOH S T (intA D w • (1 - realIdem D) • x) ((1 - realIdem D) • x)) else 0

def serO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (a : RW T S) : WO S T → ℂ :=
  GlobalTheory.HeisenbergGaussianSeries.series (G := WO S T) (piW θ T S) (iotaW σ T S) (fun x y => ψ (symplOH S T x y))
    (omO S T) (jO S T sS sT) (ratL T S) (chiLat ψ S T LS LT w) a

def actR (S T : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : RW T S :=
  fun τ => (b τ * Matrix.of (v τ) * a τ : Matrix (Fin T.rank) (Fin S.rank) ℂ)

def gaussR (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : ℂ :=
  Complex.exp (-(Real.pi * Complex.I) * (omO S T (actR S T a b v) v : ℝ)) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omO S T (actR S T a b v - v) (jO S T sS sT (actR S T a b v - v)) : ℝ))

def sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    Module.End K (Matrix (Fin m) (Fin n) K) where
  toFun x := b * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem sandw_apply {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K)
    (x : Matrix (Fin m) (Fin n) K) : sandw b a x = b * x * a := rfl

theorem toMatrix_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.toMatrix (Matrix.stdBasis K (Fin m) (Fin n)) (Matrix.stdBasis K (Fin m) (Fin n)) (sandw b a) = b ⊗ₖ aᵀ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, sandw_apply]
  have : ∀ x : Matrix (Fin m) (Fin n) K, (Matrix.stdBasis K (Fin m) (Fin n)).repr x (i, j) = x i j := fun x => by
    simp [Matrix.stdBasis]
  rw [this]
  simp [Matrix.mul_apply, Matrix.single, ite_and]

theorem det_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a) = (b ⊗ₖ aᵀ).det := by
  rw [← toMatrix_sandw, LinearMap.det_toMatrix]

theorem det_sandw_sub_one {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a - 1) = (b ⊗ₖ aᵀ - 1).det := by
  rw [← toMatrix_sandw, ← LinearMap.det_toMatrix (Matrix.stdBasis K (Fin m) (Fin n)), map_sub, LinearMap.toMatrix_one]

end GlobalTheory.RatAut

end
