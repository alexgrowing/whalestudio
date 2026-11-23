import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.HtInfKapX

open GlobalTheory.AdelicU (htInf htOf normInf opNorm compInf)

theorem opNorm_reindex_le {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) ≤ opNorm y := by
  unfold GlobalTheory.AdelicU.opNorm
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  let c : EuclideanSpace ℂ m → EuclideanSpace ℂ n := fun z => WithLp.toLp 2 fun i => z (e i)
  let c' : EuclideanSpace ℂ n → EuclideanSpace ℂ m := fun z => WithLp.toLp 2 fun j => z (e.symm j)
  have hc : ∀ z, ‖c z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c]
    congr 1
    exact Equiv.sum_comp e (fun j => ‖z j‖₊ ^ 2)
  have hc' : ∀ z, ‖c' z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c']
    congr 1
    exact Equiv.sum_comp e.symm (fun j => ‖z j‖₊ ^ 2)
  have h : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) (reindex e e y) x =
      c' (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y (c x)) := by
    ext j
    change ∑ k, y (e.symm j) (e.symm k) * x k = ∑ i, y (e.symm j) i * x (e i)
    rw [← Equiv.sum_comp e]
    simp
  rw [h, hc', ← hc x]
  exact ContinuousLinearMap.le_opNNNorm _ _

theorem opNorm_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) = opNorm y := by
  refine le_antisymm (opNorm_reindex_le e y) ?_
  have h : reindex e.symm e.symm (reindex e e y) = y := by ext; simp
  calc opNorm y = opNorm (reindex e.symm e.symm (reindex e e y)) := by rw [h]
    _ ≤ opNorm (reindex e e y) := opNorm_reindex_le e.symm _

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (w : NumberField.InfinitePlace F)

theorem normInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n (w.Completion ⊗[F] E)) : normInf F w (reindex e e y) = normInf F w y := by
  unfold GlobalTheory.AdelicU.normInf
  congr 1
  funext τ
  rw [reindex_apply, ← Matrix.submatrix_map, ← reindex_apply, opNorm_reindex]

theorem htInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (g : (Matrix n n (w.Completion ⊗[F] E))ˣ) :
    htInf F w (Units.map (Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e).toMonoidHom g) =
      htInf F w g := by
  have key : ∀ y, normInf F w ((Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e) y) =
      normInf F w y := fun y => by rw [Matrix.reindexAlgEquiv_apply, normInf_reindex]
  show GlobalTheory.AdelicU.htOf (normInf F w) _ = GlobalTheory.AdelicU.htOf (normInf F w) _
  rw [GlobalTheory.AdelicU.htOf, GlobalTheory.AdelicU.htOf, ← map_inv, Units.coe_map, Units.coe_map]
  exact congrArg₂ _ rfl (congrArg₂ _ (key _) (key _))

theorem bc_reindex {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) (g : (Matrix n n A)ˣ) :
    Formalism.UG.bc φ (Units.map (Matrix.reindexAlgEquiv A A e).toMonoidHom g) =
      Units.map (Matrix.reindexAlgEquiv B B e).toMonoidHom (Formalism.UG.bc φ g) := by
  ext i j
  rfl

theorem htInf_kapX_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal, ∀ h : GA D X, ∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) ≤ C * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h := by
  intro D θ hθ X d e J hJ
  refine ⟨1, fun h => ?_⟩
  rw [one_mul]
  refine le_of_eq ?_
  have key : ∀ w, GlobalTheory.AdelicU.htInf D.host.F w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) =
      GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom X h)) :=
    fun w => by
      show GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc _
        (Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (Formalism.L2.Theta.matHom X h))) = _
      rw [bc_reindex, htInf_reindex]
  simp only [key]
  exact (Function.Bijective.prod_comp (GlobalTheory.CMTypePlaces.places_bijective D) _).symm.trans
    (Finset.prod_congr rfl fun τ _ => GlobalTheory.Grow.htInf_eq_infHt X hθ τ h)

end GlobalTheory.HtInfKapX
