import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

noncomputable section

namespace GlobalTheory.ChainDesc.FreeAct

open GlobalTheory.LatGlue (coords coords_resM)

variable (X : Scheme.{0}) (h : ℕ)

def actLin (N : Matrix (Fin h) (Fin h) ℤ) (W : X.Opens) :
    Γ(freeModule X (Fin h), W) →ₗ[Γ(X, W)] Γ(freeModule X (Fin h), W) :=
  (coords X h W).symm.toLinearMap ∘ₗ (N.map (Int.cast : ℤ → Γ(X, W))).mulVecLin ∘ₗ (coords X h W).toLinearMap

theorem coords_actLin (N : Matrix (Fin h) (Fin h) ℤ) (W : X.Opens) (s : Γ(freeModule X (Fin h), W)) :
    coords X h W (actLin X h N W s) = (N.map (Int.cast : ℤ → Γ(X, W))).mulVec (coords X h W s) :=
  (coords X h W).apply_symm_apply _

theorem actLin_resM (N : Matrix (Fin h) (Fin h) ℤ) {V W : X.Opens} (hle : W ≤ V) (s : Γ(freeModule X (Fin h), V)) :
    actLin X h N W (resM _ hle s) = resM _ hle (actLin X h N V s) := by
  apply (coords X h W).injective
  rw [coords_actLin, coords_resM, coords_resM, coords_actLin]
  funext i
  simp [Matrix.mulVec, dotProduct, GlobalTheory.PerfdLat.piMap_apply, map_sum]

def act (N : Matrix (Fin h) (Fin h) ℤ) : freeModule X (Fin h) ⟶ freeModule X (Fin h) :=
  GlobalTheory.LB.homOfLinear (actLin X h N) fun hle s => actLin_resM X h N hle s

theorem coords_act (N : Matrix (Fin h) (Fin h) ℤ) (W : X.Opens) (s : Γ(freeModule X (Fin h), W)) :
    coords X h W ((act X h N).app W s) = ((Int.castRingHom Γ(X, W)).mapMatrix N).mulVec (coords X h W s) :=
  coords_actLin X h N W s

def actHom : Matrix (Fin h) (Fin h) ℤ →+* End (freeModule X (Fin h)) where
  toFun := act X h
  map_one' := by
    change act X h 1 = 𝟙 _
    ext W s
    apply (coords X h W).injective
    refine (coords_act X h 1 W s).trans ?_
    rw [map_one, Matrix.one_mulVec]
    rfl
  map_mul' N M := by
    change act X h (N * M) = act X h M ≫ act X h N
    ext W s
    apply (coords X h W).injective
    refine (coords_act X h _ W s).trans ?_
    rw [map_mul, ← Matrix.mulVec_mulVec, ← coords_act, ← coords_act]
    rfl
  map_zero' := by
    change act X h 0 = 0
    ext W s
    apply (coords X h W).injective
    refine (coords_act X h 0 W s).trans ?_
    rw [map_zero, Matrix.zero_mulVec]
    exact (map_zero _).symm
  map_add' N M := by
    change act X h (N + M) = act X h N + act X h M
    ext W s
    apply (coords X h W).injective
    refine (coords_act X h _ W s).trans ?_
    rw [map_add, Matrix.add_mulVec, ← coords_act, ← coords_act, ← map_add]
    rfl

theorem exists_act : ∀ (X : Scheme.{0}) (h : ℕ), ∃ μ : Matrix (Fin h) (Fin h) ℤ →+* End (freeModule X (Fin h)), ∀ (N : Matrix (Fin h) (Fin h) ℤ) (W : X.Opens) (s : Γ(freeModule X (Fin h), W)), GlobalTheory.LatGlue.coords X h W ((μ N : freeModule X (Fin h) ⟶ freeModule X (Fin h)).app W s) = mv (RingHom.id _) N (GlobalTheory.LatGlue.coords X h W s) :=
  fun X h => ⟨actHom X h, fun N W s => coords_actLin X h N W s⟩

end GlobalTheory.ChainDesc.FreeAct
