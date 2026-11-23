import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

universe w

variable {K : Type} [Field K]

abbrev Idx.swap {c n : ℕ} (t : Idx c n) : Idx c n :=
  ⟨t.a', t.j, t.a, t.i, by have := t.ha; omega, by have := t.h; omega⟩

def swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) :
    (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) →ₗ[K]
      (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) :=
  DirectSum.toModule K _ _ fun t =>
    ((-1 : ℤ) ^ (t.i * t.j)) •
      ((DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap).comp
        (TensorProduct.comm K ((P t.a).H t.i) ((Q t.a').H t.j)).toLinearMap)

theorem swapSum_lof (P Q : ℕ → Cx.{w} K) (c n : ℕ) (t : Idx c n) (u : (P t.a).H t.i) (v : (Q t.a').H t.j) :
    swapSum P Q c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t (u ⊗ₜ v)) =
      ((-1 : ℤ) ^ (t.i * t.j)) •
        DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap (v ⊗ₜ u) := by
  unfold swapSum
  rw [DirectSum.toModule_lof]
  rfl

theorem swapSum_swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) (z) :
    swapSum Q P c n (swapSum P Q c n z) = z := by
  have key : (swapSum Q P c n).comp (swapSum P Q c n) = LinearMap.id := by
    refine DirectSum.linearMap_ext K fun t => TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, swapSum_lof, map_zsmul]
    have hs : ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.swap.i * t.swap.j)) = 1 := by
      change ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.j * t.i)) = 1
      rw [Nat.mul_comm t.j t.i, ← mul_pow]
      simp
    refine (congrArg (fun w => ((-1 : ℤ) ^ (t.i * t.j)) • w) (swapSum_lof Q P c n t.swap v u)).trans ?_
    dsimp only
    rw [smul_smul, hs, one_smul]
  exact LinearMap.congr_fun key z

theorem kunE_swap {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (h : KunE pr) :
    KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  intro c n
  obtain ⟨e, he⟩ := h c n
  let σ : (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) ≃ₗ[K]
      (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) :=
    LinearEquiv.ofLinear (swapSum Q P c n) (swapSum P Q c n)
      (LinearMap.ext fun z => swapSum_swapSum P Q c n z) (LinearMap.ext fun z => swapSum_swapSum Q P c n z)
  refine ⟨σ.trans e, fun t x y hx hy hz => ?_⟩
  have hz' : (T c).d n ((pr (show t.a' + t.a = c by have := t.ha; omega)).μ (show t.j + t.i = n by have := t.h; omega) y x) = 0 := by
    have e0 := (pr (show t.a' + t.a = c by have := t.ha; omega)).leib (show t.j + t.i = n by have := t.h; omega) y x
    rw [e0, hx, hy]
    simp
  have e1 := he t.swap y x hy hx hz'
  change e (swapSum Q P c n (DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t
    ((Q t.a).cls x hx ⊗ₜ (P t.a').cls y hy))) = _
  rw [swapSum_lof, map_zsmul]
  refine (congrArg _ e1).trans ?_
  rfl

end GlobalTheory.CompanionTheory.KunGlue
