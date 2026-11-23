import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesCartanDoubleCoset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.LocKerMod.FrameIdx

variable {K : Type} [Field K] {n : ℕ}

def colHom : (Fin n → K) →+ Matrix (Fin n) (Fin 1) K where
  toFun y := fun i _ => y i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colHom_injective : Function.Injective (colHom (K := K) (n := n)) :=
  fun x y h => funext fun i => congrFun (congrFun h i) 0

@[simp] theorem colHom_apply (y : Fin n → K) (i : Fin n) (j : Fin 1) : colHom y i j = y i := rfl

theorem colHom_mulVec (P : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    colHom (P *ᵥ y) = GlobalTheory.SplitIdx.mulL (n := 1) P (colHom y) := by
  ext i j
  simp only [GlobalTheory.SplitIdx.mulL, AddMonoidHom.mk'_apply, colHom_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem mulL_one : GlobalTheory.SplitIdx.mulL (n := 1) (1 : Matrix (Fin n) (Fin n) K) = AddMonoidHom.id _ := by
  ext y : 1
  simp [GlobalTheory.SplitIdx.mulL]

end GlobalTheory.LocKerMod.FrameIdx

open GlobalTheory.LocKerMod.FrameIdx in

theorem GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → GlobalTheory.LocKerMod.idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  intro D T v w h a ha ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ g hg
  set k : GL (Fin T.rank) (w.adicCompletion D.host.E) := k₁ * t * k₂ with hk
  set Lw := (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup with hLw
  set M := GlobalTheory.SplitIdx.intMat D.host.E w T.rank 1 with hM
  let Φ : (Fin T.rank → w.adicCompletion D.host.E) →+ Matrix (Fin T.rank) (Fin 1) (w.adicCompletion D.host.E) :=
    colHom.comp (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1.mulVecLin.toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 : (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x =
        (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ y := colHom_injective hxy
    have e := congrArg (fun z => a.1 *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec] at e
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec] at e
  have hA : Lw.map Φ = M := by
    ext Y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ i j
      have hx' : a.1 *ᵥ ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x) ∈ GlobalTheory.LFun.latAt w (frameLat T) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]; exact hx
      exact (ha _).2 hx' i
    · intro hY
      refine ⟨a.1 *ᵥ (fun i => Y i 0), (ha _).1 (fun i => hY i 0), ?_⟩
      refine Matrix.ext fun i j => ?_
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ (a.1 *ᵥ fun i => Y i 0)) i 0 = Y i 0
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rfl
  have hB : (Lw.map (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).map Φ =
      M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1) := by
    rw [← hA, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    refine AddMonoidHom.ext fun x => ?_
    show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ
        ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ x)) =
      GlobalTheory.SplitIdx.mulL (n := 1) k.1 (colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x))
    rw [← colHom_mulVec, hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  have step1 : GlobalTheory.LocKerMod.idxAt T w h g = (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).relIndex M := by
    unfold GlobalTheory.LocKerMod.idxAt
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hΦ, hB, hA]
  have hinv : (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).map (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) = M := by
    rw [AddSubgroup.map_map, ← GlobalTheory.SplitIdx.LocIndex.mulL_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mulL_one, AddSubgroup.map_id]
  have hinj : Function.Injective (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) := by
    intro x y hxy
    have e := congrArg (GlobalTheory.SplitIdx.mulL (n := 1) k.1) hxy
    simpa [GlobalTheory.SplitIdx.mulL, ← Matrix.mul_assoc, ← Units.val_mul] using e
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have hv : Valued.v (0 : w.adicCompletion D.host.E) = _ := hϖ
    rw [map_zero] at hv
    exact WithZero.coe_ne_zero hv.symm
  have ht' : (t⁻¹).1 = Matrix.diagonal (fun i => ϖ ^ (-d i)) := by
    have e1 : t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
      rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
    calc (t⁻¹).1 = (t⁻¹).1 * (t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i))) := by rw [e1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hkinv : k⁻¹ = k₂⁻¹ * t⁻¹ * k₁⁻¹ := by rw [hk]; group
  rw [step1, ← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hinv, hkinv,
    GlobalTheory.SplitIdx.LocIndex.relIndex_intMat w T.rank 1 ϖ hϖ (fun i => -d i) t⁻¹ ht' k₂⁻¹ (inv_mem hk₂)
      k₁⁻¹ (inv_mem hk₁)]
  simp
