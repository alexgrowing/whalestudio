import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormPosOnOrthLiftedFlag
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.PtMatIsUnit
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ComplPos

theorem mem_orth_left {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {U U' : Submodule E S.V}
    {x : S.V} (hx : x ∈ orth S (U ⊔ U')) : x ∈ orth S U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  exact fun y hy => hx y (Submodule.mem_sup_left hy)

theorem mem_orth_right {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {U U' : Submodule E S.V}
    {x : S.V} (hx : x ∈ orth S (U ⊔ U')) : x ∈ orth S U' := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  exact fun y hy => hx y (Submodule.mem_sup_right hy)

theorem fvec_mem_Xplus {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (b : Fin (r + 1)) : F.fvec b ∈ F.Xplus := by
  refine Fin.lastCases ?_ (fun a => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)

theorem eq_zero_of_mem_X {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') (hdet : (ZhatOM (Zhat F F')).det ≠ 0) {x : S.V}
    (hxX : x ∈ F.X) (hx : x ∈ orth S F'.Xplus) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxX
  have hx' : ∀ y ∈ F'.Xplus, S.hT y (∑ i, c i • F.e i) = 0 := by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx
  have hrow : ∀ b, ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b = 0 := by
    intro b
    have h1 := hx' _ (fvec_mem_Xplus F' b)
    have h2 : S.hT (∑ i, c i • F.e i) (F'.fvec b) = 0 := by
      rw [← S.herm.eq, h1, map_zero]
    rw [map_sum, LinearMap.sum_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Zhat, brS, FlagG.fvec, Fin.snoc_castSucc, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply]
  set v : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) (fun a => star (c a)) 0 with hv
  have hvZ : Matrix.vecMul v (ZhatOM (Zhat F F')) = 0 := by
    funext b
    simp only [Matrix.vecMul, dotProduct, ZhatOM, Pi.zero_apply]
    rw [Fin.sum_univ_castSucc]
    simp only [hv, Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
    have := hrow b
    calc ∑ a : Fin r, star (c a) * ((-1) ^ (r - b.val) * Zhat F F' a.castSucc b)
        = (-1) ^ (r - b.val) * ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
      _ = 0 := by rw [this, mul_zero]
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvZ
  have hc : ∀ a, c a = 0 := by
    intro a
    have := congrFun hv0 a.castSucc
    simp only [hv, Fin.snoc_castSucc, Pi.zero_apply, star_eq_zero] at this
    exact this
  simp [hc]

end GlobalTheory.ComplPos

theorem GlobalTheory.ComplPos.complement_totPos : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x) := by
  intro D X Y u u' F F' w hZ _ x hx hx0
  have hdet : (ZhatOM (Zhat F.fl F'.fl)).det ≠ 0 := by
    have e : ZhatOM (Zhat F.fl F'.fl) = ptMat w := hZ
    rw [e]
    exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w
  by_cases hxX : x ∈ Xsp F
  · exact absurd (GlobalTheory.ComplPos.eq_zero_of_mem_X F.fl F'.fl hdet hxX (GlobalTheory.ComplPos.mem_orth_right hx)) hx0
  · have hT : 0 < Tu D u := (D.mem u).A.T_prime.pos
    exact GlobalTheory.LoopC.PerpPos.trace_pos_perp D (Tu D u) F hT x (GlobalTheory.ComplPos.mem_orth_left hx) hxX
