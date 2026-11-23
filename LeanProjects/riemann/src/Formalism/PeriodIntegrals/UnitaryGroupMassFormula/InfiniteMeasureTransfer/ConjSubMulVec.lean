import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasureIsomorphismAtInfinity

noncomputable section

open NumberField Matrix Formalism.L2.SG.AdBridge
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)

namespace Formalism.L2.SG.Pf.MeasInfW

variable (I : AutInst)

def thV (v : InfinitePlace I.F) (w : Fin I.n → TI I) : Fin I.n → ℂ := fun i => thI I v (w i)

theorem thV_zero (v : InfinitePlace I.F) : thV I v 0 = 0 := by
  funext i
  simp [thV]

theorem thV_add (v : InfinitePlace I.F) (w w' : Fin I.n → TI I) :
    thV I v (w + w') = thV I v w + thV I v w' := by
  funext i
  simp [thV]

theorem thV_sub (v : InfinitePlace I.F) (w w' : Fin I.n → TI I) :
    thV I v (w - w') = thV I v w - thV I v w' := by
  funext i
  simp [thV]

theorem thV_smul (v : InfinitePlace I.F) (c : TI I) (w : Fin I.n → TI I) :
    thV I v (c • w) = thI I v c • thV I v w := by
  funext i
  simp [thV]

theorem thV_sum {ι : Type} (s : Finset ι) (v : InfinitePlace I.F) (f : ι → Fin I.n → TI I) :
    thV I v (∑ a ∈ s, f a) = ∑ a ∈ s, thV I v (f a) := by
  funext i
  simp [thV, Finset.sum_apply, map_sum]

theorem thV_mulVec (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) (TI I)) (w : Fin I.n → TI I) :
    thV I v (M *ᵥ w) = M.map (thI I v) *ᵥ thV I v w := by
  funext i
  exact RingHom.map_mulVec (thI I v) M w i

theorem thV_ratV (v : InfinitePlace I.F) (x : Fin I.n → I.E) :
    thV I v (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) x) = fun i => I.φ v (x i) := by
  funext i
  simp only [thV, Formalism.L2.SG.Sub.ratV, thI_inclR]

theorem thV_ext (w w' : Fin I.n → TI I) (h : ∀ v, thV I v w = thV I v w') : w = w' := by
  funext i
  exact thI_ext I (w i) (w' i) fun v => congrFun (h v) i

open Classical in

theorem exists_single (v0 : InfinitePlace I.F) (u : Fin I.n → ℂ) :
    ∃ w : Fin I.n → TI I, ∀ v, thV I v w = if v = v0 then u else 0 := by
  choose y hy using fun i => thI_surj I (fun v => if v = v0 then u i else 0)
  refine ⟨y, fun v => ?_⟩
  funext i
  simp only [thV, hy]
  split_ifs <;> rfl

def phV (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ := fun i => I.φ v (x i)

theorem mem_spanR_iff {m : ℕ} (Y : Fin m → Fin I.n → I.E) (t : Set (Fin m)) (w : Fin I.n → TI I) :
    w ∈ Formalism.L2.SG.Sub.spanR (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) Y t ↔
      ∀ v, thV I v w ∈ Submodule.span ℂ ((fun a => phV I v (Y a)) '' t) := by
  classical
  unfold Formalism.L2.SG.Sub.spanR
  constructor
  · intro hw v
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      simp only [thV_ratV]
      exact Submodule.subset_span ⟨a, ha, rfl⟩
    | zero => rw [thV_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [thV_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [thV_smul]; exact Submodule.smul_mem _ _ hx
  · intro h
    have hc : ∀ v, ∃ c : t → ℂ, ∑ a, c a • phV I v (Y a) = thV I v w := by
      intro v
      have hv := h v
      rw [Set.image_eq_range] at hv
      exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
    choose c hc using hc
    choose y hy using fun a : t => thI_surj I (fun v => c v a)
    have hw : w = ∑ a : t, y a • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (Y a) := by
      apply thV_ext I
      intro v
      rw [thV_sum, ← hc v]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [thV_smul, thV_ratV]
      exact congrArg₂ (· • ·) (hy a v).symm rfl
    rw [hw]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, a.2, rfl⟩)

theorem hPP (v : InfinitePlace I.F) : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))

theorem hPP' (v : InfinitePlace I.F) : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, hPP I v, Matrix.conjTranspose_one]

def Bv (v : InfinitePlace I.F) (a b : Fin I.n → ℂ) : ℂ := ∑ i, ∑ j, star (a i) * I.φ v (I.J i j) * b j

theorem thI_hR (v : InfinitePlace I.F) (x : Fin I.n → I.E) (w : Fin I.n → TI I) :
    thI I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
      (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) x) w) = Bv I v (phV I v x) (thV I v w) := by
  have hs : ∀ a : I.E, I.φ v (I.cm.sig a) = star (I.φ v a) := fun a => I.cm.cmUnram.2.1 (I.φ v) a
  have h1 : ∀ a : I.E, thI I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) a)) = star (I.φ v a) := by
    intro a
    have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) a) =
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (I.cm.sig a) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    rw [e, thI_inclR, hs]
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, map_sum, map_mul, Formalism.L2.SG.Sub.ratV,
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply, h1, thI_inclR, Bv, thV, phV]

theorem phi_hE (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    I.φ v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE I.cm.sig I.J x y) = Bv I v (phV I v x) (phV I v y) := by
  have hs : ∀ a : I.E, I.φ v (I.cm.sig a) = star (I.φ v a) := fun a => I.cm.cmUnram.2.1 (I.φ v) a
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom,
    RingHom.coe_coe, hs, Bv, phV]

theorem hJ_conj (v : InfinitePlace I.F) (a b : Fin I.n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ (I.ε v) ((I.P v)⁻¹ *ᵥ a) ((I.P v)⁻¹ *ᵥ b) = Bv I v a b := by
  have hJ' : I.J.map (I.φ v) = ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ := by
    rw [← I.P_spec v]
    simp only [← mul_assoc]
    rw [hPP' I v, one_mul, mul_assoc, hPP I v, mul_one]
  have key : Bv I v a b = star a ⬝ᵥ (I.J.map (I.φ v) *ᵥ b) := by
    simp [Bv, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [key, hJ', Formalism.L2.SG.HidaSetting.hJ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.star_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec]

end Formalism.L2.SG.Pf.MeasInfW
