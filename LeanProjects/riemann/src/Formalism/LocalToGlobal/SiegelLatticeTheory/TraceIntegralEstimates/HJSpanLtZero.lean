import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal
open Matrix

namespace Formalism.L2.S.Pv.TauS

open Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {n r : ℕ} (ε : Fin n → Bool) {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}

private theorem hJ_add_lemma (x a b : Fin n → ℂ) : hJ ε x (a + b) = hJ ε x a + hJ ε x b := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

private theorem hJ_smul_lemma_2 (x a : Fin n → ℂ) (c : ℂ) : hJ ε x (c • a) = c * hJ ε x a := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem hJ_zero_lemma_3 (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp only [hJ, Matrix.mulVec_zero, dotProduct_zero]

private theorem spanLt_mono_lemma_4 (e : Fin r → Fin n → ℂ) {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b := by
  unfold spanLt
  exact Submodule.span_mono (Set.image_mono (fun x (hx : x.1 < a) => (lt_of_lt_of_le hx h : x.1 < b)))

theorem hJ_spanLt_zero (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (a : Fin r) :
    ∀ u ∈ spanLt e a.1, hJ ε (f a) u = 0 := by
  intro u hu
  unfold spanLt at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [hfe, if_neg]
    intro hab
    subst hab
    simp only [Set.mem_setOf_eq, lt_self_iff_false] at hb
  | zero => exact hJ_zero_lemma_3 ε _
  | add x y _ _ hx hy => rw [hJ_add_lemma, hx, hy, add_zero]
  | smul c x _ hx => rw [hJ_smul_lemma_2, hx, mul_zero]

theorem sub_one_spanLt {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (k : ℕ) :
    ∀ u ∈ spanLt e (k + 1), (g - 1) *ᵥ u ∈ spanLt e k := by
  intro u hu
  unfold spanLt at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hbk : b.1 ≤ k := Nat.lt_succ_iff.mp hb
    exact spanLt_mono_lemma_4 e hbk (hg.1 b)
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx

theorem sub_one_nxt {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : Fin r) :
    (g - 1) *ᵥ nxt e z a ∈ spanLt e (a.1 + 1) := by
  have ha := a.isLt
  unfold nxt
  split_ifs with h
  · exact hg.1 ⟨a.1 + 1, h⟩
  · have hr : a.1 + 1 = r := by omega
    rw [hr]
    exact hg.2

theorem hJ_nxt (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (a : Fin r) : hJ ε (f a) (nxt e z a) = 0 := by
  unfold nxt
  split_ifs with h
  · rw [hfe, if_neg]
    intro hc
    have := congrArg Fin.val hc
    simp at this
  · exact hfz a

theorem rootCoord_mul (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hg' : InS e z g') (a : Fin r) :
    rootCoord ε e f z (g * g') a = rootCoord ε e f z g a + rootCoord ε e f z g' a := by
  unfold rootCoord
  have hs_mem : (g' - 1) *ᵥ nxt e z a ∈ spanLt e (a.1 + 1) := sub_one_nxt hg' a
  have h1 : (g - 1) *ᵥ ((g' - 1) *ᵥ nxt e z a) ∈ spanLt e a.1 := sub_one_spanLt hg a.1 _ hs_mem
  have hg'v : g' *ᵥ nxt e z a = nxt e z a + (g' - 1) *ᵥ nxt e z a := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hgs : g *ᵥ ((g' - 1) *ᵥ nxt e z a) =
      (g' - 1) *ᵥ nxt e z a + (g - 1) *ᵥ ((g' - 1) *ᵥ nxt e z a) := by
    rw [Matrix.sub_mulVec g 1, Matrix.one_mulVec]
    abel
  rw [← Matrix.mulVec_mulVec, hg'v, Matrix.mulVec_add, hgs]
  simp only [hJ_add_lemma]
  rw [hJ_spanLt_zero ε hfe a _ h1, hJ_nxt ε hfe hfz a]
  ring

theorem rootCoord_one (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (a : Fin r) : rootCoord ε e f z 1 a = 0 := by
  simp only [rootCoord, Matrix.one_mulVec]
  exact hJ_nxt ε hfe hfz a

theorem psiR_mul (gg : ℕ) (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0)
    (hfz : ∀ a, hJ ε (f a) z = 0) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hg' : InS e z g') :
    psiR ε gg e f z (g * g') = psiR ε gg e f z g * psiR ε gg e f z g' := by
  have hsum : ∀ a, rootCoord ε e f z (g * g') a + star (rootCoord ε e f z (g * g') a) =
      (rootCoord ε e f z g a + star (rootCoord ε e f z g a)) +
        (rootCoord ε e f z g' a + star (rootCoord ε e f z g' a)) := by
    intro a
    rw [rootCoord_mul ε hfe hfz hg hg', star_add]
    ring
  unfold psiR
  rw [← Complex.exp_add]
  congr 1
  simp only [hsum, Finset.sum_add_distrib]
  ring

theorem psiR_one (gg : ℕ) (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0)
    (hfz : ∀ a, hJ ε (f a) z = 0) : psiR ε gg e f z 1 = 1 := by
  simp only [psiR, rootCoord_one ε hfe hfz, star_zero, add_zero, Finset.sum_const_zero, zero_div, mul_zero,
    Complex.exp_zero]

end Loc

section Glob

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

private theorem hJ_swap_lemma_5 {m : ℕ} (ε : Fin m → Bool) (x y : Fin m → ℂ) : hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : ε i <;> simp [h] <;> ring

theorem hfe_X (v : InfinitePlace X.B.I.F) (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if a = b then 1 else 0 := by
  rw [hJ_swap_lemma_5, ← Formalism.L2.SG.PoincareInHH.Cut.phi_hform]
  have h1 := Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) (X.eX b) (X.fY a)
  rw [X.ef b a] at h1
  have h0 : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR b) (X.fR a) = if a = b then 1 else 0 := by
    apply X.ιE.injective
    refine h1.trans ?_
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg (Ne.symm hab), if_neg hab, map_zero]
  rw [h0]
  by_cases hab : a = b <;> simp [hab]

theorem hfz_X (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := by
  rw [← Formalism.L2.SG.PoincareInHH.Cut.phi_hform]
  have h0 : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.fR a) (X.zR u) = 0 := by
    apply X.ιE.injective
    rw [map_zero]
    exact (Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) (X.fY a) (X.zu u)).trans (X.zu_orth u a).2
  rw [h0, map_zero]

theorem psiInfU_one (u : D.what₂.Word) : X.psiInfU u 1 = 1 := by
  unfold HidaSetting.psiInfU psiInf
  refine Finset.prod_eq_one (fun v _ => ?_)
  have h1 : uMat ((1 : X.B.I.Ginf) v) = 1 := rfl
  rw [h1]
  exact psiR_one (X.B.I.ε v) X.B.g (hfe_X X v) (hfz_X X u v)

theorem psiInfU_mul (u : D.what₂.Word) {s t : X.B.I.Ginf} (hs : s ∈ X.SinfU u) (ht : t ∈ X.SinfU u) :
    X.psiInfU u (s * t) = X.psiInfU u s * X.psiInfU u t := by
  unfold HidaSetting.psiInfU psiInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  have h1 : uMat ((s * t) v) = uMat (s v) * uMat (t v) := rfl
  rw [h1]
  exact psiR_mul (X.B.I.ε v) X.B.g (hfe_X X v) (hfz_X X u v) (hs v) (ht v)

theorem tauU_one (u : D.what₂.Word) : Formalism.L2.SG.RealObj.EnergyInst.tauU X u 1 = 1 := by
  unfold Formalism.L2.SG.RealObj.EnergyInst.tauU
  rw [psiInfU_one, (X.piU_rep u).1, one_smul]

theorem tauU_mul (u : D.what₂.Word) : ∀ s ∈ X.SinfU u, ∀ t ∈ X.SinfU u,
    Formalism.L2.SG.RealObj.EnergyInst.tauU X u (s * t) =
      Formalism.L2.SG.RealObj.EnergyInst.tauU X u s * Formalism.L2.SG.RealObj.EnergyInst.tauU X u t := by
  intro s hs t ht
  unfold Formalism.L2.SG.RealObj.EnergyInst.tauU
  rw [psiInfU_mul X u hs ht, (X.piU_rep u).2.1 s hs t ht, smul_mul_smul_comm]

end Glob

end Formalism.L2.S.Pv.TauS
