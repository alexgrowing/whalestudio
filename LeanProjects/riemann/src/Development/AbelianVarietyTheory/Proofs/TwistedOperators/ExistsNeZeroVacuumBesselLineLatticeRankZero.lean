import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.LineZero

variable {D : D7}

theorem rat_mul_mem_latO_neg {V T T' : HSp D} {LS : Set (Fin V.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hq : ∀ t ∈ LT, q *ᵥ t ∈ LT') :
    ∀ x ∈ latO (negSp V) T LS LT P, rat q ⬝ x ∈ latO V T' LS (LT' : Set _) P := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hv, a, ha, s, hs, t, ht, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨α, hα, hv, a, ha, s, hs, -(q *ᵥ t), neg_mem (hq t ht), ?_⟩
    ext i j
    simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply]
    have e : ∀ (e : D.host.E) (u : AF D.host.F) (c : D.host.E), incA D e * (u ⊗ₜ[D.host.F] c) = u ⊗ₜ[D.host.F] (e * c) := by
      intro e u c
      show (Algebra.TensorProduct.includeRight e : AF D.host.F ⊗[D.host.F] D.host.E) * _ = _
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    simp only [e, ← TensorProduct.tmul_sum]
    congr 1
    have hX : ∑ k, star (s k) * (negSp V).gram k j = -∑ k, star (s k) * V.gram k j := by
      simp only [negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [hX]
    generalize (∑ k, star (s k) * V.gram k j) = X
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem exists_vacG_lineLat_zero : OnStd fun {D} _ _ _ {G} W F => ∃ Φ₀, VacG W.ψ _ _ (lineLat F 0) Φ₀ ∧ Φ₀ ≠ 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF
  have hq0 : ∀ t ∈ (G.Λ (.core 0) : Set (Fin (G.V (.core 0)).rank → D.host.E)),
      F.oz.qB *ᵥ t ∈ Submodule.span (𝓞 D.host.E) {F.ζ 0} := by
    intro t ht
    have ht' : t ∈ G.sp.dec0.lat (L.ΛY 0) fun _ => 1 := by rw [← G.sp.lat0]; exact ht
    obtain ⟨y, -, u, hu, rfl⟩ := ht'
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 (hu 0)
    have ha : G.sp.dec0.a *ᵥ u = u 0 • (F.oz.iB *ᵥ F.ζ 0) := by
      rw [hF.zB]
      funext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [Matrix.mulVec_add, ha, Matrix.mulVec_smul, ← hF.zA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, F.oz.qB_iA,
      F.oz.qB_iB, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  have hLT : IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    have hs : Subsingleton (Fin F.Lz.rank) := by rw [F.rk]; infer_instance
    have hne : Nonempty (Fin F.Lz.rank) := ⟨⟨0, by rw [F.rk]; omega⟩⟩
    let B : Matrix (Fin F.Lz.rank) (Fin F.Lz.rank) D.host.E := Matrix.of fun i _ => F.ζ 0 i
    let f : Fin F.Lz.rank → Fin 1 := fun _ => 0
    have hiB : F.oz.iB * B = G.sp.dec0.a.submatrix id f := by
      refine Matrix.ext fun i j => ?_
      have := congrFun hF.zB i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Matrix.mul_apply, B, Matrix.of_apply, Matrix.submatrix_apply, id, f]
      exact this
    have hB : Bᴴ * F.Lz.gram * B = 1 := by
      rw [← F.oz.isoB]
      have e : Bᴴ * (F.oz.iBᴴ * (G.V (.core 0)).gram * F.oz.iB) * B =
          (F.oz.iB * B)ᴴ * (G.V (.core 0)).gram * (F.oz.iB * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [e, hiB]
      refine (G.sp.dec0.gram_sub f f).trans (Matrix.ext fun i j => ?_)
      rw [Subsingleton.elim i j]
      simp [antiDiagonalSignGramMatrix, f]
    have hB' : B * (Bᴴ * F.Lz.gram) = 1 := mul_eq_one_comm.1 hB
    let Bg : GL (Fin F.Lz.rank) D.host.E := ⟨B, Bᴴ * F.Lz.gram, hB', hB⟩
    have hc : IsSelfDualC F.Lz (Formalism.L2.DIV.colLat Bg) :=
      GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal F.Lz Bg hB
    have hcs : Formalism.L2.DIV.colLat Bg = Submodule.span (𝓞 D.host.E) {F.ζ 0} := by
      unfold Formalism.L2.DIV.colLat
      congr 1
      ext v
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; rfl
      · rintro rfl; exact ⟨Classical.arbitrary _, rfl⟩
    rw [hcs] at hc
    exact isSelfDualC_neg hc
  have hLS : IsSelfDualC (G.V (.core 1)) (G.Λ (.core 1)) := (G.sp.P_is 1 (by have := D.R.two_le_m; omega)).sd
  have hle : lineLat F 0 ≤ latO (G.V (.core 1)) (negSp F.Lz) (G.Λ (.core 1) : Set _)
      (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) (fun _ => True) := by
    intro b hb
    rw [lineLat] at hb
    have hb' : F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.jB ⬝ b ∈ latCore G 0 := hb
    have e : b = rat F.oz.qB ⬝ (F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.jB ⬝ b) := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      change b = F.oz.pB ⬝ F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.pB ⬝ F.oz.jB ⬝ b
      rw [OrthDec.pB_jA, OrthDec.pB_jB, Matrix.mul_zero, zero_add, Matrix.one_mul]
    rw [e]
    exact rat_mul_mem_latO_neg (V := G.V (.core 1)) F.oz.qB hq0 _ hb'.1
  exact GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero D W.ψ W.ψ_std _ _ _ _ hLS hLT _ hle

end GlobalTheory.AscFin.LineZero
