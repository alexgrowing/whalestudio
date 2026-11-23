import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem zhat_int {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')
    (hF : ∀ b, F.fvec b ∈ Λ) (hF' : ∀ b, F'.fvec b ∈ Λ) :
    ∃ FinalForm : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      Zhat F F' = FinalForm.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  have hmem : ∀ a b, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = Zhat F F' a b := by
    intro a b
    have hx : F'.fvec b ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
      rw [show Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ from hun]
      exact hF' b
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hx
    have h1 := (Submodule.mem_iInf _).mp hx (F.fvec a)
    have h2 := (Submodule.mem_iInf _).mp h1 (hF a)
    rw [Submodule.mem_comap] at h2
    exact Submodule.mem_one.mp h2
  choose FinalForm hZo using hmem
  exact ⟨Matrix.of FinalForm, by ext a b; exact (hZo a b).symm⟩

theorem yv_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (n : ℕ) {T' : D.host.E} (F : FlagG (VS D) D.R.rS (n : D.host.E)) (F' : FlagG (VS D) D.R.rS T')
    (hF : ∀ b, F.fvec b ∈ Λ) (hF' : ∀ b, F'.fvec b ∈ Λ) : NormalVectorPairings.yv F F' ∈ Λ := by
  obtain ⟨FinalForm, hZo⟩ := zhat_int hun F F' hF hF'
  have hadj : (Zhat F F').adjugate = FinalForm.adjugate.map (algebraMap (𝓞 D.host.E) D.host.E) := by
    rw [hZo]
    exact (RingHom.map_adjugate _ _).symm
  have hD : Dl F F' (D.R.rS + 1) = algebraMap (𝓞 D.host.E) D.host.E
      ((FinalForm.submatrix (Fin.castLE le_rfl) (Fin.castLE le_rfl)).det) := by
    unfold Dl leadMinorE
    rw [dif_pos le_rfl, hZo, Matrix.submatrix_map, RingHom.map_det]
    rfl
  unfold NormalVectorPairings.yv NormalVectorPairings.omp
  refine Λ.add_mem ?_ ?_
  · rw [Nat.cast_smul_eq_nsmul]
    refine nsmul_mem (Λ.sum_mem fun b _ => ?_) n
    rw [hadj, Matrix.map_apply, algebraMap_smul]
    exact Λ.smul_mem _ (hF' b)
  · rw [hD, algebraMap_smul]
    have hz : F.z = F.fvec (Fin.last _) := by simp [FlagG.fvec]
    rw [hz]
    exact Λ.smul_mem _ (hF _)

theorem yv_orth_X {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') :
    ∀ x ∈ F.X, brS (VS D) (NormalVectorPairings.yv F F') x = 0 := by
  have key : ∀ a : Fin D.R.rS, (VS D).hT (F.e a) (NormalVectorPairings.yv F F') = 0 := by
    intro a
    have hz : ∀ b, (VS D).hT (F.e a) (F'.fvec b) = Zhat F F' a.castSucc b := by
      intro b
      simp [Zhat, brS, FlagG.fvec, Fin.snoc_castSucc]
    have hm := congrFun (congrFun (Matrix.mul_adjugate (Zhat F F')) a.castSucc) (Fin.last _)
    rw [Matrix.mul_apply] at hm
    simp only [Matrix.smul_apply, Matrix.one_apply, Fin.castSucc_ne_last, if_false, smul_zero] at hm
    unfold NormalVectorPairings.yv NormalVectorPairings.omp
    rw [map_add, map_smul, map_smul, F.z_orth a, smul_zero, add_zero, map_sum]
    simp only [map_smul, smul_eq_mul, hz]
    rw [show ∑ b, (Zhat F F').adjugate b (Fin.last D.R.rS) * Zhat F F' a.castSucc b =
        ∑ b, Zhat F F' a.castSucc b * (Zhat F F').adjugate b (Fin.last D.R.rS) from
      Finset.sum_congr rfl fun b _ => mul_comm _ _, hm, mul_zero]
  intro x hx
  simp only [brS]
  refine Submodule.span_induction (p := fun y _ => (VS D).hT y (NormalVectorPairings.yv F F') = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩
    exact key a
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro c y _ hy
    simp [hy]

theorem X_iso {T : D.host.E} (F : FlagG (VS D) D.R.rS T) : ∀ x ∈ F.X, ∀ x' ∈ F.X, brS (VS D) x x' = 0 := by
  intro x hx x' hx'
  simp only [brS]
  refine Submodule.span_induction (p := fun y _ => (VS D).hT y x = 0) ?_ ?_ ?_ ?_ hx'
  · rintro _ ⟨b, rfl⟩
    refine Submodule.span_induction (p := fun y _ => (VS D).hT (F.e b) y = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, rfl⟩
      exact F.e_iso b a
    · simp
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro c y _ hy
      simp [hy]
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro c y _ hy
    simp [hy]

theorem abs_norm_TG (n : ℕ) (g : D.host.E) :
    |((Algebra.norm ℚ ((n : D.host.E) * g) : ℚ) : ℝ)| =
      (n : ℝ) ^ (2 * D.R.f) * (∏ w : InfinitePlace D.host.E, w g) ^ 2 := by
  have hc : ∀ w : InfinitePlace D.host.E, w.mult = 2 := by
    intro w
    have hnr : ¬ w.IsReal := by
      intro hw
      have hr := InfinitePlace.isReal_iff.mp hw
      have h2 : starRingEnd ℂ (w.embedding D.host.sqq) = w.embedding D.host.sqq :=
        RingHom.congr_fun hr _
      have h1 : w.embedding D.host.sqq ^ 2 = w.embedding (-(D.host.q : D.host.E)) := by
        rw [← map_pow, D.host.sqq_sq]
      have h3 := Complex.conj_eq_iff_re.mp h2
      rw [← h3, map_neg, map_natCast] at h1
      have h4 := congrArg Complex.re h1
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.neg_re, Complex.natCast_re] at h4
      have hq0 : 0 < D.host.q := by have := D.host.qd_big.1; omega
      have hq : (0 : ℝ) < D.host.q := by exact_mod_cast hq0
      nlinarith [mul_self_nonneg (w.embedding D.host.sqq).re]
    simp [InfinitePlace.mult, hnr]
  have hprod := InfinitePlace.prod_eq_abs_norm g
  simp only [hc, Finset.prod_pow] at hprod
  rw [← map_natCast (algebraMap ℚ D.host.E) n, map_mul, Algebra.norm_algebraMap,
    Formalism.MainNotions.BridgeLemma.szf_finrankE D, hprod]
  push_cast
  rw [abs_mul, abs_pow, Nat.abs_cast]

end Formalism.L2.SG.NGCut.NormalIntegrality
