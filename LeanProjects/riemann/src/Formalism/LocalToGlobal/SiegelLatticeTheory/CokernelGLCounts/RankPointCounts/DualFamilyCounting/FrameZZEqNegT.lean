import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MMatEntryMeasurable
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {n : ℕ} (ε : Fin n → Bool)

private theorem hJ_eq_lemma (x y : Fin n → ℂ) :
    hJ ε x y = ∑ i, star (x i) * ((if ε i then 1 else -1) * y i) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, mulVec_diagonal, Pi.star_apply]

theorem hJa (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  rw [hJ_eq_lemma, hJ_eq_lemma, hJ_eq_lemma, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

theorem hJs (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  rw [hJ_eq_lemma, hJ_eq_lemma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem hJsub (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  rw [hJ_eq_lemma, hJ_eq_lemma, hJ_eq_lemma, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem hJswap (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  rw [hJ_eq_lemma, hJ_eq_lemma, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp only [star_mul', star_star, star_one, star_neg] <;> ring

theorem hJzr (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  rw [hJ_eq_lemma]
  simp

theorem hJzl (y : Fin n → ℂ) : hJ ε 0 y = 0 := by
  rw [hJ_eq_lemma]
  simp

theorem hJal (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  rw [hJ_eq_lemma, hJ_eq_lemma, hJ_eq_lemma, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, star_add]
  ring

theorem hJsl (x y : Fin n → ℂ) (c : ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  rw [hJ_eq_lemma, hJ_eq_lemma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem hJsubl (x x' y : Fin n → ℂ) : hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  rw [hJ_eq_lemma, hJ_eq_lemma, hJ_eq_lemma, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, star_sub]
  ring

theorem hJsumr {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, c i * hJ ε x (y i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hJzr]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hJa, hJs, ih]

theorem hJsuml {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε (∑ i ∈ s, c i • y i) x = ∑ i ∈ s, star (c i) * hJ ε (y i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hJzl]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hJal, hJsl, ih]

theorem hJ_nondeg {d : Fin n → ℂ} (h : ∀ y, hJ ε y d = 0) : d = 0 := by
  funext i
  have h1 := h (Pi.single i 1)
  rw [hJ_eq_lemma, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at h1
  simp only [Pi.single_eq_same, star_one, one_mul] at h1
  split_ifs at h1
  · simpa using h1
  · simpa using h1

theorem hJ_test {ι : Type*} (b : ι → Fin n → ℂ) (hs : Submodule.span ℂ (Set.range b) = ⊤)
    {x x' : Fin n → ℂ} (h : ∀ i, hJ ε (b i) x = hJ ε (b i) x') : x = x' := by
  have key : ∀ y, hJ ε y (x - x') = 0 := by
    intro y
    have hy : y ∈ Submodule.span ℂ (Set.range b) := by
      rw [hs]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      rw [hJsub, h i, sub_self]
    | zero => exact hJzl ε _
    | add a c _ _ ha hc => rw [hJal, ha, hc, add_zero]
    | smul c a _ ha => rw [hJsl, ha, mul_zero]
  exact sub_eq_zero.mp (hJ_nondeg ε key)

theorem span_perp {r : ℕ} (e : Fin r → Fin n → ℂ) (S : Set (Fin r)) (y : Fin n → ℂ)
    (hy : ∀ c ∈ S, hJ ε y (e c) = 0) {d : Fin n → ℂ} (hd : d ∈ Submodule.span ℂ (e '' S)) :
    hJ ε y d = 0 := by
  induction hd using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, rfl⟩ := hz
    exact hy c hc
  | zero => exact hJzr ε y
  | add a c _ _ ha hc => rw [hJa, ha, hc, add_zero]
  | smul c a _ ha => rw [hJs, ha, mul_zero]

theorem span_recon {r : ℕ} (e f : Fin r → Fin n → ℂ) (S : Set (Fin r))
    (hfe : ∀ b c, hJ ε (f b) (e c) = if b = c then 1 else 0) {d : Fin n → ℂ}
    (hd : d ∈ Submodule.span ℂ (e '' S)) : d = ∑ c, hJ ε (f c) d • e c := by
  induction hd using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, _, rfl⟩ := hz
    simp only [hfe]
    simp [ite_smul]
  | zero => simp [hJzr]
  | add a c _ _ ha hc =>
    conv_lhs => rw [ha, hc]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hJa, add_smul]
  | smul c a _ ha =>
    conv_lhs => rw [ha]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hJs, smul_smul]

theorem mulVec_split (G : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : G *ᵥ x = x + (G - 1) *ᵥ x := by
  rw [sub_mulVec, one_mulVec]
  abel

end Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)

theorem fr_ee (a b : Fin D.R.rS) : hJ (X.B.I.ε v) (eV X v a) (eV X v b) = 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_ee X a b
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [eV, eV, Formalism.L2.SG.Pf.hJ_rv_sc, h, map_zero]

theorem fr_ff (a b : Fin D.R.rS) : hJ (X.B.I.ε v) (fV X v a) (fV X v b) = 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_ff X a b
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [fV, fV, Formalism.L2.SG.Pf.hJ_rv_sc, h, map_zero]

theorem fr_ef (a b : Fin D.R.rS) : hJ (X.B.I.ε v) (eV X v a) (fV X v b) = if a = b then 1 else 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_ef X a b
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [eV, fV, Formalism.L2.SG.Pf.hJ_rv_sc, h]
  split_ifs <;> simp

theorem fr_fe (a b : Fin D.R.rS) : hJ (X.B.I.ε v) (fV X v a) (eV X v b) = if a = b then 1 else 0 := by
  rw [hJswap, fr_ef]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem fr_ez (a : Fin D.R.rS) : hJ (X.B.I.ε v) (eV X v a) (zV X u v) = 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_ez X u a
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [eV, zV, Formalism.L2.SG.Pf.hJ_rv_sc, h, map_zero]

theorem fr_fz (a : Fin D.R.rS) : hJ (X.B.I.ε v) (fV X v a) (zV X u v) = 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_fz X u a
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [fV, zV, Formalism.L2.SG.Pf.hJ_rv_sc, h, map_zero]

theorem frame_z_z_eq_neg_t : hJ (X.B.I.ε v) (zV X u v) (zV X u v) = -(((D.mem u).A.T : ℕ) : ℂ) := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_crd X (X.zu u) (X.zu u)
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [zV, HidaSetting.zR, Formalism.L2.SG.Pf.hJ_rv_sc, h, X.zu_norm, map_neg, map_natCast, map_neg, map_natCast]

theorem fr_ew (a : Fin D.R.rS) (j : Fin D.R.k) : hJ (X.B.I.ε v) (eV X v a) (X.wfr u v j) = 0 :=
  ((X.wfr_perp u v j).1 a).1

theorem fr_fw (a : Fin D.R.rS) (j : Fin D.R.k) : hJ (X.B.I.ε v) (fV X v a) (X.wfr u v j) = 0 :=
  ((X.wfr_perp u v j).1 a).2

theorem fr_zw (j : Fin D.R.k) : hJ (X.B.I.ε v) (zV X u v) (X.wfr u v j) = 0 :=
  (X.wfr_perp u v j).2

theorem fr_ww (i j : Fin D.R.k) : hJ (X.B.I.ε v) (X.wfr u v i) (X.wfr u v j) = if i = j then 1 else 0 :=
  X.wfr_on u v i j

theorem fr_we (j : Fin D.R.k) (a : Fin D.R.rS) : hJ (X.B.I.ε v) (X.wfr u v j) (eV X v a) = 0 := by
  rw [hJswap, fr_ew, star_zero]

theorem fr_wf (j : Fin D.R.k) (a : Fin D.R.rS) : hJ (X.B.I.ε v) (X.wfr u v j) (fV X v a) = 0 := by
  rw [hJswap, fr_fw, star_zero]

theorem fr_wz (j : Fin D.R.k) : hJ (X.B.I.ε v) (X.wfr u v j) (zV X u v) = 0 := by
  rw [hJswap, fr_zw, star_zero]

theorem fr_ze (a : Fin D.R.rS) : hJ (X.B.I.ε v) (zV X u v) (eV X v a) = 0 := by
  rw [hJswap, fr_ez, star_zero]

theorem fr_zf (a : Fin D.R.rS) : hJ (X.B.I.ε v) (zV X u v) (fV X v a) = 0 := by
  rw [hJswap, fr_fz, star_zero]

def fam : Fin D.R.rS ⊕ (Fin D.R.rS ⊕ (Fin D.R.k ⊕ Unit)) → Fin X.B.I.n → ℂ :=
  Sum.elim (eV X v) (Sum.elim (fV X v) (Sum.elim (X.wfr u v) fun _ => zV X u v))

theorem T_ne : (((D.mem u).A.T : ℕ) : ℂ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero

theorem fam_li : LinearIndependent ℂ (fam X u v) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ y, ∑ i, c i * hJ (X.B.I.ε v) y (fam X u v i) = 0 := by
    intro y
    rw [← hJsumr, hc, hJzr]
  rintro (a | a | j | ⟨⟩)
  · have h := key (fV X v a)
    simpa [Fintype.sum_sum_type, fam, fr_fe, fr_ff, fr_fw, fr_fz] using h
  · have h := key (eV X v a)
    simpa [Fintype.sum_sum_type, fam, fr_ee, fr_ef, fr_ew, fr_ez] using h
  · have h := key (X.wfr u v j)
    simpa [Fintype.sum_sum_type, fam, fr_we, fr_wf, fr_ww, fr_wz] using h
  · have h := key (zV X u v)
    simp [Fintype.sum_sum_type, fam, fr_ze, fr_zf, fr_zw, frame_z_z_eq_neg_t] at h
    rcases h with h | h
    · exact h
    · exact absurd h ((D.mem u).A.T_prime).ne_zero

theorem card_fam : Fintype.card (Fin D.R.rS ⊕ (Fin D.R.rS ⊕ (Fin D.R.k ⊕ Unit))) = X.B.I.n := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  rw [X.n_eq]
  unfold Formalism.BasicNotions.Ranks.rS Formalism.BasicNotions.Ranks.r
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  omega

theorem fam_span : Submodule.span ℂ (Set.range (fam X u v)) = ⊤ := by
  exact (fam_li X u v).span_eq_top_of_card_eq_finrank (by rw [card_fam, Module.finrank_fin_fun])

end Formalism.L2.SG.Pf.LsNc5
