import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowVZero

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev pV (v : InfinitePlace X.B.I.F) (p : (VS D).V) : Fin X.B.I.n → ℂ := rv X.B.I v (X.crd p)

theorem hJ_pV (v : InfinitePlace X.B.I.F) (p q : (VS D).V) :
    hJ (X.B.I.ε v) (pV X v p) (pV X v q) = embS D (X.pl v) ((VS D).hT p q) :=
  PI.SchurPlaces.hJ_psiV X v p q

theorem Tpos : (0 : ℝ) < (((D.mem u).A.T : ℕ) : ℝ) := by
  exact_mod_cast ((D.mem u).A.T_prime).pos

theorem decompY (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → ℂ)
    (hye : ∀ a, hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.eV X v a) y = 0)
    (hyf : ∀ a, hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.fV X v a) y = 0) :
    y = ∑ c, hJ (X.B.I.ε v) (X.wfr u v c) y • X.wfr u v c +
      (-(hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) y) / ((((D.mem u).A.T : ℕ) : ℝ) : ℂ)) •
        Formalism.L2.SG.Pf.LsNc5.zV X u v := by
  have hy : y ∈ Submodule.span ℂ (Set.range (Formalism.L2.SG.Pf.LsNc5.fam X u v)) := by
    rw [Formalism.L2.SG.Pf.LsNc5.fam_span]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
  subst hc

  have pair : ∀ t : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) t (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      (∑ a, c (Sum.inl a) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.eV X v a)) +
        ((∑ a, c (Sum.inr (Sum.inl a)) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.fV X v a)) +
        ((∑ j, c (Sum.inr (Sum.inr (Sum.inl j))) * hJ (X.B.I.ε v) t (X.wfr u v j)) +
          c (Sum.inr (Sum.inr (Sum.inr ()))) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.zV X u v))) := by
    intro t
    rw [PI.SchurPlaces.hJ_sum_r]
    simp only [Fintype.sum_sum_type, Formalism.L2.SG.Pf.LsNc5.fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  have hcf : ∀ a, c (Sum.inr (Sum.inl a)) = 0 := by
    intro a
    have h := hye a
    rw [pair] at h
    simpa [Formalism.L2.SG.Pf.LsNc5.fr_ee, Formalism.L2.SG.Pf.LsNc5.fr_ef, Formalism.L2.SG.Pf.LsNc5.fr_ew,
      Formalism.L2.SG.Pf.LsNc5.fr_ez] using h
  have hce : ∀ a, c (Sum.inl a) = 0 := by
    intro a
    have h := hyf a
    rw [pair] at h
    simpa [Formalism.L2.SG.Pf.LsNc5.fr_fe, Formalism.L2.SG.Pf.LsNc5.fr_ff, Formalism.L2.SG.Pf.LsNc5.fr_fw,
      Formalism.L2.SG.Pf.LsNc5.fr_fz, hcf] using h
  have hw : ∀ j, hJ (X.B.I.ε v) (X.wfr u v j) (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      c (Sum.inr (Sum.inr (Sum.inl j))) := by
    intro j
    rw [pair]
    simp [Formalism.L2.SG.Pf.LsNc5.fr_we, Formalism.L2.SG.Pf.LsNc5.fr_wf, Formalism.L2.SG.Pf.LsNc5.fr_ww,
      Formalism.L2.SG.Pf.LsNc5.fr_wz]
  have hz : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      c (Sum.inr (Sum.inr (Sum.inr ()))) * -((((D.mem u).A.T : ℕ) : ℂ)) := by
    rw [pair]
    simp [Formalism.L2.SG.Pf.LsNc5.fr_ze, Formalism.L2.SG.Pf.LsNc5.fr_zf, Formalism.L2.SG.Pf.LsNc5.fr_zw,
      Formalism.L2.SG.Pf.LsNc5.frame_z_z_eq_neg_t]
  simp only [hw, hz]
  have hT := Formalism.L2.SG.Pf.LsNc5.T_ne u
  have hcoef : -(c (Sum.inr (Sum.inr (Sum.inr ()))) * -((((D.mem u).A.T : ℕ) : ℂ))) /
      ((((D.mem u).A.T : ℕ) : ℝ) : ℂ) = c (Sum.inr (Sum.inr (Sum.inr ()))) := by
    push_cast; field_simp
  rw [hcoef]
  simp only [Fintype.sum_sum_type, Formalism.L2.SG.Pf.LsNc5.fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
    hce, hcf, zero_smul, Finset.sum_const_zero, zero_add]

theorem decompW (v : InfinitePlace X.B.I.F) (x : (VS D).V) (hx : InW X x) :
    pV X v x = ∑ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v x) • X.wfr u v c +
      (-(hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v x)) / ((((D.mem u).A.T : ℕ) : ℝ) : ℂ)) •
        Formalism.L2.SG.Pf.LsNc5.zV X u v := by
  refine decompY X u v _ (fun a => ?_) (fun a => ?_)
  · show hJ (X.B.I.ε v) (pV X v (X.eX a)) (pV X v x) = 0
    rw [hJ_pV, (hx a).1, map_zero]
  · show hJ (X.B.I.ε v) (pV X v (X.fY a)) (pV X v x) = 0
    rw [hJ_pV, (hx a).2, map_zero]

theorem rowV_w (x : (VS D).V) (v : InfinitePlace X.B.I.F) (j : Fin D.R.k) :
    rowV X u x v (Fin.castSucc j) = hJ (X.B.I.ε v) (pV X v x) (X.wfr u v j) := by
  simp [rowV]

theorem rowV_last_eq_hJ (x : (VS D).V) (v : InfinitePlace X.B.I.F) :
    rowV X u x v (Fin.last D.R.k) = hJ (X.B.I.ε v) (pV X v x) (Formalism.L2.SG.Pf.LsNc5.zV X u v) := by
  simp [rowV]
  rfl

theorem rowV_gram (v : InfinitePlace X.B.I.F) (x y : (VS D).V) (hy : InW X y) :
    embS D (X.pl v) ((VS D).hT x y) =
      (∑ j : Fin D.R.k, rowV X u x v (Fin.castSucc j) * star (rowV X u y v (Fin.castSucc j))) -
        rowV X u x v (Fin.last D.R.k) * star (rowV X u y v (Fin.last D.R.k)) / (((D.mem u).A.T : ℕ) : ℂ) := by
  rw [← hJ_pV, decompW X u v y hy, PI.SchurPlaces.hJ_add_r, PI.SchurPlaces.hJ_sum_r, PI.SchurPlaces.hJ_smul_r]
  simp only [rowV_w, rowV_last_eq_hJ]
  have e1 : ∀ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v y) = star (hJ (X.B.I.ε v) (pV X v y) (X.wfr u v c)) :=
    fun c => hJ_conj' _ _ _
  have e2 : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v y) =
      star (hJ (X.B.I.ε v) (pV X v y) (Formalism.L2.SG.Pf.LsNc5.zV X u v)) := hJ_conj' _ _ _
  simp only [e1, e2]
  push_cast
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun c _ => by ring
  · ring

theorem rowV_inj (x : (VS D).V) (hx : InW X x) (h : rowV X u x = 0) : x = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hp : pV X v x = 0 := by
    rw [decompW X u v x hx]
    have h1 : ∀ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v x) = 0 := by
      intro c
      rw [hJ_conj', ← rowV_w, h]; simp
    have h2 : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v x) = 0 := by
      rw [hJ_conj', ← rowV_last_eq_hJ, h]; simp
    simp [h1, h2]
  refine (VS D).nondeg.1 x fun y => ?_
  apply (embS D (X.pl v)).injective
  rw [← hJ_pV, hp, map_zero]
  unfold hJ; simp

end Formalism.L2.SG.Pf.NcReal.JX.NOf
