import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxCloseAt

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem mem_stSet_of_pat (a : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a)
    (hpat : ∀ i j, Formalism.L2.SG.Pf.fσ w j < Formalism.L2.SG.Pf.fσ w i → a i j = 0) :
    ∃ b : Formalism.L2.SG.PairVal.MatR D, IsUpUni b ∧ a * ptMat w * b = ptMat w := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ x, σ (σ x) = x := Formalism.L2.SG.Pf.fσ_fσ w
  set ν : Fin (D.R.rS + 1) → D.host.E := fun x => Formalism.L2.SG.Pf.pv w.1 x
  have hν : ∀ x, IsUnit (ν x) := fun x => isUnit_iff_ne_zero.2 (Formalism.L2.SG.Pf.pv_ne' w x)
  have hfix := fix_cOf hσ ν hν a
  obtain ⟨hc1, hc2⟩ := cOf_up hσ ν a (fun i => (ha i i).2 rfl) hpat hν
  have hcU : IsUpUni (cOf σ ν a) := fun i j => ⟨fun h => hc2 i j h, fun h => by subst h; exact hc1 i⟩
  obtain ⟨hbU, -, hcb⟩ := ZsVolGrp.isUpUni_inv hcU
  refine ⟨(cOf σ ν a)⁻¹, hbU, ?_⟩
  rw [ptMat_mono, hfix, Matrix.mul_assoc, hcb, Matrix.mul_one]

theorem approx_core (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (S : Finset (PlF D))
    (hS : ∀ p, p ∉ S → ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
      (∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O) →
        ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p)
    (h : ∀ p, ProdE.StP M δ u u' w p) :
    ∃ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
      (∀ p ∈ S, (h p)⁻¹ * ProdE.πP M δ u u' w (hA p) g ∈
        ProdE.AP M δ u u' w p ⊓ ProdE.CPL M δ u u' w (hA p) L U hL hU) ∧
      ∀ p, p ∉ S → ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p := by
  classical
  set σ := Formalism.L2.SG.Pf.fσ w with hσd
  choose c hc0 hcO hcong using fun p => cong_at M δ u u' w (hA p) L U hL hU
  choose τ hτ1 hτ2 hτ3 c' hc'0 hc'O hcl using fun p => close_at M δ u u' w (hA p) (h p) (c p) (hc0 p) (hcO p)
  choose t ht1 ht2 using fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
    sa_lat (fun p => D.s.atP p) S (fun p => τ p ij.1 ij.2) c' (fun p _ => hc'0 p)
  set a : Formalism.L2.SG.PairVal.MatR D := fun i j =>
    if j < i ∧ σ i < σ j then t (i, j) else (1 : Formalism.L2.SG.PairVal.MatR D) i j with had
  have ha : IsLoUni a := by
    intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · have : ¬ (j < i ∧ σ i < σ j) := fun h' => absurd h'.1 (not_lt.2 hij.le)
      simp only [had, if_neg this]
      exact Matrix.one_apply_ne (ne_of_lt hij)
    · subst hij
      have : ¬ (i < i ∧ σ i < σ i) := fun h' => lt_irrefl _ h'.1
      simp only [had, if_neg this, Matrix.one_apply_eq]
  have hpat : ∀ i j, σ j < σ i → a i j = 0 := by
    intro i j hij
    have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    have : ¬ (j < i ∧ σ i < σ j) := fun h' => absurd h'.2 (not_lt.2 hij.le)
    simp only [had, if_neg this]
    exact Matrix.one_apply_ne hne
  have hdet : IsUnit a.det := by rw [ZsVolGrp.det_lo (fun x => (ha x x).2 rfl) (fun x y hxy => (ha x y).1 hxy)]; exact isUnit_one
  obtain ⟨b, hb, hab⟩ := mem_stSet_of_pat w a ha hpat
  let gGL : Formalism.L2.SG.PairVal.GLR D := Matrix.nonsingInvUnit a hdet
  have hgv : (gGL : Formalism.L2.SG.PairVal.MatR D) = a := rfl
  let g : Formalism.L2.SG.Pf.VolPinAsm.StG w := ⟨gGL, ⟨by rw [hgv]; exact ha, b, hb, by rw [hgv]; exact hab⟩⟩
  have hgv' : ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = a := rfl
  refine ⟨g, fun p hp => ?_, fun p hp => hS p hp g ?_⟩
  · have hclose : EntIn (latS (D.s.atP p) (c' p))
        (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE - τ p) := by
      intro i j
      rw [hgv', Matrix.sub_apply, Matrix.map_apply]
      by_cases hz : j < i ∧ σ i < σ j
      · simp only [had, if_pos hz]
        exact mem_latS.2 (ht1 (i, j) p hp)
      · simp only [had, if_neg hz]
        have e : (D.s.atP p).ιE ((1 : Formalism.L2.SG.PairVal.MatR D) i j) - τ p i j = 0 := by
          rcases lt_trichotomy i j with hij | hij | hij
          · rw [Matrix.one_apply_ne (ne_of_lt hij), map_zero, hτ1 p i j hij, sub_zero]
          · subst hij; rw [Matrix.one_apply_eq, map_one, hτ2 p i, sub_self]
          · have hs : σ j < σ i := by
              rcases lt_or_gt_of_ne (fun e : σ i = σ j => (ne_of_gt hij) (by
                rw [← Formalism.L2.SG.Pf.fσ_fσ w i, ← Formalism.L2.SG.Pf.fσ_fσ w j]; exact congrArg _ e)) with h' | h'
              · exact absurd ⟨hij, h'⟩ hz
              · exact h'
            rw [Matrix.one_apply_ne (ne_of_gt hij), map_zero, hτ3 p i j hs, sub_zero]
        rw [e]; exact (latS (D.s.atP p) (c' p)).zero_mem
    obtain ⟨h1, h2⟩ := hcl p g hclose
    exact hcong p _ h1 h2
  · intro i j
    rw [hgv']
    by_cases hz : j < i ∧ σ i < σ j
    · simp only [had, if_pos hz]
      exact ht2 (i, j) p hp
    · simp only [had, if_neg hz]
      rw [Matrix.one_apply]
      split_ifs
      · rw [map_one]; exact (D.s.atP p).O.one_mem
      · rw [map_zero]; exact (D.s.atP p).O.zero_mem

end Main

end Formalism.L2.SG.Pf.ProdEApprox
