import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsLoOfIntLow

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section IntM

variable {K : Type*} [CommRing K] (I : Subring K) {n : ℕ}

theorem int_mul {A B : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) :
    ∀ i j, (A * B) i j ∈ I := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem (hA i k) (hB k j)

theorem int_diag {d : Fin n → K} (hd : ∀ a, d a ∈ I) : ∀ i j, Matrix.diagonal d i j ∈ I := by
  intro i j
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact I.zero_mem

end IntM

section Good

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem gY_int (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) {U₁ X' : PairVal.MatR D} (hX' : IsLo X')
    (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0) (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O)
    (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) :
    ∀ i j, ((gY w U₁ X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
  have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
  have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
  have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
  have hcm : ∀ i j, ((cOf (fσ w) (fun a => pv w.1 a) X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    simp only [Matrix.map_apply, cOf, Matrix.of_apply, Ring.inverse_eq_inv', map_mul]
    exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem (hν' _) (hX _ _)) (hν _)
  have hci : ∀ i j, (((cOf (fσ w) (fun a => pv w.1 a) X')⁻¹).map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    rw [ZsVolGrp.inv_eq_adj (det_up' hc)]
    have e := RingHom.map_adjugate (D.s.atP p).ιE (cOf (fσ w) (fun a => pv w.1 a) X')
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at e
    rw [e]
    exact ZsVolGrp.adj_mem (D.s.atP p).O hcm i j
  simp only [gY, Matrix.map_mul]
  exact int_mul _ (int_mul _ hU' hci) hU

theorem good_at (p : PlF D) (hM : (Zd.M p).split = none) (w : Point D.host.E (D.R.rS + 1))
    {L₁ U₁ A₀ B₀ X' : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀)
    (hX' : IsLo X') (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0)
    (hcf : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O)
    (hcfi : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O)
    (hA : ∀ i j, (D.s.atP p).ιE (A₀ i j) ∈ (D.s.atP p).O) (hB : ∀ i j, (D.s.atP p).ιE (B₀ i j) ∈ (D.s.atP p).O)
    (hL : ∀ i j, (D.s.atP p).ιE (L₁ i j) ∈ (D.s.atP p).O) (hL' : ∀ i j, (D.s.atP p).ιE (L₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O) (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) : GoodAt Zd p w L₁ U₁ A₀ B₀ X' := by
  obtain ⟨hgX, hgY, -⟩ : IsLo (gX L₁ X') ∧ IsUp (gY w U₁ X') ∧ True := by
    have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
    have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
    have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
    exact ⟨isLo_mul (isLo_mul hL₁ hX') (isLo_inv hL₁), isUp_mul (isUp_mul (isUp_inv hU₁) (isUp_inv hc)) hU₁, trivial⟩
  have hgYi := gY_int p w hX' hpat hU hU' hν hν' hX
  have hR : (Zd.M p).R = (D.s.atP p).O := Formalism.L2.SG.Pf.LMK.R_eq_O (Zd.agree p) hM
  have hlo := locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  have hup := locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  refine ⟨⟨hlo.1, hlo.2, fun i j => ?_⟩, ⟨hup.1, fun a b hab => hup.2 b a hab, fun i j => ?_⟩⟩
  · rw [hR, locL_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcf) ?_) (int_diag _ hcfi) i j
    simp only [gX, Matrix.map_mul]
    exact int_mul _ hA (int_mul _ (int_mul _ hL hX) hL')
  · rw [hR, locR_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcfi) ?_) (int_diag _ hcf) i j
    rw [Matrix.map_mul]
    exact int_mul _ hgYi hB

end Good

end Formalism.L2.SG.Pf.TupGlobApprox
