import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemRNone

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good3

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

set_option maxHeartbeats 1000000 in
theorem good_places (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ∃ S : Finset (PlF D), (∀ p, p ∉ S → ProdE.AP M δ u u' w p = ProdE.CPL M δ u u' w (hA p) L U hL hU) ∧
      ∀ p, p ∉ S → ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
        (∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O) →
          ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p := by
  classical
  set X : Finset D.host.E := Finset.univ.image (fun a : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.pv w.1 a) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L⁻¹ ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U⁻¹ ij.1 ij.2) with hX
  have hev := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA X
  have hfin := Filter.eventually_cofinite.1 hev
  refine ⟨hfin.toFinset, ?_⟩
  have key : ∀ p, p ∉ hfin.toFinset → (M p).split = none ∧
      (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
      ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
      (∀ t ∈ X, (D.s.atP p).ιE t ∈ (D.s.atP p).O) ∧ (∀ t ∈ X, t ≠ 0 → (D.s.atP p).ιE t⁻¹ ∈ (D.s.atP p).O) := by
    intro p hp
    have hp' : ¬ ¬ _ := fun h => hp (hfin.mem_toFinset.2 h)
    obtain ⟨h1, h2, h3, h4⟩ := not_not.1 hp'
    refine ⟨h1, h2, h3, fun t ht => ?_, fun t ht ht0 => ?_⟩
    · by_cases ht0 : t = 0
      · rw [ht0, map_zero]; exact (D.s.atP p).O.zero_mem
      · have := (h4 t ht 0 (by simpa using ht0)).1
        simpa using this
    · have := (h4 t ht 0 (by simpa using ht0)).2
      simpa using this
  have hpvX : ∀ a : Fin (D.R.rS + 1), Formalism.L2.SG.Pf.pv w.1 a ∈ X := fun a =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun a : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.pv w.1 a) (Finset.mem_univ a)))))
  have hLX : ∀ i j, L i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L ij.1 ij.2) (Finset.mem_univ (i, j))))))
  have hUX : ∀ i j, U i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U ij.1 ij.2) (Finset.mem_univ (i, j)))))
  have hLiX : ∀ i j, L⁻¹ i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L⁻¹ ij.1 ij.2) (Finset.mem_univ (i, j))))
  have hUiX : ∀ i j, U⁻¹ i j ∈ X := fun i j =>
    Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U⁻¹ ij.1 ij.2) (Finset.mem_univ (i, j)))
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  refine ⟨fun p hp => ?_, fun p hp g hg => ?_⟩
  · obtain ⟨hs, hδ, huP, hXi, -⟩ := key p hp
    have hR := mem_R_none M δ (hA p) hs
    have i1 := lOf_ρOf_int M δ (hA p) hs hδ huP L U (fun i j => hXi _ (hLX i j)) (fun i j => hXi _ (hUX i j))
    have i2 := lOf_ρOf_int M δ (hA p) hs hδ huP L⁻¹ U⁻¹ (fun i j => hXi _ (hLiX i j)) (fun i j => hXi _ (hUiX i j))
    have hLp := ProdE.lOf_loUni M δ (hA p) L U hL hU
    have hLpi := ProdE.lOf_loUni M δ (hA p) L⁻¹ U⁻¹ hLi.1 hUi.1
    have hUp := ProdE.ρOf_upUni M δ (hA p) L U hL hU
    have hUpi := ProdE.ρOf_upUni M δ (hA p) L⁻¹ U⁻¹ hLi.1 hUi.1
    have iLp : Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p L U) :=
      ⟨fun a => (hLp a a).2 rfl, fun a b h => (hLp a b).1 h, fun a b => (hR _).2 (i1.1 a b)⟩
    have iLpi : Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p L⁻¹ U⁻¹) :=
      ⟨fun a => (hLpi a a).2 rfl, fun a b h => (hLpi a b).1 h, fun a b => (hR _).2 (i2.1 a b)⟩
    have iUp : Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p L U) :=
      ⟨fun a => (hUp a a).2 rfl, fun a b h => (hUp a b).1 h, fun a b => (hR _).2 (i1.2 a b)⟩
    have iUpi : Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p L⁻¹ U⁻¹) :=
      ⟨fun a => (hUpi a a).2 rfl, fun a b h => (hUpi a b).1 h, fun a b => (hR _).2 (i2.2 a b)⟩
    have hLL := ProdE.lp_inv M δ (hA p) L U hL hU
    have hUU := ProdE.up_inv M δ (hA p) L U hL hU
    ext k
    constructor
    · rintro ⟨hk1, hk2⟩
      exact ⟨ZsVolGrp.intLow_mul _ (ZsVolGrp.intLow_mul _ iLp hk1) iLpi,
        ZsVolGrp.intUp_mul _ (ZsVolGrp.intUp_mul _ iUpi hk2) iUp⟩
    · rintro ⟨hk1, hk2⟩
      refine ⟨?_, ?_⟩
      · have e : ((k.1.1 : ProdE.GLp p) : ProdE.MP p) = lOf δ M p L⁻¹ U⁻¹ *
            (lOf δ M p L U * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) * lOf δ M p L⁻¹ U⁻¹) * lOf δ M p L U := by
          rw [show lOf δ M p L⁻¹ U⁻¹ * (lOf δ M p L U * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) * lOf δ M p L⁻¹ U⁻¹) *
              lOf δ M p L U = (lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U) * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) *
                (lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U) by simp only [Matrix.mul_assoc], hLL, Matrix.one_mul, Matrix.mul_one]
        rw [e]
        exact ZsVolGrp.intLow_mul _ (ZsVolGrp.intLow_mul _ iLpi hk1) iLp
      · have e : ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) = ρOf δ M p L U *
            (ρOf δ M p L⁻¹ U⁻¹ * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) * ρOf δ M p L U) * ρOf δ M p L⁻¹ U⁻¹ := by
          rw [show ρOf δ M p L U * (ρOf δ M p L⁻¹ U⁻¹ * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) * ρOf δ M p L U) *
              ρOf δ M p L⁻¹ U⁻¹ = (ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹) * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) *
                (ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹) by simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one]
        rw [e]
        exact ZsVolGrp.intUp_mul _ (ZsVolGrp.intUp_mul _ iUp hk2) iUpi
  · obtain ⟨hs, hδ, huP, hXi, hXinv⟩ := key p hp
    have hR := mem_R_none M δ (hA p) hs
    have hb := bOf_int w g hg (fun a => ⟨hXi _ (hpvX a), hXinv _ (hpvX a) (Formalism.L2.SG.Pf.pv_ne' w a)⟩)
    have i0 := lOf_ρOf_int M δ (hA p) hs hδ huP _ _ hg hb
    obtain ⟨hπl, hπρ, -⟩ := (ProdE.πP M δ u u' w (hA p) g).2
    exact ⟨⟨fun a => (hπl a a).2 rfl, fun a b h => (hπl a b).1 h, fun a b => (hR _).2 (i0.1 a b)⟩,
      ⟨fun a => (hπρ a a).2 rfl, fun a b h => (hπρ a b).1 h, fun a b => (hR _).2 (i0.2 a b)⟩⟩

end Good3

end Formalism.L2.SG.Pf.ProdEApprox
