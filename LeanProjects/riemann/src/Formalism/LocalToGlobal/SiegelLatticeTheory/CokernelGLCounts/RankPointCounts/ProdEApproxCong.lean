import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAt

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem one_mem_R {p : PlF D} (a b : Fin (D.R.rS + 1)) :
    (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (M p).R := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (M p).R.one_mem
  · exact (M p).R.zero_mem

theorem mem_R_of_sub_one {p : PlF D} (hA : Agree δ M p) {X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (h : EntIn (latS (D.s.atP p) (ellP p)) (X - 1)) (a b : Fin (D.R.rS + 1)) : X a b ∈ (M p).R := by
  have e : X a b = (X - 1) a b + (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b := by
    rw [Matrix.sub_apply]; ring
  rw [e]
  exact (M p).R.add_mem (latS_R hA (h a b)) (one_mem_R M a b)

theorem cong_at {p : PlF D} (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ∃ c : (D.s.atP p).Fp, c ≠ 0 ∧ c ∈ 𝒪[(D.s.atP p).Fp] ∧ ∀ k : ProdE.StP M δ u u' w p,
      EntIn (latS (D.s.atP p) c) ((k.1.1 : ProdE.MP p) - 1) → EntIn (latS (D.s.atP p) c) ((k.1.2.unop : ProdE.MP p) - 1) →
        k ∈ ProdE.AP M δ u u' w p ⊓ ProdE.CPL M δ u u' w hA L U hL hU := by
  set Lp := lOf δ M p L U
  set Lpi := lOf δ M p L⁻¹ U⁻¹
  set Up := ρOf δ M p L U
  set Upi := ρOf δ M p L⁻¹ U⁻¹
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLL : Lp * Lpi = 1 := by
    rw [← lOf_mul δ M hA, hLi.2.2, hUi.2.1, lOf_one δ M hA]
  have hUU : Upi * Up = 1 := by
    rw [← ρOf_mul δ M hA, hLi.2.2, hUi.2.1, ρOf_one δ M hA]
  have hLp := ProdE.lOf_loUni M δ hA L U hL hU
  have hLpi := ProdE.lOf_loUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  have hUp := ProdE.ρOf_upUni M δ hA L U hL hU
  have hUpi := ProdE.ρOf_upUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  obtain ⟨s1, hs10, hs1O, hs1⟩ := bounded_mat (L := D.s.atP p) Lp
  obtain ⟨s2, hs20, hs2O, hs2⟩ := bounded_mat (L := D.s.atP p) Lpi
  obtain ⟨s3, hs30, hs3O, hs3⟩ := bounded_mat (L := D.s.atP p) Up
  obtain ⟨s4, hs40, hs4O, hs4⟩ := bounded_mat (L := D.s.atP p) Upi
  refine ⟨ellP p * (s1 * s2 * s3 * s4),
    mul_ne_zero (ellP_ne p) (mul_ne_zero (mul_ne_zero (mul_ne_zero hs10 hs20) hs30) hs40),
    Subring.mul_mem _ (ellP_mem p) (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O),
    fun k h1 h2 => ?_⟩
  obtain ⟨hk1, hk2, -⟩ := k.2
  have hO12 : s1 * s2 * s3 * s4 ∈ 𝒪[(D.s.atP p).Fp] :=
    Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O
  have h1l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.1 : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h1
  have h2l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.2.unop : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h2
  have h1c : EntIn (latS (D.s.atP p) (ellP p)) (Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi) :=
    entIn_sandwich hs1 hs2 (entIn_latS_of_eq (t := s3 * s4) (by ring) (Subring.mul_mem _ hs3O hs4O) h1)
  have h2c : EntIn (latS (D.s.atP p) (ellP p)) (Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up) :=
    entIn_sandwich hs4 hs3 (entIn_latS_of_eq (t := s1 * s2) (by ring) (Subring.mul_mem _ hs1O hs2O) h2)
  have e1 : Lp * (k.1.1 : ProdE.MP p) * Lpi - 1 = Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hLL]
  have e2 : Upi * (k.1.2.unop : ProdE.MP p) * Up - 1 = Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
  have hc1 := ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hLp hk1) hLpi
  have hc2 := ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hUpi hk2) hUp
  refine Subgroup.mem_inf.2 ⟨⟨⟨fun a => (hk1 a a).2 rfl, fun a b h => (hk1 a b).1 h,
    mem_R_of_sub_one M δ hA h1l⟩, ⟨fun a => (hk2 a a).2 rfl, fun a b h => (hk2 a b).1 h, mem_R_of_sub_one M δ hA h2l⟩⟩,
    ⟨⟨fun a => (hc1 a a).2 rfl, fun a b h => (hc1 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e1]; exact h1c)⟩,
    ⟨fun a => (hc2 a a).2 rfl, fun a b h => (hc2 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e2]; exact h2c)⟩⟩⟩

end Cong

end Formalism.L2.SG.Pf.ProdEApprox
