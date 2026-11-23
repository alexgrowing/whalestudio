import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPol
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeight
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.PolarFormula

theorem weight_rowW_le_colSum {N : ℕ} (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (rowW N N) d c ≤ ∑ s, Finsupp.weight (colW N N) d s := by
  classical
  have h2 : ∑ c', Finsupp.weight (rowW N N) d c' = ∑ s, Finsupp.weight (colW N N) d s := by
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, Pi.add_apply, Finset.sum_add_distrib, hf, hg]
    | single v k => simp [Finsupp.weight_apply, rowW, colW, Finsupp.sum_single_index, Pi.single_apply]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)).trans h2.le

theorem sum_rowComp {O : Type} [CommRing O] {N : ℕ} (ν : Fin N → ℕ) (M : ℕ) (hM : ∑ s, ν s ≤ M)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : IsWeightedHomogeneous (colW N N) f ν) :
    ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      weightedHomogeneousComponent (rowW N N) w f = f := by
  classical
  ext d
  rw [coeff_sum]
  simp_rw [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    rw [Fintype.mem_piFinset]
    intro c
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have e := hf (Ne.symm hne)
    calc _ ≤ _ := weight_rowW_le_colSum d c
      _ = ∑ s, ν s := by rw [e]
      _ ≤ M := hM

theorem comp_of_rowZ {O : Type} [CommRing O] {N : ℕ} (H : Fin N → ℤ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h H) (w : Fin N → ℕ) :
    weightedHomogeneousComponent (rowW N N) w h = if (fun c => (w c : ℤ)) = H then h else 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : coeff d h = 0
  · split_ifs <;> simp [hd]
  · have e := hh hd
    have key : Finsupp.weight (rowW N N) d = w ↔ (fun c => (w c : ℤ)) = H := by
      rw [← e]
      constructor
      · intro hw; funext c; rw [GlobalTheory.LvT.KerLat.weight_rowZ, hw]
      · intro hw; funext c
        have := congrFun hw c
        rw [GlobalTheory.LvT.KerLat.weight_rowZ] at this
        exact_mod_cast this.symm
    by_cases hw : (fun c => (w c : ℤ)) = H
    · rw [if_pos (key.mpr hw), if_pos hw]
    · rw [if_neg (mt key.mp hw), if_neg hw, coeff_zero]

theorem eq_zero_of_rowZ_neg {O : Type} [CommRing O] {N : ℕ} (H : Fin N → ℤ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h H) (c : Fin N) (hc : H c < 0) : h = 0 := by
  ext d
  rw [coeff_zero]
  by_contra hd
  have e := congrFun (hh hd) c
  rw [GlobalTheory.LvT.KerLat.weight_rowZ] at e
  omega

theorem rowZ_of_rowW {O : Type} [CommRing O] {N : ℕ} (w : Fin N → ℕ) (h : MvPolynomial (Fin N × Fin N) O)
    (hh : IsWeightedHomogeneous (rowW N N) h w) :
    IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) h (fun c => (w c : ℤ)) := by
  intro d hd
  funext c
  rw [GlobalTheory.LvT.KerLat.weight_rowZ, hh hd]

theorem rowAct_transvection {O : Type} [CommRing O] {N : ℕ} (a b : Fin N) (f : MvPolynomial (Fin N × Fin N) O) :
    rowAct O (n := N) (Matrix.transvection b a (1 : O)) f = (rowGen O a b f).eval 1 := by
  have e : (rowAct O (n := N) (Matrix.transvection b a (1 : O))).toRingHom =
      (Polynomial.evalRingHom (1 : MvPolynomial (Fin N × Fin N) O)).comp (rowGen O a b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [rowAct, rowGen]
    · intro v
      simp [rowAct, rowGen, Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Finset.sum_add_distrib,
        add_mul, ite_and]
      by_cases hv : v.1 = b
      · simp [hv]
      · simp [hv, Ne.symm hv]
  exact congrArg (fun φ : MvPolynomial (Fin N × Fin N) O →+* MvPolynomial (Fin N × Fin N) O => φ f) e

end GlobalTheory.PolarFormula

namespace GlobalTheory.PolarFormula

theorem comp_rowAct_transvection {O : Type} [CommRing O] {N : ℕ} (a b : Fin N) (hab : a ≠ b) (w : Fin N → ℕ)
    (h : MvPolynomial (Fin N × Fin N) O) (hh : IsWeightedHomogeneous (rowW N N) h w) :
    weightedHomogeneousComponent (rowW N N) (w + Pi.single a 1 - Pi.single b 1)
      (rowAct O (n := N) (Matrix.transvection b a (1 : O)) h) = rowDiv O a b 1 h := by
  classical
  have hZ := rowZ_of_rowW w h hh
  rw [rowAct_transvection, Polynomial.eval_eq_sum_range' (n := (rowGen O a b h).natDegree + 2) (by omega)]
  simp only [one_pow, mul_one, map_sum]
  have hk : ∀ k ∈ Finset.range ((rowGen O a b h).natDegree + 2),
      weightedHomogeneousComponent (rowW N N) (w + Pi.single a 1 - Pi.single b 1) ((rowGen O a b h).coeff k) =
        if k = 1 then rowDiv O a b 1 h else 0 := by
    intro k _
    have hs := GlobalTheory.LvT.KerLat.rowDiv_shift O _ a b k h hZ
    change weightedHomogeneousComponent _ _ (rowDiv O a b k h) = _
    rw [comp_of_rowZ _ _ hs]
    by_cases hk1 : k = 1
    · subst hk1
      by_cases hb : 1 ≤ w b
      · rw [if_pos, if_pos rfl]
        funext c
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
        by_cases hca : c = a
        · subst hca; simp [hab]
        · by_cases hcb : c = b
          · subst hcb; simp [hca]; omega
          · simp [hca, hcb]
      · have h0 : rowDiv O a b 1 h = 0 :=
          eq_zero_of_rowZ_neg _ _ hs b (by simp [Pi.single_apply, Ne.symm hab]; omega)
        simp [h0]
    · rw [if_neg hk1, if_neg]
      intro he
      have := congrFun he a
      simp [Pi.single_apply, hab] at this
      omega
  rw [Finset.sum_congr rfl hk, Finset.sum_ite_eq', if_pos (by simp)]

end GlobalTheory.PolarFormula

namespace GlobalTheory.PolarFormula

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

theorem polar_formula : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι) (M : ℕ) (a b : Fin N), ∃ F : FreeAlgebra O (Letter O N ι), ∀ (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)), (∀ σ, Antitone (res N (lam σ))) → (∀ σ w, IsProj O N lam σ w (P σ w)) → ∑ c : Fin N, lam τ c ≤ M → ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O a b 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧ evalE O N lam P F (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y) := by
  intro O _ N ι _ _ τ M a b
  by_cases hab : a = b
  · subst hab
    refine ⟨∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      (w a : O) • FreeAlgebra.ι O (Sum.inr (τ, w)), ?_⟩
    intro lam P _ hP hM x
    refine ⟨⟨rowDiv O a a 1 (x τ), Formalism.GradedWeylDivisibility.rowDivStable O N N _ a a 1 _ (x τ).2⟩, rfl, ?_⟩
    have hcol := ((rowdiv_mem_dualWeyl_iff O N N _ _).mp (x τ).2).1
    let cmp : (Fin N → ℕ) → dualWeyl O N N (res N (lam τ)) := fun w =>
      ⟨weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O),
        Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N _ w _ (x τ).2⟩
    have hPx : ∀ w, P τ w (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (Function.update x τ (cmp w)) :=
      fun w => hP τ w x (cmp w) rfl
    simp only [evalE, map_sum, map_smul, FreeAlgebra.lift_ι_apply, Sum.elim_inr, LinearMap.sum_apply,
      Finset.sum_apply, LinearMap.smul_apply, hPx]
    simp_rw [← MultilinearMap.map_update_smul]
    rw [← MultilinearMap.map_update_sum]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    conv_rhs => rw [← sum_rowComp _ M hM _ hcol]
    rw [show rowDiv O a a 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) =
        rowDivL O a a 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) from rfl, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rowDivL_apply, (GlobalTheory.ValCmp.rowDiv_rowWeight O N N w _
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)).2 a 1, Nat.choose_one_right,
      Nat.cast_smul_eq_nsmul]
  · let gt : GL (Fin N) O := ⟨Matrix.transvection b a (-1), Matrix.transvection b a 1,
        by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp,
        by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp⟩
    let g : ι → GL (Fin N) O := Pi.mulSingle τ gt
    refine ⟨∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
      FreeAlgebra.ι O (Sum.inr (τ, w + Pi.single a 1 - Pi.single b 1)) * FreeAlgebra.ι O (Sum.inl g) *
        FreeAlgebra.ι O (Sum.inr (τ, w)), ?_⟩
    intro lam P _ hP hM x
    refine ⟨⟨rowDiv O a b 1 (x τ), Formalism.GradedWeylDivisibility.rowDivStable O N N _ a b 1 _ (x τ).2⟩, rfl, ?_⟩
    have hcol := ((rowdiv_mem_dualWeyl_iff O N N _ _).mp (x τ).2).1
    let cmp : (Fin N → ℕ) → dualWeyl O N N (res N (lam τ)) → dualWeyl O N N (res N (lam τ)) := fun w v =>
      ⟨weightedHomogeneousComponent (rowW N N) w (v : MvPolynomial (Fin N × Fin N) O),
        Formalism.GradedWeylDivisibility.dualWeylRowGraded O N N _ w _ v.2⟩
    have hPz : ∀ w (z : ∀ σ, dualWeyl O N N (res N (lam σ))), P τ w (PiTensorProduct.tprod O z) =
        PiTensorProduct.tprod O (Function.update z τ (cmp w (z τ))) :=
      fun w z => hP τ w z (cmp w (z τ)) rfl
    have hg : ∀ z : ∀ σ, dualWeyl O N N (res N (lam σ)), grp O N lam g (PiTensorProduct.tprod O z) =
        PiTensorProduct.tprod O (Function.update z τ (Formalism.UG.dualWeylRep O N N _ gt (z τ))) := by
      intro z
      unfold grp
      rw [(Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun σ => res N (lam σ)) g z).1]
      congr 1
      funext σ
      by_cases hσ : σ = τ
      · subst hσ; simp [g]
      · simp [g, hσ, Pi.mulSingle_eq_of_ne hσ]
    simp only [evalE, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inr, Sum.elim_inl, LinearMap.sum_apply,
      Finset.sum_apply, Module.End.mul_apply, hPz, hg, Function.update_self, Function.update_idem]
    rw [← MultilinearMap.map_update_sum]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_sum]
    conv_rhs => rw [← sum_rowComp _ M hM _ hcol]
    rw [show rowDiv O a b 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) =
        rowDivL O a b 1 (∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (M + 1)),
        weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O)) from rfl, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rowDivL_apply]
    exact comp_rowAct_transvection a b hab w _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

end GlobalTheory.PolarFormula
