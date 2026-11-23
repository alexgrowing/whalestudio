import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem eq_of_esymm {n : ℕ} {B B' : Multiset ℂ} (hB : B.card = n) (hB' : B'.card = n)
    (h : ∀ i : Fin n, B.esymm (i + 1) = B'.esymm (i + 1)) : B = B' := by
  have h2 : (B.map fun r => Polynomial.X - Polynomial.C r).prod = (B'.map fun r => Polynomial.X - Polynomial.C r).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hB, hB']
    refine Finset.sum_congr rfl fun j hj => ?_
    rcases j with _ | j
    · simp [Multiset.esymm]
    · rw [h ⟨j, by simpa using hj⟩]
  simpa using congrArg Polynomial.roots h2

open UpperTheory.ConvolutionTheory in
theorem UpperTheory.ConvolutionTheory.Dp.sSatUnit :
    UpperTheory.ConvolutionTheory.Dp.SSatUnit := by
  intro K _ _ n μ _ w V B hB
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hB.2.1
  refine ⟨?_, fun B₁ h₁ => eq_of_esymm h₁.1 hB.1 fun i =>
    smul_left_injective ℂ h0 ((h₁.2.2 i v hv).symm.trans (hB.2.2 i v hv))⟩
  have hne : ∀ b ∈ B, b ≠ 0 := by
    intro b hb e
    subst e
    have hn : 0 < n := hB.1 ▸ Multiset.card_pos_iff_exists_mem.2 ⟨_, hb⟩
    have h1 := hB.2.2 ⟨n - 1, by omega⟩ v hv
    have h2 : B.esymm (n - 1 + 1) = 0 := by
      rw [Nat.sub_add_cancel hn, ← hB.1, Multiset.esymm, Multiset.powersetCard_self]
      simpa using hb
    set J := GLnLocal.integralGL (w.adicCompletion K) n
    set x := Cartan.diagPow (w.adicCompletion K) n fun _ => 1 with hx
    have hxc : x ∈ Subgroup.center _ :=
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 ⟨_, by rw [Matrix.scalar_apply, hx, Cartan.coe_diagPow]⟩
    have e1 : (fun a : Fin n => if a ≤ (⟨n - 1, by omega⟩ : Fin n) then (1 : ℤ) else 0) = fun _ => 1 :=
      funext fun a => if_pos (Fin.le_def.2 (by have := a.2; simp only; omega))
    have e2 : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} = {QuotientGroup.mk x} := by
      ext c
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [Subgroup.mem_center_iff.1 hxc k]
        exact QuotientGroup.mk_mul_of_mem x hk
      · rintro rfl
        exact ⟨1, J.one_mem, by rw [one_mul]⟩
    have e3 : prj (fixL μ w J) v = v :=
      Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv.2)
    have e4 : Hop μ w J x v = rhoL μ w (QuotientGroup.mk x : _ ⧸ J).out v := by
      rw [Hop, e2, finsum_mem_singleton, ContinuousLinearMap.comp_apply, e3]
    rw [h2, zero_smul, Tsph, e1, ContinuousLinearMap.smul_apply, e4] at h1
    rcases smul_eq_zero.1 h1 with h | h
    · refine (Real.rpow_pos_of_pos ?_ _).ne' (Complex.ofReal_eq_zero.1 h)
      exact Nat.cast_pos.2 (Nat.pos_of_ne_zero fun e => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 e))
    · refine h0 (norm_eq_zero.1 ?_)
      have h3 : ∀ g, ‖rhoF μ g v‖ = ‖v‖ := fun g => by
        unfold rhoF
        exact UnitaryRep.norm_map _ _ v
      rw [← h3, ← rhoL, h, norm_zero]
  refine ⟨B.attach.map fun b => Units.mk0 b.1 (hne b.1 b.2), ?_⟩
  rw [Multiset.map_map]
  exact (Multiset.attach_map_val B).symm
