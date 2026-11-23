import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LatticeFlagExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CoordLInjective

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Unimod

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {f : Fin D.R.rS → (VS D).V}
  {M : Submodule (𝓞 D.host.E) (WbQ D F0)}

theorem rs_mem_one_iff (x : D.host.E) :
    x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = x := by
  rw [Submodule.mem_one]
  all_goals first
    | rfl
    | exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩

theorem rs_fone_iff (x : D.host.E) :
    x ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = x := by
  rw [FractionalIdeal.mem_one_iff]
  all_goals first
    | rfl
    | exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩

theorem rs_mem_dual {h : (VS D).V →ₗ⋆[D.host.E] (VS D).V →ₗ[D.host.E] D.host.E}
    {L : Submodule (𝓞 D.host.E) (VS D).V} {v : (VS D).V} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars]

theorem rs_mem_dualW {h : WbQ D F0 →ₗ⋆[D.host.E] WbQ D F0 →ₗ[D.host.E] D.host.E}
    {L : Submodule (𝓞 D.host.E) (WbQ D F0)} {v : WbQ D F0} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars]

theorem rs_inv_mul {a : Fin D.R.rS} {s x : D.host.E} (hs : s ∈ (aaI D a)⁻¹) (hx : x ∈ aaI D a) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = s * x := by
  by_cases hI : aaI D a = 0
  · rw [hI, inv_zero] at hs
    simp only [FractionalIdeal.mem_zero_iff] at hs
    exact ⟨0, by simp [hs]⟩
  · exact (rs_fone_iff _).1 ((FractionalIdeal.mem_inv_iff hI).1 hs x hx)

theorem rs_int_star {x : D.host.E} (hx : ∃ o : 𝓞 D.host.E, (o : D.host.E) = x) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = star x := by
  obtain ⟨o, rfl⟩ := hx
  exact star_int D o

private theorem mem_lamC_iff {v : (VS D).V} : v ∈ lamC D F0 f M ↔
    ((∀ a, star ((VS D).hT (F0.e a) v) ∈ (aaI D a)⁻¹) ∧
      (∃ w : perpS (VS D) F0.X, (w : (VS D).V) = vPr D F0 f v ∧
        (Submodule.Quotient.mk w : WbQ D F0) ∈ M) ∧
      ∀ a, (VS D).hT (f a) (vPr D F0 f v) ∈ aaI D a) := Iff.rfl

private theorem hs_lemma_2 (x z : (VS D).V) : star ((VS D).hT x z) = (VS D).hT z x := by
  have h := (VS D).herm.eq x z
  first
    | exact h
    | rwa [starRingEnd_apply] at h

private theorem hT_eq_hT_vPr_right_add_sum (x z : (VS D).V) : (VS D).hT x z =
    (VS D).hT x (vPr D F0 f z) + ∑ b, (VS D).hT (F0.e b) z * (VS D).hT x (f b) := by
  simp [vPr, map_sub, map_sum, map_smul]

private theorem hT_eq_hT_vPr_left_add_sum (x z : (VS D).V) : (VS D).hT x z =
    (VS D).hT (vPr D F0 f x) z + ∑ a, star ((VS D).hT (F0.e a) x) * (VS D).hT (f a) z := by
  simp [vPr, LinearMap.map_sub₂, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, starRingEnd_apply]

private theorem mem_perpS_X_of_hT_e_eq_zero (z : (VS D).V) (hz : ∀ b, (VS D).hT (F0.e b) z = 0) :
    z ∈ perpS (VS D) F0.X := by
  have hK : F0.X ≤ LinearMap.ker ((VS D).hT z) := by
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hs_lemma_2, hz b, star_zero]
  intro x hx
  rw [← hs_lemma_2, LinearMap.mem_ker.1 (hK hx), star_zero]

private theorem hT_e_vPr_eq_zero_of_partnerOK (hf : PartnerOK D F0 f) (z : (VS D).V) (b : Fin D.R.rS) :
    (VS D).hT (F0.e b) (vPr D F0 f z) = 0 := by
  simp [vPr, map_sub, map_sum, map_smul, hf.1]

theorem rs_lam_le_dual (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    lamC D F0 f M ≤ Formalism.HermitianLatticesTheory.dual (VS D).hT (lamC D F0 f M) := by
  intro v hv
  rw [rs_mem_dual]
  intro y hy
  obtain ⟨hv1, ⟨w, hw, hwM⟩, hv3⟩ := mem_lamC_iff.1 hv
  obtain ⟨hy1, ⟨u, hu, huM⟩, hy3⟩ := mem_lamC_iff.1 hy
  have hU : Formalism.HermitianLatticesTheory.dual (hWb D F0) M = M := hM.2.1
  have hwD : (Submodule.Quotient.mk w : WbQ D F0) ∈ Formalism.HermitianLatticesTheory.dual (hWb D F0) M := by
    rw [hU]; exact hwM
  have hqp : (VS D).hT (vPr D F0 f y) (vPr D F0 f v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    have h1 := rs_mem_dualW.1 hwD _ huM
    rw [← hu, ← hw, ← hWbFun_mk]
    exact h1
  rw [hT_eq_hT_vPr_right_add_sum (F0 := F0) (f := f) y v]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun b _ => ?_)
  · rw [hT_eq_hT_vPr_left_add_sum (F0 := F0) (f := f) y (vPr D F0 f v)]
    refine Submodule.add_mem _ hqp (Submodule.sum_mem _ fun a _ => ?_)
    exact (rs_mem_one_iff _).2 (rs_inv_mul (hy1 a) (hv3 a))
  · have e0 : (VS D).hT y (f b) = (VS D).hT (vPr D F0 f y) (f b) := by
      rw [hT_eq_hT_vPr_left_add_sum (F0 := F0) (f := f) y (f b)]
      simp [hf.2.1]
    rw [e0, ← hs_lemma_2 (f b) (vPr D F0 f y)]
    obtain ⟨o, ho⟩ := rs_int_star (rs_inv_mul (hv1 b) (hy3 b))
    refine (rs_mem_one_iff _).2 ⟨o, ?_⟩
    rw [ho, star_mul', star_star]

theorem rs_vPr_smul_f (hf : PartnerOK D F0 f) (a : Fin D.R.rS) (c : D.host.E) : vPr D F0 f (c • f a) = 0 := by
  rw [vPr_smul]
  have h0 : vPr D F0 f (f a) = 0 := by simp [vPr, hf.1]
  rw [h0, smul_zero]

theorem rs_smul_f_mem (hf : PartnerOK D F0 f) {a : Fin D.R.rS} {s : D.host.E} (hs : s ∈ (aaI D a)⁻¹) :
    star s • f a ∈ lamC D F0 f M := by
  refine mem_lamC_iff.2 ⟨fun b => ?_, ⟨0, ?_, ?_⟩, fun b => ?_⟩
  · rw [map_smul, hf.1, smul_eq_mul]
    by_cases hab : b = a
    · subst hab; rw [if_pos rfl, mul_one, star_star]; exact hs
    · rw [if_neg hab, mul_zero, star_zero]; exact fi_zero D _
  · simp [rs_vPr_smul_f hf]
  · rw [Submodule.Quotient.mk_zero]; exact M.zero_mem
  · rw [rs_vPr_smul_f hf, map_zero]; exact fi_zero D _

theorem rs_dual_le_lam (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    Formalism.HermitianLatticesTheory.dual (VS D).hT (lamC D F0 f M) ≤ lamC D F0 f M := by
  intro v hv
  have hv' := rs_mem_dual.1 hv
  have hI0 : ∀ a, aaI D a ≠ 0 := by
    intro a
    have hd : ddS D ≠ 0 := by
      rw [ddS, Ne, FractionalIdeal.coeIdeal_eq_zero]
      first
        | exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
        | exact Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot (A := ℤ))
        | (intro h
           rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h
           exact differentIdeal_ne_bot h)
    rw [aaI]
    exact zpow_ne_zero _ hd
  have heX : ∀ a, F0.e a ∈ F0.X := by
    intro a
    rw [FlagG.X]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hfe : ∀ a b, (VS D).hT (f b) (F0.e a) = if a = b then 1 else 0 := by
    intro a b
    rw [← hs_lemma_2 (F0.e a) (f b), hf.1 a b]
    split_ifs <;> simp
  have hxe : ∀ a, ∀ x ∈ aaI D a, x • F0.e a ∈ lamC D F0 f M := by
    intro a x hx
    have hv0 : vPr D F0 f (x • F0.e a) = x • F0.e a := by
      simp [vPr, map_smul, F0.e_iso]
    have hxP : x • F0.e a ∈ perpS (VS D) F0.X :=
      Submodule.smul_mem _ x (mem_perpS_X_of_hT_e_eq_zero _ fun b => F0.e_iso b a)
    refine mem_lamC_iff.2 ⟨fun b => ?_, ⟨⟨x • F0.e a, hxP⟩, hv0.symm, ?_⟩, fun b => ?_⟩
    · rw [map_smul, F0.e_iso, smul_zero, star_zero]; exact fi_zero D _
    · rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.2 (Submodule.smul_mem _ x (heX a)))]
      exact M.zero_mem
    · rw [hv0, map_smul, hfe a b, smul_eq_mul]
      split_ifs with hab
      · subst hab; simpa using hx
      · rw [mul_zero]; exact fi_zero D _
  have hPerp : vPr D F0 f v ∈ perpS (VS D) F0.X := mem_perpS_X_of_hT_e_eq_zero _ (hT_e_vPr_eq_zero_of_partnerOK hf v)
  have key : ∀ u' : perpS (VS D) F0.X, (Submodule.Quotient.mk u' : WbQ D F0) ∈ M →
      (VS D).hT (u' : (VS D).V) (vPr D F0 f v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro u' hy
    obtain ⟨t, ht⟩ : ∃ t : (VS D).V, t = (u' : (VS D).V) - ∑ a, (VS D).hT (f a) u' • F0.e a :=
      ⟨_, rfl⟩
    have ht1 : ∀ b, (VS D).hT (F0.e b) t = 0 := by
      intro b
      rw [ht]
      simp [map_sub, map_sum, map_smul, F0.e_iso, hT_X_perp D F0 (heX b) u'.2]
    have ht3 : ∀ b, (VS D).hT (f b) t = 0 := by
      intro b
      rw [ht]
      simp [map_sub, map_sum, map_smul, hfe]
    have htP : t ∈ perpS (VS D) F0.X := mem_perpS_X_of_hT_e_eq_zero t ht1
    have hvt : vPr D F0 f t = t := by simp [vPr, ht1]
    have hq : (Submodule.Quotient.mk ⟨t, htP⟩ : WbQ D F0) = Submodule.Quotient.mk u' := by
      rw [Submodule.Quotient.eq]
      show t - (u' : (VS D).V) ∈ F0.X
      rw [ht, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (heX a))
    have htL : t ∈ lamC D F0 f M := by
      refine mem_lamC_iff.2 ⟨fun b => ?_, ⟨⟨t, htP⟩, hvt.symm, ?_⟩, fun b => ?_⟩
      · rw [ht1 b, star_zero]; exact fi_zero D _
      · rw [hq]; exact hy
      · rw [hvt, ht3 b]; exact fi_zero D _
    have htf : ∀ b, (VS D).hT t (f b) = 0 := fun b => by
      rw [← hs_lemma_2 (f b) t, ht3 b, star_zero]
    have e1 : (VS D).hT t v = (VS D).hT (u' : (VS D).V) (vPr D F0 f v) := by
      rw [hT_eq_hT_vPr_right_add_sum (F0 := F0) (f := f) t v]
      simp only [htf, mul_zero, Finset.sum_const_zero, add_zero]
      rw [ht]
      simp [LinearMap.map_sub₂, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, hT_e_vPr_eq_zero_of_partnerOK hf]
    rw [← e1]
    exact hv' t htL
  have hWM : (Submodule.Quotient.mk ⟨vPr D F0 f v, hPerp⟩ : WbQ D F0) ∈
      Formalism.HermitianLatticesTheory.dual (hWb D F0) M := by
    rw [rs_mem_dualW]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H u' =>
      have e2 : hWb D F0 (Submodule.Quotient.mk u') (Submodule.Quotient.mk ⟨vPr D F0 f v, hPerp⟩) =
          (VS D).hT (u' : (VS D).V) (vPr D F0 f v) := hWbFun_mk D F0 u' ⟨vPr D F0 f v, hPerp⟩
      rw [e2]
      exact key u' hy
  have hU : Formalism.HermitianLatticesTheory.dual (hWb D F0) M = M := hM.2.1
  rw [hU] at hWM
  refine mem_lamC_iff.2 ⟨fun a => ?_, ⟨⟨_, hPerp⟩, rfl, hWM⟩, fun a => ?_⟩
  · rw [FractionalIdeal.mem_inv_iff (hI0 a)]
    intro x hx
    obtain ⟨o, ho⟩ := rs_int_star ((rs_mem_one_iff _).1 (hv' _ (hxe a x hx)))
    rw [rs_fone_iff]
    refine ⟨o, ?_⟩
    rw [ho, LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul, star_mul', star_star, mul_comm]
  · have e3 : (VS D).hT (f a) (vPr D F0 f v) = (VS D).hT (f a) v := by
      rw [hT_eq_hT_vPr_right_add_sum (F0 := F0) (f := f) (f a) v]
      simp [hf.2.1]
    rw [e3, ← inv_inv (aaI D a), FractionalIdeal.mem_inv_iff (inv_ne_zero (hI0 a))]
    intro s hs
    obtain ⟨o, ho⟩ := (rs_mem_one_iff _).1 (hv' _ (rs_smul_f_mem hf hs))
    rw [rs_fone_iff]
    refine ⟨o, ?_⟩
    rw [ho, LinearMap.map_smulₛₗ₂, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]

end Unimod

theorem lamUnimod : LamUnimod := by
  intro D u F0 f M hf hM
  exact le_antisymm (rs_dual_le_lam hf hM) (rs_lam_le_dual hf hM)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
