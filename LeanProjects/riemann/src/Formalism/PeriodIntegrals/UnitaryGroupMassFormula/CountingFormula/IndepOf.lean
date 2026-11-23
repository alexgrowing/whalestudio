import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFC

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem prim_of (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) (hP : H.Prim Λ v) :
    LinearIndependent k (fun a => red hR (v a)) := by
  obtain ⟨-, hind, hsat⟩ := hP
  have hϖ0 : ((ϖ : 𝒪[F]) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rw [Fintype.linearIndependent_iff]
  intro g hg a0
  choose h hh using fun a => hR.surj (g a)
  have hsum_mem : ∑ a, ((h a : M.L.O) : E) • v a ∈ Λ :=
    Submodule.sum_mem _ fun a _ => Λ.smul_mem (h a) (hv a)
  have hred : red hR (∑ a, ((h a : M.L.O) : E) • v a) = 0 := by
    rw [red_lincomb hR h v hv]
    simp only [hh]
    exact hg
  obtain ⟨w, hw, hweq⟩ := (red_zero_iff hR hsum_mem).mp hred

  have hwspan : w ∈ Submodule.span E (Set.range v) := by
    have e : w = algebraMap F E ((ϖ : F))⁻¹ • ∑ a, ((h a : M.L.O) : E) • v a := by
      rw [hweq, smul_smul, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).mp (hsat w hw hwspan)

  have hzero : ∑ a, (((h a : M.L.O) : E) - algebraMap F E (ϖ : F) * (c a : E)) • v a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [← Finset.smul_sum, sub_eq_zero, hweq, ← hc]
    simp only [Subring.smul_def]
  have ha0 := Fintype.linearIndependent_iff.mp hind _ hzero a0
  rw [← hh a0]
  exact (hR.ker (h a0)).mpr ⟨c a0, (c a0).2, sub_eq_zero.mp ha0⟩

theorem indep_of (hR : RedData ϖ k r n b Λ) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ)
    (hX : LinearIndependent k (fun a => red hR (v a))) : LinearIndependent E v := by
  have hϖ0 : ((ϖ : 𝒪[F]) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hOalg : ∀ c : 𝒪[F], algebraMap F E (c : F) ∈ M.L.O := by
    intro c
    rw [M.L.O_def]
    exact (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := c)).map (IsScalarTower.toAlgHom 𝒪[F] F E)
  rw [Fintype.linearIndependent_iff]
  intro g hg a0
  by_contra hne

  choose c hc0 hcO using fun a => o2 (g a)
  have hDne : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc0 a
  have hD0 : (((∏ a, c a : 𝒪[F])) : F) ≠ 0 := fun h => hDne (Subtype.ext h)
  have hDg : ∀ a, algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a ∈ M.L.O := by
    intro a
    have e : ((∏ b, c b : 𝒪[F]) : F) = (c a : F) * ((∏ b ∈ Finset.univ.erase a, c b : 𝒪[F]) : F) := by
      rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ a)]
      rfl
    rw [e, map_mul, mul_comm (algebraMap F E (c a : F)), mul_assoc]
    exact M.L.O.mul_mem (hOalg _) (hcO a)
  let h : ι → M.L.O := fun a => ⟨algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a, hDg a⟩
  have hsum : ∑ a, ((h a : M.L.O) : E) • v a = 0 := by
    simp only [h, mul_smul, ← Finset.smul_sum, hg, smul_zero]
  have hh0 : ((h a0 : M.L.O) : E) ≠ 0 := by
    intro h0
    apply hne
    have h1 := congrArg (algebraMap F E (((∏ b, c b : 𝒪[F]) : F))⁻¹ * ·) h0
    simp only [h, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hD0, map_one, one_mul] at h1
    exact h1
  obtain ⟨j, z, hz, hzeq, a1, ha1⟩ :=
    minpow hR hϖ o3 (fun a => ((h a : M.L.O) : E)) (fun a => (h a).2) a0 hh0
  have hsumz : ∑ a, z a • v a = 0 := by
    have e1 : ∑ a, ((h a : M.L.O) : E) • v a = (algebraMap F E (ϖ : F)) ^ j • ∑ a, z a • v a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hzeq a, mul_smul]
    rw [e1] at hsum
    have h2 := congrArg (fun x => (algebraMap F E ((ϖ : F))⁻¹) ^ j • x) hsum
    simp only [smul_smul, ← mul_pow, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_pow, one_smul,
      smul_zero] at h2
    exact h2
  have hred : ∑ a, r ⟨z a, hz a⟩ • red hR (v a) = 0 := by
    rw [← red_lincomb hR (fun a => (⟨z a, hz a⟩ : M.L.O)) v hv]
    simp only [hsumz, red_zero]
  exact ha1 (Fintype.linearIndependent_iff.mp hX _ hred a1)

theorem sat_of (hR : RedData ϖ k r n b Λ) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ)
    (hX : LinearIndependent k (fun a => red hR (v a))) :
    ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range v) → x ∈ Submodule.span M.L.O (Set.range v) := by
  have hϖ0 : ((ϖ : 𝒪[F]) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hOalg : ∀ c : 𝒪[F], algebraMap F E (c : F) ∈ M.L.O := by
    intro c
    rw [M.L.O_def]
    exact (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := c)).map (IsScalarTower.toAlgHom 𝒪[F] F E)
  have hϖO : algebraMap F E (ϖ : F) ∈ M.L.O := hOalg ϖ
  have hϖu : IsUnit (algebraMap F E (ϖ : F)) := (isUnit_iff_ne_zero.mpr hϖ0).map (algebraMap F E)
  intro x hx hxs
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hxs

  choose c hc0 hcO using fun a => o2 (g a)
  have hDne : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc0 a
  have hD0 : (((∏ a, c a : 𝒪[F])) : F) ≠ 0 := fun h => hDne (Subtype.ext h)
  have hDg : ∀ a, algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a ∈ M.L.O := by
    intro a
    have e : ((∏ b, c b : 𝒪[F]) : F) = (c a : F) * ((∏ b ∈ Finset.univ.erase a, c b : 𝒪[F]) : F) := by
      rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ a)]
      rfl
    rw [e, map_mul, mul_comm (algebraMap F E (c a : F)), mul_assoc]
    exact M.L.O.mul_mem (hOalg _) (hcO a)
  have hdO : algebraMap F E ((∏ b, c b : 𝒪[F]) : F) ∈ M.L.O := hOalg _
  have hdu : IsUnit (algebraMap F E ((∏ b, c b : 𝒪[F]) : F)) :=
    (isUnit_iff_ne_zero.mpr hD0).map (algebraMap F E)
  let h : ι → M.L.O := fun a => ⟨algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a, hDg a⟩
  have hdx : algebraMap F E ((∏ b, c b : 𝒪[F]) : F) • x = ∑ a, ((h a : M.L.O) : E) • v a := by
    rw [← hg, Finset.smul_sum]
    simp only [h, mul_smul]
  by_cases hall : ∀ a, ((h a : M.L.O) : E) = 0
  · have h0 : algebraMap F E ((∏ b, c b : 𝒪[F]) : F) • x = 0 := by
      rw [hdx]
      simp [hall]
    have hx0 : x = 0 := by
      rw [← smul_zero (algebraMap F E ((∏ b, c b : 𝒪[F]) : F))] at h0
      exact hdu.smul_left_cancel.mp h0
    rw [hx0]
    exact zero_mem _
  push_neg at hall
  obtain ⟨a0, ha0⟩ := hall
  obtain ⟨j, z, hz, hzeq, a1, ha1⟩ :=
    minpow hR hϖ o3 (fun a => ((h a : M.L.O) : E)) (fun a => (h a).2) a0 ha0
  haveI : Nontrivial E := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h10 : (1 : M.L.O) = 0 := Subtype.ext (Subsingleton.elim _ _)
    have h11 := congrArg r h10
    simp at h11
  obtain ⟨m, u, huO, ⟨w, hwO, huw⟩, hdeq⟩ := o3 _ hdO hdu.ne_zero
  have key : (algebraMap F E (ϖ : F)) ^ m • (u • x) =
      (algebraMap F E (ϖ : F)) ^ j • ∑ a, z a • v a := by
    rw [smul_smul, ← hdeq, hdx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hzeq a, mul_smul]
  by_cases hjm : m ≤ j
  · rw [show j = m + (j - m) by omega, pow_add, mul_smul] at key
    have e1 := (hϖu.pow m).smul_left_cancel.mp key
    have hx' : x = ∑ a, (w * (algebraMap F E (ϖ : F)) ^ (j - m) * z a) • v a := by
      have e2 : x = w • (u • x) := by rw [smul_smul, mul_comm w u, huw, one_smul]
      rw [e2, e1, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, smul_smul, mul_assoc]
    rw [hx']
    refine Submodule.sum_mem _ fun a _ => ?_
    have hmem : w * (algebraMap F E (ϖ : F)) ^ (j - m) * z a ∈ M.L.O :=
      M.L.O.mul_mem (M.L.O.mul_mem hwO (M.L.O.pow_mem hϖO _)) (hz a)
    have h3 := Submodule.smul_mem (Submodule.span M.L.O (Set.range v)) (⟨_, hmem⟩ : M.L.O)
      (Submodule.subset_span ⟨a, rfl⟩)
    rwa [Subring.smul_def] at h3
  · push_neg at hjm
    rw [show m = j + ((m - j - 1) + 1) by omega, pow_add, mul_smul] at key
    have e1 := (hϖu.pow j).smul_left_cancel.mp key
    have hzs : ∑ a, z a • v a = algebraMap F E (ϖ : F) •
        ((algebraMap F E (ϖ : F)) ^ (m - j - 1) • (u • x)) := by
      rw [← e1, pow_succ, mul_smul, smul_comm]
    have hmemΛ : ∑ a, z a • v a ∈ Λ :=
      Submodule.sum_mem _ fun a _ => Λ.smul_mem (⟨z a, hz a⟩ : M.L.O) (hv a)
    have hred0 : red hR (∑ a, z a • v a) = 0 := by
      rw [red_zero_iff hR hmemΛ]
      refine ⟨(algebraMap F E (ϖ : F)) ^ (m - j - 1) • (u • x), ?_, hzs⟩
      have hc : (algebraMap F E (ϖ : F)) ^ (m - j - 1) * u ∈ M.L.O :=
        M.L.O.mul_mem (M.L.O.pow_mem hϖO _) huO
      have h4 := Λ.smul_mem (⟨_, hc⟩ : M.L.O) hx
      rwa [Subring.smul_def, mul_smul] at h4
    have hred : ∑ a, r ⟨z a, hz a⟩ • red hR (v a) = 0 := by
      rw [← red_lincomb hR (fun a => (⟨z a, hz a⟩ : M.L.O)) v hv]
      exact hred0
    exact absurd (Fintype.linearIndependent_iff.mp hX _ hred a1) ha1

theorem prim_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    H.Prim Λ v ↔ LinearIndependent k (fun a => red hR (v a)) :=
  ⟨prim_of hR H hϖ v hv, fun hX => ⟨hv, indep_of hR hϖ o2 o3 v hv hX, sat_of hR hϖ o2 o3 v hv hX⟩⟩

end FC

end PI.UnitaryGroupMassFormula.CntFormula
