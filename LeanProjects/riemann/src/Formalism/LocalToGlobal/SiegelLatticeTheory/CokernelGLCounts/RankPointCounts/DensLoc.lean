import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Assemble
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsAdmissibleIntegralBasisChangeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PerpendicularDefinitionHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.TotPosOfFlags

noncomputable section

namespace Formalism.L2.SG.Pf.DensLoc

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.DataCut Formalism.L2.SG.DataInst
open Formalism.HermitianLattices.Ext.L3
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_lower_third {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 3) {η : ℝ} (hη : η = 1 ∨ η = -1) (a b : ℕ)
    (ha : 1 ≤ a) : Real.exp (-(3 * x ^ a)) ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i * x ^ i) := by
  have habs : ∀ i, |η ^ i| = 1 := fun i => by rcases hη with rfl | rfl <;> simp
  have hxi : ∀ i ∈ Finset.Icc a b, x ^ i ≤ 1 / 2 := fun i hi => by
    have hi1 : 1 ≤ i := le_trans ha (Finset.mem_Icc.1 hi).1
    calc x ^ i ≤ x ^ 1 := pow_le_pow_of_le_one hx0 (by linarith) hi1
      _ ≤ 1 / 2 := by rw [pow_one]; linarith
  have hlow : ∀ i ∈ Finset.Icc a b, 1 - x ^ i ≤ 1 - η ^ i * x ^ i := fun i _ => by
    have : η ^ i * x ^ i ≤ x ^ i := by
      have h1 := le_abs_self (η ^ i * x ^ i)
      rw [abs_mul, habs, one_mul, abs_of_nonneg (pow_nonneg hx0 _)] at h1
      exact h1
    linarith
  have hS : ∑ i ∈ Finset.Icc a b, x ^ i ≤ 3 / 2 * x ^ a := by
    have hI : Finset.Icc a b = Finset.Ico a (b + 1) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI]
    refine (geom_sum_Ico_le_of_lt_one hx0 (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg hx0 a]
  calc Real.exp (-(3 * x ^ a)) ≤ Real.exp (-(2 * ∑ i ∈ Finset.Icc a b, x ^ i)) := by
        apply Real.exp_le_exp.2; linarith
    _ = ∏ i ∈ Finset.Icc a b, Real.exp (-(2 * x ^ i)) := by
        rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    _ ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i * x ^ i) := by
        refine Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i hi => ?_
        exact (LocModel.exp_neg_two_le (pow_nonneg hx0 _) (hxi i hi)).trans (hlow i hi)

section Alpha

variable {K F : Type} [Field K] [Field F] [NumberField F] [Algebra F K]

theorem etaF_pm (𝔭 : Ideal (𝓞 F)) : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
  unfold etaF
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem alphaStd_eq (𝔭 : Ideal (𝓞 F)) (n : ℕ) :
    alphaStd K 𝔭 n = ∏ i ∈ Finset.Icc 1 n, (1 - etaF K F 𝔭 ^ i * ((Ideal.absNorm 𝔭 : ℝ))⁻¹ ^ i) := by
  unfold alphaStd
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem alphaStd_split (𝔭 : Ideal (𝓞 F)) {j n : ℕ} (h : j ≤ n) :
    alphaStd K 𝔭 n = alphaStd K 𝔭 j *
      ∏ i ∈ Finset.Icc (j + 1) n, (1 - etaF K F 𝔭 ^ i * ((Ideal.absNorm 𝔭 : ℝ))⁻¹ ^ i) := by
  rw [alphaStd_eq, alphaStd_eq]
  have hU : Finset.Icc 1 n = Finset.Icc 1 j ∪ Finset.Icc (j + 1) n := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hD : Disjoint (Finset.Icc 1 j) (Finset.Icc (j + 1) n) :=
    Finset.disjoint_left.2 fun i h1 h2 => by
      simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hU, Finset.prod_union hD]

theorem ratio_bounds (𝔭 : Ideal (𝓞 F)) (hN : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ)) {j n s : ℕ} (hjn : j ≤ n)
    (hs : s ≤ j + 1) (_hs1 : 1 ≤ s) :
    0 < alphaStd K 𝔭 n / alphaStd K 𝔭 j ∧
      alphaStd K 𝔭 n / alphaStd K 𝔭 j ≤ Real.exp (2 * ((Ideal.absNorm 𝔭 : ℝ))⁻¹ ^ s) ∧
      ((3 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) →
        Real.exp (-(3 * ((Ideal.absNorm 𝔭 : ℝ))⁻¹ ^ s)) ≤ alphaStd K 𝔭 n / alphaStd K 𝔭 j) := by
  set x : ℝ := ((Ideal.absNorm 𝔭 : ℝ))⁻¹ with hxdef
  have hx0 : 0 ≤ x := inv_nonneg.2 (by linarith)
  have hx : x ≤ 1 / 2 := by rw [hxdef, one_div]; exact inv_anti₀ (by norm_num) hN
  have hη := etaF_pm (K := K) 𝔭
  have hj0 : 0 < alphaStd K 𝔭 j := by
    rw [alphaStd_eq]
    exact lt_of_lt_of_le (Real.exp_pos _) (LocModel.prod_bounds hx0 hx hη 1 j le_rfl).1
  have hsp := alphaStd_split (K := K) 𝔭 hjn
  set P := ∏ i ∈ Finset.Icc (j + 1) n, (1 - etaF K F 𝔭 ^ i * x ^ i) with hP
  have hq : alphaStd K 𝔭 n / alphaStd K 𝔭 j = P := by
    rw [hsp, mul_div_cancel_left₀ _ hj0.ne']
  rw [hq]
  obtain ⟨hlo, hup⟩ := LocModel.prod_bounds hx0 hx hη (j + 1) n (by omega)
  have hxs : x ^ (j + 1) ≤ x ^ s := pow_le_pow_of_le_one hx0 (by linarith) hs
  refine ⟨lt_of_lt_of_le (Real.exp_pos _) hlo, hup.trans (Real.exp_le_exp.2 (by linarith)), fun h3 => ?_⟩
  have hx3 : x ≤ 1 / 3 := by rw [hxdef, one_div]; exact inv_anti₀ (by norm_num) h3
  exact (Real.exp_le_exp.2 (by linarith)).trans (prod_lower_third hx0 hx3 hη (j + 1) n (by omega))

end Alpha

theorem qP_lt_three_finite (D : Formalism.BasicNotions.D7) : {p : PlF D | qP p < 3}.Finite := by
  obtain ⟨hl, hc⟩ := placesOver_holds D
  have hfin : ∀ m : ℕ, {p : PlF D | Loc.resChar p = m}.Finite := by
    intro m
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (D.R.f + 1)
    have := hc m t fun p hp => ht hp
    omega
  refine ((Set.finite_le_nat 2).biUnion fun m _ => hfin m).subset fun p hp => ?_
  simp only [Set.mem_setOf_eq] at hp
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  refine ⟨Loc.resChar p, ?_, rfl⟩
  have h1 := hl p
  have h2 : ((Loc.resChar p : ℕ) : ℝ) < 3 := lt_of_le_of_lt h1 hp
  have h3 : Loc.resChar p < 3 := by exact_mod_cast h2
  omega

def DensAllAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (Cnt.MMof D F0 F') →
          (∀ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = Formalism.HermitianLattices.Ext.L3.alphaStd D.host.E p.asIdeal D.R.r /
            Formalism.HermitianLattices.Ext.L3.alphaStd D.host.E p.asIdeal (D.R.k - 1 - Cnt.cJ (VS D).hT (Cnt.UPair D F0 F') (Cnt.MMof D F0 F') p.asIdeal)) ∧
          Multipliable (densP L δ ϖ (Tn u) (Tn u') Z)) ∧
        (¬ Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (Cnt.MMof D F0 F') → ∃ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = 0)

theorem densAllAt_of (h5 : Cnt.DensAll) (D : Formalism.BasicNotions.D7) : DensAllAt D := h5 D

theorem densLocBound_at {D : Formalism.BasicNotions.D7} (h5 : DensAllAt D) : DensLocBound D := by
  intro hk δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z hEx
  obtain ⟨Λ, hΛ, F', hF'⟩ := hEx
  have hF'2 := hF'
  obtain ⟨⟨⟨-, hzt⟩, -, hG⟩, -, -, -, hZ⟩ := hF'2
  have hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) := by
    have h1 : GZ (Tn u) (Tn u') Z = Gflag F0 F'.fl := by rw [← hZ]; rfl
    rw [h1]
    exact PI.CntNotPosW.totPos_of_flags D F0 F'.fl hG
  obtain ⟨-, hiff⟩ := Cnt.mmChar_of Cnt.local_unimodular_holds D u u' hT F0 what₂ hR Z F' hzt hZ hP
  have hGl := (hiff Λ).1 ⟨hR.1 Λ hΛ, hF'⟩
  have hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (Cnt.MMof D F0 F') := by
    by_contra hI
    rw [Asm.glueSet_eq_empty hI] at hGl
    exact hGl
  obtain ⟨h5i, -⟩ := h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hzt hZ hP
  obtain ⟨hd, -⟩ := h5i hI
  obtain ⟨-, -, hUr, -⟩ := Cnt.perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hzt hZ hP
  have hm : D.R.m = 2 * D.R.rS + 2 := by
    have h1 : D.R.rS = D.R.m / 2 - 1 := rfl
    obtain ⟨t, ht⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  have hkm := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hα := alpBound_holds D hk u u'

  have key : ∀ p : PlF D,
      0 < densP L δ ϖ (Tn u) (Tn u') Z p ∧
      densP L δ ϖ (Tn u) (Tn u') Z p ≤ Real.exp (2 * (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹) ∧
      ((3 : ℝ) ≤ qP p → Real.exp (-(3 * (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹)) ≤
        densP L δ ϖ (Tn u) (Tn u') Z p) := by
    intro p
    have hc : Cnt.cJ (VS D).hT (Cnt.UPair D F0 F') (Cnt.MMof D F0 F') p.asIdeal ≤ D.R.m :=
      (Asm.cJ_le (F := D.host.F) _ _ _ _).trans hUr.le
    have hqe : qP p = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := LocModel.qPl_eq p
    have hq2 : (2 : ℝ) ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := hqe ▸ LocModel.two_le_qPl p
    have hinv : (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹ =
        ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ ^ (D.R.k - 2 * D.R.rS - 2) := by
      rw [hqe, inv_pow]
    obtain ⟨h1, h2, h3⟩ := ratio_bounds (K := D.host.E) p.asIdeal hq2
      (j := D.R.k - 1 - Cnt.cJ (VS D).hT (Cnt.UPair D F0 F') (Cnt.MMof D F0 F') p.asIdeal) (n := D.R.r)
      (s := D.R.k - 2 * D.R.rS - 2) (by omega) (by omega) (by omega)
    rw [hd p, hinv]
    exact ⟨h1, h2, fun h => h3 (hqe ▸ h)⟩
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨h0, hup, -⟩ := key p
    obtain ⟨hαl, -⟩ := hα p
    have hαpos : 0 < alpD u u' p := lt_of_lt_of_le (Real.exp_pos _) hαl
    refine ⟨h0, ?_⟩
    rw [div_le_iff₀ hαpos]
    set y := (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹
    calc densP L δ ϖ (Tn u) (Tn u') Z p ≤ Real.exp (2 * y) := hup
      _ = Real.exp (4 * y) * Real.exp (-(2 * y)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (4 * y) * alpD u u' p := mul_le_mul_of_nonneg_left hαl (Real.exp_pos _).le
  · refine (qP_lt_three_finite D).subset fun p hp => ?_
    simp only [Set.mem_setOf_eq] at hp ⊢
    by_contra h3
    push_neg at h3
    obtain ⟨-, -, hlo⟩ := key p
    obtain ⟨hαl, hαu⟩ := hα p
    have hαpos : 0 < alpD u u' p := lt_of_lt_of_le (Real.exp_pos _) hαl
    set y := (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹
    refine absurd hp (not_lt.2 ?_)
    rw [le_div_iff₀ hαpos]
    calc Real.exp (-(5 * y)) * alpD u u' p ≤ Real.exp (-(5 * y)) * Real.exp (2 * y) :=
          mul_le_mul_of_nonneg_left hαu (Real.exp_pos _).le
      _ = Real.exp (-(3 * y)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ densP L δ ϖ (Tn u) (Tn u') Z p := hlo h3

theorem densLocBound_of (h5 : Cnt.DensAll) (D : Formalism.BasicNotions.D7) : DensLocBound D :=
  densLocBound_at (densAllAt_of h5 D)

end Formalism.L2.SG.Pf.DensLoc
