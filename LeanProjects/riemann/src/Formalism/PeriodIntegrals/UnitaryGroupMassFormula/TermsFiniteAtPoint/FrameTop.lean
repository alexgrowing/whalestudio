import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FrameOp

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW.HeisW
  PI.TermsAtPtFiniteW.LeviW PI.TermsAtPtFiniteW.FrameW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frameOp_holds : FrameOp := by
  intro D u
  obtain ⟨θ, hθ⟩ := PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D
  set N := Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, ne_eq, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  have hT0 : 0 < Tu D u := (D.mem u).A.T_prime.pos
  refine ⟨Tu D u * N ^ D.R.rS, Nat.mul_pos hT0 (pow_pos (Nat.pos_of_ne_zero hN0) _), ?_⟩
  intro F0 Λ hΛ B hB
  obtain ⟨f, L, hff, hef, hL, hzL, hΛeq⟩ := split_row_iso D u F0 Λ hΛ
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hz : F0.z ∈ Λ := hΛ.2.1.2.2.1.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y :=
    fun x hx y hy => PI.SRW.pair_int _ hU hy hx
  have he : ∀ a, F0.e a ∈ Λ := fun a => by
    rw [hΛeq]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.subset_span ⟨a, 1, one_mem_aaS D a, (one_smul _ _).symm⟩))
  have hfm : ∀ a, (((N ^ D.R.rS : ℕ)) : D.host.E) • f a ∈ Λ := fun a => by
    rw [hΛeq]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, _, m_mem_aaS_inv D a, rfl⟩)
  have hBd : ∀ i j, i < j → ∃ o : 𝓞 D.host.E,
      B i j = ((Tu D u : ℕ) : 𝓞 D.host.E) * ((N ^ D.R.rS : ℕ) : 𝓞 D.host.E) * o := by
    intro i j hij
    obtain ⟨o, ho⟩ := (hB i j).2.2 hij
    exact ⟨o, by rw [ho]; push_cast; ring⟩

  obtain ⟨m, hm⟩ : ∃ m : D.host.E, m = ((N ^ D.R.rS : ℕ) : D.host.E) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : D.host.E, T = ((Tu D u : ℕ) : D.host.E) := ⟨_, rfl⟩
  have hfm' : ∀ a, m • f a ∈ Λ := fun a => by rw [hm]; exact hfm a
  have hTs : star T = T := by rw [hT]; exact star_natCast _
  have hms : star m = m := by rw [hm]; exact star_natCast _

  choose oz hoz using fun c : Fin D.R.rS => hBd (Fin.castSucc c) (Fin.last D.R.rS) (Fin.castSucc_lt_last c)
  set lam : Fin D.R.rS → D.host.E := fun c => m * star ((oz c : 𝓞 D.host.E) : D.host.E) with hlam
  set a : Fin D.R.rS → (VS D).V := fun c => lam c • F0.z with ha
  set s : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c d => (θ : D.host.E) * T * star (lam c) * lam d
    with hs
  have hlamO : ∀ c, ∃ o : 𝓞 D.host.E, (o : D.host.E) = lam c := fun c => by
    obtain ⟨o', ho'⟩ := PI.SRW.star_int (oz c)
    exact ⟨((N ^ D.R.rS : ℕ) : 𝓞 D.host.E) * o', by simp only [hlam, hm, ← ho']; push_cast; ring⟩
  have hslamO : ∀ c, ∃ o : 𝓞 D.host.E, (o : D.host.E) = star (lam c) := fun c =>
    ⟨((N ^ D.R.rS : ℕ) : 𝓞 D.host.E) * oz c, by
      simp only [hlam, star_mul', star_star, hms, hm]; push_cast; simp only [star_pow, star_natCast]⟩
  have hzz : (VS D).hT F0.z F0.z = -T := by rw [hT]; exact F0.z_norm
  have haa : ∀ c d, (VS D).hT (a c) (a d) = star (lam c) * lam d * -T := fun c d => by
    simp only [ha, LinearMap.map_smulₛₗ₂, map_smul, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hzz]
    ring
  have hea : ∀ c d, (VS D).hT ((lf D F0).fl.e c) (a d) = 0 := fun c d => by
    simp only [ha, map_smul, smul_eq_mul]
    rw [show (lf D F0).fl.e c = F0.e c from rfl, F0.z_orth c, mul_zero]
  have hsO : ∀ c d, ∃ o : 𝓞 D.host.E, (o : D.host.E) = s c d := fun c d => by
    obtain ⟨o1, h1⟩ := hslamO c
    obtain ⟨o2, h2⟩ := hlamO d
    refine ⟨θ * ((Tu D u : ℕ) : 𝓞 D.host.E) * o1 * o2, ?_⟩
    simp only [hs, ← h1, ← h2, hT]
    push_cast
    ring
  have hss : ∀ c d, s c d + star (s d c) = -(VS D).hT (a c) (a d) := fun c d => by
    rw [haa]
    simp only [hs, star_mul', star_star, hTs]
    linear_combination (T * star (lam c) * lam d) * hθ
  have haΛ : ∀ c, a c ∈ Λ := fun c => smul_memO Λ (hlamO c) hz
  obtain ⟨nH, hnH, hnHapp⟩ := heisOp_holds D.host.E (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E) Λ (lf D F0) a s
    hint he haΛ hea hsO hss
  have hnHe : ∀ j, nH (F0.e j) = F0.e j := fun j => by
    rw [show F0.e j = (lf D F0).fl.e j from rfl, hnHapp]
    have h1 : ∀ c, (VS D).hT ((lf D F0).fl.e c) ((lf D F0).fl.e j) = 0 := fun c => F0.e_iso c j
    have h2 : ∀ c, (VS D).hT (a c) ((lf D F0).fl.e j) = 0 := fun c => by
      rw [← hsym, hea j c, star_zero]
    simp [PI.TermsAtPtFiniteW.heisFun, h1, h2]
  have hnHz : nH F0.z = F0.z + ∑ c, ((B (Fin.castSucc c) (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E) • F0.e c := by
    rw [show F0.z = (lf D F0).fl.z from rfl, hnHapp]
    have h1 : ∀ c, (VS D).hT ((lf D F0).fl.e c) ((lf D F0).fl.z) = 0 := fun c => F0.z_orth c
    have h2 : ∀ c, (VS D).hT (a c) ((lf D F0).fl.z) = star (lam c) * -T := fun c => by
      simp only [ha, LinearMap.map_smulₛₗ₂, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
      rw [show (lf D F0).fl.z = F0.z from rfl, hzz]
    simp only [PI.TermsAtPtFiniteW.heisFun, h1, h2, zero_smul, Finset.sum_const_zero, add_zero, mul_zero]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← neg_smul, hoz c]
    congr 1
    simp only [hlam, star_mul', star_star, hm, hT]
    push_cast
    simp only [star_pow, star_natCast]
    ring

  set U : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E) := fun c j => B (Fin.castSucc c) (Fin.castSucc j)
    with hUdef
  have hUlo : ∀ i j, j < i → U i j = 0 := fun i j h =>
    (hB (Fin.castSucc i) (Fin.castSucc j)).1 (Fin.castSucc_lt_castSucc_iff.mpr h)
  have hUd1 : ∀ i, U i i = 1 := fun i => (hB _ _).2.1 rfl
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j h => hUlo i j h)]
    exact Finset.prod_eq_one fun i _ => hUd1 i
  have hUiU : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U (by rw [hdet]; exact isUnit_one)
  set UE : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c j => ((U c j : 𝓞 D.host.E) : D.host.E) with hUE
  set U'E : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c b => star ((U⁻¹ b c : 𝓞 D.host.E) : D.host.E)
    with hU'E
  have hentry : ∀ b a, ∑ c, ((U⁻¹ b c : 𝓞 D.host.E) : D.host.E) * ((U c a : 𝓞 D.host.E) : D.host.E) =
      if b = a then 1 else 0 := by
    intro b a
    have h := congrArg (fun M : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E) =>
      algebraMap (𝓞 D.host.E) D.host.E (M b a)) hUiU
    simp only [Matrix.mul_apply, Matrix.one_apply, map_sum, map_mul] at h
    exact h.trans (by split_ifs <;> simp)
  have hUU : ∀ a b, ∑ c, star (UE c a) * U'E c b = if a = b then 1 else 0 := by
    intro a b
    calc ∑ c, star (UE c a) * U'E c b =
          star (∑ c, ((U⁻¹ b c : 𝓞 D.host.E) : D.host.E) * ((U c a : 𝓞 D.host.E) : D.host.E)) := by
          rw [star_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [hUE, hU'E, star_mul']
          ring
      _ = if a = b then 1 else 0 := by
          rw [hentry]
          rcases eq_or_ne a b with h | h
          · subst h; simp
          · simp [h, Ne.symm h]
  have hUd : ∀ c a, ∃ o : 𝓞 D.host.E, (o : D.host.E) * m = UE c a - if c = a then 1 else 0 := by
    intro c a
    rcases lt_trichotomy c a with h | h | h
    · obtain ⟨o, ho⟩ := hBd (Fin.castSucc c) (Fin.castSucc a) (Fin.castSucc_lt_castSucc_iff.mpr h)
      refine ⟨((Tu D u : ℕ) : 𝓞 D.host.E) * o, ?_⟩
      simp only [hUE, hUdef, ho, if_neg h.ne, sub_zero, hm]
      push_cast
      ring
    · subst h
      exact ⟨0, by simp [hUE, hUd1]⟩
    · exact ⟨0, by simp [hUE, hUlo c a h, if_neg h.ne']⟩
  have hW : ∀ d c, ∃ w : 𝓞 D.host.E,
      (if d = c then (1 : 𝓞 D.host.E) else 0) - U d c = ((N ^ D.R.rS : ℕ) : 𝓞 D.host.E) * w := by
    intro d c
    rcases lt_trichotomy d c with h | h | h
    · obtain ⟨o, ho⟩ := hBd (Fin.castSucc d) (Fin.castSucc c) (Fin.castSucc_lt_castSucc_iff.mpr h)
      refine ⟨-(((Tu D u : ℕ) : 𝓞 D.host.E) * o), ?_⟩
      simp only [hUdef, ho, if_neg h.ne, zero_sub]
      ring
    · subst h
      exact ⟨0, by simp [hUd1]⟩
    · exact ⟨0, by simp [hUlo d c h, if_neg h.ne']⟩
  choose W hW using hW
  have hUi1 : U⁻¹ - 1 = U⁻¹ * (1 - U) := by rw [Matrix.mul_sub, Matrix.mul_one, hUiU]
  have hUi1' : ∀ a c, U⁻¹ a c - (if a = c then 1 else 0) =
      ((N ^ D.R.rS : ℕ) : 𝓞 D.host.E) * ∑ d, U⁻¹ a d * W d c := by
    intro a c
    have := congrFun (congrFun hUi1 a) c
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply] at this
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hW d c]
    ring
  have hU'd : ∀ c a, ∃ o : 𝓞 D.host.E, (o : D.host.E) * m = U'E c a - if c = a then 1 else 0 := by
    intro c a
    obtain ⟨o', ho'⟩ := PI.SRW.star_int (∑ d, U⁻¹ a d * W d c)
    refine ⟨o', ?_⟩
    have key : ((U⁻¹ a c : 𝓞 D.host.E) : D.host.E) - (if a = c then 1 else 0) =
        m * ((∑ d, U⁻¹ a d * W d c : 𝓞 D.host.E) : D.host.E) := by
      have h := congrArg (algebraMap (𝓞 D.host.E) D.host.E) (hUi1' a c)
      simp only [map_sub, map_mul, map_natCast, apply_ite (algebraMap (𝓞 D.host.E) D.host.E), map_one,
        map_zero] at h
      rw [hm]
      exact h
    have h2 : star ((U⁻¹ a c : 𝓞 D.host.E) : D.host.E) - (if c = a then (1 : D.host.E) else 0) =
        star (((U⁻¹ a c : 𝓞 D.host.E) : D.host.E) - if a = c then 1 else 0) := by
      rw [star_sub]
      congr 1
      rcases eq_or_ne a c with h | h
      · subst h; simp
      · simp [h, Ne.symm h]
    simp only [hU'E]
    rw [h2, key, star_mul', hms, ho']
    ring
  have hisoL := isom_psiF F0.e f F0.e_iso hff hef UE U'E hUU
  let nL : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
    LinearEquiv.ofInjectiveEndo (psiF F0.e f UE U'E) (inj_of_isom _ hisoL)
  have hnL : ∀ v, nL v = psiF F0.e f UE U'E v := fun v =>
    congrFun (LinearEquiv.coe_ofInjectiveEndo _ _) v
  have hnLmem : nL ∈ NLam Λ (lf D F0) := by
    refine ⟨⟨fun x y => by rw [hnL, hnL]; exact hisoL x y, ?_⟩, ?_, ?_⟩
    · exact gmap_of_isom Λ hU nL (fun x y => by rw [hnL, hnL]; exact hisoL x y)
        (fun v hv => by rw [hnL]; exact psiF_mem Λ F0.e f UE U'E m hms hint he hfm' hUd hU'd hv)
    · intro j x hx
      have hsub : F0.Xa (j + 1) ≤ (F0.Xa j).comap (psiF F0.e f UE U'E - LinearMap.id) := by
        unfold Formalism.MainNotions.S.FlagG.Xa
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
        rw [psiF_e F0.e f hef UE U'E F0.e_iso i, sum_sub_delta]
        refine Submodule.sum_mem _ fun c _ => ?_
        rcases lt_trichotomy c i with h | h | h
        · exact Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨c, show c.1 < j from lt_of_lt_of_le (Fin.lt_def.mp h) (Nat.lt_succ_iff.mp hi), rfl⟩)
        · subst h
          simp [hUE, hUd1]
        · simp [hUE, hUlo c i h, if_neg h.ne']
      have := hsub hx
      rw [hnL]
      exact this
    · intro x hx
      have hφ : ∀ c, (VS D).hT (F0.e c) x = 0 := fun c =>
        (PI.DCRelEquiv.UnitaryGroupMassFormula.mem_orth_iff.mp hx) _ (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D F0) c)
      rw [hnL, psiF_apply]
      simp only [hφ, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
      refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D F0) c))
        (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D F0) a))
  refine ⟨nH * nL, PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul hnH hnLmem, frame_fin D F0 _ B hB nH nL hnHe hnHz
    (fun i => by rw [hnL]; exact psiF_e F0.e f hef UE U'E F0.e_iso i)
    (by rw [hnL]; exact psiF_fix F0.e f UE U'E F0.z (fun a => (hL _ hzL a).2) (fun a => F0.z_orth a))⟩

end PI.TermsAtPtFiniteW
