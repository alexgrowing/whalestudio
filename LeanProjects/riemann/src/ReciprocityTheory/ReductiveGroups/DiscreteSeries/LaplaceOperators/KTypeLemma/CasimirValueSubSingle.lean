import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CoordinateEqPartialSumDifference
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ExistsCommutingProjectionImage
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SingleSmulFin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.DualKTypeOfStandardKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K2Vd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SchmidCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ConeNorm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchPhiOneApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem casimirValue_sub_single {n : ℕ} (lam : Fin n → ℝ) (s : Fin n) :
    casVal (lam - Pi.single s 1) = casVal lam + n + 2 * thVd lam s := by
  have hd1 : dot lam (Pi.single s 1) = lam s := by simp [dot, Pi.single_apply]
  have hd2 : nsq (Pi.single s (1 : ℝ)) = 1 := by simp [nsq, dot, Pi.single_apply]
  unfold casVal thVd
  rw [nsq_sub', hd1, hd2]
  ring

theorem three_add_le_gapBound_dual {n : ℕ} (ε : Fin n → Bool) : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 3 ≤ hNeed ε := by
  unfold hNeed
  have h1 := le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
  have h2 := le_max_left (2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)))
    (max (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2)
      (8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) *
        (4 * max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) + 1)))
  linarith

theorem k3Vd (n : ℕ) : QuotientHighestWeightTensorDual n := by
  intro ε lam h H _ _ _ σ D E V s N _ _ EN φ x hσ hD hV hc hVK hint hmono hgap hp hq hmono' hEN hUN hφ hx hφx
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hKU := isKUnitary_of_isInfUnitary hU
  have hKUN := isKUnitary_of_isInfUnitary hUN
  have hVk : IsKStableSub ε E V := hV.2.1
  have hVfd : FiniteDimensional ℂ V := hV.1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => generated_submodule_stable_under_action V a b hv
  have hXg : ∀ f ∈ Xs (eeVd E) (genSub E V) (thVd lam s), ∀ c, f c ∈ genSub E V :=
    fun f hf => (mem_euler_eigenspace_iff.1 hf).1
  have hps : ∀ k (u v : Fin n → ℝ), kirrPs k (u - v) = kirrPs k u - kirrPs k v := by
    intro k u v; rw [← k3vdPs_apply, map_sub, k3vdPs_apply, k3vdPs_apply]
  have hpa : ∀ k (u v : Fin n → ℝ), kirrPs k (u + v) = kirrPs k u + kirrPs k v := by
    intro k u v; rw [← k3vdPs_apply, map_add, k3vdPs_apply, k3vdPs_apply]
  have hN3 := three_add_le_gapBound_dual ε
  have hnpq : 0 ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by positivity
  have hh := hgap.2.2
  set Y := (Xs (eeVd E) (genSub E V) (thVd lam s)).map φ with hYdef

  have hYst : ∀ a b, ∀ y ∈ Y, EN a b y ∈ Y := by
    intro a b y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    rw [← hφ a b f (hXg f hf)]
    exact Submodule.mem_map_of_mem (euler_eigenspace_stable_under_action hE hGs a b hf)

  have hcasY : ∀ y ∈ Y, casimir EN y = (casVal (lam - Pi.single s 1) : ℂ) • y := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    have hfg := hXg f hf
    have h1 : casimir EN (φ f) = φ (casimir (tensVd E) f) := by
      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← hφ b a f hfg, ← hφ a b _ (dualTensorAction_mem hGs b a hfg)]
    have h2 := ((tens_statement n) (↥D) E hE).2.2.2 f
    have h3 : (fun c => casimir E (f c)) = (casVal lam : ℂ) • f :=
      funext fun c => casimir_genSub hE hc (f c) (hfg c)
    have hnum : (casVal (lam - Pi.single s 1) : ℂ) = (casVal lam : ℂ) + n + 2 * ((thVd lam s : ℝ) : ℂ) := by
      rw [casimirValue_sub_single]; push_cast; ring
    rw [h1, h2, h3, (mem_euler_eigenspace_iff.1 hf).2, smul_smul, ← add_smul, ← add_smul, ← hnum, map_smul]

  have hK2 := (k2Vd n ε lam h H σ D E V s hσ hD hV hc hVK hint hmono hgap hp hq).1
  have hcone : ∀ (μ : Fin n → ℝ) (y : N), y ∈ Y → y ≠ 0 → IsKHWVec ε EN μ y →
      InRootCone (μ - lowK ε (lam - Pi.single s 1)) :=
    fun μ y hy hy0 hμ => image_weights_in_root_cone hE hU hVfd hVk hφ hK2 hy hy0 hμ

  have hx0 : x ≠ 0 := by rintro rfl; exact hφx (map_zero φ)
  have hinj : ∀ t, t ≠ s → thVd lam t ≠ thVd lam s := by
    intro t hts heq
    apply hts
    have : lam t = lam s := by unfold thVd at heq; linarith
    exact hmono.injective this
  set Fs : ℂ[X] := ∏ t ∈ univ.erase s, (X - C (((thVd lam t : ℝ) : ℂ))) with hFs
  set P : Module.End ℂ (Fin n → D) := aeval (eeVd E) Fs with hP
  have hPg : ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → ∀ c, P f c ∈ genSub E V := by
    intro f hf
    have := aeval_mem_invariant_submodule (eeVd E) (Submodule.pi Set.univ fun _ => genSub E V)
      (fun g hg => mem_pi_submodule_iff.2 (euler_tensor_dual_mem_of_stable hGs (mem_pi_submodule_iff.1 hg))) Fs f (mem_pi_submodule_iff.2 hf)
    exact mem_pi_submodule_iff.1 this
  have hPc : ∀ a b, Commute P (tensVd E a b) := fun a b =>
    aeval_commute_of_commute (eeVd E) (tensVd E a b) (euler_tensor_dual_commute_gl_action hE a b) Fs
  have hPX : ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → P f ∈ Xs (eeVd E) (genSub E V) (thVd lam s) := by
    intro f hf
    have hk1 := k1Vd n ε lam h H σ D E V hσ hD hV hc hVK hint hmono hgap hp hq f hf
    rw [shifted_product_eq_aeval, ← Finset.mul_prod_erase univ _ (mem_univ s), map_mul, Module.End.mul_apply,
      map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at hk1
    refine mem_euler_eigenspace_iff.2 ⟨hPg f hf, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hk1
    exact hk1
  have hPx : P x = (Fs.eval ((thVd lam s : ℝ) : ℂ)) • x := by
    apply Module.End.aeval_apply_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.2 (mem_euler_eigenspace_iff.1 hx).2, hx0⟩
  have hFs0 : Fs.eval ((thVd lam s : ℝ) : ℂ) ≠ 0 := by
    rw [hFs, eval_prod, Finset.prod_ne_zero_iff]
    intro t ht
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    exact_mod_cast (hinj t (Finset.ne_of_mem_erase ht)).symm
  have hφPx : φ (P x) ≠ 0 := by
    rw [hPx, map_smul]; exact smul_ne_zero hFs0 hφx
  have hGen := (gen_statement n ε (↥D) E V hE hVk).2
  obtain ⟨u, huV, hu⟩ := exists_commuting_projection_image V hGen P hPg hPc φ hφ (hXg x hx) hφPx

  have hpiV : ∀ a b, ε a = ε b → ∀ w ∈ Submodule.pi Set.univ (fun _ : Fin n => V),
      tensVd E a b w ∈ Submodule.pi Set.univ (fun _ : Fin n => V) := by
    intro a b hab w hw
    refine mem_pi_submodule_iff.2 fun c => ?_
    rw [tensor_dual_action_apply_component]
    refine sub_mem (hVk a b hab _ (mem_pi_submodule_iff.1 hw c)) ?_
    split_ifs
    · exact mem_pi_submodule_iff.1 hw a
    · exact zero_mem _
  have hVg : ∀ w ∈ Submodule.pi Set.univ (fun _ : Fin n => V), ∀ c, w c ∈ genSub E V :=
    fun w hw c => le_generatedSubmodule_dual V (mem_pi_submodule_iff.1 hw c)
  have hfPV : ∀ a b, ε a = ε b → ∀ w ∈ Submodule.pi Set.univ (fun _ : Fin n => V),
      (φ ∘ₗ P) (tensVd E a b w) = EN a b ((φ ∘ₗ P) w) := by
    intro a b _ w hw
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, (hPc a b).eq, Module.End.mul_apply, hφ a b _ (hPg w (hVg w hw))]
  have hfdpi : FiniteDimensional ℂ (Submodule.pi Set.univ (fun _ : Fin n => V)) := pi_submodule_finiteDimensional V
  set Z := (Submodule.pi Set.univ (fun _ : Fin n => V)).map (φ ∘ₗ P) with hZ
  have hZst : IsKStableSub ε EN Z := by
    intro a b hab z hz
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
    rw [← hfPV a b hab w hw]
    exact Submodule.mem_map_of_mem (hpiV a b hab w hw)
  have hZne : Z ≠ ⊥ := by
    intro hZb
    have : (φ ∘ₗ P) u ∈ Z := Submodule.mem_map_of_mem (mem_pi_submodule_iff.2 huV)
    rw [hZb, Submodule.mem_bot] at this
    exact hu this
  obtain ⟨y0, hy0Z, hy00, ν0, hν0⟩ := exists_khw hEN hKUN inferInstance hZst hZne
  obtain ⟨w0, hw0, rfl⟩ := Submodule.mem_map.1 hy0Z
  have hy0Y : (φ ∘ₗ P) w0 ∈ Y := Submodule.mem_map_of_mem (hPX w0 (hVg w0 hw0))
  have hν0lo : ∀ k, kirrPs k ν0 ≤ kirrPs k (lowK ε lam) := by
    obtain ⟨u1, hu1, hkhw, hfu1⟩ := exists_highest_weight_lift_pi hKU (φ ∘ₗ P) hfdpi
      (fun a b hab w hw => hpiV a b hab w hw) hfPV hw0 hν0
    have hu10 : u1 ≠ 0 := by rintro rfl; rw [map_zero] at hfu1; exact hy00 hfu1.symm
    obtain ⟨c, hc0⟩ := Function.ne_iff.1 hu10
    have hwt : ∀ a, E a a (u1 c) = (((ν0 + Pi.single c (1 : ℝ) : Fin n → ℝ) a : ℝ) : ℂ) • u1 c := by
      intro a
      have := congrFun (hkhw.1 a) c
      rw [tensor_dual_action_apply_component, Pi.smul_apply] at this
      by_cases hca : c = a
      · subst hca
        simp only [if_true] at this
        rw [sub_eq_iff_eq_add] at this
        rw [this]; simp [add_smul, Pi.add_apply]
      · simp only [hca, if_false, sub_zero] at this
        rw [this]; simp [Pi.add_apply, Pi.single_apply, Ne.symm hca]
    obtain ⟨w1, hw1V, hw10, hw1⟩ := hV.2.2.2
    intro k
    have := kirrPs_le hE hV hw1V hw10 hw1 (mem_pi_submodule_iff.1 hu1 c) (by simpa using hc0) hwt k
    rw [hpa, partial_sum_of_basis_vector] at this
    split_ifs at this <;> linarith

  have hQ : ∃ m : ℕ, ∃ y ∈ Y, y ≠ 0 ∧ ∃ ν : Fin n → ℝ, IsKHWVec ε EN ν y ∧
      (∀ k, kirrPs k ν ≤ kirrPs k ν0) ∧ weightHeightFunctional (ν - lowK ε (lam - Pi.single s 1)) = m := by
    obtain ⟨N0, hN0⟩ := root_cone_height_natural (hcone ν0 _ hy0Y hy00 hν0)
    exact ⟨N0, _, hy0Y, hy00, ν0, hν0, fun k => le_rfl, hN0⟩
  obtain ⟨y, hyY, hy0, ν, hν, hνbd, hνht⟩ := Nat.find_spec hQ
  have hβ := hcone ν y hyY hy0 hν
  have hlowK' : lowK ε (lam - Pi.single s 1) = lowK ε lam - Pi.single s 1 := by
    ext a; simp only [lowK, Pi.add_apply, Pi.sub_apply]; ring
  set γ : Fin n → ℝ := ν - lowK ε lam with hγ
  have hγβ : γ = (ν - lowK ε (lam - Pi.single s 1)) - Pi.single s 1 := by
    rw [hlowK', hγ]; abel
  have hγps : ∀ k, kirrPs k γ = kirrPs k (ν - lowK ε (lam - Pi.single s 1)) - (if (s : ℕ) < k then 1 else 0) := by
    intro k; rw [hγβ, hps, partial_sum_of_basis_vector]
  have hSγ : ∀ k, -1 ≤ kirrPs k γ ∧ kirrPs k γ ≤ 0 := by
    intro k
    obtain ⟨Nk, hNk⟩ := root_cone_partial_sum_natural hβ k
    have hNk0 : (0 : ℝ) ≤ Nk := Nat.cast_nonneg _
    refine ⟨by rw [hγps, hNk]; split_ifs <;> linarith, ?_⟩
    rw [hγ, hps]
    linarith [hνbd k, hν0lo k]

  obtain ⟨T, hTY, hTfd, hTk, hyT⟩ := image_eigenspace_K_finite hE hVfd hVk hφ hyY
  obtain ⟨W, hWT, hWirr⟩ := exists_irreducible_highest_weight_submodule hKUN _ T rfl hTfd hTk y hyT hy0 hν
  have hWY : W ≤ Y := hWT.trans hTY

  set lam'' : Fin n → ℝ := ν + rhoC ε - rhoN ε with hlam''
  have hlowK'' : lowK ε lam'' = ν := by
    ext a; simp only [lowK, hlam'', Pi.add_apply, Pi.sub_apply]; ring
  have hlam''γ : ∀ a, lam'' a = lam a + γ a := by
    intro a; simp only [hlam'', hγ, lowK, Pi.add_apply, Pi.sub_apply]; ring
  have hγd : ∀ a b, |γ a - γ b| ≤ 2 := coordinate_difference_le_two γ hSγ
  have hmono'' : StrictAnti lam'' := by
    refine strictAnti_of_consecutive_lt fun a b hb => ?_
    have hab : a < b := Fin.lt_def.2 (by omega)
    by_cases he : ε a = ε b
    · obtain ⟨h1, h2⟩ := rho_consecutive_compact_pair ε a b hb he
      have := highest_weight_dominant_of_unitary hEN hKUN hν hy0 hab he
      simp only [hlam'', Pi.add_apply, Pi.sub_apply]
      linarith
    · have h1 := hgap.2.1 a b he
      have hlt := hmono hab
      rw [abs_of_pos (sub_pos.2 hlt)] at h1
      have h2 := abs_le.1 (hγd a b)
      rw [hlam''γ, hlam''γ]
      linarith
  have hgap'' : GapAtLeast ε lam'' (h - 2) := by
    intro a b he
    rw [hlam''γ, hlam''γ]
    have h1 := hgap.2.1 a b he
    have h2 := abs_sub_abs_le_abs_sub (lam a - lam b) (γ b - γ a)
    have h3 : |γ b - γ a| ≤ 2 := by rw [abs_sub_comm]; exact hγd a b
    have e : lam a - lam b - (γ b - γ a) = lam a + γ a - (lam b + γ b) := by ring
    rw [e] at h2
    linarith
  have hint'' : ∀ a, ∃ m : ℤ, lam'' a - ((n : ℝ) - 1) / 2 = (m : ℝ) := by
    intro a
    obtain ⟨m1, hm1⟩ := hint a
    obtain ⟨N1, hN1⟩ := root_cone_partial_sum_natural hβ ((a : ℕ) + 1)
    obtain ⟨N2, hN2⟩ := root_cone_partial_sum_natural hβ (a : ℕ)
    refine ⟨m1 + N1 - N2 - (if (s : ℕ) < (a : ℕ) + 1 then 1 else 0) + (if (s : ℕ) < (a : ℕ) then 1 else 0), ?_⟩
    rw [hlam''γ, coordinate_eq_partial_sum_difference γ a, hγps, hγps, hN1, hN2]
    split_ifs <;> push_cast <;> linarith
  have hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h - 2 := by linarith
  have hW'' : IsKIrrHW ε EN (lowK ε lam'') W := by rw [hlowK'']; exact hWirr

  have hSch : ∀ w ∈ Wm ε EN W, phi EN 1 w = 0 := by
    intro w hw
    by_contra hne
    have := finiteDimensional_ncV (ε := ε) hWirr.1 1
    have hfdW : FiniteDimensional ℂ (Wm ε EN W) := Submodule.finiteDimensional_of_le Wm_le_ncV
    have hWst : IsKStableSub ε (bAct EN 1) (Wm ε EN W) := Wm_kStable hEN hUN hW''
    set T' : Submodule ℂ N := (Wm ε EN W).map (phi EN 1) with hT'
    have hT'st : IsKStableSub ε EN T' := by
      intro a b hab v hv
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv
      rw [← phi_bAct hEN 1 hab z]
      exact Submodule.mem_map_of_mem (hWst a b hab z hz)
    have hT'ne : T' ≠ ⊥ := by
      intro hb
      have : phi EN 1 w ∈ T' := Submodule.mem_map_of_mem hw
      rw [hb, Submodule.mem_bot] at this
      exact hne this
    obtain ⟨y', hy'T, hy'0, μ', hy'μ⟩ := exists_khw hEN hKUN inferInstance hT'st hT'ne
    obtain ⟨w0', hw0', rfl⟩ := Submodule.mem_map.1 hy'T
    obtain ⟨x1, hx1, -, hkhw, hfx⟩ := lift_khw (A := bAct EN 1) (bAct_isKUnitary hUN 1) (phi EN 1)
      (fun a b hab z => phi_bAct hEN 1 hab z) hfdW hWst hw0' hy'μ
    have hx10 : x1 ≠ 0 := by rintro rfl; rw [map_zero] at hfx; exact hy'0 hfx.symm
    obtain ⟨a, b, hab, -, hμ'⟩ := Wm_khw hEN hUN hW'' hmono'' hgap'' hbig hx1 hx10 hkhw
    rw [hlowK''] at hμ'
    have hw0Y : phi EN 1 w0' ∈ Y := by
      rw [sch_phi_one_apply]
      refine Submodule.sum_mem _ fun p _ => hYst _ _ _ (hWY ?_)
      have hn := Wm_le_ncV hw0'
      unfold ncV at hn
      have h1 := (Submodule.mem_iInf _).1 hn (fun _ => p)
      rw [Submodule.mem_comap] at h1
      split_ifs at h1
      · exact h1
      · rw [Submodule.mem_bot] at h1
        rw [← sch_coord_apply, h1]
        exact zero_mem _
    have hcone' := hcone μ' _ hw0Y hy'0 hy'μ
    obtain ⟨N', hN'⟩ := root_cone_height_natural hcone'
    have hbd' : ∀ k, kirrPs k μ' ≤ kirrPs k ν0 := by
      intro k
      rw [hμ', hps, partial_sum_of_root]
      have := Fin.lt_def.1 hab
      have hνk := hνbd k
      by_cases h1 : (a : ℕ) < k <;> by_cases h2 : (b : ℕ) < k
      · simp only [h1, h2, if_true]; linarith
      · simp only [h1, h2, if_true, if_false]; linarith
      · omega
      · simp only [h1, h2, if_false]; linarith
    have hmin := Nat.find_min' hQ ⟨_, hw0Y, hy'0, μ', hy'μ, hbd', hN'⟩
    have e : μ' - lowK ε (lam - Pi.single s 1) = (ν - lowK ε (lam - Pi.single s 1)) - root a b := by
      rw [hμ']; abel
    rw [e, map_sub, hνht, k3vdHt_root] at hN'
    have hba : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast Fin.lt_def.1 hab
    have hmin' : ((Nat.find hQ : ℕ) : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hmin
    linarith

  have hcasW : ∀ v ∈ W, casimir EN v = (casVal (lam - Pi.single s 1) : ℂ) • v :=
    fun v hv => hcasY v (hWY hv)
  have hSC := schmid_casimir n ε ν (h - 2) (casVal (lam - Pi.single s 1) : ℂ) N EN W hEN hUN hWirr hSch hcasW
    hint'' hmono'' hgap'' (by linarith) hp hq
  have hcv : casVal (lam - Pi.single s 1) = casVal lam'' := by exact_mod_cast hSC
  have hsum : (lam - Pi.single s 1) + (ν - lowK ε (lam - Pi.single s 1)) = lam'' := by
    ext a; simp only [hlam'', lowK, Pi.add_apply, Pi.sub_apply]; ring
  have hnsq : nsq ((lam - Pi.single s 1) + (ν - lowK ε (lam - Pi.single s 1))) = nsq (lam - Pi.single s 1) := by
    rw [hsum]; unfold casVal at hcv; linarith
  have hβ0 := cone_norm n (lam - Pi.single s 1) _ hmono'.antitone hβ hnsq
  have hνeq : ν = lowK ε (lam - Pi.single s 1) := sub_eq_zero.1 hβ0
  exact ⟨W, hWY, hνeq ▸ hWirr, hcasW⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
