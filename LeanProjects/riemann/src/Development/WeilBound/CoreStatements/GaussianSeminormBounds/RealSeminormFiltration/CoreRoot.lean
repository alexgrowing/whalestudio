import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSplit

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

private theorem not_sameBlock_of_sameBlock_of_not_sameBlock {r s : ℕ} {a b c : Ix r s} (h1 : sameBlock a b) (h2 : ¬ sameBlock b c) :
    ¬ sameBlock a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock]

private theorem not_sameBlock_of_not_sameBlock_of_sameBlock {r s : ℕ} {a b c : Ix r s} (h1 : sameBlock b c) (h2 : ¬ sameBlock a b) :
    ¬ sameBlock a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock]

theorem root_of_hw {p q r s : ℕ} (c : ℂ) (c0 : ℚ) (hc : c = c0) (La : Ix r s → ℚ)
    (hU : ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = La) (d0 : ℕ)
    (hd : (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0)) {ν : Ix r s → ℚ} {g : Pol p q r s}
    (hg : g ∈ harm1 p q r s ⊓ polChi p q r s c ⊓ homog (Ix p q × Ix r s) (d0 + 2))
    (hw : IsHW (fockAct2 p q r s) ν g) :
    (∃ a b, ¬ sameBlock a b ∧ RootTo ν a b La) ∧
      degW (cPair p q) ν = degW (cPair r s) (fun _ : Ix p q => c0) + 2 := by
  obtain ⟨hg12, hgD⟩ := Submodule.mem_inf.1 hg
  obtain ⟨hgH, hgC⟩ := Submodule.mem_inf.1 hg12
  have hH1 : ∀ Z : Mat p q, IsPC Z → minusPart ((fockAct1 p q r s) Z) g = 0 :=
    (mem_harm1_iff g).1 hgH
  have hdeg : ((d0 + 2 : ℕ) : ℚ) = degW (cPair p q) ν :=
    PI.FockOneDegW.Swap.hwHarmDeg2
      (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff)
      p q r s ν (d0 + 2) g hgD hw hH1
  refine ⟨?_, by rw [← hdeg, ← hd]; push_cast; ring⟩
  have hlow0 : ∀ h : Pol p q r s, h ∈ polChi p q r s c → h ∈ homog (Ix p q × Ix r s) d0 →
      ∀ c' d' : Ix r s, ¬ sameBlock c' d' → PI.FockOneDegW.lowOp c' d' h = 0 := by
    intro h hC hD c' d' hcd
    rcases Nat.lt_or_ge d0 2 with h2 | h2
    · exact low_homog_small c' d' h2 hD
    · obtain ⟨e, rfl⟩ : ∃ e, d0 = e + 2 := ⟨d0 - 2, by omega⟩
      have hD' := low_homog c' d' (e := e) hD
      have hC' := polChi_low c hcd hC
      refine polChi_small c c0 hc e ?_ hD' hC'
      rw [← hd]
      exact_mod_cast (by omega : e < e + 2)
  have hw1 := hw.1
  have hhw := hw.2
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hhw
  obtain ⟨hwt, hpos⟩ := hhw
  have shapeOf := PI.FJM.shapeOf_of_cauchy PI.FJM.cauchy_highest_weight
  have hK1 : ∀ h : Pol p q r s, h ∈ polChi p q r s c →
      h ∈ hwSub (fockAct1 p q r s) (fun _ : Ix p q => c0) :=
    fun h hh => (mem_polChi_iff_hw c c0 hc h).1 hh
  by_cases hex : ∃ cd : Ix r s × Ix r s,
      ¬ sameBlock cd.1 cd.2 ∧ PI.FockOneDegW.lowOp cd.1 cd.2 g ≠ 0
  · obtain ⟨⟨c1, d1⟩, hmem, hmax⟩ := Finset.exists_max_image
      (Finset.univ.filter fun cd : Ix r s × Ix r s =>
        ¬ sameBlock cd.1 cd.2 ∧ PI.FockOneDegW.lowOp cd.1 cd.2 g ≠ 0)
      (fun cd => PI.FockOneDegW.HwC.tw cd.1 - PI.FockOneDegW.HwC.tw cd.2)
      (by obtain ⟨cd, h⟩ := hex; exact ⟨cd, by simpa using h⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem hmax
    obtain ⟨hcd, hne⟩ := hmem
    have hlg : PI.FockOneDegW.lowOp c1 d1 g ∈ polChi p q r s c := polChi_low c hcd hgC
    have hlD : PI.FockOneDegW.lowOp c1 d1 g ∈ homog (Ix p q × Ix r s) d0 := low_homog c1 d1 hgD
    have hJ : PI.FockOneDegW.lowOp c1 d1 g ∈ jHarm p q r s :=
      (mem_jHarm_iff _).2 ⟨harmonic_stable_lowering hcd hgH, fun c' d' h' => hlow0 _ hlg hlD c' d' h'⟩
    have hc1d1 : c1 ≠ d1 := fun h => hcd (h ▸ PI.FockOneDegW.HwC.sameBlock_refl' c1)
    have hK2 : PI.FockOneDegW.lowOp c1 d1 g ∈ hwSub (fockAct2 p q r s)
        (fun x => (ν x + if x = c1 then 1 else 0) - if x = d1 then 1 else 0) := by
      simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
      refine ⟨fun x => ?_, fun a b hab => ?_⟩
      · have key := low_comm (PI.FockOneDegW.HwC.sameBlock_refl' x) hcd g
        have hx := hwt x
        rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx
        rw [hx, map_smul, sub_eq_iff_eq_add] at key
        rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, key]
        by_cases h1 : x = c1
        · subst h1
          have h2 : ¬ d1 = x := fun h => hc1d1 h.symm
          simp only [if_true, h2, if_false, hc1d1]
          push_cast
          module
        · by_cases h2 : d1 = x
          · subst h2
            have h3 : ¬ d1 = c1 := fun h => hc1d1 h.symm
            simp only [h1, if_true, if_false]
            push_cast
            module
          · have h3 : ¬ x = d1 := fun h => h2 h.symm
            simp only [h1, h2, h3, if_false]
            push_cast
            module
      · have hsb := PI.FockOneDegW.Core.posC_sb a b hab
        have key := low_comm hsb hcd g
        rw [hpos a b hab, map_zero, sub_zero] at key
        rw [key]
        have hA : (if b = c1 then PI.FockOneDegW.lowOp a d1 g else 0) = 0 := by
          split_ifs with hb
          · subst hb
            by_contra hz
            have hm := hmax (a, d1) ⟨not_sameBlock_of_sameBlock_of_not_sameBlock hsb hcd, hz⟩
            have := (PI.FockOneDegW.HwC.posC_facts hab).2.2
            simp only at hm
            linarith
          · rfl
        have hB : (if d1 = a then PI.FockOneDegW.lowOp c1 b g else 0) = 0 := by
          split_ifs with hd1
          · subst hd1
            by_contra hz
            have hm := hmax (c1, b) ⟨not_sameBlock_of_not_sameBlock_of_sameBlock hsb hcd, hz⟩
            have := (PI.FockOneDegW.HwC.posC_facts hab).2.2
            simp only at hm
            linarith
          · rfl
        rw [hA, hB, sub_zero]
    have hJH : PI.FockOneDegW.lowOp c1 d1 g ∈ PI.FJM.JH p q r s (fun _ => c0)
        (fun x => (ν x + if x = c1 then 1 else 0) - if x = d1 then 1 else 0) :=
      Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hK1 _ hlg, hK2⟩, hJ⟩
    have hEq := hU _ (shapeOf p q r s _ _ _ hJH hne)
    exact ⟨c1, d1, hcd, fun x => congrFun hEq x⟩
  · push_neg at hex
    exfalso
    have hJ : g ∈ jHarm p q r s :=
      (mem_jHarm_iff g).2 ⟨hgH, fun c' d' h' => hex (c', d') h'⟩
    have hK2 : g ∈ hwSub (fockAct2 p q r s) ν := hw.2
    have hJH : g ∈ PI.FJM.JH p q r s (fun _ => c0) ν :=
      Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hK1 g hgC, hK2⟩, hJ⟩
    obtain ⟨⟨e, he, hge⟩, -⟩ := PI.FJMF.minimal_degree_joint p q r s _ _ g hJH hw1
    have he' : e = d0 := by
      have : (e : ℚ) = d0 := by rw [he, hd]
      exact_mod_cast this
    subst he'
    have := MvPolynomial.IsHomogeneous.inj_right
      ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hge)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hgD) hw1
    omega

end PositivityTheory.KReal

end
