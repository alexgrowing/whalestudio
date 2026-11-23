import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

set_option maxHeartbeats 800000 in
theorem pf_GFin : GFin := by
  intro hSHt hSm hRS hRE hRL hRD hRLip hTh hPr hBu hNr hDB
  intro L _ _ hTC
  refine ⟨1, fun N hN => ?_⟩
  obtain ⟨μ, hμ⟩ := hSm L N hN
  obtain ⟨cL, hcL, hL⟩ := hRL L N hN μ hμ
  obtain ⟨cD, hcD, hD⟩ := hRD L hTC N hN μ hμ
  obtain ⟨K, hKc, hKP, hKt⟩ := hTh L hTC N hN (min cL cD) (lt_min hcL hcD)
  obtain ⟨ψ, K', Cψ, hK'c, hK'P, hψ, hψsupp, hψb, hψsum, hψlip⟩ := hBu L N K hKc hKP
  obtain ⟨nf, Cn, hCn, hnS, hnt, hnEq, hnH, hnLL, hnLip⟩ := hNr L N hN
  obtain ⟨Cr, hCr, hrLip⟩ := hRLip L N hN μ hμ
  obtain ⟨c0, hc0, hc0le⟩ := (hSHt L hTC N hN).2.2.1
  have hPopen : IsOpen (Pos L N) := (hPr L N).1
  have hcone : ∀ t : ℝ, 0 < t → ∀ h ∈ Pos L N, t • h ∈ Pos L N := by
    intro t ht h hh
    unfold Pos at hh ⊢
    intro w
    have e : mat (t • h) w = t • mat h w := by simp
    rw [e]
    exact (hh w).smul ht
  have hnP : ∀ h ∈ Pos L N, nf h ∈ Pos L N := by
    intro h hh
    obtain ⟨t, ht, e⟩ := hnt h hh
    rw [e]
    exact hcone t ht h hh
  have hFP : ∀ h ∈ Pos L N, ret μ (nf h) ∈ Pos L N := fun h hh =>
    (hRE L N hN μ hμ (nf h) (hnP h hh)).2.1
  have hFeq : ∀ γ : Gm L N, ∀ h ∈ Pos L N, ret μ (nf (ac γ h)) = ac γ (ret μ (nf h)) := by
    intro γ h hh
    rw [hnEq γ h hh, (hRE L N hN μ hμ (nf h) (hnP h hh)).1 γ]
  have hinv : ∀ (γ : Gm L N) (h : HS L N), actL ((emb L N) γ)⁻¹ h = ac γ⁻¹ h := by
    intro γ h
    rw [← map_inv]
  have hretS : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ret μ) (Pos L N) := hRS L N hN μ hμ
  have hFS : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun h => ret μ (nf h)) (Pos L N) :=
    hretS.comp hnS (fun h hh => hnP h hh)
  have hFc : ContinuousOn (fun h => ret μ (nf h)) (Pos L N) := hFS.continuousOn
  have hφS : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun h => ψ (ret μ (nf h))) (Pos L N) :=
    hψ.comp_contDiffOn hFS
  have hCψ : 0 ≤ Cψ := (abs_nonneg _).trans (hψb 0)
  refine ⟨⟨fun h => ψ (ret μ (nf h)), hφS, ?_, ?_, ?_, ?_, ⟨Cψ, fun h _ => hψb _⟩, ?_⟩⟩
  · intro h0
    obtain ⟨V, hV, hV0, hVP⟩ := exists_compact_subset hPopen h0.2
    have hW : IsCompact ((fun h => ret μ (nf h)) '' V) := hV.image_of_continuousOn (hFc.mono hVP)
    have hWP : (fun h => ret μ (nf h)) '' V ⊆ Pos L N := by
      rintro _ ⟨y, hy, rfl⟩
      exact hFP y (hVP hy)
    have hfin := (hPr L N).2 _ (hW.union hK'c) (Set.union_subset hWP hK'P)
    refine ⟨Subtype.val ⁻¹' interior V,
      continuous_subtype_val.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hV0), ?_⟩
    refine (hfin.preimage inv_injective.injOn).subset ?_
    rintro γ ⟨h, hS, hU⟩
    have hk := hψsupp _ hS
    rw [hinv, hFeq _ _ h.2] at hk
    exact ⟨_, Or.inl ⟨h, interior_subset hU, rfl⟩, Or.inr hk⟩
  · intro h hh
    have h1 : min cL cD ≤ lam (ret μ (nf h)) := (min_le_left cL cD).trans (hL (nf h) (hnP h hh))
    have h2 : min cL cD ≤ lamD (ret μ (nf h)) := (min_le_right cL cD).trans (hD (nf h) (hnP h hh))
    obtain ⟨γ0, hγ0⟩ := hKt (ret μ (nf h)) (hFP h hh) h1 h2
    rw [← hψsum (ret μ (nf h)) (hFP h hh) ⟨γ0, hγ0⟩]
    refine finsum_congr fun γ => ?_
    rw [hinv, hinv, hFeq _ _ hh]
  · have hcl : closure {k : ↑(Pos L N) | ψ (ret μ (nf ↑k)) ≠ 0} ⊆
        {k : ↑(Pos L N) | ret μ (nf ↑k) ∈ K'} := by
      apply closure_minimal
      · intro k hk
        exact hψsupp _ hk
      · exact hK'c.isClosed.preimage hFc.restrict
    refine (((hPr L N).2 K' hK'c hK'P).preimage inv_injective.injOn).subset ?_
    rintro γ ⟨h, hh, hg⟩
    have a := hcl hh
    have b := hcl hg
    simp only [Set.mem_setOf_eq] at a b
    change ret μ (nf (actL ((emb L N) γ)⁻¹ ↑h)) ∈ K' at b
    rw [hinv, hFeq _ _ h.2] at b
    exact ⟨_, a, b⟩
  · intro r hr h hh
    simp only [hnH r hr h hh]
  · refine ⟨(N : ℝ) * (Cψ * Cr * Cn * (1 + c0⁻¹)), fun x => ?_⟩
    have h0P : actL x ↑(one L N) ∈ Pos L N := (x • one L N).2
    obtain ⟨t, htp, et⟩ := hnt _ h0P
    have hprod : lam (nf (actL x ↑(one L N))) * lamD (nf (actL x ↑(one L N))) =
        lam (actL x ↑(one L N)) * lamD (actL x ↑(one L N)) := by
      rw [et]
      exact hnLL t htp _ h0P
    have hhtx : (lam (actL x ↑(one L N)) * lamD (actL x ↑(one L N)))⁻¹ = ht x := rfl
    have hx0 : c0 ≤ ht x := hc0le x
    have hxnn : 0 ≤ ht x := hc0.le.trans hx0
    have hB : 0 ≤ Cψ * Cr * (1 + ht x) * Cn :=
      mul_nonneg (mul_nonneg (mul_nonneg hCψ hCr) (by linarith)) hCn
    have hε : (0 : ℝ) < 1 / (4 * (Cn + 1)) := by positivity
    have hdiff : DifferentiableAt ℝ (fun h => ψ (ret μ (nf h))) (actL x ↑(one L N)) :=
      (hφS.contDiffAt (hPopen.mem_nhds h0P)).differentiableAt (by simp)
    have key := hDB L N (fun h => ψ (ret μ (nf h))) x (Cψ * Cr * (1 + ht x) * Cn)
      (1 / (4 * (Cn + 1))) hB hε hdiff (by
        intro δ hδ0 hδε k hk
        have hm : δ * (4 * (Cn + 1)) ≤ 1 := by
          rw [le_div_iff₀ (by positivity)] at hδε
          exact hδε
        have hδ4 : δ ≤ 1 / 4 := by nlinarith
        have hCnδ : Cn * δ ≤ 1 / 4 := by nlinarith
        have c1 := hnLip δ hδ0 hδ4 _ h0P k hk
        have c2 := hrLip (Cn * δ) (mul_nonneg hCn hδ0) hCnδ _ (hnP _ h0P) (nf k) c1
        rw [hprod, hhtx] at c2
        have c3 := hψlip _ (mul_nonneg (mul_nonneg hCr (by linarith))
          (mul_nonneg hCn hδ0)) _ (hFP _ h0P) _ c2
        exact le_of_le_of_eq c3 (by ring))
    show _ ≤ _ * ht x ^ 1
    rw [pow_one]
    have e1 : 1 ≤ c0⁻¹ * ht x := by
      rw [inv_mul_eq_div, le_div_iff₀ hc0]
      linarith
    have e2 : 1 + ht x ≤ (1 + c0⁻¹) * ht x := by nlinarith
    have hK0 : 0 ≤ (N : ℝ) * (Cψ * Cr * Cn) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hCψ hCr) hCn)
    calc _ ≤ (N : ℝ) * (Cψ * Cr * (1 + ht x) * Cn) := key
      _ = (N : ℝ) * (Cψ * Cr * Cn) * (1 + ht x) := by ring
      _ ≤ (N : ℝ) * (Cψ * Cr * Cn) * ((1 + c0⁻¹) * ht x) := mul_le_mul_of_nonneg_left e2 hK0
      _ = _ := by ring

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
