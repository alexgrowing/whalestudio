import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerEqualRank.MulDivCancelOfEq

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter PositivityTheory.SiegelWeilFormula.Gen.W
open scoped TensorProduct Matrix Topology Classical

theorem whitGenEqOf : WhitGenEqOf := by
  intro hLoc hUnr hReal hFac hLO hDE F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD hok hrange _ ht
    μH 𝓕 hμH h𝓕
  obtain ⟨hMn, hM1⟩ := hok
  subst hMn
  have hani : ∀ x : Fin M → E, hE σ J x x = 0 → x = 0 := by
    rcases hrange with h | h
    · omega
    · exact h
  obtain ⟨t, ht⟩ := ht
  have hT := hD.hT

  have h0 := hDE F E σ hD.cm M hM1 J hD.herm hani T hT hD.det d bs 0 0 Φf Φv isSchwartzInf_zero hD.pure
    (fun X => by simp)
  have h1 := ((h0.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr
  obtain ⟨μi, hμi⟩ := h1.1
  obtain ⟨νi, hνi⟩ := (h1.2 μi hμi).1
  obtain ⟨μv, hμv⟩ := ((h1.2 μi hμi).2 νi hνi).1
  obtain ⟨νv, hνv⟩ := (((h1.2 μi hμi).2 νi hνi).2 μv hμv).1

  have hR := hReal F E σ hD.cm M J hD.herm M le_rfl ψ hD.chr ι θ l hD.places ε fr hD.frames g P μi νi hμi hνi

  have h2 := hDE F E σ hD.cm M hM1 J hD.herm hani T hT hD.det d bs Φ (phiInf θ l fr g P) Φf Φv hR.1 hD.pure hD.prod
  obtain ⟨ginf, gv, hdinf, hdv, -, hmean⟩ :=
    (((((h2.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr).2 μi hμi).2 νi hνi).2 μv hμv |>.2 νv hνv
  obtain ⟨Wi, hWi, hWi0, ti, hti⟩ := hR.2 ginf hdinf (hermOf (Ainf F) σ T hT) (hermOf_unit σ T hT hD.det _)

  have hL := fun v => hLoc F E σ hD.cm M J hD.herm M ψ hD.chr v (μv v) (νv v) (lam v) (L₁ v) (L₂ v) (hμv v)
    (hνv v) (hD.haar v) (hD.co v).1 (hD.co v).2 (Φv v) (hD.pure.1 v) (gv v) (hdv v) (hermOf (Fv F v) σ T hT)
    (hermOf_unit σ T hT hD.det _)
  choose Wv hWv hWv0 tv htv using hL

  obtain ⟨tu, hU⟩ := hUnr F E σ hD.cm M J hD.herm M T hT hD.det d bs ψ hD.chr
  have hev := (hU.and hD.std).and hD.pure.2.1
  obtain ⟨S, hSout⟩ := exists_finset_of_cofinite hev
  have hPv : ∀ v, v ∉ S → ∀ z : ℂ, tu < z.re →
      Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z) (νv v) ∧
      ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v) =
        unrX M M (eSp E v) (Ideal.absNorm v.asIdeal) z := by
    intro v hv z hz
    obtain ⟨⟨hu, hs1, hs2⟩, hpv⟩ := hSout v hv
    have hL12 : L₂ v = L₁ v := SetLike.coe_injective (hs2.trans hs1.symm)
    rw [hL12, hpv]
    exact hu (μv v) (νv v) (lam v) (L₁ v) (hμv v) (hνv v) (hD.haar v) hs1 z hz
  have hs00 : (((M : ℂ) - M) / 2) = 0 := by simp

  have hgv : ∀ v, v ∉ S → gv v (hermOf (Fv F v) σ T hT) = unrX M M (eSp E v) (Ideal.absNorm v.asIdeal) 0 := by
    intro v hv
    have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v
      omega
    have heq := eq_of_eqOn_right (hWv v) (unrX_differentiable M M (eSp E v) _ hq) (max (tv v) tu) fun z hz =>
      ((htv v z (lt_of_le_of_lt (le_max_left _ _) hz)).2).trans
        ((hPv v hv z (lt_of_le_of_lt (le_max_right _ _) hz)).2)
    rw [← hWv0 v, heq, hs00]
  obtain ⟨K, hKm, hKa, hKp, lam0, P0, hlam, hP0, hKval⟩ := lpack hLO σ hD.cm S M hM1
  have hPd : Differentiable ℂ (fun z => ∏ v ∈ S, Wv v z) := Differentiable.fun_finsetProd fun v _ => hWv v
  let G : ℂ → ℂ := fun z => Wi z * ((∏ v ∈ S, Wv v z) * K z)
  have hGm : MeromorphicOn G Set.univ := fun z _ =>
    (hWi.analyticAt z).meromorphicAt.mul ((hPd.analyticAt z).meromorphicAt.mul (hKm z (Set.mem_univ z)))
  have hGa : AnalyticAt ℂ G (((M : ℂ) - M) / 2) := by
    rw [hs00]
    exact (hWi.analyticAt 0).mul ((hPd.analyticAt 0).mul hKa)

  have hGs0 : G (((M : ℂ) - M) / 2) = 2 * meanC μH 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) := by
    have hP0' : HasProd (fun v : {v // v ∉ S} => gv v.1 (hermOf (Fv F v.1) σ T hT) /
        (1 - eSp E v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))) P0 := by
      convert hP0 using 2 with v
      rw [hgv v.1 v.2]
    have hp := hasProd_split' (fun v => gv v (hermOf (Fv F v) σ T hT) /
        (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) S P0 hP0'
    rw [hmean lam0 hlam, hp.tprod_eq]
    show Wi _ * ((∏ v ∈ S, Wv v _) * K _) = _
    rw [hWi0, Finset.prod_congr rfl fun v _ => hWv0 v, hs00, Finset.prod_div_distrib]
    have hSne : ∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => one_sub_eSp_ne v
    field_simp
    linear_combination (ginf (hermOf (Ainf F) σ T hT) * ∏ v ∈ S, gv v (hermOf (Fv F v) σ T hT)) * hKval

  have hright : Set.EqOn G
      (fun z => ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν)
      (rightOf (|t| + |ti| + |tu| + ∑ v ∈ S, |tv v|)) := by
    intro z hz
    have hz' : |t| + |ti| + |tu| + ∑ v ∈ S, |tv v| < z.re := hz
    have hsum : 0 ≤ ∑ v ∈ S, |tv v| := Finset.sum_nonneg fun v _ => abs_nonneg _
    have zt : t < z.re := by linarith [le_abs_self t, abs_nonneg ti, abs_nonneg tu]
    have zti : ti < z.re := by linarith [le_abs_self ti, abs_nonneg t, abs_nonneg tu]
    have ztu : tu < z.re := by linarith [le_abs_self tu, abs_nonneg t, abs_nonneg ti]
    have z0 : 0 < z.re := by linarith [abs_nonneg t, abs_nonneg ti, abs_nonneg tu]
    have ztv : ∀ v ∈ S, tv v < z.re := fun v hv => by
      have := Finset.single_le_sum (f := fun v => |tv v|) (fun v _ => abs_nonneg _) hv
      linarith [le_abs_self (tv v), abs_nonneg t, abs_nonneg ti, abs_nonneg tu]
    have hint : ∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z) (νv v) := by
      intro v
      by_cases hv : v ∈ S
      · exact (htv v z (ztv v hv)).1
      · exact (hPv v hv z ztu).1
    have hF := hFac F E σ M M d J T bs ψ ι θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD μi νi μv νv hμi hνi hμv hνv z
      (ht z zt) (hti z zti).1 hint
    have hp := hasProd_split' (fun v => ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z b ∂(νv v)) S (K z) (by
      convert hKp z z0 using 2 with v
      exact (hPv v.1 v.2 z ztu).2)
    have hlim : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v)
        (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v)) atTop
        (nhds ((∏ v ∈ S, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
          (T.map (inclR (Fv F v))) z b ∂(νv v)) * K z)) := hp
    have hIi : ∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi =
        Wi z := (hti z zti).2.symm
    rw [hIi] at hF
    have hu := tendsto_nhds_unique hF (hlim.const_mul (Wi z))
    show Wi z * ((∏ v ∈ S, Wv v z) * K z) = _
    rw [Finset.prod_congr rfl fun v hv => (htv v z (ztv v hv)).2]
    exact hu.symm
  exact ⟨G, ⟨Set.univ, Set.mem_univ _, ⟨⟨0, fun _ _ => trivial⟩, fun _ _ _ _ => trivial⟩, hGm, ⟨_, hright⟩⟩,
    hGa, hGs0⟩

end PositivityTheory.SiegelWeilFormula.Gen.WQ

theorem PositivityTheory.SiegelWeilFormula.Gen.whitGenEqOf : PositivityTheory.SiegelWeilFormula.Gen.WhitGenEqOf := PositivityTheory.SiegelWeilFormula.Gen.WQ.whitGenEqOf

end
