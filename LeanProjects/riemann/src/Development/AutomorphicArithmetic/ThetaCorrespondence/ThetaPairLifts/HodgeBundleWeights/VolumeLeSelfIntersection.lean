import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open PositivityTheory.UnitarySelfGeneration.FrameHeightScaling
theorem PositivityTheory.UnitarySelfGeneration.volume_le_self_intersection : PositivityTheory.UnitarySelfGeneration.ChowFormHeight → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (t : ℝ), IsFrame Nm L b g A → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev d → ∀ (M : GlobalTheory.ZH.RatModel (𝓞 K) Ω), M.HasDiv (fun k => ev (∑ j, g j k • b j)) → GlobalTheory.IsArithVar M.s d → ∀ (H : ReciprocityTheory.ChartRestriction.G.Semi.LB M.Z) (hH : H.IsLB) (e : H.ι → Ω), M.GenTriv H e → ∀ (s : Fin m → H.Sec), (∀ k, M.HasVal e (s k) (ev (∑ j, g j k • b j))) → ∀ (hs : ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) (hdet : ∀ σ, (Mt σ).det ≠ 0) (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U), (∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2) → ((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).shift (fun _ => t) (fun _ => rfl)).IsSelfInter (((d : ℝ) + 1) * (Module.finrank ℚ K : ℝ) * (imageDeg ev d : ℝ) * (imageHeight Nm L ev d + t)) := by
  intro HP hP K V Ω _ _ _ _ _ _ _ _ Nm L ev d N m b g A t hF hG hd M hNm hX H hH e he s hv hs Mt hdet hc hMt
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hcomb := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model.exists_comb ev b g hF.full
  obtain ⟨i, hi, -⟩ := hNm (genericPoint M.Z)
  have htop := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model.closure_eq_top ev (fun k => ev (∑ j, g j k • b j))
    hcomb i hi hG.2
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.pos; omega⟩
  obtain ⟨Z, hZ, hZp⟩ := GlobalTheory.ZH.exists_isCl_isProjOver (𝓞 K) Ω n _ ⟨i, hi⟩ htop
  have hZX : GlobalTheory.IsArithVar Z.s d := by
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ K := Algebra.IsAlgebraic.trans ℤ ℚ K
    have h1 : Algebra.trdeg ℤ Ω = d :=
      (GlobalTheory.trdeg_eq_of_isAlgebraic_bot ℤ K Ω).trans (ModelDimension.ModelDim.trdeg_eq ev hG hd)
    refine ⟨inferInstance, inferInstance, inferInstance, hZp, (GlobalTheory.flat_int_iff_charZero _).2 ?_,
      ModelDimension.ModelDim.topologicalKrullDim_model inferInstance Z h1⟩
    exact (Z.res ⊤ ⟨genericPoint Z.Z, trivial⟩).charZero
  obtain ⟨π, hπ⟩ := hZ.exists_isHom (M' := M) (φ := AlgHom.id _ _) hNm
  obtain ⟨H', hH', e', s', he', hv', hs'⟩ := exists_bundle Z _ hZ.1
  obtain ⟨N', b', f', hf'⟩ := (imageDeg_pos_iff ev d).1 hd
  have hf := isChowFormInt_basis ev b' b hf'
  set f := GlobalTheory.ChowHt.linSubst (b'.toMatrix b) f'
  set δ := imageDeg ev d with hδ
  have hN : 0 < N := by
    obtain ⟨y, hy, -⟩ := hf.exists_point
    obtain ⟨j, -⟩ := Function.ne_iff.1 hy
    exact j.pos
  have hδ0 : ((d : ℝ) + 1) * δ ≠ 0 := mul_ne_zero (by positivity) (Nat.cast_ne_zero.2 hd.ne')
  have hh : imageHeight Nm L ev d = GlobalTheory.ChowHt.formHeight δ g A f / (((d : ℝ) + 1) * δ) :=
    GlobalTheory.ImageHeightUnique.imageHeight_eq K V Ω Nm L ev d _
      ⟨N, _, b, g, A, δ, f, hF, hf, mul_div_cancel₀ _ hδ0⟩
  have hc0 : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'
  have ht : (fun k => ev (∑ j, g j k • b j)) = fun k => ∑ j, algebraMap K Ω (g j k) * ev (b j) := funext fun k => by
    simp only [map_sum, map_smul, Algebra.smul_def]
  have hdet' : ∀ σ, (((Real.exp t : ℝ) : ℂ) • Mt σ).det ≠ 0 := fun σ => by
    rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) (hdet σ)
  have hc' : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ, ((Real.exp t : ℝ) : ℂ) • Mt ((starRingEnd ℂ).comp σ) =
      (((Real.exp t : ℝ) : ℂ) • Mt σ).map (starRingEnd ℂ) * U := fun σ => by
    obtain ⟨U, hU, h⟩ := hc σ
    refine ⟨U, hU, ?_⟩
    rw [h, ← smul_mul_assoc]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  have h1 := HP K Ω d N (n + 1) δ g (fun σ => ((Real.exp t : ℝ) : ℂ) • A σ) hF.full
    (fun σ => by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) (hF.herm σ))
    (conjCompat_smul hF.herm hF.conj hc0) (fun j => ev (b j)) Z (ht ▸ hZ) hZX f hf H' hH' e' he' s'
    (fun k => congrFun ht k ▸ hv' k) hs' (fun σ => ((Real.exp t : ℝ) : ℂ) • Mt σ) hdet' hc'
    (fun σ x => by rw [sum_smul, archSize_smul_sq, hMt])
  have h2 := (hP.p4.arProj _ _ _ Z.s M.s d hZX hX π hπ.inducedModelMorphism_comp_structureMap (map_generic hπ)
    (by rw [residueDegree_eq_one hπ]; exact one_ne_zero)).1 _ _ h1
  have h3 := (isometric_pull_fs hπ hH' he' hv' hs' hH he hv hs Mt _ hdet hc hdet' hc' t
    (fun _ => rfl)).isSelfInter hX h2
  convert h3 using 1
  rw [residueDegree_eq_one hπ, formHeight_smul hN g hF.herm hf.ne_zero hf.homog, hh]
  push_cast
  field_simp
end
