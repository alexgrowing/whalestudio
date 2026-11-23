import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CuspUmg
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RapidDecay
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.GoodSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousConstantTerm
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
open GroundTheory.Automorphic.AutomorphicForm

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

private theorem lev_entry_le {F : Type*} [NormedField F] (ev : Ad E →+* F) (a : GA E r) (A : GL (Fin r) F)
    (hA : ∀ i j, (A : Matrix (Fin r) (Fin r) F) i j = ev ((a : Matrix (Fin r) (Fin r) (Ad E)) i j)) (i j : Fin (r + s)) :
    ‖ev (((lev (Ad E) r s (a, 1) : GL (Fin (r + s)) (Ad E)) : Matrix (Fin (r + s)) (Fin (r + s)) (Ad E)) i j)‖ ≤ locHeight A := by
  rw [GlobalTheory.SmGL.val_emb₂]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  have h0 : (0 : ℝ) ≤ locHeight A := (locHeight_pos A).le
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa [hA] using norm_apply_le_locHeight A i' j'
  · simpa using h0
  · simpa using h0
  · by_cases h : i' = j'
    · subst h
      simpa using one_le_locHeight A
    · simpa [Matrix.one_apply_ne h] using h0

private theorem lev_inv (a : GA E r) : (lev (Ad E) r s (a, 1))⁻¹ = lev (Ad E) r s (a⁻¹, 1) := by
  rw [← map_inv, Prod.inv_mk, inv_one]

private theorem locHeight_inf_le (w : InfinitePlace E) (a : GA E r) :
    locHeight (infAt w (lev (Ad E) r s (a, 1))) ≤ locHeight (infAt w a) := by
  refine locHeight_le (one_le_locHeight _) (fun i j => lev_entry_le (infEval w) a _ (fun _ _ => rfl) i j) fun i j => ?_
  rw [← infAt_inv, lev_inv, ← locHeight_inv (infAt w a), ← infAt_inv]
  exact lev_entry_le (infEval w) a⁻¹ _ (fun _ _ => rfl) i j

private theorem locHeight_fin_le (v : HeightOneSpectrum (𝓞 E)) (a : GA E r) :
    locHeight (finAt v (lev (Ad E) r s (a, 1))) ≤ locHeight (finAt v a) := by
  refine locHeight_le (one_le_locHeight _) (fun i j => lev_entry_le (finEval v) a _ (fun _ _ => rfl) i j) fun i j => ?_
  rw [← finAt_inv, lev_inv, ← locHeight_inv (finAt v a), ← finAt_inv]
  exact lev_entry_le (finEval v) a⁻¹ _ (fun _ _ => rfl) i j

private theorem height_lev_le (s : ℕ) (a : GA E r) : AutomorphicForm.height (lev (Ad E) r s (a, 1)) ≤ AutomorphicForm.height a := by
  classical
  set x : GA E (r + s) := lev (Ad E) r s (a, 1) with hx
  set t := (finite_mulSupport_locHeight_finAt x).union (finite_mulSupport_locHeight_finAt a)
  have e1 : ∏ᶠ v : HeightOneSpectrum (𝓞 E), locHeight (finAt v x) = ∏ v ∈ t.toFinset, locHeight (finAt v x) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inl hv
  have e2 : ∏ᶠ v : HeightOneSpectrum (𝓞 E), locHeight (finAt v a) = ∏ v ∈ t.toFinset, locHeight (finAt v a) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inr hv
  unfold AutomorphicForm.height
  refine mul_le_mul ?_ ?_ (le_trans zero_le_one (one_le_finprod_locHeight _)) (le_trans zero_le_one (one_le_prod_locHeight _))
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (locHeight_pos _).le _)
      fun w _ => pow_le_pow_left₀ (locHeight_pos _).le (locHeight_inf_le w a) _
  · rw [e1, e2]
    exact Finset.prod_le_prod (fun v _ => (locHeight_pos _).le) fun v _ => locHeight_fin_le v a

private theorem ct_growth {n : ℕ} (r : ℕ) (φ : GA E n → ℂ) {B : ℝ} {N : ℕ} (hφ : ∀ g, ‖φ g‖ ≤ B * AutomorphicForm.height g ^ N) :
    ∃ C : ℝ, ∀ g, ‖constantTerm r φ g‖ ≤ C * AutomorphicForm.height g ^ N := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact (hC.image (continuous_unipGL (K := E) (n := n) (r := r)))
  have hc : 1 ≤ heightConst E n := one_le_heightConst
  have hμ : unipMeasure E n r (unipFundamentalDomain E n r) < ⊤ := (measure_mono hDC).trans_lt hC.measure_lt_top
  refine ⟨|B| * (heightConst E n * max M 1) ^ N * (unipMeasure E n r).real (unipFundamentalDomain E n r), fun g => ?_⟩
  have hg := height_pos g
  have hb : ∀ X ∈ unipFundamentalDomain E n r, ‖φ (unipGL X * g)‖ ≤ |B| * (heightConst E n * max M 1) ^ N * AutomorphicForm.height g ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst E n * max M 1 * AutomorphicForm.height g :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((hM _ ⟨X, hDC hX, rfl⟩).trans (le_max_left _ _)) (by linarith)) hg.le)
    refine (hφ _).trans ((mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg (height_pos _).le _)).trans ?_)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le h1 _) (abs_nonneg _)
  have := norm_setIntegral_le_of_norm_le_const hμ hb
  refine this.trans_eq ?_
  ring

end

theorem UpperTheory.integrable_constantTerm_leviEmbedding_mul_conj_cuspForm :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (S : Set (Pl E)) (r s : ℕ) (b : Blo S r) (φ : Sm E (r + s)), Umg φ → ∀ (g : GA E r) (m : GA E s),
      Integrable (fun y : RightCosetSpace (rationalGLOne E r) => AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (((Quotient.out y : normOneGL E r) : GA E r) * g, m)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))) (quotientMeasure (rationalGLOne E r) (mu1 E r)) := by
  intro E _ _ _ S r s b φ hφ g m
  obtain ⟨F, hF, -, hFl, -⟩ := UpperTheory.ConvolutionTheory.BW.ctOps E r s φ hφ
  have hcφ : Continuous φ.1 := ((UpperTheory.ConvolutionTheory.BW.umgOps E (r + s)).2 φ hφ).1
  obtain ⟨hfU, hfC⟩ := UpperTheory.ConvolutionTheory.BW.cuspUmg E r b.f b.cusp
  have hcf : Continuous b.f.1 := ((UpperTheory.ConvolutionTheory.BW.umgOps E r).2 b.f hfU).1
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨B, hB⟩ := hN 1
  have hB' : ∀ g, ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N := fun g => by
    simpa using hB g
  obtain ⟨C, hC⟩ := ct_growth r φ.1 hB'
  obtain ⟨D, hD⟩ := UpperTheory.ConvolutionTheory.BW.rapidDecay E r b.f hfU hfC N
  let H : GA E r → ℂ := fun x =>
    AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (x * g, m)) * starRingEnd ℂ (b.f.1 x)
  have hct : ∀ (γ : GL (Fin r) E) (x : GA E r),
      AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (ratGL E r γ * x * g, m)) =
        AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (x * g, m)) := fun γ x => by
    have e : lev (Ad E) r s (ratGL E r γ * x * g, m) =
        lev (Ad E) r s (ratGL E r γ, ratGL E s 1) * lev (Ad E) r s (x * g, m) := by
      rw [← map_mul, Prod.mk_mul_mk, map_one, one_mul, mul_assoc]
    rw [← hF, e]
    exact hFl (γ, 1) _
  have hHl : AutomorphicForm.IsLeftInvariant H := fun γ x => by
    change AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (ratGL E r γ * x * g, m)) *
      starRingEnd ℂ (b.f.1 (ratGL E r γ * x)) = _
    rw [hct]
    exact congrArg _ (congrArg _ (hfU.left γ x))
  have hHc : Continuous H := by
    refine ((UpperTheory.continuous_constantTerm E (r + s) r φ.1 hcφ).comp ?_).mul (Complex.continuous_conj.comp hcf)
    exact ((GlobalTheory.SmGL.continuous_leviEmb (Ad E) _).comp (GlobalTheory.SmGL.continuous_leviTwo (Ad E))).comp ((continuous_id.mul continuous_const).prodMk continuous_const)
  set L := AutomorphicForm.height (lev (Ad E) r s (g, m)) with hL
  have hL0 : 0 < L := AutomorphicForm.height_pos _
  have hc0 : 0 < AutomorphicForm.heightConst E (r + s) := one_pos.trans_le AutomorphicForm.one_le_heightConst
  have hbound : ∀ y : normOneGL E r, ‖H (y : GA E r)‖ ≤ |C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * D := by
    intro y
    have hq1 : 1 ≤ PositivityTheory.Rg.Tf.Core.qht y := le_ciInf fun γ => AutomorphicForm.one_le_height _
    obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (show PositivityTheory.Rg.Tf.Core.qht y < 2 * PositivityTheory.Rg.Tf.Core.qht y by linarith)
    obtain ⟨γ', hγ'⟩ := Subgroup.mem_subgroupOf.1 γ.2
    have hγ'' : ((γ : normOneGL E r) : GA E r) = ratGL E r γ' := hγ'.symm
    set y' : GA E r := ratGL E r γ' * (y : GA E r) with hy'
    have hy'h : AutomorphicForm.height y' < 2 * PositivityTheory.Rg.Tf.Core.qht y := by
      rw [hy', ← hγ'']; exact hγ
    have e1 : H (y : GA E r) = H y' := (hHl γ' _).symm
    have e2 : ‖b.f.1 y'‖ = ‖b.f.1 (y : GA E r)‖ := congrArg _ (hfU.left γ' _)
    have h3 : AutomorphicForm.height (lev (Ad E) r s (y' * g, m)) ≤
        2 * AutomorphicForm.heightConst E (r + s) * L * PositivityTheory.Rg.Tf.Core.qht y := by
      have e : lev (Ad E) r s (y' * g, m) = lev (Ad E) r s (y', 1) * lev (Ad E) r s (g, m) := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      rw [e]
      refine (AutomorphicForm.height_mul_le _ _).trans ?_
      have h4 := (height_lev_le s y').trans hy'h.le
      calc _ ≤ AutomorphicForm.heightConst E (r + s) * (2 * PositivityTheory.Rg.Tf.Core.qht y) * L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hc0.le) hL0.le
        _ = _ := by ring
    have hq0 : 0 ≤ PositivityTheory.Rg.Tf.Core.qht y := by linarith
    have h5 : ‖AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (y' * g, m))‖ ≤
        |C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * PositivityTheory.Rg.Tf.Core.qht y ^ N := by
      refine (hC _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (AutomorphicForm.height_pos _).le _)).trans ?_)
      calc _ ≤ |C| * (2 * AutomorphicForm.heightConst E (r + s) * L * PositivityTheory.Rg.Tf.Core.qht y) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le h3 _) (abs_nonneg _)
        _ = _ := by rw [mul_pow]; ring
    have hK : 0 ≤ |C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N := by positivity
    rw [e1]
    change ‖_ * _‖ ≤ _
    rw [norm_mul, RCLike.norm_conj, e2]
    calc _ ≤ (|C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * PositivityTheory.Rg.Tf.Core.qht y ^ N) * ‖b.f.1 (y : GA E r)‖ :=
          mul_le_mul_of_nonneg_right h5 (norm_nonneg _)
      _ = |C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * (‖b.f.1 (y : GA E r)‖ * PositivityTheory.Rg.Tf.Core.qht y ^ N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hD y) hK
  have := isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  have he : (fun y : RightCosetSpace (rationalGLOne E r) => AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (((Quotient.out y : normOneGL E r) : GA E r) * g, m)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : GA E r))) =
      CuspidalSpectrum.cuspQuot hHl := funext fun y => by
    have h := CuspidalSpectrum.cuspQuot_mk hHl (Quotient.out y)
    rw [show RightCosetSpace.mk (rationalGLOne E r) (Quotient.out y) = y from Quotient.out_eq y] at h
    exact h.symm
  rw [he]
  refine Integrable.of_bound (CuspidalSpectrum.continuous_cuspQuot hHl hHc).aestronglyMeasurable
    (|C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * D) (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨y, rfl⟩ := mk_surjective (rationalGLOne E r) q
  rw [CuspidalSpectrum.cuspQuot_mk]
  exact hbound y
