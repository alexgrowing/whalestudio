import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.RepsRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem int_map {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (C : Co K ι) (n : ℕ)
    [MeasurableSpace (unitaryGroup (Fin n) ℂ)] [BorelSpace (unitaryGroup (Fin n) ℂ)]
    (ν : Measure (ι → unitaryGroup (Fin n) ℂ)) (F : archCompact K n → ℂ) :
    ∫ k, F k ∂(Measure.map (C.Φ n).symm ν) = ∫ y, F ((C.Φ n).symm y) ∂ν :=
  ((C.Φ n).symm.toHomeomorph.measurableEmbedding).integral_map F

private theorem sw {G : Type} [Group G] (L u v w : G) (h1 : u * w = w * u) (h2 : v * w = w * v) :
    L * w * (u * v) = L * u * v * w := by
  rw [mul_assoc L w, ← mul_assoc w, ← h1, mul_assoc u, ← h2]
  simp only [mul_assoc]

private theorem zt_zero' {K : Type} [Field K] [NumberField K] : zt K 0 = 1 := by
  unfold zt
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext Real.exp_zero
  rw [this, map_one]

private theorem lv_zero {K : Type} [Field K] [NumberField K] (m₁ m₂ : G1 K 2) :
    ((lv m₁ m₂ 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (m₁ : AdelicGLn.AdelicGL K 2) (m₂ : AdelicGLn.AdelicGL K 2) := by
  rw [(blkLaws (K := K)).1, neg_zero, zt_zero', mul_one, mul_one]

private theorem un_cont {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (C : Co K ι) (i : ι) :
    Continuous (C.un i) := by
  have h : Continuous (fun m : U2 => (Pi.mulSingle i m : ι → U2)) := by
    refine continuous_pi fun j => ?_
    by_cases hj : j = i
    · subst hj
      simp only [Pi.mulSingle_eq_same]
      exact continuous_id
    · simpa [Pi.mulSingle_eq_of_ne hj] using continuous_const
  exact continuous_archP.comp (continuous_subtype_val.comp ((C.Φ 2).symm.continuous.comp h))

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.lineInj :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ →
      ∀ (μ : Measure U4) (e : ι → U4 → ℂ) n q n' q' (x : ι → U4), Haar4 μ → ExtP μ e n q n' q' x →
      (∀ i, C.MinAt μ₂ τ₁ i (n i) (q i)) → (∀ i, C.MinAt μ₂ τ₂ i (n' i) (q' i)) → ∀ f, IsSec τ₁ τ₂ f → FixA (C.κ₄ μ) (C.e e) f →
        (∀ (h : FA K (2 + 2)) m₁ m₂, f (lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h) = 0) → f = 0 := by
  intro K _ _ _ ι _ C μ₂ _ τ₁ τ₂ _ μ e n q n' q' x h4 hE hmin hmin' f hf hfix hz
  obtain ⟨-, -, -, -, -, -, -, -, -, hlv, hcomm, hKG⟩ := coLaws K ι C
  have hb := blkLaws (K := K)
  have hmul := hb.2.1
  obtain ⟨-, -, hbd1, -⟩ := u4
  have he : ∀ k, C.e e ((C.Φ (2 + 2)).symm k) = ∏ i, e i (k i) := by
    intro k; simp only [Co.e, ContinuousMulEquiv.apply_symm_apply]
  have ha : ∀ a b : ι → U4, arc1 ((C.Φ (2 + 2)).symm (a * b)) =
      arc1 ((C.Φ (2 + 2)).symm a) * arc1 ((C.Φ (2 + 2)).symm b) := by
    intro a b; simp [arc1, map_mul]
  have h1 : (arc1 ((C.Φ 2).symm (1 : ι → U2)) : G1 K 2) = 1 := by simp [arc1, map_one]
  have hun : ∀ i (a b : U2), C.un i (a * b) = C.un i a * C.un i b := by
    intro i a b; simp [Co.un, arc1, Pi.mulSingle_mul, map_mul]
  have hs₁ : ∀ i (m : U2), arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd m 1))) = lv (C.un i m) 1 0 := by
    intro i m
    have hl := hlv (Pi.mulSingle i m) 1
    rw [h1] at hl
    have e1 : (fun j => bd ((Pi.mulSingle i m : ι → U2) j) ((1 : ι → U2) j)) = Pi.mulSingle i (bd m 1) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj, hbd1]
    rw [e1] at hl
    exact hl.symm
  have hs₂ : ∀ i (m : U2), arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd 1 m))) = lv 1 (C.un i m) 0 := by
    intro i m
    have hl := hlv 1 (Pi.mulSingle i m)
    rw [h1] at hl
    have e1 : (fun j => bd ((1 : ι → U2) j) ((Pi.mulSingle i m : ι → U2) j)) = Pi.mulSingle i (bd 1 m) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj, hbd1]
    rw [e1] at hl
    exact hl.symm
  have key₁ : ∀ (y : G1 K (2 + 2)) (M m₂ : G1 K 2) i n₀ q₀, ¬ Above (n i) (q i) n₀ q₀ →
      ∫ m, conj (KT.psi n₀ q₀ n₀ m) * f (lv (M * C.un i m) m₂ 0 * y) ∂μK = 0 := by
    intro y M m₂ i n₀ q₀ hA
    obtain ⟨d, φ, ψ, p₁, p₂, p₃⟩ := hf.levi y
    have hs : ∀ a b : G1 K 2, f (lv a b 0 * y) = ∑ j, φ j a * ψ j b := fun a b =>
      p₃ a b _ (by rw [Subgroup.coe_mul, lv_zero])
    simp only [hs, Finset.mul_sum]
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨v, hv, hr⟩ := (p₁ j).2
      have h0 := (ptPi K ι C μ₂ v (φ j) (p₁ j).1 hr).1 i n₀ q₀ ((hmin i).2 n₀ q₀ hA v hv) M
      have e1 : ∀ m, conj (KT.psi n₀ q₀ n₀ m) * (φ j (M * C.un i m) * ψ j m₂) =
          (conj (KT.psi n₀ q₀ n₀ m) * φ j (M * C.un i m)) * ψ j m₂ := fun m => by ring
      simp only [e1]
      rw [integral_mul_const, h0, zero_mul]
    · intro j _
      exact KT.integrable_of_continuous ((KT.continuous_conj_psi n₀ q₀ n₀).mul
        (((p₁ j).1.comp (continuous_const.mul (un_cont C i))).mul continuous_const))
  have key₂ : ∀ (y : G1 K (2 + 2)) (M m₁ : G1 K 2) i n₀ q₀, ¬ Above (n' i) (q' i) n₀ q₀ →
      ∫ m, conj (KT.psi n₀ q₀ n₀ m) * f (lv m₁ (M * C.un i m) 0 * y) ∂μK = 0 := by
    intro y M m₁ i n₀ q₀ hA
    obtain ⟨d, φ, ψ, p₁, p₂, p₃⟩ := hf.levi y
    have hs : ∀ a b : G1 K 2, f (lv a b 0 * y) = ∑ j, φ j a * ψ j b := fun a b =>
      p₃ a b _ (by rw [Subgroup.coe_mul, lv_zero])
    simp only [hs, Finset.mul_sum]
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨v, hv, hr⟩ := (p₂ j).2
      have h0 := (ptPi K ι C μ₂ v (ψ j) (p₂ j).1 hr).1 i n₀ q₀ ((hmin' i).2 n₀ q₀ hA v hv) M
      have e1 : ∀ m, conj (KT.psi n₀ q₀ n₀ m) * (φ j m₁ * ψ j (M * C.un i m)) =
          (conj (KT.psi n₀ q₀ n₀ m) * ψ j (M * C.un i m)) * φ j m₁ := fun m => by ring
      simp only [e1]
      rw [integral_mul_const, h0, zero_mul]
    · intro j _
      exact KT.integrable_of_continuous ((KT.continuous_conj_psi n₀ q₀ n₀).mul
        (continuous_const.mul ((p₂ j).1.comp (continuous_const.mul (un_cont C i)))))
  have hall : ∀ (m₁ m₂ : G1 K 2) (h : FA K (2 + 2)) (a : archCompact K (2 + 2)),
      f (lv m₁ m₂ 0 * fin1 h * arc1 a) = 0 := by
    intro m₁ m₂ h a
    have hc : Continuous fun k : ι → U4 => f (lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
      refine hf.cont.comp (continuous_const.mul ?_)
      exact continuous_archP.comp (continuous_subtype_val.comp (C.Φ (2 + 2)).symm.continuous)
    have hr : RFix (Measure.pi fun _ : ι => μ) (fun k => ∏ i, e i (k i))
        fun k : ι → U4 => f (lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
      intro g
      have := hfix (lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm g))
      rw [Co.κ₄, int_map] at this
      simp only [he] at this
      simp only [ha, ← mul_assoc]
      exact this
    have hzero := hE.inj _ hc hr (fun i n₀ q₀ hA l k => ?_) (fun i n₀ q₀ hA l k => ?_) (fun a b => ?_)
    · have := congrFun hzero (C.Φ (2 + 2) a)
      simpa only [ContinuousMulEquiv.symm_apply_apply, Pi.zero_apply] using this
    · have e1 : ∀ m : U2, lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd (l * m) 1) * k)) =
          lv (m₁ * C.un i l * C.un i m) m₂ 0 * (fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
        intro m
        have h2 : lv (m₁ * C.un i l * C.un i m) m₂ 0 =
            lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd (l * m) 1))) := by
          have := hmul m₁ m₂ (C.un i (l * m)) 1 0 0
          rw [mul_one, add_zero, hun, ← mul_assoc] at this
          rw [hs₁, hun]
          rw [this]
        rw [h2, ha, mul_assoc, mul_assoc, ← mul_assoc (fin1 h), ← mul_assoc (arc1 _), (hcomm _ _ h).eq]
      simp only [e1]
      exact key₁ _ _ _ i n₀ q₀ hA
    · have e1 : ∀ m : U2, lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd 1 (l * m)) * k)) =
          lv m₁ (m₂ * C.un i l * C.un i m) 0 * (fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
        intro m
        have h2 : lv m₁ (m₂ * C.un i l * C.un i m) 0 =
            lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd 1 (l * m)))) := by
          have := hmul m₁ m₂ 1 (C.un i (l * m)) 0 0
          rw [mul_one, add_zero, hun, ← mul_assoc] at this
          rw [hs₂, hun]
          rw [this]
        rw [h2, ha, mul_assoc, mul_assoc, ← mul_assoc (fin1 h), ← mul_assoc (arc1 _), (hcomm _ _ h).eq]
      simp only [e1]
      exact key₂ _ _ _ i n₀ q₀ hA
    · have h2 : lv (m₁ * arc1 ((C.Φ 2).symm a)) (m₂ * arc1 ((C.Φ 2).symm b)) 0 =
          lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i)) := by
        rw [← hlv, hmul, add_zero]
      show f (lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm ((fun i => bd (a i) (b i)) * x))) = 0
      rw [ha, sw _ _ _ _ (hcomm _ _ h).eq (hcomm _ _ h).eq, ← h2]
      exact hz h _ _
  have hray : ∀ (t : ℝ) (y : G1 K (2 + 2)), f (lv 1 1 t * y) = f y := by
    intro t y
    refine hf.ray ⟨Real.exp t, Real.exp_pos t⟩ _ y ?_
    rw [Subgroup.coe_mul, hb.1, Subgroup.coe_one, one_mul, one_mul]
    have e2 : (⟨Real.exp (-t), Real.exp_pos (-t)⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ :=
      Subtype.ext (Real.exp_neg t)
    simp only [zt, e2]
  funext g
  obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
  obtain ⟨a, h, -, rfl⟩ := hKG (2 + 2) k hk
  have e3 : lv m₁ m₂ t = lv 1 1 t * lv m₁ m₂ 0 := by
    rw [hmul, one_mul, one_mul, add_zero]
  rw [mul_assoc, hf.unip X, e3, mul_assoc, hray, (hcomm _ _ h).eq, ← mul_assoc]
  exact hall m₁ m₂ h a
