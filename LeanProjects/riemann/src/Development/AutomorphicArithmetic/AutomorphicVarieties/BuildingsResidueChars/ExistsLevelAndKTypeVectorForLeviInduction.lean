import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.PiLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MaximalCompactUniqueArchFiniteDecomposition
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnipotentMemMaximalCompactFiniteIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLevelIndicatorUnipotentInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HaarDecompositionNormOneGl2

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

private theorem arcV {n : ℕ} (a : archCompact K n) :
    ((arc1 a : G1 K n) : AdelicGLn.AdelicGL K n) = infEmb K n (a : archGroup K n) :=
  congrArg Subtype.val (archProj_of_mem (A := ((a : archGroup K n) : ArchUnits K n))
    (maxCompact_le_normOneGL a.2))

private theorem finV {n : ℕ} (h : AdelicGLn.integralFiniteGL K n) :
    ((fin1 (h : FA K n) : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n (h : FA K n) :=
  congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact h.2)))

private theorem cm {n : ℕ} (a : archCompact K n) (h : FA K n) : Commute (arc1 a) (fin1 h) :=
  (MultiplicityOne.finProj_mul_archProj_comm h _).symm

private theorem arcM {n : ℕ} (a b : archCompact K n) : (arc1 (a * b) : G1 K n) = arc1 a * arc1 b :=
  map_mul (archP K n) _ _

private theorem arcI {n : ℕ} (a : archCompact K n) : (arc1 a⁻¹ : G1 K n) = (arc1 a)⁻¹ :=
  map_inv (archP K n) _

private theorem fin1M {n : ℕ} (a b : FA K n) : (fin1 (a * b) : G1 K n) = fin1 a * fin1 b :=
  map_mul (MultiplicityOne.finProj K n) a b

private theorem finite_projection_one {n : ℕ} : (fin1 (1 : FA K n) : G1 K n) = 1 := map_one (MultiplicityOne.finProj K n)

private theorem archimedean_projection_one {n : ℕ} : (arc1 (1 : archCompact K n) : G1 K n) = 1 := map_one (archP K n)

private theorem zt00 : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

private theorem fin_fst {n : ℕ} (y : FA K n) (a b : Fin n) :
    (finEmb K n y a b).1 = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) a b := by
  rw [← AdelicGLn.prodEquiv_apply_fst, prodEquiv_finEmb]
  rfl

private theorem blk_fst (d₁ d₂ : FA K 2) :
    (AdelicGLn.prodEquiv K (2 + 2) (blk (finEmb K 2 d₁) (finEmb K 2 d₂))).1 = 1 := by
  refine Units.ext (Matrix.ext fun r s => ?_)
  rw [AdelicGLn.prodEquiv_apply_fst]
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective r
  obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective s
  change _ = (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (InfiniteAdeleRing K)) _ _
  rw [← Matrix.submatrix_apply (1 : Matrix _ _ _) finSumFinEquiv finSumFinEquiv, Matrix.submatrix_one_equiv,
      ← Matrix.fromBlocks_one]
  simp only [blk, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases r with r | r <;> rcases s with s | s
  · exact fin_fst _ r s
  · rfl
  · rfl
  · exact fin_fst _ r s

private theorem lv_fin (d₁ d₂ : AdelicGLn.integralFiniteGL K 2) :
    ∃ h : AdelicGLn.integralFiniteGL K (2 + 2), lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 = fin1 (h : FA K (2 + 2)) := by
  obtain ⟨α, β, -, -, hdec, -, -, -⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) (2 + 2)
  obtain ⟨_, _, _, _, _, _, _, hfin⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) 2
  have hmem : lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 ∈ KG K (2 + 2) :=
    (blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.1 _ (hfin d₁) _ (hfin d₂)
  have e := hdec ⟨_, hmem⟩
  simp only at e
  have e1 : ((lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (finEmb K 2 (d₁ : FA K 2)) (finEmb K 2 (d₂ : FA K 2)) := by
    rw [(blkLaws (K := K)).1, neg_zero, zt00, mul_one, mul_one, finV, finV]
  have e2 := congrArg (fun g : G1 K (2 + 2) => (AdelicGLn.prodEquiv K (2 + 2) (g : AdelicGLn.AdelicGL K (2 + 2))).1) e
  simp only [e1, blk_fst, Subgroup.coe_mul, arcV, finV, map_mul, prodEquiv_infEmb, prodEquiv_finEmb, Prod.fst_mul, mul_one] at e2
  have e3 : α ⟨_, hmem⟩ = 1 := by
    apply Subtype.ext
    have := congrArg (archEquiv K (2 + 2)) e2
    simpa using this.symm
  refine ⟨β ⟨_, hmem⟩, ?_⟩
  rw [e3, archimedean_projection_one, one_mul] at e
  exact e

end SlopeTestRemainingChoices

section Aux2

variable {K : Type} [Field K] [NumberField K]

private theorem cont_int {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] (ν : Measure Z) [IsFiniteMeasure ν] (F : Y → Z → ℝ) (hF : Continuous (Function.uncurry F)) :
    Continuous fun y => ∫ z, F y z ∂ν := by
  let G : C(Y, C(Z, ℝ)) := ContinuousMap.curry ⟨Function.uncurry F, hF⟩
  have hL : Continuous fun g : C(Z, ℝ) => ∫ z, g z ∂ν := by
    refine (LipschitzWith.of_dist_le_mul (K := (ν.real Set.univ).toNNReal) fun f g => ?_).continuous
    have hi : ∀ g : C(Z, ℝ), Integrable g ν := fun g =>
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [dist_eq_norm, ← integral_sub (hi f) (hi g), Real.coe_toNNReal _ measureReal_nonneg, dist_eq_norm, mul_comm]
    refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun z => ?_)
    exact (f - g).norm_coe_le_norm z
  exact hL.comp G.continuous

private theorem int_pos {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] [ν.IsOpenPosMeasure] (g : Z → ℝ) (hg : Continuous g) (h0 : ∀ z, 0 ≤ g z) (z₀ : Z)
    (hz : 0 < g z₀) : 0 < ∫ z, g z ∂ν := by
  rw [integral_pos_iff_support_of_nonneg h0
    (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  exact (isOpen_compl_singleton.preimage hg).measure_pos ν ⟨z₀, hz.ne'⟩

private theorem drop {n : ℕ} (V : Subgroup (FA K n)) (φ : G1 K n → ℂ) (hF : FixF V φ) (a : archCompact K n) (d : FA K n)
    (hd : d ∈ V) (m : G1 K n) : φ (m * (arc1 a * fin1 d)⁻¹) = φ (m * arc1 a⁻¹) := by
  have e : (arc1 a * fin1 d)⁻¹ = arc1 a⁻¹ * fin1 d⁻¹ := by
    rw [_root_.mul_inv_rev, ← arcI, ← map_inv (MultiplicityOne.finProj K n) d]
    exact (cm a⁻¹ d⁻¹).eq.symm
  rw [e, ← mul_assoc]
  exact hF _ (V.inv_mem hd) _

private theorem fixInv {n : ℕ} (κ : Measure (archCompact K n)) (hinv : MeasurePreserving (·⁻¹) κ κ) (p : archCompact K n → ℂ)
    (hs : ∀ k, p k⁻¹ = conj (p k)) (φ : G1 K n → ℂ) (h : FixA κ p φ) (m : G1 K n) :
    ∫ a, conj (p a) * φ (m * arc1 a⁻¹) ∂κ = φ m := by
  rw [← h m]
  have := hinv.integral_comp (Homeomorph.inv (archCompact K n)).measurableEmbedding (fun k => p k * φ (m * arc1 k))
  simp only [hs] at this
  exact this

private theorem κInv {ι : Type} [Fintype ι] (C : Co K ι) : MeasurePreserving (·⁻¹) C.κ₂ C.κ₂ := by
  have hm : Measurable (C.Φ 2).symm := (C.Φ 2).symm.continuous.measurable
  have hE : MeasurePreserving (C.Φ 2).symm (Measure.pi fun _ : ι => μK) C.κ₂ := ⟨hm, rfl⟩
  refine hE.of_semiconj (measurePreserving_pi _ _ fun i => Measure.measurePreserving_inv μK) (fun x => ?_)
    continuous_inv.measurable
  change (C.Φ 2).symm (fun i => (x i)⁻¹) = ((C.Φ 2).symm x)⁻¹
  rw [← map_inv]
  rfl

private theorem pCont {ι : Type} [Fintype ι] (C : Co K ι) (n : ι → ℕ) (q : ι → ℤ) : Continuous (C.p n q) :=
  continuous_finset_prod _ fun i _ =>
    (continuous_const.mul (KT.continuous_conj_psi (n i) (q i) (n i))).comp ((continuous_apply i).comp (C.Φ 2).continuous)

private theorem pStar {ι : Type} [Fintype ι] (C : Co K ι) (n : ι → ℕ) (q : ι → ℤ) (k : archCompact K 2) :
    C.p n q k⁻¹ = conj (C.p n q k) := by
  simp only [Co.p, map_inv, Pi.inv_apply, map_prod, T, KT.psi_self_inv, map_mul, map_inv₀, Complex.conj_ofReal,
    starRingEnd_self_apply]

private noncomputable def psi {m : ℕ} (α : KG K m → archCompact K m) (β : KG K m → AdelicGLn.integralFiniteGL K m)
    (f : archCompact K m → ℂ) (χ : AdelicGLn.integralFiniteGL K m → ℂ) (g : G1 K m) : ℂ :=
  if h : g ∈ KG K m then f (α ⟨g, h⟩) * χ (β ⟨g, h⟩) else 0

private theorem psi_at {m : ℕ} {α : KG K m → archCompact K m} {β : KG K m → AdelicGLn.integralFiniteGL K m}
    (f : archCompact K m → ℂ) (χ : AdelicGLn.integralFiniteGL K m → ℂ)
    (hu : ∀ (a : archCompact K m) (h : AdelicGLn.integralFiniteGL K m) (k : KG K m),
      (k : G1 K m) = arc1 a * fin1 (h : FA K m) → α k = a ∧ β k = h)
    (ha : ∀ a : archCompact K m, arc1 a ∈ KG K m) (hf : ∀ h : AdelicGLn.integralFiniteGL K m, fin1 (h : FA K m) ∈ KG K m)
    (a : archCompact K m) (h : AdelicGLn.integralFiniteGL K m) :
    psi α β f χ (arc1 a * fin1 (h : FA K m)) = f a * χ h := by
  have hm : arc1 a * fin1 (h : FA K m) ∈ KG K m := mul_mem (ha a) (hf h)
  obtain ⟨h1, h2⟩ := hu a h ⟨_, hm⟩ rfl
  rw [psi, dif_pos hm, h1, h2]

private theorem psi_cont {m : ℕ} {α : KG K m → archCompact K m} {β : KG K m → AdelicGLn.integralFiniteGL K m}
    {f : archCompact K m → ℂ} {χ : AdelicGLn.integralFiniteGL K m → ℂ} (hα : Continuous α) (hβ : Continuous β)
    (hf : Continuous f) (hχ : Continuous χ) : Continuous fun k : KG K m => psi α β f χ k := by
  have e : (fun k : KG K m => psi α β f χ k) = fun k => f (α k) * χ (β k) := by
    funext k
    rw [psi, dif_pos k.2]
  rw [e]
  exact (hf.comp hα).mul (hχ.comp hβ)

end Aux2

section Aux3

variable {K : Type} [Field K] [NumberField K]

private theorem lvKG (v₁ v₂ : KG K 2) : lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 ∈ KG K (2 + 2) :=
  (blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.1 _ v₁.2 _ v₂.2

private theorem arcKG (y : archCompact K (2 + 2)) : arc1 y ∈ KG K (2 + 2) := by
  obtain ⟨_, _, _, _, _, _, h, _⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) (2 + 2)
  exact h y

private theorem lvy_cont (Ψ : G1 K (2 + 2) → ℂ) (hΨc : Continuous fun k : KG K (2 + 2) => Ψ k) (y : archCompact K (2 + 2))
    (v₁ : KG K 2) : Continuous fun k : KG K 2 => Ψ (lv (v₁ : G1 K 2) (k : G1 K 2) 0 * arc1 y) := by
  have h1 : Continuous fun k : KG K 2 => ((v₁ : G1 K 2), (k : G1 K 2), (0 : ℝ)) :=
    continuous_const.prodMk (continuous_subtype_val.prodMk continuous_const)
  have h0 : Continuous (fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2) := (blkLaws (K := K)).2.2.2.1
  have h2 : Continuous fun k : KG K 2 => lv (v₁ : G1 K 2) (k : G1 K 2) 0 := by
    have h := Continuous.comp h0 h1
    exact h
  have h3 : Continuous fun k : KG K 2 => (⟨lv (v₁ : G1 K 2) (k : G1 K 2) 0 * arc1 y, mul_mem (lvKG v₁ k) (arcKG y)⟩ : KG K (2 + 2)) :=
    Continuous.subtype_mk (h2.mul continuous_const) _
  exact hΨc.comp h3

private theorem pt_val (Ψ : G1 K (2 + 2) → ℂ) (y : archCompact K (2 + 2))
    (B : AdelicGLn.integralFiniteGL K 2 → AdelicGLn.integralFiniteGL K 2 → AdelicGLn.integralFiniteGL K (2 + 2))
    (hB : ∀ d₁ d₂ : AdelicGLn.integralFiniteGL K 2, lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 = fin1 (B d₁ d₂ : FA K (2 + 2)))
    (χ : AdelicGLn.integralFiniteGL K (2 + 2) → ℂ) (f₁ f₂ : archCompact K 2 → ℂ)
    (hΨ : ∀ a₁ a₂ (h : AdelicGLn.integralFiniteGL K (2 + 2)),
      Ψ (lv (arc1 a₁) (arc1 a₂) 0 * arc1 y * fin1 (h : FA K (2 + 2))) = f₁ a₁ * f₂ a₂ * χ h)
    (V₁ V₂ : Subgroup (FA K 2)) (hχV : ∀ d₁ d₂, χ (B d₁ d₂) ≠ 0 → (d₁ : FA K 2) ∈ V₁ ∧ (d₂ : FA K 2) ∈ V₂)
    (φ₁ φ₂ : G1 K 2 → ℂ) (hF₁ : FixF V₁ φ₁) (hF₂ : FixF V₂ φ₂) (m₁ m₂ : G1 K 2)
    (a₁ : archCompact K 2) (d₁ : AdelicGLn.integralFiniteGL K 2) (a₂ : archCompact K 2) (d₂ : AdelicGLn.integralFiniteGL K 2) :
    Ψ (lv (arc1 a₁ * fin1 (d₁ : FA K 2)) (arc1 a₂ * fin1 (d₂ : FA K 2)) 0 * arc1 y) *
        φ₁ (m₁ * (arc1 a₁ * fin1 (d₁ : FA K 2))⁻¹) * φ₂ (m₂ * (arc1 a₂ * fin1 (d₂ : FA K 2))⁻¹) =
      (f₁ a₁ * φ₁ (m₁ * arc1 a₁⁻¹)) * (f₂ a₂ * φ₂ (m₂ * arc1 a₂⁻¹)) * χ (B d₁ d₂) := by
  have e1 : lv (arc1 a₁ * fin1 (d₁ : FA K 2)) (arc1 a₂ * fin1 (d₂ : FA K 2)) 0 * arc1 y =
      lv (arc1 a₁) (arc1 a₂) 0 * arc1 y * fin1 (B d₁ d₂ : FA K (2 + 2)) := by
    have e := (blkLaws (K := K)).2.1 (arc1 a₁) (arc1 a₂) (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 0
    rw [add_zero] at e
    rw [← e, hB, mul_assoc, mul_assoc, (cm y _).eq]
  rw [e1, hΨ]
  by_cases h0 : χ (B d₁ d₂) = 0
  · simp [h0]
  · obtain ⟨h₁, h₂⟩ := hχV d₁ d₂ h0
    rw [drop V₁ φ₁ hF₁ a₁ _ h₁, drop V₂ φ₂ hF₂ a₂ _ h₂]
    ring

private theorem closing (κ : Measure (archCompact K 2)) (ν : Measure (AdelicGLn.integralFiniteGL K 2)) (ρ : Measure (KG K 2))
    (hρF : ∀ F : G1 K 2 → ℂ, (Continuous fun k : KG K 2 => F k) →
      ∫ v, F (v : G1 K 2) ∂ρ = ∫ a, ∫ d, F (arc1 a * fin1 (d : FA K 2)) ∂ν ∂κ)
    (g₁ : archCompact K 2 → ℂ) (hg₁c : Continuous g₁) (G : ℂ)
    (X : AdelicGLn.integralFiniteGL K 2 → ℂ) (hXc : Continuous X) (J : KG K 2 → ℂ)
    (α₂ : KG K 2 → archCompact K 2) (β₂ : KG K 2 → AdelicGLn.integralFiniteGL K 2) (hα₂ : Continuous α₂) (hβ₂ : Continuous β₂)
    (huniq₂ : ∀ (a : archCompact K 2) (h : AdelicGLn.integralFiniteGL K 2) (k : KG K 2),
      (k : G1 K 2) = arc1 a * fin1 (h : FA K 2) → α₂ k = a ∧ β₂ k = h)
    (harc₂ : ∀ a : archCompact K 2, arc1 a ∈ KG K 2) (hfin₂ : ∀ h : AdelicGLn.integralFiniteGL K 2, fin1 (h : FA K 2) ∈ KG K 2)
    (hJ : ∀ v, J v = g₁ (α₂ v) * G * X (β₂ v)) :
    ∫ v, J v ∂ρ = (∫ a, g₁ a ∂κ) * G * ∫ d, X d ∂ν := by
  have hFc : Continuous fun k : KG K 2 => psi α₂ β₂ (fun a => g₁ a * G) X k :=
    psi_cont hα₂ hβ₂ (hg₁c.mul continuous_const) hXc
  calc _ = ∫ v₁ : KG K 2, psi α₂ β₂ (fun a => g₁ a * G) X (v₁ : G1 K 2) ∂ρ := by
        refine integral_congr_ae (Eventually.of_forall fun v₁ => ?_)
        change J v₁ = psi α₂ β₂ (fun a => g₁ a * G) X (v₁ : G1 K 2)
        rw [hJ, psi, dif_pos v₁.2]
    _ = ∫ a, ∫ d, g₁ a * G * X d ∂ν ∂κ := by
        rw [hρF _ hFc]
        simp only [psi_at _ _ huniq₂ harc₂ hfin₂]
    _ = _ := by
        simp only [integral_const_mul, integral_mul_const]

private theorem value (κ : Measure (archCompact K 2)) (ν : Measure (AdelicGLn.integralFiniteGL K 2)) (ρ : Measure (KG K 2))
    (hρF : ∀ F : G1 K 2 → ℂ, (Continuous fun k : KG K 2 => F k) →
      ∫ v, F (v : G1 K 2) ∂ρ = ∫ a, ∫ d, F (arc1 a * fin1 (d : FA K 2)) ∂ν ∂κ)
    (Ψ : G1 K (2 + 2) → ℂ) (hΨc : Continuous fun k : KG K (2 + 2) => Ψ k) (y : archCompact K (2 + 2))
    (B : AdelicGLn.integralFiniteGL K 2 → AdelicGLn.integralFiniteGL K 2 → AdelicGLn.integralFiniteGL K (2 + 2))
    (hB : ∀ d₁ d₂ : AdelicGLn.integralFiniteGL K 2, lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 = fin1 (B d₁ d₂ : FA K (2 + 2)))
    (χ : AdelicGLn.integralFiniteGL K (2 + 2) → ℂ) (f₁ f₂ : archCompact K 2 → ℂ) (hf₁ : Continuous f₁)
    (hΨ : ∀ a₁ a₂ (h : AdelicGLn.integralFiniteGL K (2 + 2)),
      Ψ (lv (arc1 a₁) (arc1 a₂) 0 * arc1 y * fin1 (h : FA K (2 + 2))) = f₁ a₁ * f₂ a₂ * χ h)
    (X : AdelicGLn.integralFiniteGL K 2 → ℂ) (hX : ∀ d₁, ∫ d₂, χ (B d₁ d₂) ∂ν = X d₁) (hXc : Continuous X)
    (V₁ V₂ : Subgroup (FA K 2)) (hχV : ∀ d₁ d₂, χ (B d₁ d₂) ≠ 0 → (d₁ : FA K 2) ∈ V₁ ∧ (d₂ : FA K 2) ∈ V₂)
    (φ₁ φ₂ : G1 K 2 → ℂ) (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (hF₁ : FixF V₁ φ₁) (hF₂ : FixF V₂ φ₂) (m₁ m₂ : G1 K 2) :
    (∫ v₁ : KG K 2, ∫ v₂ : KG K 2, Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * arc1 y) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) *
      φ₂ (m₂ * (v₂ : G1 K 2)⁻¹) ∂ρ ∂ρ) =
      (∫ a, f₁ a * φ₁ (m₁ * arc1 a⁻¹) ∂κ) * (∫ a, f₂ a * φ₂ (m₂ * arc1 a⁻¹) ∂κ) * ∫ d, X d ∂ν := by
  obtain ⟨α₂, β₂, hα₂, hβ₂, hdec₂, huniq₂, harc₂, hfin₂⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) 2
  have hac : Continuous (arc1 : archCompact K 2 → G1 K 2) := continuous_archP.comp continuous_subtype_val
  have hg₁c : Continuous fun a => f₁ a * φ₁ (m₁ * arc1 a⁻¹) :=
    hf₁.mul (hφ₁.comp (continuous_const.mul (hac.comp continuous_inv)))
  refine closing κ ν ρ hρF _ hg₁c _ X hXc _ α₂ β₂ hα₂ hβ₂ huniq₂ harc₂ hfin₂ fun v₁ => ?_
  have hc : Continuous fun k : KG K 2 => Ψ (lv (v₁ : G1 K 2) (k : G1 K 2) 0 * arc1 y) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) *
      φ₂ (m₂ * (k : G1 K 2)⁻¹) :=
    ((lvy_cont Ψ hΨc y v₁).mul continuous_const).mul (hφ₂.comp (continuous_const.mul continuous_subtype_val.inv))
  rw [hρF (fun g => Ψ (lv (v₁ : G1 K 2) g 0 * arc1 y) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * g⁻¹)) hc]
  have e : ∀ a (d : AdelicGLn.integralFiniteGL K 2),
      Ψ (lv (v₁ : G1 K 2) (arc1 a * fin1 (d : FA K 2)) 0 * arc1 y) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) *
        φ₂ (m₂ * (arc1 a * fin1 (d : FA K 2))⁻¹) =
      (f₁ (α₂ v₁) * φ₁ (m₁ * arc1 (α₂ v₁)⁻¹)) * (f₂ a * φ₂ (m₂ * arc1 a⁻¹)) * χ (B (β₂ v₁) d) := by
    intro a d
    have := pt_val Ψ y B hB χ f₁ f₂ hΨ V₁ V₂ hχV φ₁ φ₂ hF₁ hF₂ m₁ m₂ (α₂ v₁) (β₂ v₁) a d
    rwa [← hdec₂ v₁] at this
  simp only [e, integral_const_mul, hX, integral_mul_const]

end Aux3

section PrimeReciprocalSums

variable {K : Type} [Field K] [NumberField K]

private theorem blockEx (β : KG K (2 + 2) → AdelicGLn.integralFiniteGL K (2 + 2)) (hβ : Continuous β)
    (huniq : ∀ (a : archCompact K (2 + 2)) (h : AdelicGLn.integralFiniteGL K (2 + 2)) (k : KG K (2 + 2)),
      (k : G1 K (2 + 2)) = arc1 a * fin1 (h : FA K (2 + 2)) → β k = h) :
    ∃ B : AdelicGLn.integralFiniteGL K 2 → AdelicGLn.integralFiniteGL K 2 → AdelicGLn.integralFiniteGL K (2 + 2),
      (∀ d₁ d₂ : AdelicGLn.integralFiniteGL K 2, lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 = fin1 (B d₁ d₂ : FA K (2 + 2))) ∧
      Continuous (Function.uncurry B) ∧ B 1 1 = 1 := by
  obtain ⟨_, _, _, _, _, _, _, hfin⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) 2
  have hm : ∀ d₁ d₂ : AdelicGLn.integralFiniteGL K 2, lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 ∈ KG K (2 + 2) :=
    fun d₁ d₂ => lvKG ⟨_, hfin d₁⟩ ⟨_, hfin d₂⟩
  have hB : ∀ d₁ d₂ : AdelicGLn.integralFiniteGL K 2, lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 =
      fin1 (β ⟨_, hm d₁ d₂⟩ : FA K (2 + 2)) := by
    intro d₁ d₂
    obtain ⟨h, eh⟩ := lv_fin d₁ d₂
    rw [huniq 1 h ⟨_, hm d₁ d₂⟩ (by rw [archimedean_projection_one, one_mul]; exact eh)]
    exact eh
  refine ⟨fun d₁ d₂ => β ⟨_, hm d₁ d₂⟩, hB, ?_, ?_⟩
  · have h0 : Continuous (fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2) := (blkLaws (K := K)).2.2.2.1
    have hf : Continuous fun d : AdelicGLn.integralFiniteGL K 2 => fin1 (d : FA K 2) :=
      MultiplicityOne.continuous_finProj.comp continuous_subtype_val
    have h1 : Continuous fun p : AdelicGLn.integralFiniteGL K 2 × AdelicGLn.integralFiniteGL K 2 =>
        ((fin1 (p.1 : FA K 2) : G1 K 2), (fin1 (p.2 : FA K 2) : G1 K 2), (0 : ℝ)) :=
      (hf.comp continuous_fst).prodMk ((hf.comp continuous_snd).prodMk continuous_const)
    have h2 : Continuous fun p : AdelicGLn.integralFiniteGL K 2 × AdelicGLn.integralFiniteGL K 2 =>
        lv (fin1 (p.1 : FA K 2)) (fin1 (p.2 : FA K 2)) 0 := by
      have h := Continuous.comp h0 h1
      exact h
    have h3 : Continuous fun p : AdelicGLn.integralFiniteGL K 2 × AdelicGLn.integralFiniteGL K 2 =>
        (⟨_, hm p.1 p.2⟩ : KG K (2 + 2)) := Continuous.subtype_mk h2 _
    exact hβ.comp h3
  · apply huniq 1 1
    simp only [OneMemClass.coe_one, finite_projection_one, archimedean_projection_one, one_mul, mul_one]
    exact (blkLaws (K := K)).2.2.1

private theorem compact_integral_finite_gl2 : CompactSpace (AdelicGLn.integralFiniteGL K 2) := by
  obtain ⟨α, β, -, hβ, -, huniq, harc, hfin⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) 2
  haveI : CompactSpace (KG K 2) := isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 2).1
  refine Function.Surjective.compactSpace (f := β) hβ (fun h => ⟨⟨_, hfin h⟩, ?_⟩)
  exact (huniq 1 h ⟨_, hfin h⟩ (by rw [archimedean_projection_one, one_mul])).2

private theorem cEx (ν : Measure (AdelicGLn.integralFiniteGL K 2)) [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure]
    (B : AdelicGLn.integralFiniteGL K 2 → AdelicGLn.integralFiniteGL K 2 → AdelicGLn.integralFiniteGL K (2 + 2))
    (hBc : Continuous (Function.uncurry B)) (hB1 : B 1 1 = 1)
    (χ : AdelicGLn.integralFiniteGL K (2 + 2) → ℂ) (hχc : Continuous χ) (h01 : ∀ h, χ h = 0 ∨ χ h = 1) (h1 : χ 1 = 1) :
    ∃ (c : ℝ) (X : AdelicGLn.integralFiniteGL K 2 → ℂ), 0 < c ∧ Continuous X ∧ (∀ d₁, ∫ d₂, χ (B d₁ d₂) ∂ν = X d₁) ∧
      ∫ d, X d ∂ν = c := by
  haveI := compact_integral_finite_gl2 (K := K)
  have hre : ∀ h, χ h = (((χ h).re : ℝ) : ℂ) := by
    intro h
    rcases h01 h with e | e <;> simp [e]
  have hnn : ∀ h, 0 ≤ (χ h).re := by
    intro h
    rcases h01 h with e | e <;> simp [e]
  have hc2 : Continuous (Function.uncurry fun d₁ d₂ => (χ (B d₁ d₂)).re) :=
    Complex.continuous_re.comp (hχc.comp hBc)
  have hXc : Continuous fun d₁ => ∫ d₂, (χ (B d₁ d₂)).re ∂ν := cont_int ν _ hc2
  have hs : Continuous fun d₂ => (χ (B 1 d₂)).re :=
    hc2.comp (continuous_const.prodMk continuous_id)
  refine ⟨∫ d₁, ∫ d₂, (χ (B d₁ d₂)).re ∂ν ∂ν, fun d₁ => ((∫ d₂, (χ (B d₁ d₂)).re ∂ν : ℝ) : ℂ), ?_,
    Complex.continuous_ofReal.comp hXc, fun d₁ => ?_, ?_⟩
  · refine int_pos ν _ hXc (fun d₁ => integral_nonneg fun d₂ => hnn _) 1 ?_
    refine int_pos ν _ hs (fun d₂ => hnn _) 1 ?_
    simp [hB1, h1]
  · refine Eq.trans ?_ integral_complex_ofReal
    exact integral_congr_ae (Eventually.of_forall fun d₂ => hre _)
  · exact integral_complex_ofReal

end PrimeReciprocalSums

theorem UpperTheory.exists_level_and_KTypeVector_for_leviInduction :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure U4) (e : ι → U4 → ℂ) n q n' q' (x : ι → U4), Haar4 μ → ExtP μ e n q n' q' x → ∀ (S : Finset (Pl K)) (U₁ U₂ : ∀ w : Pl K, Subgroup (Gw 2 w)), Lev U₁ → Lev U₂ → ∃ (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)) (ρ : Measure (KG K 2)) (Ψ : G1 K (2 + 2) → ℂ) (c : ℝ), Lev U ∧ IsProbabilityMeasure ρ ∧ (∀ u : KG K 2, MeasurePreserving (· * u) ρ ρ) ∧ (Continuous fun k : KG K (2 + 2) => Ψ k) ∧ (∀ X, nn X ∈ KG K (2 + 2) → ∀ k ∈ KG K (2 + 2), Ψ (nn X * k) = Ψ k) ∧ (∀ k ∈ KG K (2 + 2), ∫ a, C.e e a * Ψ (k * arc1 a) ∂C.κ₄ μ = Ψ k) ∧ (∀ k ∈ KG K (2 + 2), ∀ u ∈ levOn S U, Ψ (k * fin1 u) = Ψ k) ∧ 0 < c ∧ ∀ φ₁ φ₂ : G1 K 2 → ℂ, Continuous φ₁ → Continuous φ₂ → FixA C.κ₂ (C.p n q) φ₁ → FixA C.κ₂ (C.p n' q') φ₂ → FixF (levOn S U₁) φ₁ → FixF (levOn S U₂) φ₂ → ∀ m₁ m₂, (∫ v₁ : KG K 2, ∫ v₂ : KG K 2, Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * arc1 ((C.Φ (2 + 2)).symm x)) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹) ∂ρ ∂ρ) = c * φ₁ m₁ * φ₂ m₂ := by
  intro K _ _ _ ι _ C μ e n q n' q' x hμ hE S U₁ U₂ hU₁ hU₂
  obtain ⟨α, β, hα, hβ, hdec, huniq, harc, hfin⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) (2 + 2)
  obtain ⟨U, χ, hU, hχc, hχ01, hχ1, hχN, hχR, hχL⟩ := UpperTheory.exists_level_indicator_unipotent_invariant S U₁ U₂ hU₁ hU₂
  have hCo := coLaws K ι C
  obtain ⟨ν, ρ, hν, hνo, hρ, hρr, hρF⟩ := UpperTheory.haar_decomposition_norm_one_gl2 C.κ₂ hCo.1
  obtain ⟨ψ, hψc, hψfix, hψval⟩ := hE.ex
  obtain ⟨B, hB, hBc, hB1⟩ := blockEx β hβ fun a h k hk => (huniq a h k hk).2
  obtain ⟨c, X, hc, hXc, hX, hXi⟩ := cEx ν B hBc hB1 χ hχc hχ01 hχ1
  have hf : Continuous fun a : archCompact K (2 + 2) => ψ (C.Φ (2 + 2) a) := hψc.comp (C.Φ (2 + 2)).continuous
  have hat := psi_at (fun a : archCompact K (2 + 2) => ψ (C.Φ (2 + 2) a)) χ huniq harc hfin
  have hcont := psi_cont hα hβ hf hχc
  have hdc : ∀ k ∈ KG K (2 + 2), ∃ (a : archCompact K (2 + 2)) (h : AdelicGLn.integralFiniteGL K (2 + 2)),
      k = arc1 a * fin1 (h : FA K (2 + 2)) := fun k hk => ⟨_, _, hdec ⟨k, hk⟩⟩
  have hle : levOn S U ≤ AdelicGLn.integralFiniteGL K (2 + 2) := by
    intro u hu
    refine (AdelicGLn.mem_integralFiniteGL_iff_forall K (2 + 2)).2 fun v => ?_
    have h : finAt v (finEmb K (2 + 2) u) ∈
      (if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) (2 + 2)) := hu v
    split_ifs at h
    · exact (hU v).2 h
    · exact h
  refine ⟨U, ρ, psi α β (fun a => ψ (C.Φ (2 + 2) a)) χ, c, hU, hρ, hρr, hcont, ?_, ?_, ?_, hc, ?_⟩
  · intro Y hY k hk
    obtain ⟨h₀, e₀⟩ := UpperTheory.unipotent_mem_maximalCompact_finite_integral Y hY
    obtain ⟨a, h, rfl⟩ := hdc k hk
    have e1 : nn Y * (arc1 a * fin1 (h : FA K (2 + 2))) = arc1 a * fin1 ((h₀ * h : AdelicGLn.integralFiniteGL K (2 + 2)) : FA K (2 + 2)) := by
      rw [e₀, Subgroup.coe_mul, fin1M, ← mul_assoc, ← mul_assoc, (cm a (h₀ : FA K (2 + 2))).eq]
    rw [e1, hat, hat, hχN h₀ h Y e₀.symm]
  · intro k hk
    obtain ⟨a₀, h, rfl⟩ := hdc k hk
    have e1 : ∀ a, psi α β (fun a => ψ (C.Φ (2 + 2) a)) χ (arc1 a₀ * fin1 (h : FA K (2 + 2)) * arc1 a) =
        ψ (C.Φ (2 + 2) (a₀ * a)) * χ h := by
      intro a
      rw [mul_assoc, ← (cm a (h : FA K (2 + 2))).eq, ← mul_assoc, ← arcM, hat]
    have hi : ∀ g : archCompact K (2 + 2) → ℂ, ∫ a, g a ∂C.κ₄ μ = ∫ m, g ((C.Φ (2 + 2)).symm m) ∂(Measure.pi fun _ : ι => μ) :=
      fun g => (C.Φ (2 + 2)).symm.toHomeomorph.measurableEmbedding.integral_map g
    have e2 : ∫ a, C.e e a * ψ (C.Φ (2 + 2) (a₀ * a)) ∂C.κ₄ μ = ψ (C.Φ (2 + 2) a₀) := by
      rw [hi]
      simp only [Co.e, map_mul, ContinuousMulEquiv.apply_symm_apply]
      exact hψfix _
    simp only [e1, ← mul_assoc]
    rw [integral_mul_const, e2, hat]
  · intro k hk u hu
    obtain ⟨a, h, rfl⟩ := hdc k hk
    have e1 : arc1 a * fin1 (h : FA K (2 + 2)) * fin1 u =
        arc1 a * fin1 ((h * ⟨u, hle hu⟩ : AdelicGLn.integralFiniteGL K (2 + 2)) : FA K (2 + 2)) := by
      rw [Subgroup.coe_mul, fin1M, mul_assoc]
    rw [e1, hat, hat, hχR h ⟨u, hle hu⟩ hu]
  · intro φ₁ φ₂ hφ₁ hφ₂ hA₁ hA₂ hF₁ hF₂ m₁ m₂
    have hΨ : ∀ a₁ a₂ (h : AdelicGLn.integralFiniteGL K (2 + 2)),
        psi α β (fun a => ψ (C.Φ (2 + 2) a)) χ (lv (arc1 a₁) (arc1 a₂) 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 (h : FA K (2 + 2))) =
          conj (C.p n q a₁) * conj (C.p n' q' a₂) * χ h := by
      intro a₁ a₂ h
      have e1 := hCo.2.2.2.2.2.2.2.2.2.1 (C.Φ 2 a₁) (C.Φ 2 a₂)
      simp only [ContinuousMulEquiv.symm_apply_apply] at e1
      rw [e1, ← arcM, hat]
      simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
      change ψ ((fun i => bd (C.Φ 2 a₁ i) (C.Φ 2 a₂ i)) * x) * χ h = _
      rw [hψval]
      rfl
    rw [value C.κ₂ ν ρ hρF _ hcont _ B hB χ (fun a => conj (C.p n q a)) (fun a => conj (C.p n' q' a))
      (Complex.continuous_conj.comp (pCont C n q)) hΨ X hX hXc _ _
      (fun d₁ d₂ h => hχL d₁ d₂ _ (hB d₁ d₂).symm h) φ₁ φ₂ hφ₁ hφ₂ hF₁ hF₂ m₁ m₂,
      fixInv C.κ₂ (κInv C) _ (pStar C n q) φ₁ hA₁, fixInv C.κ₂ (κInv C) _ (pStar C n' q') φ₂ hA₂, hXi]
    ring
