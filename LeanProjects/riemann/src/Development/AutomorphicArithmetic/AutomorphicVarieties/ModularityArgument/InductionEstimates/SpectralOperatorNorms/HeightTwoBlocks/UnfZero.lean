import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.ExProb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.AbsMain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.HeightLv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Master
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

attribute [local instance 100000] MeasurableSpace.pi

variable {K : Type} [Field K] [NumberField K]

theorem finFd {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] : IsFiniteMeasure (fd μ) := by
  have h := (isFiniteMeasure_quotientMeasure (K := K) (n := n) μ).measure_univ_lt_top
  rw [quotientMeasure_univ μ (isFundamentalDomain_fundamentalDomain _ μ)] at h
  exact ⟨by rwa [Measure.restrict_apply_univ]⟩

private theorem finN : IsFiniteMeasure ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) := by
  obtain ⟨CN, hCN, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := 2 + 2) (r := 2)
  exact ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hsub).trans_lt hCN.measure_lt_top⟩

private theorem fixW (D : TypeDat K (2 + 2)) (Φ W : G1 K (2 + 2) → ℂ) (hΦ : Continuous Φ) (hfix : D.Fix Φ)
    (hW : ∀ g, W g = ∫ X in unipFundamentalDomain K (2 + 2) 2, Φ (nn X * g) ∂unipMeasure K (2 + 2) 2) : D.Fix W := by
  intro g
  obtain ⟨hU, hle, -⟩ := typeFin D
  haveI := D.prob
  haveI := finN (K := K)
  obtain ⟨CN, hCN, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := 2 + 2) (r := 2)
  have hnn := continuous_unipOne (K := K) (n := 2 + 2) 2
  have hH : Continuous fun z : G1 K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K]) => Φ (nn z.2 * z.1) :=
    hΦ.comp ((hnn.comp continuous_snd).mul continuous_fst)
  simp only [hW]
  refine fix_swap D.ν _ hU D.supp D.e D.cont _ _ hH (fun C hC => ?_) g fun X => ?_
  · obtain ⟨B, hB⟩ := (hC.prod hCN).exists_bound_of_continuousOn hH.continuousOn
    exact ⟨B, (ae_restrict_mem measurableSet_unipFundamentalDomain).mono fun y hy z hz => hB (z, y) ⟨hz, hsub hy⟩⟩
  · simpa only [mul_assoc] using hfix (nn X * g)

private theorem sfin {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] : SFinite ν := inferInstance

private theorem hsp (a b : G1 K 2) (t : ℝ) (g : G1 K (2 + 2)) : lv a b t * g = lv a b 0 * (lv 1 1 t * g) := by
  rw [← mul_assoc, blkLaws.2.1, mul_one, mul_one, zero_add]

private theorem pair0 [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)) {d : ℕ} (A : Line μ τ₁ τ₂ D d) (h₁ : CuspIrr μ₂ τ₁) (h₂ : CuspIrr μ₂ τ₂)
    (v : L2 μ) (Φ W : G1 K (2 + 2) → ℂ) (hΦ : Continuous Φ) (hΓ : ∀ γ ∈ Gam K (2 + 2), ∀ g, Φ (γ * g) = Φ g)
    (hrep : Reps μ v Φ) (hJ : ∀ u, ⟪A.J u, v⟫_ℂ = 0)
    (hW : ∀ g, W g = ∫ X in unipFundamentalDomain K (2 + 2) 2, Φ (nn X * g) ∂unipMeasure K (2 + 2) 2)
    (f : G1 K (2 + 2) → ℂ) (hsec : IsSec τ₁ τ₂ f) (hff : D.Fix f) (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] [IsFiniteMeasure κ]
    (β : ℝ → ℂ) (hβ : Continuous β) (hβc : HasCompactSupport β) :
    ∫ t, ∫ k : KG K (2 + 2), ∫ m : G1 K 2 × G1 K 2, conj (β t * Complex.exp ((2 * t : ℝ) : ℂ) * f (lv m.1 m.2 0 * k)) *
      W (lv m.1 m.2 0 * (lv 1 1 t * (k : G1 K (2 + 2)))) ∂(fd μ₂).prod (fd μ₂) ∂κ
        ∂(volume : Measure ℝ).withDensity (fun t => ENNReal.ofReal (Real.exp (-4 * t))) = 0 := by
  haveI := finFd μ₂
  haveI := finN (K := K)
  haveI := sfin (fd μ₂)
  haveI := sfin κ
  haveI := sfin ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))
  obtain ⟨⟨c, hc⟩, -⟩ := unf μ μ₂ κ
  obtain ⟨v₀, hv₀⟩ := (A.onto f).2 ⟨hsec, hff⟩
  have hS := secFun μ₂ τ₁ τ₂ D h₁ h₂ _ hsec hff
  obtain ⟨u, hu⟩ := (denseCc d).2.1 β v₀ hβ hβc
  obtain ⟨p1, p2, p3⟩ := bfFun _ β hS hβ hβc
  have hr := A.spec β v₀ u hβ hβc hu
  rw [hv₀] at hr
  obtain ⟨hi, he⟩ := (master μ μ₂ κ c hc _ p1.cont p1.rat p2 p3 (A.J u) v hr).2.2 Φ hΦ hΓ hrep
  rw [hJ u, eq_comm, mul_eq_zero, Complex.ofReal_eq_zero, or_iff_right hc.1.ne'] at he
  refine Eq.trans ?_ ((fub5 _ _ _ _ _ _ hi).symm.trans he)
  refine integral_congr_ae (ae_of_all _ fun t => integral_congr_ae (ae_of_all _ fun k => integral_congr_ae (ae_of_all _ fun m => ?_)))
  have e : ∀ X, bf β f (pt (m.1, m.2, t, k, X)) = β t * Complex.exp ((2 * t : ℝ) : ℂ) * f (lv m.1 m.2 0 * k) := by
    intro X
    have h1 : HP 2 2 (pt (m.1, m.2, t, k, X)) = t := by
      have := (hpSpec (K := K)).1 X m.1 m.2 t k
      rwa [((hpSpec (K := K)).2.1 _ k.2).1, add_zero] at this
    have h2 : f (pt (m.1, m.2, t, k, X)) = f (lv m.1 m.2 0 * k) := by
      show f (nn X * lv m.1 m.2 t * k) = _
      rw [mul_assoc, hS.unip, ← hS.ray t (lv m.1 m.2 0 * k), ← mul_assoc, blkLaws.2.1, one_mul, one_mul, add_zero]
    rw [bf, h1, h2]
    norm_num
  simp only [e, integral_const_mul]
  rw [hW, ← hsp]
  simp only [pt, mul_assoc]

theorem unfZero [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)) {d : ℕ} (A : Line μ τ₁ τ₂ D d) (h₁ : CuspIrr μ₂ τ₁) (h₂ : CuspIrr μ₂ τ₂)
    (v : L2 μ) (Φ W : G1 K (2 + 2) → ℂ) (φ₁ φ₂ : G1 K 2 → ℂ) (hΦ : Continuous Φ) (hΓ : ∀ γ ∈ Gam K (2 + 2), ∀ g, Φ (γ * g) = Φ g)
    (hrep : Reps μ v Φ)
    (hgr : ∃ (N : ℕ) (C : ℝ), ∀ g : G1 K (2 + 2), ‖Φ g‖ ≤ C * AutomorphicForm.height (g : AdelicGLn.AdelicGL K (2 + 2)) ^ N)
    (hfix : D.Fix Φ) (hJ : ∀ u, ⟪A.J u, v⟫_ℂ = 0)
    (hW : ∀ g, W g = ∫ X in unipFundamentalDomain K (2 + 2) 2, Φ (nn X * g) ∂unipMeasure K (2 + 2) 2)
    (hrat : ∀ γ₁ ∈ Gam K 2, ∀ γ₂ ∈ Gam K 2, ∀ g, W (lv γ₁ γ₂ 0 * g) = W g) (hun : ∀ X g, W (nn X * g) = W g)
    (r₁ : Rd τ₁ φ₁) (r₂ : Rd τ₂ φ₂) (t₀ : ℝ) (k₀ : G1 K (2 + 2)) (hk₀ : k₀ ∈ KG K (2 + 2)) :
    Integrable (fun m : G1 K 2 × G1 K 2 => conj (φ₁ m.1 * φ₂ m.2) * W (lv m.1 m.2 t₀ * k₀)) ((fd μ₂).prod (fd μ₂)) ∧
    ∫ m : G1 K 2 × G1 K 2, conj (φ₁ m.1 * φ₂ m.2) * W (lv m.1 m.2 t₀ * k₀) ∂(fd μ₂).prod (fd μ₂) = 0 := by
  obtain ⟨hWc, hbd⟩ := ctBd Φ W φ₁ φ₂ hΦ hgr hW hrat r₁.decay r₂.decay
  haveI := finFd μ₂
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 _).1
  have hmul := (blkLaws (K := K)).2.1
  have hlv := (blkLaws (K := K)).2.2.2.1
  have hlv0 : Continuous fun m : G1 K 2 × G1 K 2 => lv m.1 m.2 0 :=
    hlv.comp (f := fun m : G1 K 2 × G1 K 2 => (m.1, m.2, (0 : ℝ))) (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  have hlv1 : Continuous fun t : ℝ => lv (1 : G1 K 2) 1 t :=
    hlv.comp (f := fun t : ℝ => ((1 : G1 K 2), (1 : G1 K 2), t)) (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hF : Continuous fun m : G1 K 2 × G1 K 2 => φ₁ m.1 * φ₂ m.2 := (r₁.cont.comp continuous_fst).mul (r₂.cont.comp continuous_snd)
  have hb : ∀ C : Set (G1 K (2 + 2)), IsCompact C → ∃ B : ℝ, ∀ m : G1 K 2 × G1 K 2, ∀ g ∈ C,
      ‖φ₁ m.1 * φ₂ m.2‖ * ‖W (lv m.1 m.2 0 * g)‖ ≤ B := fun C hC => by
    obtain ⟨B, hB⟩ := hbd C hC
    exact ⟨B, fun m g hg => by rw [norm_mul]; exact hB m.1 m.2 g hg⟩
  haveI := D.prob
  obtain ⟨hIi, I, hI, hIc, hIf⟩ : (∀ g, Integrable (fun m : G1 K 2 × G1 K 2 => conj (φ₁ m.1 * φ₂ m.2) * W (lv m.1 m.2 0 * g))
      ((fd μ₂).prod (fd μ₂))) ∧ ∃ I : G1 K (2 + 2) → ℂ, (∀ g, I g =
      ∫ m : G1 K 2 × G1 K 2, conj (φ₁ m.1 * φ₂ m.2) * W (lv m.1 m.2 0 * g) ∂(fd μ₂).prod (fd μ₂)) ∧ Continuous I ∧ D.Fix I := by
    obtain ⟨a1, a2, a3⟩ := absI ((fd μ₂).prod (fd μ₂)) (fun m => lv m.1 m.2 0) hlv0 (fun m => φ₁ m.1 * φ₂ m.2) hF W hWc hb D.ν _
      (typeFin D).1 D.supp D.e D.cont (fixW D Φ W hΦ hfix hW)
    exact ⟨a1, _, fun _ => rfl, a2, a3⟩
  have e0 : (fun m : G1 K 2 × G1 K 2 => conj (φ₁ m.1 * φ₂ m.2) * W (lv m.1 m.2 t₀ * k₀)) =
      fun m => conj (φ₁ m.1 * φ₂ m.2) * W (lv m.1 m.2 0 * (lv 1 1 t₀ * k₀)) := funext fun m => by rw [hsp]
  rw [e0]
  refine ⟨hIi _, (hI _).symm.trans ?_⟩
  obtain ⟨U, _, lam, _, x, f, hUK, hx, hux, hsec, hff, hv⟩ := secEx μ₂ τ₁ τ₂ D h₁ h₂ φ₁ φ₂ r₁ r₂ (fun g => I (lv 1 1 t₀ * g))
    (hIc.comp (continuous_const_mul _)) fun g =>
      (integral_congr_ae (ae_of_all _ fun k => by simp only [mul_assoc])).trans (hIf (lv 1 1 t₀ * g))
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.1 hK
  obtain ⟨κ, _, _⟩ := ex_prob (KG K (2 + 2))
  refine absMain ((fd μ₂).prod (fd μ₂)) (KG K (2 + 2)) U hUK κ lam (fun m => lv m.1 m.2 0) hlv0 (fun t => lv 1 1 t) hlv1
    (fun m => φ₁ m.1 * φ₂ m.2) hF W hWc hb x hx (fun u m t k => ?_) I hI hIc (fun g y => ?_) t₀ f
    (fun m k => ?_) (pair0 μ μ₂ τ₁ τ₂ D A h₁ h₂ v Φ W hΦ hΓ hrep hJ hW f hsec hff κ) ⟨k₀, hk₀⟩
  · obtain ⟨X, hX⟩ := hux u
    obtain ⟨Y, hY⟩ := lv_nn m.1 m.2 t X
    have e : lv m.1 m.2 t * k = nn Y * (lv (m * x u).1 (m * x u).2 0 * (lv 1 1 t * ((u : G1 K (2 + 2))⁻¹ * k))) := by
      rw [← hsp, Prod.fst_mul, Prod.snd_mul, ← add_zero t, ← hmul, add_zero, ← mul_assoc, ← mul_assoc (nn Y), ← hY,
        mul_assoc _ (nn X), ← hX]
      group
    rw [← hsp, e, hun]
  · obtain ⟨B, hB⟩ := hb _ (isCompact_singleton (x := g))
    rw [hI]
    exact transl2 (Gam K 2) μ₂ (isFundamentalDomain_fundamentalDomain _ μ₂)
      (fun m => conj (φ₁ m.1 * φ₂ m.2) * W (lv m.1 m.2 0 * g))
      ((Complex.continuous_conj.comp hF).mul (hWc.comp (hlv0.mul continuous_const))) B
      (fun m => by rw [norm_mul, RCLike.norm_conj]; exact hB m g rfl)
      (fun γ₁ h1 γ₂ h2 a b => by
        simp only [r₁.rat _ h1, r₂.rat _ h2]
        rw [← hrat γ₁ h1 γ₂ h2 (lv a b 0 * _), ← mul_assoc (lv γ₁ γ₂ 0), hmul, add_zero]) y
  · have := hv 0 m.1 m.2 0 k k.2
    rwa [nn, unipOne_zero, one_mul] at this

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX
