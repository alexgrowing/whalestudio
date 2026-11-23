import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlowInvSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHolomorphicTypeFamilyHolomorphicTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDomaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosedStatement
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.ZDecay

theorem eq_zero_of_le_div {x K T : ℝ} (hx : 0 ≤ x) (h : ∀ t : ℝ, T ≤ t → 0 ≤ t → x * (1 + t) ≤ K) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  have h1 := h (max (max T 0) (K / x)) ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))
  have h2 : K / x ≤ max (max T 0) (K / x) := le_max_right _ _
  have h3 : x * (K / x) = K := mul_div_cancel₀ _ hne
  nlinarith

theorem holFn_eq_zero {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n}
    {w : ι → Fin n → ℤ} (hx : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {e : ι → Fin n → ℂ}
    (he : ∀ τ, star (e τ) ⬝ᵥ (Hm τ).mulVec (e τ) = 0) {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f)
    (hinv : ∀ m : ι → Mt n, (∀ τ, InZe (Hm τ) (e τ) (m τ)) → ∀ u ∈ UG Hm, m * u ∈ UG Hm ∧ f (m * u) = f u)
    (hdec : ∀ k : ℕ, ∃ K : ℝ, ∀ u ∈ UG Hm, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ τ i, ‖((u τ)⁻¹.mulVec (e τ)) i‖ ≤ δ) →
      ‖f u‖ ≤ K * δ ^ k) :
    ∀ u ∈ UG Hm, f u = 0 := by
  intro u hu
  obtain ⟨P, hP, hfP⟩ := hf
  have hflow := GlobalTheory.HolDict.flowInv n ι Hm q x₀ w hx P e he hP (fun m hm v hv => by
    obtain ⟨h1, h2⟩ := hinv m hm v hv
    rw [hfP _ h1, hfP _ hv] at h2
    exact h2) u hu
  choose C A hCA using fun τ => GlobalTheory.HolDict.FlowGS.flowGS n (Hm τ) (q τ) (x₀ τ) (hx τ) (w τ) (e τ) (he τ) (u τ) (hu τ)
  have hC0 : ∀ τ, 0 ≤ C τ := fun τ => by
    obtain ⟨u', -, b, -, -, h, -⟩ := hCA τ 0 le_rfl
    have := (norm_nonneg _).trans h
    simpa using this
  obtain ⟨K, hK⟩ := hdec (2 * (∑ τ, A τ + 1))
  obtain ⟨-, -, hst, hbase⟩ := GlobalTheory.HolDict.frDoms_open_preconnected_stable n ι Hm q x₀ hx
  set C' : ℝ := ∑ τ, C τ + 1 with hC'
  have hCs : 0 ≤ ∑ τ, C τ := Finset.sum_nonneg fun τ _ => hC0 τ
  have hC'pos : 0 < C' := by linarith
  have hCle : ∀ τ, C τ ≤ C' := fun τ => by
    have := Finset.single_le_sum (f := C) (fun τ _ => hC0 τ) (Finset.mem_univ τ)
    linarith
  rw [← norm_eq_zero]
  refine eq_zero_of_le_div (K := (∏ τ, C τ) * K * C' ^ (∑ τ, A τ + 1)) (T := C') (norm_nonneg _) fun t hT ht => ?_
  choose u' hu' b hb hdecomp hchi hshort using fun τ => hCA τ t ht
  have ht1 : 0 < 1 + t := by linarith
  have hone : ∀ _ : ι, UpT (1 : Mt n) := fun _ => ⟨by simp, fun a c hc => Matrix.one_apply_ne hc.ne'⟩
  have hmem : (fun τ => (u' τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
    have := hst u' hu' (fun _ => 1) hone _ hbase
    simp only [Matrix.mul_one] at this
    exact this
  have h1 : f u = (∏ τ, ∏ a, b τ a a ^ w τ a) * f u' := by
    rw [hfP u hu, ← hflow t ht, hfP u' hu', ← hP.2 _ hmem b hb]
    congr 1
    funext τ
    exact hdecomp τ
  have hq : 0 < C' / (1 + t) := div_pos hC'pos ht1
  have h2 := hK u' hu' (Real.sqrt (C' / (1 + t))) (Real.sqrt_pos.2 hq)
    (Real.sqrt_le_one.2 ((div_le_one ht1).2 (by linarith))) fun τ i =>
      Real.le_sqrt_of_sq_le ((le_div_iff₀ ht1).2 ((hshort τ i).trans (hCle τ)))
  rw [pow_mul, Real.sq_sqrt hq.le] at h2
  have h3 : ‖∏ τ, ∏ a, b τ a a ^ w τ a‖ ≤ (∏ τ, C τ) * (1 + t) ^ (∑ τ, A τ) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun τ _ => norm_nonneg _) fun τ _ => hchi τ
  have h4 : ‖f u‖ ≤ (∏ τ, C τ) * (1 + t) ^ (∑ τ, A τ) * (K * (C' / (1 + t)) ^ (∑ τ, A τ + 1)) := by
    rw [h1, norm_mul]
    exact mul_le_mul h3 h2 (norm_nonneg _) ((norm_nonneg _).trans h3)
  refine (mul_le_mul_of_nonneg_right h4 ht1.le).trans_eq ?_
  rw [div_pow, pow_succ (1 + t)]
  field_simp

theorem setIntegral_translate {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (hc : ∀ a b : G, a * b = b * a) (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ) (hF : ∀ γ ∈ Γ, ∀ z, F (γ * z) = F z) (z₀ : G) :
    ∫ z in 𝓕, F (z₀ * z) ∂μ = ∫ z in 𝓕, F z ∂μ := by
  have : SMulCommClass G Γ G := ⟨fun a γ z => by
    change a * ((γ : G) * z) = γ * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  have h2 := h𝓕.smul_of_comm z₀
  rw [h𝓕.setIntegral_eq h2 fun γ z => hF γ γ.2 z]
  exact ((measurePreserving_mul_left μ z₀).setIntegral_image_emb (measurableEmbedding_mulLeft z₀) F 𝓕).symm

theorem iso_tau {D : D7} {V : HSp D} {ξ : Fin V.rank → D.host.E} (hξ : IsoVec V ξ) (τ : D.what₂.Tau) :
    star (fun i => tauE D τ (ξ i)) ⬝ᵥ (gramAt D V τ).mulVec (fun i => tauE D τ (ξ i)) = 0 := by
  have hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := fun x => by
    have := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x
  have h := congrArg (tauE D τ) hξ.2
  rw [map_zero] at h
  rw [← h]
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, gramAt, Matrix.map_apply, Pi.star_apply]

theorem zCusp_of_rapidDecay : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → ∀ φ : GA D V → ℂ, IsAutFun V φ → HolAd θ M w φ → GlobalTheory.CuspDecay.IsRapidDecay θ V φ → ZCusp V φ := by
  intro D θ V S M w hθ hM φ haut hhol hdec ξ hξ μ 𝓕 hμ h𝓕 g
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : BorelSpace (ZI V ξ) := Subtype.borelSpace (ZI V ξ : Set (GA D V))
  have : Countable ((GQ V).subgroupOf (ZI V ξ)) :=
    Function.Injective.countable (f := fun γ : (GQ V).subgroupOf (ZI V ξ) => (⟨γ.1.1, γ.2⟩ : GQ V))
      fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  obtain ⟨L, hL, hLmul, -, hUG, hLa, -, hsplit, hcomm, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨⟨ε, -⟩, -, -, hlift, -⟩ := GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hθ ξ hξ
  have hfin := ((GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ ξ hξ).2.1 μ 𝓕 hμ h𝓕).2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have hc : ∀ a b : ZI V ξ, a * b = b * a := fun a b => by
    obtain ⟨a, rfl⟩ := ε.surjective a
    obtain ⟨b, rfl⟩ := ε.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨a, ha, u, hu, rfl⟩ := hsplit g
  have hx : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hM).1
  obtain ⟨B, hB⟩ := hdec.bounded
  have hf : HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w
      fun v => ∫ z in 𝓕, φ ((z : GA D V) * a * L v) ∂μ := by
    refine GlobalTheory.T.integral_holomorphicTypeFamily_holomorphicType _ _ _ _ _ w hx (ZI V ξ) (μ.restrict 𝓕) (fun z v => φ ((z : GA D V) * a * L v)) B
      (fun z => ?_) (fun z v _ => hB _) fun v _ => ?_
    · obtain ⟨f, ⟨P, hP, hfP⟩, hφf⟩ := hhol ((z : GA D V) * a)
      refine ⟨P, hP, fun v hv => ?_⟩
      beta_reduce
      rw [hφf _ (hL v hv).1, ← hfP v hv]
      congr 1
      funext τ
      exact (hL v hv).2 τ
    · exact (haut.cont.comp ((continuous_subtype_val.mul continuous_const).mul continuous_const)).measurable.aestronglyMeasurable
  have key := holFn_eq_zero hx (iso_tau hξ) hf (fun m hm v hv => ?_) (fun k => ?_) _ (hUG u)
  · simp only [hLa u hu, mul_assoc] at key
    exact key
  · obtain ⟨z₀, hz₀, hz₁, hz₂⟩ := hlift m hm
    have hm' : m = fun τ => archM V (θ τ) z₀ := funext fun τ => (hz₂ τ).symm
    have hmU : m ∈ UG (gramAt D V) := hm' ▸ hUG z₀
    have hLm : L m = z₀ := by rw [hm']; exact hLa z₀ hz₁
    refine ⟨fun τ => GlobalTheory.PointAtPlaceHom.mul_mem_UH (hmU τ) (hv τ), ?_⟩
    rw [← setIntegral_translate hc _ μ h𝓕 (fun z => φ ((z : GA D V) * a * L v)) (fun γ hγ z => ?_) ⟨z₀, hz₀⟩]
    · refine integral_congr_ae (.of_forall fun z => ?_)
      have h1 := congrArg Subtype.val (hc ⟨z₀, hz₀⟩ z)
      simp only [Subgroup.coe_mul] at h1 ⊢
      rw [hLmul m hmU v hv, hLm, h1, mul_assoc (z : GA D V) z₀, ← hcomm a ha z₀ hz₁]
      simp only [mul_assoc]
    · simp only [Subgroup.coe_mul, mul_assoc]
      exact haut.left _ hγ _
  · obtain ⟨c, N, hc0, hh⟩ := GlobalTheory.T.quotientHeight_lower_bound_short_isotropic_vector D θ V hθ ξ hξ a ha
    obtain ⟨C, hC⟩ := hdec (N * k)
    refine ⟨C / c ^ k * (μ.restrict 𝓕).real Set.univ, fun v hv δ h0 h1 hs => ?_⟩
    rw [mul_right_comm]
    refine norm_integral_le_of_norm_le_const (.of_forall fun z => ?_)
    have h2 := hh z z.2 (L v) (hL v hv).1 δ h0 h1 fun τ i => by rw [(hL v hv).2 τ]; exact hs τ i
    have h3 := pow_le_pow_left₀ hc0.le h2 k
    rw [mul_pow, ← pow_mul] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc0 k)]
    calc _ ≤ ‖φ ((z : GA D V) * a * L v)‖ * (δ ^ k * _) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = (‖φ ((z : GA D V) * a * L v)‖ * _) * δ ^ k := by rw [mul_comm (δ ^ k), ← mul_assoc]
      _ ≤ C * δ ^ k := mul_le_mul_of_nonneg_right (hC _) (pow_nonneg h0.le _)

end GlobalTheory.HolDict.ZDecay

end
