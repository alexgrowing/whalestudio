import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesRealAnalytic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsDerLowKSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IteratedDerivLine
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZeroStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightGapBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightEventuallyZeroStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeAnalyticStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.FormGap

open GlobalTheory.Dec.FormF GlobalTheory.Dec.PsiEig Filter Topology

variable {n : ℕ} {ε : Fin n → Bool}

local notation "Mt" => Matrix (Fin n) (Fin n) ℂ

section Local
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem locAn_conj {f : Mt → ℂ} (h : LocAn ε f) : LocAn ε (fun g => f (g.map star)) := by
  intro g hg
  obtain ⟨F, hF, he⟩ := h _ (UJ_star hg)
  let c : Mt →ₗ[ℝ] Mt :=
    { toFun := fun x => x.map star
      map_add' := fun x y => by ext i j; simp
      map_smul' := fun r x => by ext i j; simp }
  have hc : AnalyticAt ℝ (fun x : Mt => x.map star) g := (LinearMap.toContinuousLinearMap c).analyticAt g
  refine ⟨fun x => F (x.map star), hF.comp_of_eq hc rfl, ?_⟩
  filter_upwards [hc.continuousAt.eventually he] with z hz hzJ
  exact hz (UJ_star hzJ)

theorem locAn_line {f : Mt → ℂ} (h : LocAn ε f) {X : Mt} (hX : inG ε X) :
    AnalyticOnNhd ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) Set.univ := by
  intro t _
  obtain ⟨F, hF, he⟩ := h _ (exp_indefinite_unitary_holds n ε X hX t)
  have h1 := analyticAt_curveR 1 X t
  simp only [Matrix.one_mul] at h1
  refine (hF.comp_of_eq h1 rfl).congr ?_
  filter_upwards [h1.continuousAt.eventually he] with s hs
  exact (hs (exp_indefinite_unitary_holds n ε X hX s)).symm

theorem eab_local {f f' : Mt → ℂ} {g : Mt} (hg : inUJ ε g) (h : ∀ᶠ z in 𝓝 g, inUJ ε z → f z = f' z) (a b : Fin n) :
    Eab ε a b f g = Eab ε a b f' g := by
  have hR : ∀ X, inG ε X → Rd X f g = Rd X f' g := fun X hX => by
    have h1 := (analyticAt_curveR g X 0).continuousAt.tendsto
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h1
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [h1.eventually h] with t ht
    exact ht (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))
  have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  simp only [Eab, Ec, hR _ hc.1, hR _ hc.2.1]

end Local

theorem eab_const_mul (c : ℂ) (f : Mt → ℂ) (a b : Fin n) (g : Mt) :
    Eab ε a b (fun z => c * f z) g = c * Eab ε a b f g := by
  simp only [Eab, Ec, Rd, deriv_const_mul_field']
  ring

theorem eventually_UJ {p : Mt → Prop} (h : ∀ᶠ g : UJ ε in 𝓝 1, p (umat g)) :
    ∀ᶠ y in 𝓝 (1 : Mt), inUJ ε y → p y := by
  rw [(isClosedEmbeddingMatrix n ε).1.isEmbedding.isInducing.nhds_eq_comap, eventually_comap] at h
  filter_upwards [h] with y hy hyJ
  obtain ⟨a, rfl⟩ : y ∈ Set.range (fun g : UJ ε => toM g) := by
    rw [(isClosedEmbeddingMatrix n ε).2]; exact hyJ
  exact hy a rfl

theorem exists_gap {lam : Fin n → ℝ} (hlam : IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    ∃ g₀ : ℝ, (∀ a b : Fin n, a < b → ε a ≠ ε b → g₀ ≤ lam a - lam b) ∧ 2 * (n : ℝ) < g₀ := by
  by_cases hex : ∃ a b, ε a ≠ ε b
  · refine ⟨h, fun a b hab hne => ?_, ?_⟩
    · have := hgap a b hne
      rwa [abs_of_pos (sub_pos.2 (hlam.1 hab))] at this
    · obtain ⟨a, b, hab⟩ := hex
      have hn : (0 : ℝ) < n := by exact_mod_cast a.pos
      have hq : 1 ≤ rkR ε := by
        unfold rkR
        simp only [le_min_iff, Finset.one_le_card]
        cases ha : ε a <;> cases hb : ε b
        · simp [ha, hb] at hab
        · exact ⟨⟨b, by simp [hb]⟩, ⟨a, by simp [ha]⟩⟩
        · exact ⟨⟨a, by simp [ha]⟩, ⟨b, by simp [hb]⟩⟩
        · simp [ha, hb] at hab
      have : (1 : ℝ) ≤ ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.one_le_rpow (by exact_mod_cast hq) (by norm_num)
      nlinarith
  · exact ⟨2 * n + 1, fun a b _ hne => absurd ⟨a, b, hne⟩ hex, by linarith⟩

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {S : Submodule ℂ H} [S.HasOrthogonalProjection]

theorem proj_comm (hσ : IsURepOn (Kset ε) σ) (hS : IsKStableOn ε σ S) {k : Mt} (hk : k ∈ Kset ε) (x : H) :
    S.starProjection (σ k x) = σ k (S.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.starProjection_apply_mem x)) fun s hs => ?_
  rw [← map_sub, inner_rep_K hσ hk]
  exact Submodule.starProjection_inner_eq_zero x _ (hS _ (Kset_star ε hk) s hs)

theorem ps_entry {lam abelian₂ : Fin n → ℝ} {w : S} {τ : Mt → (S →L[ℂ] S)} (hτ : IsTau ε abelian₂ τ w)
    (hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v) {z : Mt} (hz : z.map star ∈ U1 ε) (x y : H) :
    ⟪S.orthogonalProjectionOnto y, ps ε lam τ w (z.map star) (S.orthogonalProjectionOnto x)⟫_ℂ = (Module.finrank ℂ S : ℂ) *
      ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
        (⟪y, σ (toMK k) (w : H)⟫_ℂ * ⟪σ (toMK k) (w : H), x⟫_ℂ) ∂(muK ε) := by
  rw [inner_ps lam hτ _ _ hz, intK, ← integral_const_mul]
  simp only [pk]
  rw [← muConj n ε (fun k => Phi lam (k⁻¹ * z.map star * k) * ((Module.finrank ℂ S : ℂ) *
    (⟪τ k w, S.orthogonalProjectionOnto x⟫_ℂ * ⟪S.orthogonalProjectionOnto y, τ k w⟫_ℂ)))]
  congr 1
  funext k
  have hk : toMK k ∈ Kset ε := k.2
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    hτσ _ (K_star hk), map_star_star, K_inv (K_star hk), map_star_ct, ← map_star_mul, ← map_star_mul, ← K_inv hk]
  ring

def diffOp (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Mt → (H →L[ℂ] H)) (τ : Mt → (S →L[ℂ] S)) (w : S) (z : Mt) :
    H →L[ℂ] H :=
  S.starProjection.comp (σ z) - S.subtypeL.comp ((Psi ε lam τ w (z.map star)).comp S.orthogonalProjectionOnto)

theorem diffOp_apply (lam : Fin n → ℝ) (τ : Mt → (S →L[ℂ] S)) (w : S) (z : Mt) (x : H) :
    diffOp ε lam σ τ w z x =
      S.starProjection (σ z x) - (Psi ε lam τ w (z.map star) (S.orthogonalProjectionOnto x) : S) := rfl

theorem inner_diffOp (lam : Fin n → ℝ) (τ : Mt → (S →L[ℂ] S)) (w : S) (x y : H) :
    (fun z => ⟪y, diffOp ε lam σ τ w z x⟫_ℂ) = fun z => ⟪S.starProjection y, σ z x⟫_ℂ +
      (-1) * ⟪S.orthogonalProjectionOnto y, Psi ε lam τ w (z.map star) (S.orthogonalProjectionOnto x)⟫_ℂ := by
  funext z
  rw [diffOp_apply, inner_sub_right, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_starProjection_left_eq_right]
  ring

theorem diffOp_equiv {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hσ : IsURepOn (UJset ε) σ) (hS : IsKStableOn ε σ S)
    {w : S} {τ : Mt → (S →L[ℂ] S)} (hτ : IsTau ε (lowK ε lam) τ w)
    (hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v) {g k₁ k₂ : Mt} (hg : g ∈ UJset ε)
    (h₁ : k₁ ∈ Kset ε) (h₂ : k₂ ∈ Kset ε) (x : H) :
    diffOp ε lam σ τ w (k₁ * g * k₂) x = σ k₁ (diffOp ε lam σ τ w g (σ k₂ x)) := by
  have e : τ (k₂.map star) (S.orthogonalProjectionOnto x) = S.orthogonalProjectionOnto (σ k₂ x) := by
    apply Subtype.ext
    rw [hτσ _ (K_star h₂), map_star_star]
    exact (proj_comm (URep_K hσ) hS h₂ x).symm
  rw [diffOp_apply, diffOp_apply, map_sub, ← proj_comm (URep_K hσ) hS h₁, map_star_mul, map_star_mul,
    (psiPolar n ε lam S τ w hlam hτ).2.2 _ (K_star h₁) _ (K_star h₂) _ (UJ_star hg),
    hσ.1.2 _ (indefinite_unitary_mul_mem ε (K_UJ h₁) hg) _ (K_UJ h₂), hσ.1.2 _ (K_UJ h₁) _ hg]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hτσ _ (K_star h₁), map_star_star, e]

theorem psi_near_one {lam : Fin n → ℝ} (hlam : IsHCParam lam) {w : S} {τ : Mt → (S →L[ℂ] S)}
    (hτ : IsTau ε (lowK ε lam) τ w) (hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v) :
    ∀ᶠ g : UJ ε in 𝓝 1, ∀ (a b : Fin n) (x y : H),
      Eab ε a b (fun z => ⟪S.orthogonalProjectionOnto y,
        Psi ε lam τ w (z.map star) (S.orthogonalProjectionOnto x)⟫_ℂ) (umat g) = (Module.finrank ℂ S : ℂ) *
      Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
        (⟪y, σ (toMK k) (w : H)⟫_ℂ * ⟪σ (toMK k) (w : H), x⟫_ℂ) ∂(muK ε)) (umat g) := by
  have h1 := eventually_UJ (p := fun z => z ∈ U1 ε ∧ Psi ε lam τ w z = ps ε lam τ w z) (psLocal n ε lam S τ w hlam hτ)
  have h2 : Tendsto (fun g : Mt => g.map star) (𝓝 1) (𝓝 1) := by
    have := (Continuous.matrix_map (continuous_id (X := Mt)) (continuous_star (R := ℂ))).tendsto 1
    simpa only [id, map_star_one] using this
  have h3 : Tendsto (fun g : UJ ε => umat g) (𝓝 1) (𝓝 1) := (isClosedEmbeddingMatrix n ε).1.continuous.tendsto 1
  filter_upwards [h3.eventually (h2.eventually h1).eventually_nhds] with g hg a b x y
  rw [← eab_const_mul]
  refine eab_local g.2 (hg.mono fun z hz hzJ => ?_) a b
  obtain ⟨hU, he⟩ := hz (UJ_star hzJ)
  rw [he, ps_entry hτ hτσ hU]

theorem formulaGap : StrictLow → FormulaGap := by
  intro hSL n ε lam H _ _ σ hlam hσ h hgap hh w hw X hX u hu v hv
  haveI := hσ.1
  have hU := hσ.2.2.1
  have hS := (hSL n ε lam hlam H σ hσ).1
  obtain ⟨V, E, hD, hSV⟩ := GlobalTheory.DerEx.exists_isDer_lowKSub n ε lam H σ hU hS
  have han := GlobalTheory.T.lowest_K_type_analytic n ε H σ V E lam hU hD hS hSV u hu X hX.1
  obtain ⟨hw1, hwS, hwt⟩ := hw
  generalize lowKSub ε lam σ = S at *
  haveI := hS.1
  haveI := FiniteDimensional.complete ℂ S
  obtain ⟨τ, hτ, hτσ⟩ := TauExt.tauExists n ε _ H σ S ⟨w, hwS⟩ (URep_K hU) hS hw1 hwt
  have hw0 : (⟨w, hSV hwS⟩ : V) ≠ 0 := fun h0 => by
    have : w = 0 := congrArg Subtype.val h0
    simp [this] at hw1
  obtain ⟨hK, hsp, hfd⟩ := (KType.kType_iff n ε H σ V E hU hD).2 _ S ⟨w, hSV hwS⟩ hS hSV hwS hw0 hwt
  obtain ⟨g₀, hg1, hg2⟩ := exists_gap hlam hgap hh
  have hA : ∀ x y : S, LocAn ε (fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ (z.map star) x⟫_ℂ) := fun x y =>
    locAn_conj (f := fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ z x⟫_ℂ) fun g hg => psiAnalytic n ε lam S τ _ hlam hτ y x g hg
  have hsm : ∀ (x : V) (y : H), SmoothOnG ε (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z x⟫_ℂ) := fun x y => by
    rw [inner_diffOp]
    exact Line.smooth_comb _ (hD.2.2.2 x _) (hA _ _).smooth
  have hjet := GlobalTheory.T.highest_weight_gap_bound n ε H σ V E lam g₀ ⟨w, hSV hwS⟩ hU hD hK hfd hg1 hg2
    (fun z => (diffOp ε lam σ τ ⟨w, hwS⟩ z : H →ₗ[ℂ] H)) ?_ ?_ ?_ ?_
  · rw [hsp] at hjet
    have h0 := Line.vanish_of_zero_jet n ε _ X (hsm ⟨u, hSV hu⟩ v) hX.1 (fun l => hjet l u hu v) (by
      intro t ht
      have e := inner_diffOp (ε := ε) (σ := σ) lam τ ⟨w, hwS⟩ u v
      simp only [congrFun e]
      exact (((innerSL ℂ (S.starProjection v)).restrictScalars ℝ).analyticAt _ |>.comp (han t ht)).add
        (analyticAt_const.mul (locAn_line (hA _ _) hX.1 t ht)))
    have hp := exp_posDef (P_star hX)
    have h1 := (psiPolar n ε lam S τ _ hlam hτ).1 1 (one_K ε) _ (P_star hX)
    rw [one_mul, hτ.2.1.1, ← exp_star] at h1
    rw [← exp_star] at hp
    have h2 := ps_entry (lam := lam) hτ hτσ (z := NormedSpace.exp X) (fun k hk => (phiPos n lam _ (by
      rw [K_inv hk]
      exact hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1))).1) u v
    rw [congrFun (inner_diffOp lam τ ⟨w, hwS⟩ u v), h1, Submodule.starProjection_eq_self_iff.2 hv, neg_one_mul,
      add_neg_eq_zero] at h0
    refine h0.trans (h2.trans ?_)
    congr 2
    funext k
    have hk : toMK k ∈ Kset ε := k.2
    have hpos : ((toMK k)⁻¹ * NormedSpace.exp X * toMK k).PosDef := by
      rw [K_inv hk]
      exact (exp_posDef hX).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1)
    rw [Phi_star, (phiPos n lam _ hpos).2.1.le.isSelfAdjoint.star_eq]
  · rw [hsp]
    exact fun g hg x _ => ⟨S.sub_mem (S.starProjection_apply_mem _) (Subtype.prop _),
      fun k₁ h₁ k₂ h₂ => diffOp_equiv hlam hU hS.2.1 hτ hτσ hg h₁ h₂ x⟩
  · rw [hsp]
    exact fun x hx y => hsm ⟨x, hSV hx⟩ y
  · intro G hG y
    filter_upwards [psi_near_one hlam hτ hτσ, GlobalTheory.T.highest_weight_eventually_zero n ε H σ V E lam _ hU hD hK hfd G hG y] with g h1 h2
    have h3 : ∀ a b, Eab ε a b (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z (at1 G a b : V)⟫_ℂ) (umat g) =
        ⟪S.starProjection y, σ (umat g) (E a b (at1 G a b) : V)⟫_ℂ + (-1) * ((Module.finrank ℂ S : ℂ) *
          Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
            (⟪y, σ (toMK k) w⟫_ℂ * ⟪σ (toMK k) w, (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g)) := fun a b => by
      rw [inner_diffOp, ← h1 a b (at1 G a b : V) y]
      refine (Line.word_comb (-1) (hD.2.2.2 _ _) (hA _ _).smooth [(a, b)] _ g.2).trans ?_
      rw [(Coef.coef_flow n ε H σ V E hU hD).1 _ _ _ _ g.2]
      rfl
    have h4 := congrArg (fun x : V => ⟪S.starProjection y, σ (umat g) x⟫_ℂ)
      (GlobalTheory.T.highest_weight_derivative_sum_zero n ε H σ V E lam _ hlam hσ hD hK hfd G hG)
    simp only [Submodule.coe_sum, map_sum, inner_sum, Submodule.coe_zero, map_zero, inner_zero_right] at h4
    simp only [ContinuousLinearMap.coe_coe, h3, Finset.sum_add_distrib, ← Finset.mul_sum, h2, h4]
    simp
  · rw [hsp]
    intro x hx
    change diffOp ε lam σ τ ⟨w, hwS⟩ 1 x = 0
    rw [diffOp_apply, map_star_one, (psiPolar n ε lam S τ _ hlam hτ).2.1, hU.1.1]
    exact sub_self _

end GlobalTheory.Jet.FormGap
