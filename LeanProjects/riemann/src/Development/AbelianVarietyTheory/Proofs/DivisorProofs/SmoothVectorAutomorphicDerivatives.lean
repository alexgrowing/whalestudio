import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegrableRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSobolevInequalityAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentativeParametricIntegralContinuousFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRepresentativeAverageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedAverageApproxOfSubgroupFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvaluationExtensionClosureRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumIntegralCubeDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlongCurveProductsStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainL2BoundStatement

noncomputable section

namespace GlobalTheory.SmoothRep

section General

open MeasureTheory GlobalTheory.LocRep
open scoped ContDiff Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ι : K → G → ℂ}
  {ρ : G →* (K →L[ℂ] K)}

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [μ.IsHaarMeasure] [CompleteSpace K] in
theorem rep_tr [μ.IsMulRightInvariant] (htr : ∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g)) {v : K} {φ : G → ℂ}
    (h : ι v =ᵐ[μ] φ) (g : G) : ι (ρ g v) =ᵐ[μ] fun x => φ (x * g) :=
  (htr g v).trans ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h)

theorem hasDerivAt_rep [μ.IsMulRightInvariant]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x)
    (hρ : ∀ v, Continuous fun g => ρ g v) (htr : ∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g))
    {c : ℝ → G} (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ a b, c (a + b) = c a * c b) {v v' : K} {φ φ' : G → ℂ}
    (hd : HasDerivAt (fun t : ℝ => ρ (c t) v) v' 0) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hv : ι v =ᵐ[μ] φ) (hv' : ι v' =ᵐ[μ] φ') (x : G) : HasDerivAt (fun t : ℝ => φ (x * c t)) (φ' x) 0 := by
  have hd' : ∀ t, HasDerivAt (fun t : ℝ => ρ (c t) v) (ρ (c t) v') t := fun t => by
    have h1 : HasDerivAt (fun r : ℝ => ρ (c (r - t)) v) v' t := by
      have h2 : HasDerivAt (fun t : ℝ => ρ (c t) v) v' (t - t) := by rwa [sub_self]
      exact h2.comp_sub_const t t
    have h2 := ((ρ (c t)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    convert h2 using 1
    · funext r
      show _ = (ρ (c t) * ρ (c (r - t))) v
      rw [← map_mul, ← hadd, add_sub_cancel]
    · rfl
  have hw : Continuous fun t => ρ (c t) v' := (hρ v').comp hc
  have key : ∀ a b : ℝ, a ≤ b → ∀ y, φ (y * c b) - φ (y * c a) = ∫ t in a..b, φ' (y * c t) := fun a b hab => by
    obtain ⟨p1, p2⟩ := GlobalTheory.T.representative_parametric_integral_continuous_family G μ K ι hloc hlin ℝ volume (Set.Icc a b) (fun t => ρ (c t) v')
      (fun t y => φ' (y * c t)) isCompact_Icc hw (hφ'.comp (continuous_snd.mul (hc.comp continuous_fst)))
      fun t => rep_tr htr hv' _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd' t) (hw.intervalIntegrable _ _)] at p2
    have e : (fun y => φ (y * c b) - φ (y * c a)) = fun y => ∫ t in Set.Icc a b, φ' (y * c t) := by
      refine (Continuous.ae_eq_iff_eq μ (by fun_prop) p1).1 ?_
      filter_upwards [p2, rep_sub hlin (ρ (c b) v) (ρ (c a) v), rep_tr htr hv (c a), rep_tr htr hv (c b)]
        with y e1 e2 e3 e4
      rw [← e1, e2, e3, e4]
    intro y
    rw [congrFun e y, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have e : (fun t : ℝ => φ (x * c t)) = fun t => φ x + ∫ r in (0 : ℝ)..t, φ' (x * c r) := by
    funext t
    rcases le_total 0 t with h | h
    · rw [← key 0 t h x, h0, mul_one]; ring
    · rw [intervalIntegral.integral_symm, ← key t 0 h x, h0, mul_one]; ring
  rw [e]
  have hcc : Continuous fun r => φ' (x * c r) := by fun_prop
  simpa [h0] using (intervalIntegral.integral_hasDerivAt_right (hcc.intervalIntegrable 0 0)
    (hcc.stronglyMeasurableAtFilter _ _) hcc.continuousAt).const_add (φ x)

theorem exists_eval [μ.IsMulRightInvariant]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hρ : ∀ v, Continuous fun g => ρ g v) (htr : ∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g))
    {H U : Subgroup G} (hU : IsOpen (U : Set G)) (hH : ∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H)
    {N : ℕ} {Θ : (Fin N → ℝ) → G} (hΘ : Continuous Θ) {Q : Set (Fin N → ℝ)} (hQ : IsCompact Q) {Ω : Set G}
    (hΩ : IsCompact Ω) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ f : G → ℝ, Continuous f → (∀ g, 0 ≤ f g) → (∀ k ∈ H, ∀ g, f (g * k) = f g) →
      ∫ t in Q, f (Θ t) ≤ C * ∫ x in Ω, f x ∂μ)
    {κ : (Fin N → ℝ) → ℂ} (hκ : Continuous κ) :
    ∃ Λ : G → (K →L[ℂ] ℂ), ∀ v, (∀ k ∈ H, ρ k v = v) →
      (Continuous fun x => Λ x v) ∧ ι (∫ t in Q, κ t • ρ (Θ t) v) =ᵐ[μ] fun x => Λ x v := by
  have hw : ∀ v, Continuous fun t => κ t • ρ (Θ t) v := fun v => hκ.smul ((hρ v).comp hΘ)
  have hi : ∀ v, IntegrableOn (fun t => κ t • ρ (Θ t) v) Q := fun v => (hw v).continuousOn.integrableOn_compact hQ
  let A₀ : K →ₗ[ℂ] K :=
    { toFun := fun v => ∫ t in Q, κ t • ρ (Θ t) v
      map_add' := fun v w => by
        simp only [map_add, smul_add]
        exact integral_add (hi v) (hi w)
      map_smul' := fun a v => by
        simp only [map_smul, RingHom.id_apply, ← integral_smul]
        simp only [smul_comm a] }
  let A : K →L[ℂ] K := A₀.mkContinuous (∫ t in Q, ‖κ t‖) fun v => by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [norm_smul, hiso, integral_mul_const]
  let E : Submodule ℂ K :=
    { carrier := {v | (∀ k ∈ H, ρ k v = v) ∧ ∃ φ : G → ℂ, Continuous φ ∧ ι v =ᵐ[μ] φ}
      zero_mem' := ⟨fun k _ => map_zero _, fun _ => 0, continuous_const, rep_zero hlin⟩
      add_mem' := fun {v w} ⟨a1, φ, a2, a3⟩ ⟨b1, ψ, b2, b3⟩ => ⟨fun k hk => by rw [map_add, a1 k hk, b1 k hk],
        fun x => φ x + ψ x, a2.add b2, by
          filter_upwards [rep_add hlin v w, a3, b3] with x e1 e2 e3
          rw [e1, e2, e3]⟩
      smul_mem' := fun a v ⟨a1, φ, a2, a3⟩ => ⟨fun k hk => by rw [map_smul, a1 k hk],
        fun x => a * φ x, continuous_const.mul a2, by
          filter_upwards [rep_smul hlin a v, a3] with x e1 e2
          rw [e1, e2]⟩ }
  have hA : ∀ v (φ : G → ℂ), Continuous φ → ι v =ᵐ[μ] φ → (Continuous fun x => ∫ t in Q, κ t * φ (x * Θ t)) ∧
      ι (A v) =ᵐ[μ] fun x => ∫ t in Q, κ t * φ (x * Θ t) := fun v φ hφ hv =>
    GlobalTheory.T.representative_parametric_integral_continuous_family G μ K ι hloc hlin _ volume Q (fun t => κ t • ρ (Θ t) v) (fun t x => κ t * φ (x * Θ t)) hQ (hw v)
      ((hκ.comp continuous_fst).mul (hφ.comp (continuous_snd.mul (hΘ.comp continuous_fst)))) fun t => by
        filter_upwards [rep_smul hlin (κ t) (ρ (Θ t) v), rep_tr htr hv (Θ t)] with x e1 e2
        rw [e1, e2]
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.exists_evaluation_extension_closure_representatives G μ K ι hloc hlin A E (fun v ⟨_, φ, a2, a3⟩ => ⟨_, hA v φ a2 a3⟩) fun B hB => by
    obtain ⟨M, hM'⟩ := hloc (B * Ω) (hB.mul hΩ)
    obtain ⟨κ₀, hκ₀⟩ := hQ.exists_bound_of_continuousOn hκ.continuousOn
    refine ⟨max κ₀ 0 * (C * M), fun v ⟨a1, φ, a2, a3⟩ ψ hψ hv x hx => ?_⟩
    have e : ψ = _ := (hψ.ae_eq_iff_eq μ (hA v φ a2 a3).1).1 (hv.symm.trans (hA v φ a2 a3).2)
    have hk : ∀ k ∈ H, ∀ g, φ (g * k) = φ g := fun k hk => by
      have h1 := rep_tr htr a3 k
      rw [a1 k hk] at h1
      exact congrFun ((Continuous.ae_eq_iff_eq μ (by fun_prop) a2).1 (h1.symm.trans a3))
    have h1 := hM (fun g => ‖φ (x * g)‖) (by fun_prop) (fun g => norm_nonneg _) fun k hk' g => by
      simp only [← mul_assoc, hk k hk']
    have h2 : ∫ y in Ω, ‖φ (x * y)‖ ∂μ ≤ M * ‖v‖ := by
      refine le_trans ?_ (hM' v).2
      have h3 : ∫ y in B * Ω, ‖ι v y‖ ∂μ = ∫ y in B * Ω, ‖φ y‖ ∂μ :=
        integral_congr_ae (ae_restrict_of_ae (by filter_upwards [a3] with y hy; rw [hy]))
      have h4 := (measurePreserving_mul_left μ x).setIntegral_image_emb (measurableEmbedding_mulLeft x)
        (fun y => ‖φ y‖) Ω
      rw [h3, ← h4]
      refine setIntegral_mono_set (a2.norm.continuousOn.integrableOn_compact (hB.mul hΩ))
        (Filter.Eventually.of_forall fun y => norm_nonneg _) (LE.le.eventuallyLE ?_)
      rintro _ ⟨y, hy, rfl⟩
      exact Set.mul_mem_mul hx hy
    rw [e]
    calc ‖∫ t in Q, κ t * φ (x * Θ t)‖ ≤ ∫ t in Q, max κ₀ 0 * ‖φ (x * Θ t)‖ := by
          refine norm_integral_le_of_norm_le (Continuous.continuousOn (by fun_prop) |>.integrableOn_compact hQ) ?_
          filter_upwards [ae_restrict_mem hQ.measurableSet] with t ht
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right ((hκ₀ t ht).trans (le_max_left _ _)) (norm_nonneg _)
      _ ≤ max κ₀ 0 * (C * M) * ‖v‖ := by
          rw [integral_const_mul, mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hC)) (le_max_right _ _)
  refine ⟨Λ, fun v hv => hΛ v (Metric.mem_closure_iff.2 fun ε hε => ?_)⟩
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_fixed_average_approx_of_subgroup_fixed G μ K ρ hiso hρ H U hU hH v hv ε hε
  exact ⟨_, ⟨e3, GlobalTheory.T.exists_continuous_representative_average G μ K ι hloc hlin ρ hiso hρ htr η v e1 e2⟩, by rwa [dist_eq_norm]⟩

def Sm (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) (v : K) : Prop :=
  ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace K] in
theorem Sm.hasDerivAt {P : Type} {A : Set P} {e : P → ℝ → G} {v : K} (h : Sm ρ A e v) {p : P} (hp : p ∈ A) :
    HasDerivAt (fun r : ℝ => ρ (e p r) v) (deriv (fun r : ℝ => ρ (e p r) v) 0) 0 := by
  have h1 := (h 1 (fun _ => p) fun _ => hp).comp (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun r : ℝ => fun _ : Fin 1 => r)
  have h2 : ContDiff ℝ ∞ fun r : ℝ => ρ (e p r) v := by simpa [Function.comp_def] using h1
  exact (h2.differentiable (by simp) 0).hasDerivAt

theorem exists_smooth_rep [μ.IsMulRightInvariant]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hρ : ∀ v, Continuous fun g => ρ g v) (htr : ∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g))
    {H U : Subgroup G} (hU : IsOpen (U : Set G)) (hH : ∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H)
    {P : Type} {A : Set P} {e : P → ℝ → G}
    (he : ∀ p ∈ A, Continuous (e p) ∧ e p 0 = 1 ∧ ∀ a b, e p (a + b) = e p a * e p b)
    (hcomm : ∀ p t, ∀ k ∈ H, e p t * k = k * e p t)
    {N : ℕ} {qs : Fin N → P} (hq : ∀ i, qs i ∈ A) {s : ℝ} (hs : 0 < s)
    (hΘ : Continuous fun t : Fin N → ℝ => (List.ofFn fun i => e (qs i) (t i)).prod) {Ω : Set G}
    (hΩ : IsCompact Ω) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ f : G → ℝ, Continuous f → (∀ g, 0 ≤ f g) → (∀ k ∈ H, ∀ g, f (g * k) = f g) →
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), f (List.ofFn fun i => e (qs i) (t i)).prod ≤
        C * ∫ x in Ω, f x ∂μ) :
    ∃ R : K → G → ℂ, ∀ v, Sm ρ A e v → (∀ k ∈ H, ρ k v = v) → Continuous (R v) ∧ ι v =ᵐ[μ] R v ∧
      (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => R v (g * (List.ofFn fun i => e (ps i) (t i)).prod)) ∧
      ∀ p ∈ A, Sm ρ A e (deriv (fun r : ℝ => ρ (e p r) v) 0) ∧
        (∀ k ∈ H, ρ k (deriv (fun r : ℝ => ρ (e p r) v) 0) = deriv (fun r : ℝ => ρ (e p r) v) 0) ∧
        ∀ x, HasDerivAt (fun t : ℝ => R v (x * e p t)) (R (deriv (fun r : ℝ => ρ (e p r) v) 0) x) 0 := by
  obtain ⟨J, _, κ, l, hκ, hT⟩ := GlobalTheory.T.eq_sum_integral_cube_derivatives_alt G K ρ hiso hρ s hs N (fun i => e (qs i)) fun i => he _ (hq i)
  choose Λ hΛ using fun j => exists_eval hloc hlin hiso hρ htr hU hH hΘ
    (isCompact_univ_pi fun _ => isCompact_Icc) hΩ hC hM (hκ j)
  let d : P → K → K := fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0
  let S : Set K := {v | Sm ρ A e v ∧ ∀ k ∈ H, ρ k v = v}
  have hS : ∀ v ∈ S, ∀ p ∈ A, d p v ∈ S := fun v hv p hp => by
    refine ⟨(GlobalTheory.T.smooth_along_curve_products_stable_alt G K ρ P A e v hv.1).1 p hp, fun k hk => ?_⟩
    have h1 := hv.1.hasDerivAt hp
    have h2 := ((ρ k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
    refine HasDerivAt.unique (f := fun r : ℝ => ρ (e p r) v) (x := 0) ?_ h1
    convert h2 using 1
    · funext r
      show _ = (ρ k * ρ (e p r)) v
      rw [← map_mul, ← hcomm p r k hk, map_mul, mul_apply_eq_comp, hv.2 k hk]
    · rfl
  have hSl : ∀ v ∈ S, ∀ m : List (Fin N), m.foldr (fun i => d (qs i)) v ∈ S := fun v hv m => by
    induction m with
    | nil => exact hv
    | cons i m ih => exact hS _ ih _ (hq i)
  let R : K → G → ℂ := fun v x => ∑ j, Λ j x ((l j).foldr (fun i => d (qs i)) v)
  have hR : ∀ v ∈ S, Continuous (R v) ∧ ι v =ᵐ[μ] R v := fun v hv => by
    refine ⟨continuous_finsetSum _ fun j _ => (hΛ j _ (hSl v hv _).2).1, ?_⟩
    have h1 := hT (fun i => d (qs i)) S (fun w hw i => ⟨hS w hw _ (hq i), hw.1.hasDerivAt (hq i)⟩) v hv
    have h2 := rep_sum hlin Finset.univ fun j => ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
      κ j t • ρ (List.ofFn fun i => e (qs i) (t i)).prod ((l j).foldr (fun i => d (qs i)) v)
    rw [← h1] at h2
    filter_upwards [h2, ae_all_iff.2 fun j => (hΛ j _ (hSl v hv (l j)).2).2] with x e1 e2
    rw [e1]
    exact Finset.sum_congr rfl fun j _ => e2 j
  refine ⟨R, fun v h1 h2 => ⟨(hR v ⟨h1, h2⟩).1, (hR v ⟨h1, h2⟩).2, fun k ps hps g => ?_, fun p hp =>
    ⟨(hS v ⟨h1, h2⟩ p hp).1, (hS v ⟨h1, h2⟩ p hp).2, hasDerivAt_rep hloc hlin hρ htr (he p hp).1 (he p hp).2.1
      (he p hp).2.2 (h1.hasDerivAt hp) (hR v ⟨h1, h2⟩).1 (hR _ (hS v ⟨h1, h2⟩ p hp)).1 (hR v ⟨h1, h2⟩).2
      (hR _ (hS v ⟨h1, h2⟩ p hp)).2⟩⟩⟩
  obtain ⟨-, s2, s3⟩ := GlobalTheory.T.smooth_along_curve_products_stable_alt G K ρ P A e v h1
  have e1 : ∀ t : Fin k → ℝ, R v (g * (List.ofFn fun i => e (ps i) (t i)).prod) =
      R (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) g := fun t => by
    have hm : ρ (List.ofFn fun i => e (ps i) (t i)).prod v ∈ S := by
      refine ⟨s2 k ps t hps, fun a ha => ?_⟩
      have hc : Commute a (List.ofFn fun i => e (ps i) (t i)).prod :=
        Commute.list_prod_right _ _ (List.forall_mem_ofFn_iff.2 fun i => (hcomm _ _ a ha).symm)
      show (ρ a * ρ _) v = _
      rw [← map_mul, hc.eq, map_mul, mul_apply_eq_comp, h2 a ha]
    have hc := (hR v ⟨h1, h2⟩).1
    exact congrFun ((Continuous.ae_eq_iff_eq μ (by fun_prop) (hR _ hm).1).1
      ((rep_tr htr (hR v ⟨h1, h2⟩).2 _).symm.trans (hR _ hm).2)) g
  simp only [e1]
  refine ContDiff.sum fun j _ => ((Λ j g).restrictScalars ℝ).contDiff.comp ?_
  have h3 := s3 ((l j).map qs) (fun p hp => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
    exact hq i) k ps hps
  simpa only [List.foldr_map] using h3

theorem foldr_rel {P X Y : Type} {A : P → Prop} {S : X → Prop} {d : P → X → X} {d' : P → Y → Y} {R : X → Y}
    (h : ∀ w, S w → ∀ p, A p → S (d p w) ∧ d' p (R w) = R (d p w)) {v : X} (hv : S v) (l : List P)
    (hl : ∀ p ∈ l, A p) : S (l.foldr d v) ∧ l.foldr d' (R v) = R (l.foldr d v) := by
  induction l with
  | nil => exact ⟨hv, rfl⟩
  | cons p l ih =>
    obtain ⟨i1, i2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [List.foldr_cons, List.foldr_cons, i2]
    exact h _ i1 p (hl p List.mem_cons_self)

end General

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem exists_smooth_repr : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ F, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → ∃ ψ, Repr V μ 𝓕 F ψ ∧ IsAutFun V ψ ∧ (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ∧ ∀ l : List (D.what₂.Tau × Mt V.rank), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → Continuous (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) ∧ Repr V μ 𝓕 (l.foldr (dL2 θ V ρ) F) (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) := by
  intro D θ V hθ μ 𝓕 ρ hp hr U hU F hF hFU
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := hp.haar
  have := hp.right
  obtain ⟨N, τs, Xs, s, S, K, W, hX, hs, hK, hW, h⟩ := GlobalTheory.SobLoc.exists_adelic_chart hθ V U hU
  obtain ⟨-, -, -, -, -, -, -, -, -, hH⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨B, hB, hBW, hBc⟩ := local_compact_nhds hW
  have hc := fun i => GlobalTheory.SobLoc.oneP_spec hθ V (hH (τs i)).2 (hX i)
  have hΘ := GlobalTheory.continuous_prod_ofFn_curves N (fun i => oneP θ V (τs i) (Xs i)) fun i => (hc i).1
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.T.le_mul_setIntegral_image2_of_forall_le_alt (GA D V) μ N _ (Metric.closedBall 0 S) B (K ^ N) hΘ
    (isCompact_closedBall _ _) hBc hB (pow_nonneg hK _)
  have hΩ : IsCompact (Set.image2 (fun (t : Fin N → ℝ) b => (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * b)
      (Metric.closedBall 0 S) B) := by
    rw [← Set.image_prod]
    exact ((isCompact_closedBall _ _).prod hBc).image ((hΘ.comp continuous_fst).mul continuous_snd)
  obtain ⟨-, huniq, -, -, hlin, -⟩ := GlobalTheory.HolDict.RepresentativeL2.repr_properties D V μ 𝓕 ρ hp hr
  obtain ⟨R, hR⟩ := exists_smooth_rep (μ := μ) (ι := fun (F : Lp ℂ 2 (nuQ V μ 𝓕)) x => F (autMk V x)) (ρ := ρ)
    (H := U ⊓ GfC V) (U := U) (A := {p : D.what₂.Tau × Mt V.rank | p.2 ∈ lieAt V p.1})
    (e := fun p => oneP θ V p.1 p.2) (qs := fun i => (τs i, Xs i))
    (fun C hC => by
      obtain ⟨m, hm⟩ := GlobalTheory.T.ncard_rationalPoints_translatedCompact_le_pow D θ V hθ C hC
      obtain ⟨c, hc⟩ := hm 1
      refine GlobalTheory.T.fundamental_domain_L2_bound (GA D V) μ (GQ V) 𝓕 hp.fd C hC (c * normInf θ V 1 ^ m) fun y => ?_
      simpa using hc 1 (one_mem _) y)
    (fun a v w => hlin v w _ _ a (Filter.Eventually.of_forall fun _ => rfl) (Filter.Eventually.of_forall fun _ => rfl))
    hr.iso hr.cont hr.val hU
    (fun y hy k hk => ⟨U.mul_mem (U.mul_mem (U.inv_mem hy) hk.1) hy,
      (MonoidHom.normal_ker (infHom V)).conj_mem' k hk.2 y⟩)
    (fun p hp => GlobalTheory.SobLoc.oneP_spec hθ V (hH p.1).2 hp)
    (fun p t k hk => GlobalTheory.PointAtPlaceHom.comm_of_mem V (GlobalTheory.PointAtPlaceHom.atTau_mem V _ _) hk.2)
    hX hs hΘ hΩ hC₁
    (fun f hf hf0 hfk => h₁ f _ hf hf0 fun x hx => by
      obtain ⟨φ, a, haU, ha, hφ, hφ'⟩ := h x (hBW hx)
      refine GlobalTheory.T.setIntegral_le_pow_mul_setIntegral_of_expanding N _ _ K φ (fun t => f (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)
        (fun t => f ((List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * x))
        (isCompact_univ_pi fun _ => isCompact_Icc) (isCompact_closedBall _ _) hK
        (hf.comp hΘ) (hf.comp (hΘ.mul continuous_const)) (fun g => hf0 _) (fun g => hf0 _)
        (fun t ht => ⟨mem_closedBall_zero_iff.2 (hφ t ht).1, le_of_eq ?_⟩) hφ'
      rw [(hφ t ht).2, hfk a ⟨haU, ha⟩])
  have hF' : Sm ρ {p : D.what₂.Tau × Mt V.rank | p.2 ∈ lieAt V p.1} (fun p => oneP θ V p.1 p.2) F :=
    fun k ps hps => hF k (fun i => (ps i).1) (fun i => (ps i).2) hps
  have hFU' : ∀ k ∈ U ⊓ GfC V, ρ k F = F := fun k hk => hFU k hk.1 hk.2
  obtain ⟨r1, r2, r3, -⟩ := hR F hF' hFU'
  have hR' : ∀ w, Sm ρ {p : D.what₂.Tau × Mt V.rank | p.2 ∈ lieAt V p.1} (fun p => oneP θ V p.1 p.2) w →
      (∀ k ∈ U ⊓ GfC V, ρ k w = w) → ∀ p : D.what₂.Tau × Mt V.rank, p.2 ∈ lieAt V p.1 →
      Sm ρ {p : D.what₂.Tau × Mt V.rank | p.2 ∈ lieAt V p.1} (fun p => oneP θ V p.1 p.2) (dL2 θ V ρ p w) ∧
      (∀ k ∈ U ⊓ GfC V, ρ k (dL2 θ V ρ p w) = dL2 θ V ρ p w) ∧ Rder θ V p.1 p.2 (R w) = R (dL2 θ V ρ p w) := by
    intro w i1 i2 p hp
    obtain ⟨j1, j2, j3⟩ := (hR w i1 i2).2.2.2 p hp
    unfold dL2 Rder
    refine ⟨?_, ?_, ?_⟩
    · convert j1
    · convert j2
    · funext x
      convert (j3 x).deriv
  have hw := foldr_rel (A := fun p : D.what₂.Tau × Mt V.rank => p.2 ∈ lieAt V p.1)
    (S := fun w => Sm ρ {p : D.what₂.Tau × Mt V.rank | p.2 ∈ lieAt V p.1} (fun p => oneP θ V p.1 p.2) w ∧
      ∀ k ∈ U ⊓ GfC V, ρ k w = w) (d := dL2 θ V ρ) (d' := fun p f => Rder θ V p.1 p.2 f) (R := R)
    (fun w i p hp => and_assoc.2 (hR' w i.1 i.2 p hp)) ⟨hF', hFU'⟩
  refine ⟨R F, r2, ⟨fun γ hγ g => ?_, ⟨U, hU, fun k hk hk' g => ?_⟩, r1⟩,
    fun k τs Xs hX g => r3 k (fun i => (τs i, Xs i)) hX g, fun l hl => ?_⟩
  · refine congrFun (huniq F (fun x => R F (γ * x)) (R F) (by fun_prop) r1 ?_ r2) g
    filter_upwards [(measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae r2] with x hx
    rw [← hx]
    congr 1
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simpa using hγ
  · refine congrFun (huniq F (fun x => R F (x * k)) (R F) (by fun_prop) r1 ?_ r2) g
    filter_upwards [(measurePreserving_mul_right μ k).quasiMeasurePreserving.ae r2, hr.val k F] with x hx hx'
    rw [← hx, ← hx', hFU k hk hk']
  · obtain ⟨⟨i1, i2⟩, i3⟩ := hw l hl
    rw [i3]
    exact ⟨(hR _ i1 i2).1, (hR _ i1 i2).2.1⟩

end GlobalTheory.SmoothRep
