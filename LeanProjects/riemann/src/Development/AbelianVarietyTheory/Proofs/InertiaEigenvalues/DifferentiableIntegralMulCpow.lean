import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumOneAddNormRpowNegLeEuclidean
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.ThetaPoisson GlobalTheory.ShortVecDecay
  GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped ComplexConjugate nonZeroDivisors ENNReal

namespace GlobalTheory.RSTheta

theorem exists_tsum_zpow_le {T s : ℝ} (hT : 1 < T) (hs : 0 < s) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ u : ℝ, 0 < u →
    ∑' n : ℤ, (if 1 ≤ T ^ n * u then ENNReal.ofReal ((T ^ n * u) ^ (-s)) else 0) ≤ B := by
  have hT0 : 0 < T := one_pos.trans hT
  have hq : T ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hT (by linarith)
  have hq0 : 0 ≤ T ^ (-s) := by positivity
  have hsum : Summable fun k : ℤ => (T ^ (-s)) ^ k.natAbs :=
    Summable.of_nat_of_neg (by simpa using summable_geometric_of_lt_one hq0 hq)
      (by simpa using summable_geometric_of_lt_one hq0 hq)
  refine ⟨∑' k : ℤ, ENNReal.ofReal ((T ^ (-s)) ^ k.natAbs), hsum.tsum_ofReal_ne_top, fun u hu => ?_⟩
  obtain ⟨m, h1, h2⟩ := exists_mem_Ico_zpow hu hT
  rw [← (Equiv.subRight m).tsum_eq]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [Equiv.subRight_apply]
  split_ifs with h
  · have h3 : T ^ (0 : ℤ) < T ^ (k + 1) := by
      rw [zpow_zero, show k + 1 = k - m + (m + 1) by ring, zpow_add₀ hT0.ne']
      exact h.trans_lt (mul_lt_mul_of_pos_left h2 (by positivity))
    have h4 : 0 ≤ k := by have := (zpow_lt_zpow_iff_right₀ hT).1 h3; omega
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le h4
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Int.natAbs_natCast, ← Real.rpow_mul_natCast hT0.le, mul_comm (-s), Real.rpow_natCast_mul hT0.le]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    rw [← zpow_natCast, show (j : ℤ) = j - m + m by ring, zpow_add₀ hT0.ne', add_sub_cancel_right]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · exact zero_le

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in
theorem continuous_absDet : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
  continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))

theorem absDet_zpow_mul (n : ℤ) (g : GA E a) :
    (ideleModule E (GeneralLinearGroup.det (splitCentre E a 1 ^ n * g)) : ℝ) =
      (Real.exp 1 ^ (a * Module.finrank ℚ E)) ^ n * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  have h := ideleModule_det_diagUnits_posIdele (K := E) (fun _ : Fin a => Real.exp n) fun _ => Real.exp_pos _
  rw [GlobalTheory.CuspBoundSiegel.diagUnits_posIdele a (Real.exp_pos _), Real.log_exp, splitCentre_intCast] at h
  rw [map_mul, map_mul, Positive.val_mul]
  congr 1
  refine h.trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← Real.exp_one_rpow n, Real.rpow_intCast,
    ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm n]

theorem integrableOn_absDet_rpow_neg (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (-s))
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ := by
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := absDet_zpow_mul
  have hm : MeasurableSet {g | 1 ≤ δ g} := (isClosed_le continuous_const hδc).measurableSet
  have hc : Continuous fun g => δ g ^ (-s) := hδc.rpow_const fun g => Or.inl (hδ0 g).ne'
  refine ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (.of_forall fun g => Real.rpow_nonneg (hδ0 g).le _)).2 ?_⟩
  rw [Set.inter_comm, ← Measure.restrict_restrict hm, ← lintegral_indicator hm]
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * splitCentre E a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * splitCentre E a 1 ^ n = ratGL E a γ' * splitCentre E a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hd := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hd]; exact measure_ne_top _ _
  rw [← GlobalTheory.ThetaUnfold.lintegral_unfold μ (latticeGL E a) (ratGL E a).range (fun n : ℤ => splitCentre E a 1 ^ n)
    (Equiv.ofBijective φ hφ) (fun _ => rfl) hd h𝓕 _
    (by rintro _ ⟨γ, rfl⟩ g; simp only [Set.indicator_apply, Set.mem_setOf_eq]; rw [show δ (ratGL E a γ * g) = δ g from hδr γ g])
    ((hc.measurable.ennreal_ofReal.indicator hm).aemeasurable)]
  obtain ⟨B, hB, h⟩ := exists_tsum_zpow_le hT1 hs
  refine (lintegral_mono (g := fun _ => B) fun g => ?_).trans_lt ?_
  · refine le_of_eq_of_le (tsum_congr fun n => ?_) (h _ (hδ0 g))
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [hδz]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hB.lt_top h1.lt_top

def IsSmallKernel (Ψ : GA E a → (Fin a → Ad E) → ℂ) : Prop :=
  (∃ L : Set (Fin a → Af E), IsCompact L ∧ ∀ g y, Ψ g y ≠ 0 → (fun i => pFin E (y i)) ∈ L) ∧
  ∀ L : Set (Fin a → Af E), IsCompact L → ∀ N M : ℕ, ∃ C : ℝ, ∀ g : GA E a, ∀ ξ : Fin a → E, ξ ≠ 0 →
    (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L → ∀ y : Fin a → Ad E,
      ‖Ψ g y‖ ≤ C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^
        (a * Module.finrank ℚ E) / (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N *
          (1 + ‖fun i => pInf E (y i)‖) ^ (-(M : ℝ))

theorem finrank_pi_Cinf : Module.finrank ℝ (Fin a → Cinf E) = a * Module.finrank ℚ E := by
  rw [(toMixedPi E a).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp only [mixedEmbedding.finrank, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem exists_le_norm (g : GA E a) {L : Set (Fin a → Af E)} (hL : IsCompact L) : ∃ δ : ℝ, 0 < δ ∧
    ∀ ξ : Fin a → E, ξ ≠ 0 → (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
      δ ≤ ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ := by
  obtain ⟨δ, hδ, h⟩ := exists_le_norm_vecMul (isCompact_singleton (x := g)) (isCompact_singleton (x := (1 : GA E a))) hL
  refine ⟨δ, hδ, fun ξ hξ hm => ?_⟩
  have := h g rfl 1 rfl (fun _ => 1) (fun _ => one_pos) 1 one_pos (fun _ => le_rfl) ξ hξ _ (by
    rw [GlobalTheory.CuspBoundSiegel.diagUnits_posIdele a one_pos, Real.log_one, splitCentre_zero, mul_one, mul_one]) hm
  rwa [mul_one] at this

theorem IsSmallKernel.tsum_le {Ψ : GA E a → (Fin a → Ad E) → ℂ} (hΨ : IsSmallKernel Ψ) {N : ℕ} (hN : 1 ≤ N) :
    ∃ C : ℝ, ∀ g : GA E a,
      Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖Ψ g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) ∧
      ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖Ψ g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ ≤
        C * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (-(N : ℝ)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · haveI : IsEmpty {ξ : Fin 0 → E // ξ ≠ 0} := ⟨fun ξ => ξ.2 (Subsingleton.elim _ _)⟩
    exact ⟨0, fun g => ⟨summable_empty, by simp⟩⟩
  obtain ⟨⟨L, hL, hsupp⟩, hb⟩ := hΨ
  obtain ⟨J, hJ⟩ := exists_subset_idealFiniteAdeles (isCompact_iUnion fun i : Fin a => hL.image (continuous_apply i))
  have hLJ : L ⊆ latt a J := fun z hz i => hJ (Set.mem_iUnion.2 ⟨i, z, hz, rfl⟩)
  set D := a * Module.finrank ℚ E with hD
  have hD1 : 1 ≤ D := Nat.mul_pos ha Module.finrank_pos
  obtain ⟨C, hC⟩ := hb _ (isCompact_latt J) N (D * N + D + 1)
  obtain ⟨K, hK, hlat⟩ := GlobalTheory.LatticeCount.tsum_one_add_norm_rpow_neg_le_regimes (V := Fin a → Cinf E)
    (by rwa [finrank_pi_Cinf]) (M := ((D * N + D + 1 : ℕ) : ℝ)) (by rw [finrank_pi_Cinf]; exact_mod_cast (by omega))
  rw [finrank_pi_Cinf, ← hD] at hlat
  refine ⟨|C| * 2 ^ (D * N) * K, fun g => ?_⟩
  set Δ : ℝ := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hΔ
  have hΔ0 : 0 < Δ := (ideleModule E _).2
  let T : (Fin a → E) →+ (Fin a → Ad E) :=
    { toFun := fun ξ => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val
      map_zero' := by simp only [Pi.zero_apply, map_zero]; exact zero_vecMul _
      map_add' := fun x y => by simp only [Pi.add_apply, map_add]; exact add_vecMul _ _ _ }
  let TI : (Fin a → E) →+ (Fin a → Cinf E) := ((pInf E).toAddMonoidHom.compLeft (Fin a)).comp T
  let TF : (Fin a → E) →+ (Fin a → Af E) := ((pFin E).toAddMonoidHom.compLeft (Fin a)).comp T
  let P : AddSubgroup (Fin a → E) := (AddSubgroup.pi Set.univ fun _ => idealFiniteAdeles J).comap TF
  have hP : ∀ ξ, ξ ∈ P ↔ TF ξ ∈ latt a J := fun ξ => ⟨fun h i => h i trivial, fun h i _ => h i⟩
  obtain ⟨δ, hδ, hδle⟩ := exists_le_norm g (isCompact_latt J)
  replace hδle : ∀ ξ ∈ P, ξ ≠ 0 → δ ≤ ‖TI ξ‖ := fun ξ h h0 => hδle ξ h0 ((hP ξ).1 h)
  change Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖Ψ g (T ξ.1)‖) ∧ ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖Ψ g (T ξ.1)‖ ≤ _
  have hsP : ∀ ξ, Ψ g (T ξ) ≠ 0 → ξ ∈ P := fun ξ h => (hP ξ).2 (hLJ (hsupp g _ h))
  set S : Set ℝ := (fun ξ => ‖TI ξ‖) '' {ξ | ξ ∈ P ∧ ξ ≠ 0} with hS
  rcases S.eq_empty_or_nonempty with hS0 | hS0
  · have : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖Ψ g (T ξ.1)‖ = 0 := fun ξ => by
      by_contra h
      exact Set.eq_empty_iff_forall_notMem.1 hS0 _ ⟨ξ.1, ⟨hsP _ (norm_ne_zero_iff.1 h), ξ.2⟩, rfl⟩
    simp only [this, tsum_zero]
    exact ⟨summable_zero, by positivity⟩
  have hr : 0 < sInf S := hδ.trans_le (le_csInf hS0 (by rintro _ ⟨ξ, hξ, rfl⟩; exact hδle ξ hξ.1 hξ.2))
  have hrle : ∀ ξ ∈ P, ξ ≠ 0 → sInf S ≤ ‖TI ξ‖ := fun ξ h h0 =>
    csInf_le ⟨0, by rintro _ ⟨ξ, -, rfl⟩; exact norm_nonneg _⟩ ⟨ξ, ⟨h, h0⟩, rfl⟩
  obtain ⟨_, ⟨ξ₀, hξ₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hS0 (show sInf S < 2 * sInf S by linarith)
  generalize sInf S = r at hr hrle hlt
  obtain ⟨hsum, hlo, hhi⟩ := hlat (P.map TI) r hr (by
    rintro _ ⟨ξ, hξ, rfl⟩ h0
    exact hrle ξ hξ fun e => h0 (by rw [e, map_zero]))
  set A : ℝ := |C| * ((2 * r) ^ D / Δ) ^ N with hA
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ y, ‖Ψ g y‖ ≤ A * (1 + ‖fun i => pInf E (y i)‖) ^ (-((D * N + D + 1 : ℕ) : ℝ)) := fun y => by
    refine (hC g ξ₀ hξ₀.2 ((hP _).1 hξ₀.1) y).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    refine mul_le_mul (le_abs_self C) ?_ (by positivity) (abs_nonneg C)
    have : ‖TI ξ₀‖ ^ D ≤ (2 * r) ^ D := pow_le_pow_left₀ (norm_nonneg _) hlt.le _
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right this hΔ0.le) _
  let j : {ξ // ξ ∈ P ∧ ξ ≠ 0} → {ξ : Fin a → E // ξ ≠ 0} := fun ξ => ⟨ξ.1, ξ.2.2⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (congrArg (fun z : {ξ : Fin a → E // ξ ≠ 0} => z.1) h)
  have hjs : ∀ ξ ∉ Set.range j, ‖Ψ g (T ξ.1)‖ = 0 := fun ξ h => by
    by_contra h'
    exact h ⟨⟨ξ.1, hsP _ (norm_ne_zero_iff.1 h'), ξ.2⟩, rfl⟩
  let ι : {ξ // ξ ∈ P ∧ ξ ≠ 0} → ((P.map TI : Set (Fin a → Cinf E)) \ {0} : Set (Fin a → Cinf E)) := fun ξ =>
    ⟨TI ξ.1, ⟨ξ.1, ξ.2.1, rfl⟩, norm_pos_iff.1 (hr.trans_le (hrle _ ξ.2.1 ξ.2.2))⟩
  have hι : Function.Injective ι := fun x y h => Subtype.ext (by
    by_contra hne
    have h1 := hrle _ (P.sub_mem x.2.1 y.2.1) (sub_ne_zero.2 hne)
    rw [map_sub, show TI x.1 = TI y.1 from congrArg Subtype.val h, sub_self, norm_zero] at h1
    exact h1.not_gt hr)
  have hs1 := (hsum.mul_left A).comp_injective hι
  have hs2 : Summable ((fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖Ψ g (T ξ.1)‖) ∘ j) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hterm (T ξ.1)) hs1
  refine ⟨(hj.summable_iff hjs).1 hs2, ?_⟩
  rw [← hj.tsum_eq (f := fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖Ψ g (T ξ.1)‖) fun ξ h => by_contra fun h' => h (hjs ξ h')]
  refine (Summable.tsum_le_tsum_of_inj ι hι (fun _ _ => by positivity) (fun ξ => hterm (T ξ.1)) hs2
    (hsum.mul_left A)).trans ?_
  rw [tsum_mul_left]
  have hAe : A = |C| * 2 ^ (D * N) * Δ ^ (-(N : ℝ)) * r ^ ((D * N : ℕ) : ℝ) := by
    rw [hA, Real.rpow_neg hΔ0.le, Real.rpow_natCast, Real.rpow_natCast, div_pow, ← pow_mul, mul_pow]
    ring
  have key : ∀ e : ℝ, r ^ (((D * N : ℕ) : ℝ) + e) ≤ 1 → A * (K * r ^ e) ≤ |C| * 2 ^ (D * N) * K * Δ ^ (-(N : ℝ)) := by
    intro e he
    calc A * (K * r ^ e) = |C| * 2 ^ (D * N) * K * Δ ^ (-(N : ℝ)) * r ^ (((D * N : ℕ) : ℝ) + e) := by
          rw [hAe, Real.rpow_add hr]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) he
  have hDN : (D : ℝ) ≤ ((D * N : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_of_pos_right D hN
  rcases le_total r 1 with h1 | h1
  · exact (mul_le_mul_of_nonneg_left (hlo h1) hA0).trans (key _ (Real.rpow_le_one hr.le h1 (by linarith)))
  · exact (mul_le_mul_of_nonneg_left (hhi h1) hA0).trans
      (key _ (Real.rpow_le_one_of_one_le_of_nonpos h1 (by push_cast; linarith)))

theorem differentiable_integral_mul_cpow {X : Type*} [MeasurableSpace X] {ν : Measure X} {Θ : X → ℂ} {δ : X → ℝ}
    (hΘ : AEStronglyMeasurable Θ ν) (hδ : Measurable δ) (h1 : ∀ᵐ g ∂ν, 1 ≤ δ g)
    (hi : ∀ x : ℝ, Integrable (fun g => ‖Θ g‖ * δ g ^ x) ν) :
    (∀ s : ℂ, Integrable (fun g => Θ g * (δ g : ℂ) ^ s) ν) ∧ Differentiable ℂ fun s : ℂ => ∫ g, Θ g * (δ g : ℂ) ^ s ∂ν := by
  have hδ' : Measurable fun g => (δ g : ℂ) := Complex.measurable_ofReal.comp hδ
  have hm : ∀ s : ℂ, AEStronglyMeasurable (fun g => Θ g * (δ g : ℂ) ^ s) ν := fun s =>
    hΘ.mul (hδ'.pow_const s).aestronglyMeasurable
  have hI : ∀ s : ℂ, Integrable (fun g => Θ g * (δ g : ℂ) ^ s) ν := fun s =>
    (hi s.re).mono' (hm s) (h1.mono fun g hg => by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (one_pos.trans_le hg)])
  refine ⟨hI, fun s₀ => ?_⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun s g => Θ g * (δ g : ℂ) ^ s)
    (F' := fun s g => Θ g * ((δ g : ℂ) ^ s * Complex.log (δ g))) (Metric.ball_mem_nhds s₀ one_pos) (.of_forall hm) (hI s₀)
    (hΘ.mul ((hδ'.pow_const s₀).mul hδ'.clog).aestronglyMeasurable) (h1.mono fun g hg s hs => ?_) (hi (s₀.re + 1 + 1))
    (h1.mono fun g hg s _ => ?_)).2.differentiableAt
  · have h0 := one_pos.trans_le hg
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h0, ← Complex.ofReal_log h0.le, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg hg), Real.rpow_add_one h0.ne']
    refine mul_le_mul_of_nonneg_left (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hg ?_) (Real.log_le_self h0.le)
      (Real.log_nonneg hg) (by positivity)) (norm_nonneg _)
    have := (Complex.re_le_norm (s - s₀)).trans (mem_ball_iff_norm.1 hs).le
    rw [Complex.sub_re] at this
    linarith
  · exact (Complex.hasStrictDerivAt_const_cpow (Or.inl (Complex.ofReal_ne_zero.2
      (one_pos.trans_le hg).ne'))).hasDerivAt.const_mul _

theorem IsSmallKernel.integrableOn {Ψ : GA E a → (Fin a → Ad E) → ℂ} (hΨ : IsSmallKernel Ψ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] {𝓕 : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    (hm : ∀ ξ : Fin a → E, ξ ≠ 0 →
      AEStronglyMeasurable (fun g : GA E a => Ψ g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) μ) :
    (∀ x : ℝ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖Ψ g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, Ψ g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    Differentiable ℂ fun s : ℂ => ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, Ψ g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have h1 : ∀ᵐ g ∂μ.restrict (𝓕 ∩ {g | 1 ≤ δ g}), 1 ≤ δ g :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
      (ae_restrict_mem (isClosed_le continuous_const hδc).measurableSet)
  have hpow : ∀ x : ℝ, AEStronglyMeasurable (fun g => δ g ^ x) (μ.restrict (𝓕 ∩ {g | 1 ≤ δ g})) := fun x =>
    (hδc.rpow_const fun g => Or.inl (hδ0 g).ne').aestronglyMeasurable
  have hI : ∀ x : ℝ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖Ψ g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) * δ g ^ x)
      (𝓕 ∩ {g | 1 ≤ δ g}) μ := by
    intro x
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · haveI : IsEmpty {ξ : Fin 0 → E // ξ ≠ 0} := ⟨fun ξ => ξ.2 (Subsingleton.elim _ _)⟩
      simp
    obtain ⟨C, hC⟩ := hΨ.tsum_le (N := ⌈x⌉₊ + 1) (by omega)
    have hΘ : AEStronglyMeasurable (fun g : GA E a =>
        ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖Ψ g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖)
        (μ.restrict (𝓕 ∩ {g | 1 ≤ δ g})) := AEStronglyMeasurable.tsum fun ξ => (hm ξ.1 ξ.2).norm.restrict
    refine ((integrableOn_absDet_rpow_neg ha μ h𝓕 (s := (⌈x⌉₊ + 1 : ℕ) - x)
      (by push_cast; linarith [Nat.le_ceil x])).const_mul C).mono'
      (hΘ.mul (hpow x)) (.of_forall fun g => ?_)
    have h0 := hδ0 g
    rw [Real.norm_of_nonneg (mul_nonneg (tsum_nonneg fun _ => norm_nonneg _) (by positivity)), neg_sub, sub_eq_neg_add,
      Real.rpow_add h0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC g).2 (by positivity)
  obtain ⟨C, hC⟩ := hΨ.tsum_le (N := 1) le_rfl
  have hΘ : AEStronglyMeasurable (fun g : GA E a =>
      ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, Ψ g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val))
      (μ.restrict (𝓕 ∩ {g | 1 ≤ δ g})) := AEStronglyMeasurable.tsum fun ξ => (hm ξ.1 ξ.2).restrict
  refine ⟨hI, differentiable_integral_mul_cpow hΘ hδc.measurable h1 fun x =>
    (hI x).mono' (hΘ.norm.mul (hpow x)) (.of_forall fun g => ?_)⟩
  have h0 := hδ0 g
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (hC g).1) (by positivity)

theorem isSmallKernel_rsPsi {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Decays φ) (h' : Decays φ')
    (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) (hs : tsupport Φ ⊆ rowSet E ℓ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) : IsSmallKernel (rsPsi ℓ φ φ' Φ J η) := by
  refine ⟨⟨(η + ·) '' latt a J, (isCompact_latt J).image (continuous_const_add η), fun g y hy =>
    ⟨_, by_contra fun hn => hy (by rw [rsPsi, thetaFn, Set.indicator_of_notMem hn, mul_zero]), add_sub_cancel _ _⟩⟩,
    fun L hL N M => ?_⟩
  have hK := hc.isCompact.image_of_continuousOn ((continuousOn_inv_rowGL ℓ).mono hs)
  obtain ⟨C, hC⟩ := h L hL _ hK N
  obtain ⟨C', hC'⟩ := h' L hL _ hK 0
  obtain ⟨B, hB⟩ := (show Continuous fun u => ‖Φ u‖ * (1 + ‖u‖) ^ M by fun_prop).bounded_above_of_compact_support
    hc.norm.mul_right
  refine ⟨|C| * |C'| * |B|, fun g ξ hξ hm y => ?_⟩
  have hΔ : 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) := (ideleModule E _).2
  have e : ‖rsPsi ℓ φ φ' Φ J η g y‖ ≤ ‖rsInf ℓ φ φ' Φ g fun i => pInf E (y i)‖ := by
    rw [rsPsi, thetaFn, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((norm_indicator_le_norm_self _ _).trans_eq norm_one)
  refine e.trans ?_
  generalize (fun i => pInf E (y i)) = u
  by_cases hu : u ∈ tsupport Φ
  · have h1 := (hC g _ ⟨u, hu, rfl⟩ ξ hξ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have h2 := (hC' g _ ⟨u, hu, rfl⟩ ξ hξ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))
    have h3 : ‖Φ u‖ ≤ |B| * (1 + ‖u‖) ^ (-(M : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      exact (le_abs_self _).trans ((hB u).trans (le_abs_self B))
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    refine (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)).trans_eq ?_
    ring
  · rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero, norm_zero]
    positivity

end GlobalTheory.RSTheta

end
