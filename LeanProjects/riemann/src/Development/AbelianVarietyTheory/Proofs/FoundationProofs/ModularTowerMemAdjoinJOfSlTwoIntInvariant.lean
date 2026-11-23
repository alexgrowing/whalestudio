import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariantStatement

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.KZ.LevelOneFrac

open Filter Topology Polynomial

theorem isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isConnected_Hs' : IsConnected Hs :=
  ⟨⟨Complex.I, by simp [Hs]⟩, (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected⟩

theorem eventually_nhdsNE {P : ℂ → Prop} (h : ∀ᶠ w in codiscreteWithin Hs, P w) {z : ℂ} (hz : z ∈ Hs) :
    ∀ᶠ w in 𝓝[≠] z, P w := by
  rw [Filter.Eventually, mem_codiscreteWithin] at h
  have h1 := Filter.disjoint_principal_right.1 (h z hz)
  have h2 : ∀ᶠ w in 𝓝[≠] z, w ∈ Hs := nhdsWithin_le_nhds (isOpen_Hs'.mem_nhds hz)
  filter_upwards [h1, h2] with w hw1 hw2
  by_contra hP
  exact hw1 ⟨hw2, hP⟩

theorem not_order_neg {h : ℂ → ℂ} {z : ℂ} (n : ℕ) (c : ℕ → ℂ → ℂ) (hc : ∀ i, ContinuousAt (c i) z)
    (hrel : ∀ᶠ w in 𝓝[≠] z, h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i = 0) :
    ¬ meromorphicOrderAt h z < 0 := by
  intro hneg
  have hinf := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  have hinv : Tendsto (fun w => (h w)⁻¹) (𝓝[≠] z) (𝓝 0) := tendsto_inv₀_cobounded.comp hinf
  have hne : ∀ᶠ w in 𝓝[≠] z, h w ≠ 0 := by
    have : ({0}ᶜ : Set ℂ) ∈ Bornology.cobounded ℂ := Bornology.isBounded_def.1 Bornology.isBounded_singleton
    exact hinf this
  have hF : Tendsto (fun w => 1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) (𝓝[≠] z)
      (𝓝 (1 + ∑ i ∈ Finset.range n, c i z * (0 : ℂ) ^ (n - i))) :=
    tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ =>
      ((hc i).tendsto.mono_left nhdsWithin_le_nhds).mul (hinv.pow _))
  have hlim : (1 + ∑ i ∈ Finset.range n, c i z * (0 : ℂ) ^ (n - i)) = 1 := by
    rw [add_eq_left]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : n - i ≠ 0 := by have := Finset.mem_range.1 hi; omega
    rw [zero_pow this, mul_zero]
  have hev : ∀ᶠ w in 𝓝[≠] z, (1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) = 0 := by
    filter_upwards [hrel, hne] with w hw hw0
    have hp : h w ^ n ≠ 0 := pow_ne_zero _ hw0
    have e : (1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) * h w ^ n =
        h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i := by
      rw [add_mul, one_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := (Finset.mem_range.1 hi).le
      have e2 : h w ^ n = h w ^ (n - i) * h w ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
      rw [e2, inv_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hw0)]
    rw [hw] at e
    exact (mul_eq_zero.1 e).resolve_right hp
  have h1 := tendsto_nhds_unique hF (tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm))
  rw [hlim] at h1
  exact one_ne_zero h1

theorem exists_differentiableOn {h : ℂ → ℂ} (hm : MeromorphicOn h Hs) (n : ℕ) (c : ℕ → ℂ → ℂ)
    (hc : ∀ i, DifferentiableOn ℂ (c i) Hs)
    (hrel : ∀ᶠ w in codiscreteWithin Hs, h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i = 0) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ h =ᶠ[codiscreteWithin Hs] φ := by
  refine ⟨toMeromorphicNFOn h Hs, ?_, toMeromorphicNFOn_eqOn_codiscrete hm⟩
  intro z hz
  have hNF : MeromorphicNFAt (toMeromorphicNFOn h Hs) z := meromorphicNFOn_toMeromorphicNFOn h Hs hz
  rcases meromorphicNFAt_iff_analyticAt_or.1 hNF with ha | ⟨-, hneg, -⟩
  · exact ha.differentiableAt.differentiableWithinAt
  · rw [meromorphicOrderAt_toMeromorphicNFOn hm hz] at hneg
    exact absurd hneg (not_order_neg n c
      (fun i => (hc i).continuousOn.continuousAt (isOpen_Hs'.mem_nhds hz)) (eventually_nhdsNE hrel hz))

end GlobalTheory.KZ.LevelOneFrac

namespace GlobalTheory.KZ.LevelOneFrac

open Filter Topology Polynomial

theorem germ_differentiableOn (G : Mero) (a b : ℂ → ℂ) (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (hb0 : (b : Mero) ≠ 0) (hab : G * (b : Mero) = (a : Mero)) (p : Mero[X]) (hp : p.Monic)
    (hc : ∀ i, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ p.coeff i = (φ : Mero)) (he : p.eval G = 0) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ G = (φ : Mero) := by
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs'
  have hB : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs'
  have hx : ∃ x ∈ Hs, b x ≠ 0 := by
    by_contra h
    push Not at h
    apply hb0
    rw [← Filter.Germ.coe_zero]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  obtain ⟨x, hxH, hx0⟩ := hx
  have hne : b ⁻¹' {0}ᶜ ∈ codiscreteWithin Hs :=
    hB.preimage_zero_mem_codiscreteWithin hx0 hxH isConnected_Hs'
  have h1 : ((b * b⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [← Filter.Germ.coe_one]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [hne] with z hz
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact mul_inv_cancel₀ hz
  have hG : G = ((a / b : ℂ → ℂ) : Mero) := by
    calc G = G * ((b * b⁻¹ : ℂ → ℂ) : Mero) := by rw [h1, mul_one]
      _ = (G * (b : Mero)) * ((b⁻¹ : ℂ → ℂ) : Mero) := by rw [Filter.Germ.coe_mul, mul_assoc]
      _ = ((a / b : ℂ → ℂ) : Mero) := by rw [hab, ← Filter.Germ.coe_mul, div_eq_mul_inv]
  have hM : MeromorphicOn (a / b) Hs := fun z hz => (hA z hz).meromorphicAt.div (hB z hz).meromorphicAt
  choose c hcd hce using hc
  set n := p.natDegree
  set g : ℂ → ℂ := a / b
  have key : ((fun w => g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i : ℂ → ℂ) : Mero) = 0 := by
    have e1 : ((fun w => g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i : ℂ → ℂ) : Mero) =
        Filter.Germ.coeRingHom _ (g ^ n + ∑ i ∈ Finset.range n, c i * g ^ i) := by
      congr 1
      ext w
      simp [Finset.sum_apply]
    rw [e1, map_add, map_pow, map_sum]
    simp_rw [map_mul, map_pow]
    change (g : Mero) ^ n + ∑ i ∈ Finset.range n, (c i : Mero) * (g : Mero) ^ i = 0
    rw [← hG]
    simp_rw [← hce]
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at he
    rw [add_comm]
    exact he
  have hrel : ∀ᶠ w in codiscreteWithin Hs, g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i = 0 := by
    have := Filter.Germ.coe_eq.1 (key.trans Filter.Germ.coe_zero.symm)
    filter_upwards [this] with w hw using hw
  obtain ⟨φ, hφ, hgφ⟩ := exists_differentiableOn hM n c hcd hrel
  exact ⟨φ, hφ, hG.trans (Filter.Germ.coe_eq.2 hgφ)⟩

end GlobalTheory.KZ.LevelOneFrac

namespace GlobalTheory.KZ.LevelOneFrac

open Filter Topology Polynomial

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem holRep (X : Tower Ω ε) (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) {r : X.K}
    (hr : r ∈ Algebra.adjoin Ω {X.jK}) : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an r = (φ : Mero) := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hj
  | algebraMap c => exact ⟨fun _ => ε c, differentiableOn_const _, X.an_c c⟩
  | add x y _ _ hx hy =>
    obtain ⟨φ, h1, h2⟩ := hx
    obtain ⟨ψ, h3, h4⟩ := hy
    exact ⟨φ + ψ, h1.add h3, by rw [map_add, h2, h4, Filter.Germ.coe_add]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨φ, h1, h2⟩ := hx
    obtain ⟨ψ, h3, h4⟩ := hy
    exact ⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩

theorem sl_eq_of_mem (X : Tower Ω ε) {r : X.K} (hr : r ∈ Algebra.adjoin Ω {X.jK}) (γ : SL(2, ℤ)) :
    X.sl (ofSL γ) r = r := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact X.j_inv γ
  | algebraMap c => exact (X.sl (ofSL γ)).commutes c
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem exists_denom (X : Tower Ω ε) {c : X.K} (hc : c ∈ IntermediateField.adjoin Ω {X.jK}) :
    ∃ d ∈ Algebra.adjoin Ω {X.jK}, d ≠ 0 ∧ d * c ∈ Algebra.adjoin Ω {X.jK} := by
  obtain ⟨r, hr, s, hs, rfl⟩ := (IntermediateField.mem_adjoin_iff_div (x := c)).1 hc
  by_cases h : s = 0
  · refine ⟨1, Subalgebra.one_mem _, one_ne_zero, ?_⟩
    rw [h, div_zero, mul_zero]
    exact Subalgebra.zero_mem _
  · refine ⟨s, hs, h, ?_⟩
    rwa [mul_div_cancel₀ r h]

theorem exists_denom_finset (X : Tower Ω ε) (s : Finset X.K) (hs : ∀ c ∈ s, c ∈ IntermediateField.adjoin Ω {X.jK}) :
    ∃ d ∈ Algebra.adjoin Ω {X.jK}, d ≠ 0 ∧ ∀ c ∈ s, d * c ∈ Algebra.adjoin Ω {X.jK} := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Subalgebra.one_mem _, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨d, hd, hd0, hds⟩ := ih (fun c hc => hs c (Finset.mem_insert_of_mem hc))
    obtain ⟨e, he, he0, hea⟩ := exists_denom X (hs a (Finset.mem_insert_self a s))
    refine ⟨e * d, Subalgebra.mul_mem _ he hd, mul_ne_zero he0 hd0, fun c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    · rw [mul_comm e d, mul_assoc]
      exact Subalgebra.mul_mem _ hd hea
    · rw [mul_assoc]
      exact Subalgebra.mul_mem _ he (hds c hc)

theorem isAlgebraic_adjoin (X : Tower Ω ε) (f : X.K) : IsAlgebraic (Algebra.adjoin Ω {X.jK}) f := by
  classical
  obtain ⟨p, hp0, hpf⟩ := X.alg_j f
  obtain ⟨d, hd, hd0, hds⟩ := exists_denom_finset X (p.support.image (fun i => (p.coeff i : X.K)))
    (by
      intro c hc
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
      exact (p.coeff i).2)
  let P : X.K[X] := C d * p.map (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K)
  have hlift : P ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {X.jK}) X.K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ p.support
    · refine ⟨⟨_, hds _ (Finset.mem_image_of_mem _ hn)⟩, ?_⟩
      simp [P, coeff_C_mul]
    · have h0 : p.coeff n = 0 := Polynomial.notMem_support_iff.1 hn
      refine ⟨0, ?_⟩
      simp [P, coeff_C_mul, h0]
  obtain ⟨q, hq⟩ := hlift
  rw [Polynomial.coe_mapRingHom] at hq
  refine ⟨q, ?_, ?_⟩
  · rintro rfl
    rw [Polynomial.map_zero] at hq
    have h2 := hq.symm
    simp only [P, mul_eq_zero, Polynomial.C_eq_zero, Polynomial.map_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact hd0 h2
    · exact hp0 h2
  · rw [aeval_def, eval₂_eq_eval_map, hq]
    simp only [P, eval_mul, eval_C, eval_map, ← aeval_def, hpf, mul_zero]

theorem mem_adjoin_of_sl_inv : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ f : X.K,
    (∀ γ : SL(2, ℤ), X.sl (ofSL γ) f = f) → f ∈ IntermediateField.adjoin Ω {X.jK} := by
  intro Ω _ _ _ ε X hj f hf
  obtain ⟨y, hy0, hyi⟩ := (isAlgebraic_adjoin X f).exists_integral_multiple
  set g : X.K := (y : X.K) * f with hgdef
  have hyf : y • f = g := rfl
  rw [hyf] at hyi
  have hginv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) g = g := fun γ => by
    rw [hgdef, map_mul, sl_eq_of_mem X y.2 γ, hf γ]
  obtain ⟨p, hpm, hpe⟩ := hyi
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero g
  obtain ⟨φ, hφ, hgφ⟩ := germ_differentiableOn (X.an g) a b ha hb hb0 hab
    (p.map (X.an.comp (algebraMap (Algebra.adjoin Ω {X.jK}) X.K))) (hpm.map _)
    (fun i => by rw [coeff_map]; exact holRep X hj (p.coeff i).2)
    (by rw [eval_map, ← Polynomial.hom_eval₂, hpe, map_zero])
  have hgR : g ∈ Algebra.adjoin Ω {X.jK} := GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε X ε.injective hj g hginv ⟨φ, hφ, hgφ⟩
  have hle := IntermediateField.algebra_adjoin_le_adjoin Ω ({X.jK} : Set X.K)
  have hyL : (y : X.K) ∈ IntermediateField.adjoin Ω {X.jK} := hle y.2
  have hgL : g ∈ IntermediateField.adjoin Ω {X.jK} := hle hgR
  have hy0' : (y : X.K) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hfe : f = g / y := by rw [hgdef, mul_div_cancel_left₀ _ hy0']
  rw [hfe]
  exact div_mem hgL hyL

end GlobalTheory.KZ.LevelOneFrac
