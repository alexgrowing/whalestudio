import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPropertiesResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerResidueFieldFinitePowerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSequenceNormBoundsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCompatibleSequenceApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerFixedPointApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerDividesFrobeniusDifferenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCharacterEqResidueLiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerResidueCongruenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFieldEmbeddingsDifferFrobeniusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGaloisExtensionOfEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTeichmullerSequenceCompatibilityStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem frob_pow_read {l : ℕ} [Fact l.Prime] (N : ℕ) (a y : Tl l) (b : ℕ → Tl l) (D : ℕ) :
    (a - ∑ i ∈ Finset.range D, b i * y ^ i) ^ l ^ N =
      a ^ l ^ N - ∑ i ∈ Finset.range D, b i ^ l ^ N * (y ^ l ^ N) ^ i := by
  rw [sub_pow_char_pow, sum_pow_char_pow]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i]

theorem oc_eq {l : ℕ} [Fact l.Prime] (K : FinExt l) (c : ↥(OL K)) : oc K c = omC (((c : ↥K.1) : Om l)) := rfl

theorem sys_pow_iter {l : ℕ} [Fact l.Prime] {f : ℕ} {u : ℕ → Tl l} (h : ∀ n, u (n + 1) ^ l ^ f = u n)
    (n m : ℕ) : u (n + m) ^ l ^ (f * m) = u n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : u (n + (m + 1)) ^ l ^ (f * (m + 1)) = (u (n + m + 1) ^ l ^ f) ^ l ^ (f * m) := by
      rw [← pow_mul, ← pow_add, ← add_assoc]
      congr 2
      ring
    rw [e, h, ih]

theorem fix_ringHom {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖) (h1 : ‖oc K π‖ < 1)
    (hfer : ∀ c : ↥(OL K), ‖oc K c ^ l ^ f - oc K c‖ ≤ ‖oc K π‖) :
    ∃ r₀ : ↥(OL K) →+* Tl l, (∀ c, r₀ c ^ l ^ f = r₀ c) ∧ ∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖ := by
  have hex : ∀ c : ↥(OL K), ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - oc K c‖ ≤ ‖oc K π‖ := fun c =>
    GlobalTheory.T.teichmuller_fixed_point_approximation f _ hf hl h1 (oc K c) (norm_oc_le_one K c) (hfer c)
  choose F hF1 hF2 using hex
  have huniq : ∀ (x : Tl l) (A : ↥(OL K)), x ^ l ^ f = x → ‖sh x - oc K A‖ ≤ ‖oc K π‖ → F A = x := by
    intro x A hx hA
    apply fixed_unique hf (hF1 A) hx
    refine lt_of_le_of_lt (norm_sub_le_of_near hl ?_) h1
    have e : sh (F A) - sh x = (sh (F A) - oc K A) - (sh x - oc K A) := by ring
    rw [e]
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF2 A) (by rw [norm_neg]; exact hA))
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hF1, hF2⟩
  · exact huniq 1 1 (one_pow _) (by rw [map_one, sh_one, sub_self, norm_zero]; exact norm_nonneg _)
  · intro a b
    refine huniq _ _ (by rw [mul_pow, hF1, hF1]) ?_
    rw [map_mul]
    exact near_mul (norm_oc_le_one K b) (hF2 a) (hF2 b)
  · exact huniq 0 0 (zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
      (by rw [map_zero, sh_zero, sub_self, norm_zero]; exact norm_nonneg _)
  · intro a b
    refine huniq _ _ (by rw [add_pow_char_pow, hF1, hF1]) ?_
    rw [map_add]
    exact near_add hl (hF2 a) (hF2 b)

theorem tch_eq {l : ℕ} [Fact l.Prime] (f : ℕ) (hf : 0 < f) (x : Tl l) (hx : x ^ l ^ f = x) (y : Om l)
    (hy : sh x = omC y) : tch l x = rB l y := by
  have hq2 : 2 ≤ l ^ f := by
    have := Nat.pow_le_pow_right (Fact.out : l.Prime).pos hf
    have h2 := (Fact.out : l.Prime).two_le
    simp only [pow_one] at this
    omega
  have hyf : y ^ l ^ f = y := by
    apply omC.injective
    rw [map_pow, ← hy, ← sh_pow, hx]
  exact GlobalTheory.T.teichmuller_character_eq_residue_lift (l ^ f) hq2 (dvd_pow_self l hf.ne') x y hx hyf hy

theorem exp_twist {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f) (hqf : qOf π = l ^ f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖) (h1 : ‖oc K π‖ < 1) (hπ0 : π ≠ 0)
    (hmax : (Ideal.span {π}).IsMaximal) (hfin : Finite (↥(OL K) ⧸ Ideal.span {π}))
    (r₀ : ↥(OL K) →+* Tl l) (hr1 : ∀ c, r₀ c ^ l ^ f = r₀ c) (hr2 : ∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖)
    (hrπ : r₀ π = 0) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) :
    ∃ i : ℕ, ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1)) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_extension_of_embedding K μ
  haveI := hmax
  haveI := hfin
  letI : Field (↥(OL K) ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have hker : ∀ a ∈ Ideal.span {π}, r₀ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hrπ, mul_zero]
  let α : (↥(OL K) ⧸ Ideal.span {π}) →+* Tl l := Ideal.Quotient.lift _ r₀ hker
  obtain ⟨i, hi⟩ := GlobalTheory.T.finite_field_embeddings_differ_frobenius (l := l) (k := ↥(OL K) ⧸ Ideal.span {π}) (D := Tl l) α ((actT g).comp α)
  refine ⟨i, fun c => ?_⟩
  obtain ⟨c', hc'⟩ := GlobalTheory.T.teichmuller_residue_congruence K π f hf hqf hl h1 hπ0 (r₀ c) c (hr1 c) (hr2 c)
  refine ⟨c', ?_⟩
  have h : actT g (r₀ c) = r₀ c ^ l ^ i := hi (Ideal.Quotient.mk _ c)
  rw [← h, sh_actT, hc', oc_eq, galCp_omC, hg]

theorem tch_clause {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f)
    (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (r₀ : ↥(OL K) →+* Tl l) (hr1 : ∀ c, r₀ c ^ l ^ f = r₀ c) (i : ℕ)
    (hic : ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1))) :
    ∀ c, ∃ c', tch l (((iterateFrobenius (Tl l) l i).comp r₀) c) = oB K μ (c + π * c') := by
  intro c
  obtain ⟨c', hc'⟩ := hic c
  refine ⟨c', ?_⟩
  rw [RingHom.comp_apply, iterateFrobenius_def]
  have hfix : (r₀ c ^ l ^ i) ^ l ^ f = r₀ c ^ l ^ i := by
    rw [← pow_mul, mul_comm, pow_mul, hr1]
  rw [tch_eq f hf _ hfix _ hc']
  simp only [oB, RingHom.comp_apply]
  rfl

theorem gal_clause {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (g : GQ l) (r₀ : R →+* Tl l) (i : ℕ)
    (x : Tl l) (c : ℕ → R) (D : ℕ) (hd : x ^ D ∣ actT g x - ∑ j ∈ Finset.range D, r₀ (c j) * x ^ j) :
    (x ^ l ^ i) ^ D ∣ actT g (x ^ l ^ i) -
      ∑ j ∈ Finset.range D, ((iterateFrobenius (Tl l) l i).comp r₀) (c j) * (x ^ l ^ i) ^ j := by
  have h := pow_dvd_pow_of_dvd hd (l ^ i)
  rw [frob_pow_read] at h
  have e1 : (x ^ l ^ i) ^ D = (x ^ D) ^ l ^ i := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : actT g (x ^ l ^ i) = actT g x ^ l ^ i := map_pow _ _ _
  have e3 : ∀ j, ((iterateFrobenius (Tl l) l i).comp r₀) (c j) = r₀ (c j) ^ l ^ i := fun j => by
    rw [RingHom.comp_apply, iterateFrobenius_def]
  simp only [e1, e2, e3]
  exact h

end GlobalTheory.CompanionTheory.LTPer.Tilt

open GlobalTheory.CompanionTheory.LTPer.Tilt in

theorem GlobalTheory.CompanionTheory.LTPer.Tilt.tilt_period : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l,
    ∃ (r : ↥(OL K) →+* Tl l) (v : ℕ → Tl l),
      (∀ n, v (n + 1) ^ qOf π = v n) ∧ v 0 ≠ 0 ∧ ‖thB l (tch l (v 0))‖ < 1 ∧
      (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) ∧
      (∀ (g : GQ l) (hg : g ∈ GK K) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
        ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) →
        PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
        ∀ n D, v n ^ D ∣ actT g (v n) - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * v n ^ i) ∧
      (μ = K.1.val → ∀ n, ‖thB l (tch l (v n)) - ((z n : Om l) : ℂ_[l])‖ ≤ ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖) := by
  intro l _ K χ π z hLT μ
  obtain ⟨hirr, hz0, hz1, hrec, hgal⟩ := hLT
  obtain ⟨hq2, hlq, hπl, hπ1, -⟩ := GlobalTheory.CompanionTheory.LTPer.uniformiser_facts K π hirr
  obtain ⟨hmax, hfin, f, hf, hqf⟩ := GlobalTheory.T.uniformizer_residue_field_finite_power K π hirr
  have hπ1' : ‖oc K π‖ < 1 := by rw [oc_apply]; exact hπ1
  have hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ := by
    obtain ⟨a, ha⟩ := hπl
    have e : (l : ℂ_[l]) = oc K π * oc K a := by rw [← map_mul, ← ha, map_natCast]
    rw [e, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_oc_le_one K a)
  have hπ0 : π ≠ 0 := hirr.ne_zero
  obtain ⟨hzlt, hzgt⟩ := GlobalTheory.T.lubin_tate_sequence_norm_bounds K χ π z ⟨hirr, hz0, hz1, hrec, hgal⟩ hq2 hπ1'
  have hrec' : ∀ n, z (n + 1) ^ l ^ f + ((π : ↥K.1) : Om l) * z (n + 1) = z n := by
    intro n
    have h := hrec n
    rwa [show Nat.card (↥(OL K) ⧸ Ideal.span {π}) = l ^ f from hqf] at h
  have hZ : ∀ n, ‖omC (z (n + 1)) ^ l ^ f - omC (z n)‖ ≤ ‖oc K π‖ := by
    intro n
    have e : omC (z (n + 1)) ^ l ^ f - omC (z n) = -(oc K π * omC (z (n + 1))) := by
      rw [← hrec' n, map_add, map_mul, map_pow, oc_eq]
      ring
    rw [e, norm_neg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hzlt _).le
  obtain ⟨u, hu1, hu2⟩ := GlobalTheory.T.teichmuller_compatible_sequence_approximation f ‖oc K π‖ hf hl hπ1' (fun n => omC (z n)) (fun n => (hzlt n).le) hZ
  have hu0 : ∀ n, u n ≠ 0 := by
    have h2 : ∀ n, 2 ≤ n → u n ≠ 0 := by
      intro n hn h0
      have h := hu2 n
      rw [h0, sh_zero, zero_sub, norm_neg] at h
      exact absurd (hzgt n hn) (not_lt.2 h)
    intro n
    rw [← sys_pow_iter hu1 n 2]
    exact pow_ne_zero _ (h2 _ (by omega))
  have hfer : ∀ c : ↥(OL K), ‖oc K c ^ l ^ f - oc K c‖ ≤ ‖oc K π‖ := by
    intro c
    obtain ⟨a, ha⟩ := GlobalTheory.T.uniformizer_divides_frobenius_difference K π hmax hfin c
    rw [hqf] at ha
    rw [← map_pow, ← map_sub, ha, map_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_oc_le_one K a)
  obtain ⟨r₀, hr1, hr2⟩ := fix_ringHom K π f hf hl hπ1' hfer
  have hrπ : r₀ π = 0 := by
    apply fixed_unique hf (hr1 π) (zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
    refine lt_of_le_of_lt (norm_sub_le_of_near hl ?_) hπ1'
    rw [sh_zero, sub_zero]
    have e : sh (r₀ π) = (sh (r₀ π) - oc K π) + oc K π := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr2 π) le_rfl)
  have hexp : ∃ i : ℕ, (μ = K.1.val → i = 0) ∧
      ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1)) := by
    by_cases hμ : μ = K.1.val
    · refine ⟨0, fun _ => rfl, fun c => ?_⟩
      obtain ⟨c', hc'⟩ := GlobalTheory.T.teichmuller_residue_congruence K π f hf hqf hl hπ1' hπ0 (r₀ c) c (hr1 c) (hr2 c)
      refine ⟨c', ?_⟩
      rw [pow_zero, pow_one, hc', hμ]
      rfl
    · obtain ⟨i, hi⟩ := exp_twist K π f hf hqf hl hπ1' hπ0 hmax hfin r₀ hr1 hr2 hrπ μ
      exact ⟨i, fun h => absurd h hμ, hi⟩
  obtain ⟨i, hi0, hic⟩ := hexp
  refine ⟨(iterateFrobenius (Tl l) l i).comp r₀, fun n => u n ^ l ^ i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    show (u (n + 1) ^ l ^ i) ^ qOf π = u n ^ l ^ i
    rw [hqf, ← pow_mul, mul_comm, pow_mul, hu1]
  · exact pow_ne_zero _ (hu0 0)
  · show ‖thB l (tch l (u 0 ^ l ^ i))‖ < 1
    rw [thB_tch, sh_pow, norm_pow]
    have h := hu2 0
    rw [hz0, map_zero, sub_zero] at h
    exact pow_lt_one₀ (norm_nonneg _) (h.trans_lt hπ1') (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  · exact tch_clause K π f hf μ r₀ hr1 i hic
  · intro g hg φ h0 h1 hcomm n D
    have hs := hgal ⟨g, hg⟩ φ h0 h1 hcomm
    have hd := GlobalTheory.T.lubin_tate_teichmuller_sequence_compatibility K π z f hf hl hπ1' hzlt hzgt u hu1 hu2 r₀ hr1 hr2 hu0 g
      (fun k => PowerSeries.coeff k φ) hs n D
    exact gal_clause g r₀ i (u n) (fun k => PowerSeries.coeff k φ) D hd
  · intro hμ n
    show ‖thB l (tch l (u n ^ l ^ i)) - _‖ ≤ _
    rw [hi0 hμ, pow_zero, pow_one, thB_tch, ← omC_apply, ← oc_apply]
    exact hu2 n
