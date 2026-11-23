import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateAction
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ExistsNotInduces
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

namespace GlobalTheory.LTTateC

section Series

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB

variable {l : ℕ} [Fact l.Prime]

theorem summable_norm_term {R : Type} [CommRing R] (φ : R →+* ℂ_[l]) (hφ : ∀ r, ‖φ r‖ ≤ 1) {y : ℂ_[l]}
    (hy : ‖y‖ < 1) (G : PowerSeries R) : Summable fun i => ‖φ (PowerSeries.coeff i G) * y ^ i‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
    (summable_geometric_of_lt_one (norm_nonneg y) hy)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (hφ _)

theorem tsum_mul_term {R : Type} [CommRing R] (φ : R →+* ℂ_[l]) (hφ : ∀ r, ‖φ r‖ ≤ 1) {y : ℂ_[l]}
    (hy : ‖y‖ < 1) (G G' : PowerSeries R) :
    ∑' i, φ (PowerSeries.coeff i (G * G')) * y ^ i =
      (∑' i, φ (PowerSeries.coeff i G) * y ^ i) * ∑' i, φ (PowerSeries.coeff i G') * y ^ i := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_term φ hφ hy G)
    (summable_norm_term φ hφ hy G')]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  replace hp : p.1 + p.2 = n := by simpa using hp
  rw [← hp, map_mul, pow_add]
  ring

theorem tsum_coe_term {R : Type} [CommRing R] (φ : R →+* ℂ_[l]) (y : ℂ_[l]) (P : Polynomial R) :
    ∑' i, φ (PowerSeries.coeff i (P : PowerSeries R)) * y ^ i = P.eval₂ φ y := by
  rw [Polynomial.eval₂_eq_sum_range, tsum_eq_sum (s := Finset.range (P.natDegree + 1))]
  · simp only [Polynomial.coeff_coe]
  · intro i hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]

def intToC (L : FinExt l) : ↥(OL L) →+* ℂ_[l] :=
  (algebraMap (Om l) ℂ_[l]).comp (L.1.val.toRingHom.comp (OL L).val.toRingHom)

theorem norm_intToC (L : FinExt l) (x : ↥(OL L)) : ‖intToC L x‖ ≤ 1 :=
  (PadicComplex.norm_extends l _).trans_le (norm_le_one_of_mem_OL L x)

theorem mem_range_of_hasSum_zero (L : FinExt l) (G : PowerSeries ↥(OL L)) (k : ℕ)
    (hk : IsUnit (PowerSeries.coeff k G)) {y : ℂ_[l]} (hy : ‖y‖ < 1)
    (h : HasSum (fun i => intToC L (PowerSeries.coeff i G) * y ^ i) 0) :
    ∃ z : Om l, (z : ℂ_[l]) = y := by
  haveI := Formalism.MainNotions.N.Pv.LocalLengthBound.OLC.complete_max L
  have hG : G.map (IsLocalRing.residue ↥(OL L)) ≠ 0 := fun h0 => by
    have := congrArg (PowerSeries.coeff k) h0
    rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff] at this
    exact this hk
  obtain ⟨P, U, H⟩ := PowerSeries.exists_isWeierstrassFactorization hG
  obtain ⟨V, hV⟩ := H.isUnit.exists_right_inv
  have e : (P : PowerSeries ↥(OL L)) = G * V := by rw [H.eq_mul, mul_assoc, hV, mul_one]
  have h1 := tsum_coe_term (intToC L) y P
  rw [e, tsum_mul_term _ (norm_intToC L) hy, h.tsum_eq, zero_mul] at h1
  have hint : IsIntegral (Om l) y := by
    refine ⟨P.map (L.1.val.toRingHom.comp (OL L).val.toRingHom), H.isDistinguishedAt.monic.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact h1.symm
  obtain ⟨z, hz⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Om l)
    (K := ↥(integralClosure (Om l) ℂ_[l]))).2 ⟨y, hint⟩
  exact ⟨z, congrArg Subtype.val hz⟩

end Series

section Transport

open GroundTheory.LocalField.FormalGroup

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Finite (IsLocalRing.ResidueField B)]

theorem isLubinTateSeries_map (e : A ≃+* B) {π : A} {f : PowerSeries A} (hf : IsLubinTateSeries π f) :
    IsLubinTateSeries (e π) (PowerSeries.map (e : A →+* B) f) := by
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf.constantCoeff_eq_zero, map_zero]
  · rw [PowerSeries.coeff_map, hf.coeff_one]; rfl
  · have h := map_dvd (e : A →+* B) (hf.dvd_coeff_sub n)
    rw [← PowerSeries.coeff_map, map_sub, map_pow, PowerSeries.map_X,
      Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv] at h
    exact h

theorem map_lubinTateHom (e : A ≃+* B) {π : A} (hπ : Irreducible π) {f : PowerSeries A}
    (hf : IsLubinTateSeries π f) {π' : B} (hπ' : Irreducible π') {f' : PowerSeries B}
    (hf' : IsLubinTateSeries π' f') (hff : PowerSeries.map (e : A →+* B) f = f') (a : A) :
    PowerSeries.map (e : A →+* B) (lubinTateHom hπ hf hf a).toPowerSeries =
      (lubinTateHom hπ' hf' hf' (e a)).toPowerSeries := by
  refine eq_lubinTateHom_toPowerSeries hπ' hf' hf' _ ?_ ?_ ?_
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (lubinTateHom hπ hf hf a).constantCoeff_eq_zero, map_zero]
  · rw [PowerSeries.coeff_map, coeff_one_lubinTateHom]; rfl
  · have h := congrArg (PowerSeries.map (e : A →+* B)) (subst_lubinTateHom hπ hf hf a)
    have h1 := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' (lubinTateHom hπ hf hf a).constantCoeff_eq_zero) (h := (e : A →+* B)) f
    have h2 := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hf.constantCoeff_eq_zero) (h := (e : A →+* B)) (lubinTateHom hπ hf hf a).toPowerSeries
    subst hff
    exact h1.symm.trans (h.trans h2)

end Transport

section Points

open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {M : Type} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsValuativeTopology M]
  [Algebra K M] [ValuativeExtension K M] [Algebra.IsAlgebraic K M]

theorem hasSum_map_psEval (θ : M →+* ℂ_[l]) (hθ : Continuous θ) (f : PowerSeries 𝒪[K]) {x : M}
    (hx : valuation M x < 1) :
    HasSum (fun i => θ (algebraMap K M ((PowerSeries.coeff i f : 𝒪[K]) : K)) * θ x ^ i)
      (θ (psEval (f : MvPowerSeries Unit 𝒪[K]) fun _ => x)) := by
  have h := (hasSum_psEval' (f : MvPowerSeries Unit 𝒪[K]) (fun _ => x) fun _ => hx).map θ.toAddMonoidHom hθ
  rw [← (Finsupp.uniqueEquiv (M := ℕ) ()).symm.hasSum_iff] at h
  convert h using 1
  · funext i
    simp [psTerm, PowerSeries.coeff, Finsupp.uniqueEquiv]
  · rfl

theorem mem_torsion_of_hasSum (θ : M →+* ℂ_[l]) (hθ : Continuous θ) {π : 𝒪[K]} (hπ : Irreducible π)
    {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f) (x : ℕ → IdealPoint M (lubinTateFormalGroup hπ hf))
    (hS : ∀ n, HasSum (fun i => θ (algebraMap K M ((PowerSeries.coeff i f : 𝒪[K]) : K)) * θ (x (n + 1)).val ^ i)
      (θ (x n).val)) (h0 : x 0 = 0) (n : ℕ) : x n ∈ lubinTateTorsion M (hπ := hπ) hf n := by
  rw [mem_lubinTateTorsion]
  induction n with
  | zero => rw [h0, smul_zero]
  | succ n ih =>
    have e : π • x (n + 1) = x n := by
      apply IdealPoint.ext
      rw [lubinTate_uniformizer_smul_val]
      exact θ.injective ((hasSum_map_psEval θ hθ f (x (n + 1)).valuation_lt_one).unique (hS n))
    rw [pow_succ, mul_smul, e, ih]

end Points

section Algebraic

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Prism GlobalTheory.AinfK Formalism.BasicNotions.Examples₂.LB GroundTheory.LocalField.FormalGroup GlobalTheory.LTTilt

variable {l : ℕ} [Fact l.Prime]

theorem norm_lt_one (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) {F : PowerSeries ↥(OL K)}
    (hF : IsLubinTateSeries π F) {v : ℕ → OC l}
    (hS : ∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i F) * v (n + 1) ^ i : OC l) : ℂ_[l])) (v n : ℂ_[l]))
    (h0 : v 0 = 0) (n : ℕ) : ‖(v n : ℂ_[l])‖ < 1 := by
  refine norm_lt_one_of_compat K hπ (fun n => ?_) h0 n
  refine pow_sub_mem_of_hasSum _ _ (PowerSeries.map (intToOC K) F) (fun i => ?_) _ _ ?_
  · have h := hF.dvd_coeff_sub i
    rw [card_res] at h
    have := map_dvd (intToOC K) h
    rw [← PowerSeries.coeff_map, map_sub, map_pow, PowerSeries.map_X] at this
    exact Ideal.mem_span_singleton.2 this
  · simpa only [PowerSeries.coeff_map] using hS n

theorem exists_coe_eq (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) {F : PowerSeries ↥(OL K)}
    (hF : IsLubinTateSeries π F) {v : ℕ → OC l}
    (hS : ∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i F) * v (n + 1) ^ i : OC l) : ℂ_[l])) (v n : ℂ_[l]))
    (h0 : v 0 = 0) (n : ℕ) : ∃ z : Om l, (z : ℂ_[l]) = v n := by
  induction n with
  | zero => exact ⟨0, by rw [h0]; rfl⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    have hz1 : ‖z‖ < 1 := by
      rw [← PadicComplex.norm_extends l z, hz]
      exact norm_lt_one K hπ hF hS h0 n
    haveI := K.2
    haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    let L : FinExt l := ⟨K.1 ⊔ IntermediateField.adjoin ℚ_[l] {z}, inferInstance⟩
    have hKL : K.1 ≤ L.1 := le_sup_left
    have hzL : z ∈ L.1 := (le_sup_right : _ ≤ L.1) (IntermediateField.mem_adjoin_simple_self _ z)
    let r : ↥(OL K) →+* ↥(OL L) :=
      ((IntermediateField.inclusion hKL).toRingHom.comp (OL K).val.toRingHom).codRestrict (OL L) fun x =>
        (mem_OL L _).2 ((mem_OL K _).1 x.2)
    let z' : ↥(OL L) := ⟨⟨z, hzL⟩, (mem_OL L _).2 hz1.le⟩
    have hq : 1 < Nat.card (IsLocalRing.ResidueField ↥(OL K)) := Finite.one_lt_card
    refine mem_range_of_hasSum_zero L (PowerSeries.map r F - PowerSeries.C z')
      (Nat.card (IsLocalRing.ResidueField ↥(OL K))) ?_ (norm_lt_one K hπ hF hS h0 (n + 1)) ?_
    · rw [map_sub, PowerSeries.coeff_map, PowerSeries.coeff_C, if_neg (by omega), sub_zero]
      refine IsUnit.map r ?_
      have h := hF.dvd_coeff_sub (Nat.card (IsLocalRing.ResidueField ↥(OL K)))
      rw [map_sub, PowerSeries.coeff_X_pow, if_pos rfl] at h
      by_contra hu
      have h1 : PowerSeries.coeff (Nat.card (IsLocalRing.ResidueField ↥(OL K))) F - 1 ∈
          IsLocalRing.maximalIdeal ↥(OL K) := by
        obtain ⟨c, hc⟩ := h
        rw [hc]
        exact Ideal.mul_mem_right _ _ hπ.not_isUnit
      have h2 := Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hu) h1
      rw [sub_sub_cancel] at h2
      exact h2 isUnit_one
    · have h := (hS n).sub (hasSum_ite_eq 0 (v n : ℂ_[l]))
      rw [sub_self] at h
      refine (congrArg (HasSum · 0) (funext fun i => ?_)).mpr h
      rw [map_sub, map_sub, PowerSeries.coeff_map, PowerSeries.coeff_C, sub_mul]
      congr 1
      split_ifs with hi
      · rw [hi, pow_zero, mul_one, ← hz]; rfl
      · rw [map_zero, zero_mul]

end Algebraic

section Completion

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.BasicNotions.Examples₂.LB GlobalTheory.LocDict
open Filter Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] {w : HeightOneSpectrum (𝓞 E)}

theorem norm_lt_one_of_v (j : w.adicCompletion E →+* Om l) (hj : Continuous j) {x : w.adicCompletion E}
    (hx : Valued.v x < 1) : ‖j x‖ < 1 := by
  have h := (hj.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hx)
  rw [map_zero] at h
  refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h.congr fun n => ?_)
  simp

theorem norm_le_one_iff (j : w.adicCompletion E →+* Om l) (hj : Continuous j) (x : w.adicCompletion E) :
    ‖j x‖ ≤ 1 ↔ Valued.v x ≤ 1 := by
  constructor
  · intro h
    by_contra hx
    rw [not_le] at hx
    have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx
    have h1 : Valued.v x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hx
    have h2 := norm_lt_one_of_v j hj h1
    rw [map_inv₀, norm_inv, inv_lt_one₀ (norm_pos_iff.2 ((map_ne_zero j).2 hx0))] at h2
    exact h2.not_ge h
  · intro h
    by_contra hx
    rw [not_le] at hx
    obtain ⟨p, hp0, hp⟩ : ∃ p : w.adicCompletion E, p ≠ 0 ∧ Valued.v p < 1 := by
      obtain ⟨p, hp⟩ := w.valuation_exists_uniformizer E
      have hv : Valued.v (algebraMap E (w.adicCompletion E) p) = WithZero.exp (-1 : ℤ) := by
        rw [← hp]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w p
      refine ⟨algebraMap E _ p, fun h0 => ?_, ?_⟩
      · rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
      · rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hp1 : 0 < ‖j p‖ := norm_pos_iff.2 ((map_ne_zero j).2 hp0)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖j p‖⁻¹ hx
    have h2 : Valued.v (x ^ n * p) < 1 := by
      rw [map_mul, map_pow]
      exact (mul_le_of_le_one_left' (pow_le_one' h n)).trans_lt hp
    have h3 := norm_lt_one_of_v j hj h2
    rw [map_mul, map_pow, norm_mul, norm_pow] at h3
    rw [inv_lt_iff_one_lt_mul₀ hp1] at hn
    exact hn.not_gt h3

theorem isClosed_range (j : w.adicCompletion E →+* Om l) (hj : Continuous j) : IsClosed (Set.range j) := by
  have h1 : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (Formalism.MainNotions.Gaps.LevGap.compact_Ov w)
  have h2 := (h1.image hj).isClosed
  refine isClosed_of_closure_subset fun y hy => ?_
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 hy 1 one_pos
  have h3 : y - j x ∈ j '' (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
    refine h2.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨_, ⟨x', rfl⟩, hx'⟩ := Metric.mem_closure_iff.1 hy (min ε 1) (lt_min hε one_pos)
    refine ⟨_, ⟨x' - x, ?_, rfl⟩, ?_⟩
    · show Valued.v (x' - x) ≤ 1
      rw [← norm_le_one_iff j hj, map_sub, ← dist_eq_norm]
      refine (IsUltrametricDist.dist_triangle_max _ y _).trans (max_le ?_ hx.le)
      rw [dist_comm]
      exact (hx'.trans_le (min_le_right _ _)).le
    · rw [map_sub, dist_sub_right]
      exact hx'.trans_le (min_le_left _ _)
  obtain ⟨x', -, hx'⟩ := h3
  exact ⟨x' + x, by rw [map_add, hx', sub_add_cancel]⟩

variable {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem exists_ringEquiv_Kw (Bw : LocBridge l E Ω Gw O) (j : w.adicCompletion E →+* Om l) (hj : Continuous j)
    (hjE : ∀ x : E, j (algebraMap E _ x) = Bw.j (algebraMap E Ω x)) :
    ∃ k : w.adicCompletion E ≃+* ↥Bw.Kw.1, ∀ x, ((k x : ↥Bw.Kw.1) : Om l) = j x := by
  haveI := Bw.Kw.2
  have hcl : IsClosed (Bw.Kw.1 : Set (Om l)) := Bw.Kw.1.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  have hmem : ∀ x, j x ∈ Bw.Kw.1 := fun x =>
    (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => j x ∈ Bw.Kw.1) x
      (hcl.preimage hj) fun y => by rw [hjE]; exact Bw.j_E y
  refine ⟨RingEquiv.ofBijective (j.codRestrict Bw.Kw.1 hmem) ⟨RingHom.injective _, fun y => ?_⟩, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : (y : Om l) ∈ Set.range j := by
    refine closure_minimal ?_ (isClosed_range j hj) (Bw.j_dense y.2)
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hjE x⟩
  exact ⟨x, Subtype.ext hx⟩

theorem mem_integer_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ Valued.v x ≤ 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _)
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem exists_ringEquiv_OL {K : FinExt l} (j : w.adicCompletion E →+* Om l) (hj : Continuous j)
    (k : w.adicCompletion E ≃+* ↥K.1) (hk : ∀ x, ((k x : ↥K.1) : Om l) = j x) :
    ∃ e : 𝒪[w.adicCompletion E] ≃+* ↥(OL K), ∀ x, ((e x : ↥(OL K)) : ↥K.1) = k x := by
  have H : ∀ x, k x ∈ OL K ↔ x ∈ 𝒪[w.adicCompletion E] := fun x => by
    rw [mem_OL, hk, norm_le_one_iff j hj, mem_integer_iff]
  refine ⟨RingEquiv.ofBijective (((k : w.adicCompletion E →+* ↥K.1).comp (𝒪[w.adicCompletion E]).subtype).codRestrict
    (OL K) fun x => (H x).2 x.2) ⟨fun x y h => ?_, fun y => ?_⟩, fun _ => rfl⟩
  · exact Subtype.ext (k.injective (congrArg Subtype.val h))
  · refine ⟨⟨k.symm y, (H _).1 ?_⟩, Subtype.ext (k.apply_symm_apply _)⟩
    rw [k.apply_symm_apply]
    exact y.2

end Completion

section Action

open NumberField IsDedekindDomain ValuativeRel Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.BasicNotions.Examples₂.LB
open GlobalTheory.LocDict GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Prism GlobalTheory.LTTilt GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] {w : HeightOneSpectrum (𝓞 E)}

theorem isUnit_integer_iff (x : 𝒪[w.adicCompletion E]) : IsUnit x ↔ Valued.v (x : w.adicCompletion E) = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← (ValuativeRel.isEquiv (ValuativeRel.valuation _)
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one]
  exact Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)

theorem irreducible_iff (x : 𝒪[w.adicCompletion E]) :
    Irreducible x ↔ Valued.v (x : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have key : ∀ y : 𝒪[w.adicCompletion E], Valued.v (y : w.adicCompletion E) = WithZero.exp (-1 : ℤ) →
      Irreducible y := by
    intro y hy
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · rw [isUnit_integer_iff, hy] at hu
      exact hlt.ne hu
    · rw [isUnit_integer_iff, isUnit_integer_iff]
      have ha := (mem_integer_iff _).1 a.2
      have hb := (mem_integer_iff _).1 b.2
      rw [hab, Subring.coe_mul, map_mul] at hy
      generalize Valued.v (a : w.adicCompletion E) = s at *
      generalize Valued.v (b : w.adicCompletion E) = t at *
      have hs : s ≠ 0 := fun h0 => by rw [h0, zero_mul] at hy; exact WithZero.exp_ne_zero hy.symm
      have ht : t ≠ 0 := fun h0 => by rw [h0, mul_zero] at hy; exact WithZero.exp_ne_zero hy.symm
      obtain ⟨m, rfl⟩ : ∃ m, s = WithZero.exp m := ⟨_, (WithZero.exp_log hs).symm⟩
      obtain ⟨m', rfl⟩ : ∃ m, t = WithZero.exp m := ⟨_, (WithZero.exp_log ht).symm⟩
      rw [← WithZero.exp_add, WithZero.exp_inj] at hy
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha hb
      rw [← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
      omega
  refine ⟨fun hx => ?_, key x⟩
  obtain ⟨p, hp⟩ := w.valuation_exists_uniformizer E
  have hv : Valued.v (algebraMap E (w.adicCompletion E) p) = WithZero.exp (-1 : ℤ) := by
    rw [← hp]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w p
  let p' : 𝒪[w.adicCompletion E] := ⟨algebraMap E _ p, (mem_integer_iff _).2 (hv.trans_lt hlt).le⟩
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible _ (key p' hv) hx
  rw [← hu, Subring.coe_mul, map_mul, (isUnit_integer_iff _).1 u.isUnit, mul_one]
  exact hv

variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem isIntegral_iff {K : FinExt l} (θ : Kbar w ≃+* Om l) (e : 𝒪[w.adicCompletion E] ≃+* ↥(OL K))
    (hθ : ∀ x : 𝒪[w.adicCompletion E], θ (algebraMap (w.adicCompletion E) (Kbar w) x) = ((e x : ↥K.1) : Om l))
    (y : Kbar w) : IsIntegral (w.adicCompletionIntegers E) y ↔ ‖θ y‖ ≤ 1 := by
  let s : ↥(w.adicCompletionIntegers E) ≃+* 𝒪[w.adicCompletion E] :=
    RingEquiv.subringCongr (s := (w.adicCompletionIntegers E).toSubring) (t := 𝒪[w.adicCompletion E])
      (Subring.ext fun x => (mem_integer_iff x).symm)
  have h1 : IsIntegral (w.adicCompletionIntegers E) y ↔ IsIntegral ↥(OL K) (θ y) :=
    ⟨fun h => h.map_of_comp_eq (s.trans e).toRingHom θ.toRingHom (RingHom.ext fun x => (hθ (s x)).symm),
      fun h => by
        have h2 := h.map_of_comp_eq (s.trans e).symm.toRingHom θ.symm.toRingHom (RingHom.ext fun x => by
          apply θ.injective
          show θ (algebraMap (w.adicCompletion E) (Kbar w) (e.symm x : 𝒪[w.adicCompletion E])) = θ (θ.symm _)
          rw [hθ, e.apply_symm_apply, θ.apply_symm_apply]
          rfl)
        exact θ.symm_apply_apply y ▸ h2⟩
  haveI : IsScalarTower ℤ_[l] ↥(OL K) (Om l) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [h1, ← isIntegral_iff_norm_le]
  exact ⟨fun h => isIntegral_trans _ h, fun h => h.tower_top⟩

set_option maxHeartbeats 1600000 in

theorem hasSum_σO (h : IsPlaceOver A w) (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hB : GlobalTheory.Pst.Induces Bw)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (k : w.adicCompletion E ≃+* ↥Bw.Kw.1)
    (hkE : ∀ x : E, ((k (algebraMap E _ x) : ↥Bw.Kw.1) : Om l) = Bw.j (algebraMap E Ω x))
    (e : 𝒪[w.adicCompletion E] ≃+* ↥(OL Bw.Kw)) (he : ∀ x, ((e x : ↥(OL Bw.Kw)) : ↥Bw.Kw.1) = k x)
    {π : ↥(OL Bw.Kw)} (hπ : Irreducible π) (c : Dec (F := E) A →* (w.adicCompletion E)ˣ)
    (hc : Continuous fun g => ((c g : (w.adicCompletion E)ˣ) : w.adicCompletion E))
    (hcW : ∀ σ : Weil h, ((c ⟨σ, Weil_le_Dec h σ.2⟩ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      (a σ : w.adicCompletion E) * (e.symm π : w.adicCompletion E) ^ deg σ)
    {F : PowerSeries ↥(OL Bw.Kw)} (hF : IsLubinTateSeries π F) {v : ℕ → OC l}
    (hS : ∀ n, HasSum (fun i => ((intToOC Bw.Kw (PowerSeries.coeff i F) * v (n + 1) ^ i : OC l) : ℂ_[l]))
      (v n : ℂ_[l])) (h0 : v 0 = 0) (g : ↥(GK Bw.Kw)) (u : ↥(OL Bw.Kw))
    (hu : (e.symm u : w.adicCompletion E) = c (Bw.e.symm g)) (n : ℕ) :
    HasSum (fun i => ((intToOC Bw.Kw (PowerSeries.coeff i (lubinTateHom hπ hF hF u).toPowerSeries) *
      v n ^ i : OC l) : ℂ_[l])) ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) := by
  haveI : IsAlgClosure ↥Bw.Kw.1 (Om l) := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _⟩
  let θ : Kbar w ≃+* Om l := IsAlgClosure.equivOfEquiv (Kbar w) (Om l) k
  have hθ : ∀ x, θ (algebraMap (w.adicCompletion E) (Kbar w) x) = ((k x : ↥Bw.Kw.1) : Om l) :=
    fun x => IsAlgClosure.equivOfEquiv_algebraMap (Kbar w) (Om l) k x
  have hθe : ∀ x : 𝒪[w.adicCompletion E],
      θ (algebraMap (w.adicCompletion E) (Kbar w) x) = ((e x : ↥Bw.Kw.1) : Om l) := fun x => by rw [hθ, he]
  clear_value θ

  let ι : Ω →ₐ[E] Kbar w :=
    { (θ.symm : Om l →+* Kbar w).comp Bw.j with
      commutes' := fun x => by
        apply θ.injective
        show θ (θ.symm (Bw.j _)) = _
        rw [θ.apply_symm_apply, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (Kbar w), hθ, hkE] }
  have hθι : ∀ z, θ (ι z) = Bw.j z := fun z => θ.apply_symm_apply _
  have hι : IsLocEmb A w ι := fun z => by rw [isIntegral_iff θ e hθe, hθι]; exact hB z
  let τ : GalLoc w :=
    { (θ.trans (g : GQ l).toRingEquiv).trans θ.symm with
      commutes' := fun x => by
        apply θ.injective
        show θ (θ.symm ((g : GQ l) (θ _))) = _
        rw [θ.apply_symm_apply, hθ]
        exact g.2 (k x) }
  have hθτ : ∀ y, θ (τ y) = (g : GQ l) (θ y) := fun y => θ.apply_symm_apply _
  have hτ : Lifts ι τ (Bw.e.symm g : G E Ω) := fun z => by
    apply θ.injective
    rw [hθτ, hθι, hθι, ← Bw.e_comm, MulEquiv.apply_symm_apply]

  letI : NormedField (Kbar w) := NormedField.induced (Kbar w) (Om l) (θ : Kbar w →+* Om l) θ.injective
  have hn : ∀ y : Kbar w, ‖y‖ = ‖θ y‖ := fun _ => rfl
  haveI : IsUltrametricDist (Kbar w) := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => by
    simp only [hn, map_add]
    exact IsUltrametricDist.norm_add_le_max _ _
  letI : ValuativeRel (Kbar w) := ValuativeRel.ofValuation (NormedField.valuation (K := Kbar w))
  haveI hcomp : (NormedField.valuation (K := Kbar w)).Compatible := Valuation.Compatible.ofValuation _
  haveI : IsValuativeTopology (Kbar w) :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := Kbar w))
      (fun {s} => (NormedField.toValued (K := Kbar w)).is_topological_valuation s)
  have hle : ∀ x : w.adicCompletion E, ‖θ (algebraMap (w.adicCompletion E) (Kbar w) x)‖ ≤ 1 ↔ Valued.v x ≤ 1 := by
    intro x
    rw [hθ, ← mem_OL, ← mem_integer_iff]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have := (e.symm ⟨k x, hx⟩).2
      rwa [k.injective ((he _).symm.trans (congrArg Subtype.val (e.apply_symm_apply _)))] at this
    · rw [← he ⟨x, hx⟩]
      exact (e _).2
  haveI : ValuativeExtension (w.adicCompletion E) (Kbar w) := ⟨fun x y => by
    show ‖θ (algebraMap _ _ x)‖₊ ≤ ‖θ (algebraMap _ _ y)‖₊ ↔ Valued.v x ≤ Valued.v y
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    by_cases hy : y = 0
    · simp [hy]
    · have h1 := hle (x / y)
      rw [map_div₀, map_div₀, norm_div, map_div₀, div_le_one (norm_pos_iff.2 (by simpa using hy)),
        div_le_one₀ (zero_lt_iff.2 (by simpa using hy))] at h1
      exact h1⟩
  have hlt : ∀ y : Kbar w, ‖θ y‖ < 1 → valuation (Kbar w) y < 1 := fun y hy =>
    (ValuativeRel.isEquiv (ValuativeRel.valuation _) (NormedField.valuation (K := Kbar w))).lt_one_iff_lt_one.2 hy
  let θC : Kbar w →+* ℂ_[l] := (algebraMap (Om l) ℂ_[l]).comp (θ : Kbar w →+* Om l)
  have hθC : Continuous θC :=
    (AddMonoidHomClass.isometry_of_norm θC fun y => PadicComplex.norm_extends l _).continuous

  have hπ' : Irreducible (e.symm π) := (MulEquiv.irreducible_iff e.symm).2 hπ
  have hf := isLubinTateSeries_map e.symm hF
  have hff : PowerSeries.map (e : 𝒪[w.adicCompletion E] →+* ↥(OL Bw.Kw))
      (PowerSeries.map (e.symm : ↥(OL Bw.Kw) →+* 𝒪[w.adicCompletion E]) F) = F := by
    ext i
    simp
  generalize PowerSeries.map (e.symm : ↥(OL Bw.Kw) →+* 𝒪[w.adicCompletion E]) F = f at hf hff
  have hterm : ∀ (G : PowerSeries 𝒪[w.adicCompletion E]) (y : Kbar w) (s : OC l), θC y = s →
      (fun i => θC (algebraMap (w.adicCompletion E) (Kbar w)
        ((PowerSeries.coeff i G : 𝒪[w.adicCompletion E]) : w.adicCompletion E)) * θC y ^ i) =
      fun i => ((intToOC Bw.Kw (PowerSeries.coeff i (PowerSeries.map
        (e : 𝒪[w.adicCompletion E] →+* ↥(OL Bw.Kw)) G)) * s ^ i : OC l) : ℂ_[l]) := by
    intro G y s hs
    funext i
    rw [hs, PowerSeries.coeff_map]
    push_cast
    congr 1
    exact congrArg (algebraMap (Om l) ℂ_[l]) (hθe _)

  choose z hz using exists_coe_eq Bw.Kw hπ hF hS h0
  have hz1 : ∀ m, ‖θ (θ.symm (z m))‖ < 1 := fun m => by
    rw [θ.apply_symm_apply, ← PadicComplex.norm_extends l, hz]
    exact norm_lt_one Bw.Kw hπ hF hS h0 m
  let x : ℕ → IdealPoint (Kbar w) (lubinTateFormalGroup hπ' hf) := fun m => IdealPoint.mk _ (hlt _ (hz1 m))
  have hx : ∀ m, θC (x m).val = v m := fun m =>
    (congrArg (algebraMap (Om l) ℂ_[l]) (θ.apply_symm_apply (z m))).trans (hz m)
  have hx0 : x 0 = 0 := IdealPoint.ext (θC.injective (by rw [hx, h0, IdealPoint.val_zero, map_zero]; rfl))
  have htor := mem_torsion_of_hasSum θC hθC hπ' hf x
    (fun m => by rw [hterm f _ _ (hx (m + 1)), hff, hx]; exact hS m) hx0 n
  have hact := congrArg IdealPoint.val (GlobalTheory.LTRecip.lubinTate_action E Ω A w h a ha ι hι hπ' hf c hc hcW
    (Bw.e.symm g) τ hτ (e.symm u) hu n (x n) htor)
  rw [lubinTateGalPointMap_val, lubinTate_smul_val] at hact
  have hsum := hasSum_map_psEval θC hθC (lubinTateHom hπ' hf hf (e.symm u)).toPowerSeries (x n).valuation_lt_one
  rw [hterm _ _ _ (hx n), map_lubinTateHom e hπ' hf hπ hF hff, e.apply_symm_apply, ← hact] at hsum
  have hval : θC (τ (x n).val) = ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) := by
    rw [GlobalTheory.RingIface.sigO_coe, ← hx]
    exact (congrArg (algebraMap (Om l) ℂ_[l]) (hθτ _)).trans (GlobalTheory.RingBasics.σC_coe _ _).symm
  rwa [hval] at hsum

end Action

end GlobalTheory.LTTateC

namespace GlobalTheory.LTTateC

open NumberField IsDedekindDomain ValuativeRel Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.BasicNotions.Examples₂.LB
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Prism GlobalTheory.LTTilt GroundTheory.LocalField.FormalGroup Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    GlobalTheory.Pst.Induces Bw → ∀ (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    (∃ j : w.adicCompletion E →+* Om l, Continuous j ∧
      ∀ x : E, j (algebraMap E (w.adicCompletion E) x) = Bw.j (algebraMap E Ω x)) ∧
    ∀ j : w.adicCompletion E →+* Om l, Continuous j →
      (∀ x : E, j (algebraMap E (w.adicCompletion E) x) = Bw.j (algebraMap E Ω x)) →
      (∀ π : ↥(OL Bw.Kw), Irreducible π →
        ∃ π' : (w.adicCompletion E)ˣ, IsUnifAt w π' ∧ j π' = ((π : ↥Bw.Kw.1) : Om l)) ∧
      (∀ π' : (w.adicCompletion E)ˣ, IsUnifAt w π' →
        ∃ π : ↥(OL Bw.Kw), Irreducible π ∧ j π' = ((π : ↥Bw.Kw.1) : Om l)) ∧
      ∀ (π : ↥(OL Bw.Kw)) (hπ : Irreducible π) (π' : (w.adicCompletion E)ˣ), j π' = ((π : ↥Bw.Kw.1) : Om l) →
        (∃ c : ↥(Dec (F := E) A) →* (w.adicCompletion E)ˣ,
          Continuous (fun g => ((c g : (w.adicCompletion E)ˣ) : w.adicCompletion E)) ∧
          ∀ σ : Weil h, c ⟨σ, Weil_le_Dec h σ.2⟩ = a σ * π' ^ deg σ) ∧
        ∀ c : ↥(Dec (F := E) A) →* (w.adicCompletion E)ˣ,
          Continuous (fun g => ((c g : (w.adicCompletion E)ˣ) : w.adicCompletion E)) →
          (∀ σ : Weil h, c ⟨σ, Weil_le_Dec h σ.2⟩ = a σ * π' ^ deg σ) →
          ∀ g : ↥(GK Bw.Kw),
            (∃ u : ↥(OL Bw.Kw), IsUnit u ∧ ((u : ↥Bw.Kw.1) : Om l) = j (c (Bw.e.symm g) : (w.adicCompletion E)ˣ)) ∧
            ∀ u : ↥(OL Bw.Kw), ((u : ↥Bw.Kw.1) : Om l) = j (c (Bw.e.symm g) : (w.adicCompletion E)ˣ) →
            ∀ (F : PowerSeries ↥(OL Bw.Kw)) (hF : IsLubinTateSeries π F) (v : ℕ → OC l),
              (∀ n, HasSum (fun i => ((intToOC Bw.Kw (PowerSeries.coeff i F) * v (n + 1) ^ i : OC l) : ℂ_[l]))
                (v n : ℂ_[l])) → v 0 = 0 →
              ∀ n, HasSum (fun i => ((intToOC Bw.Kw
                (PowerSeries.coeff i (lubinTateHom hπ hF hF u).toPowerSeries) * v n ^ i : OC l) : ℂ_[l]))
                ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) := by
  intro E Ω _ _ _ _ _ l _ w A h O _ _ _ Bw hB a ha
  refine ⟨?_, fun j hj hjE => ?_⟩
  · obtain ⟨j, hj⟩ := GlobalTheory.PY.LTInh.exists_emb Bw h hB (AlgHom.id ℚ_[l] ↥Bw.Kw.1)
    exact ⟨j.1, j.2, hj⟩
  obtain ⟨k, hk⟩ := exists_ringEquiv_Kw Bw j hj hjE
  obtain ⟨e, he⟩ := exists_ringEquiv_OL j hj k hk
  have hje : ∀ y : ↥(OL Bw.Kw), j (e.symm y : w.adicCompletion E) = ((y : ↥Bw.Kw.1) : Om l) := fun y => by
    rw [← hk, ← he, e.apply_symm_apply]
  have hunif : ∀ (π : ↥(OL Bw.Kw)), Irreducible π →
      Valued.v (e.symm π : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := fun π hπ =>
    (irreducible_iff _).1 ((MulEquiv.irreducible_iff e.symm).2 hπ)
  refine ⟨fun π hπ => ?_, fun π' hπ' => ?_, fun π hπ π' hππ => ?_⟩
  · have h0 : (e.symm π : w.adicCompletion E) ≠ 0 := fun h0 => by
      have := hunif π hπ
      rw [h0, map_zero] at this
      exact WithZero.exp_ne_zero this.symm
    exact ⟨Units.mk0 _ h0, hunif π hπ, hje π⟩
  · have hv : Valued.v (π' : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := hπ'
    let p : 𝒪[w.adicCompletion E] := ⟨π', (mem_integer_iff _).2 (by
      rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)⟩
    refine ⟨e p, (MulEquiv.irreducible_iff e).2 ((irreducible_iff p).2 hv), ?_⟩
    rw [he, hk]
  have hπe : (e.symm π : w.adicCompletion E) = π' := j.injective ((hje π).trans hππ.symm)
  have hπ' : IsUnifAt w π' := by
    show Valued.v (π' : w.adicCompletion E) = _
    rw [← hπe]
    exact hunif π hπ
  obtain ⟨c₀, hc₀, hc₀W, hc₀u, huniq⟩ := GlobalTheory.LTExt.exists_lubinTate_char E Ω w A h a ha π' hπ'
  refine ⟨⟨c₀, hc₀, hc₀W⟩, fun c hc hcW g => ⟨?_, fun u hu F hF v hS h0 n => ?_⟩⟩
  · obtain rfl := huniq c hc hcW
    have hv : Valued.v ((c (Bw.e.symm g) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := hc₀u _
    let p : 𝒪[w.adicCompletion E] := ⟨_, (mem_integer_iff _).2 hv.le⟩
    refine ⟨e p, ((isUnit_integer_iff p).2 hv).map e, ?_⟩
    rw [he, hk]
  · refine hasSum_σO h Bw hB a ha k (fun x => by rw [hk, hjE]) e he hπ c hc (fun σ => ?_) hF hS h0 g u
      (j.injective ((hje u).trans hu)) n
    rw [hcW, hπe, Units.val_mul, Units.val_zpow_eq_zpow_val]

end GlobalTheory.LTTateC

end
