import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ShortVectorEveryPlace
import Formalism.HermitianLattices.FinalMass
import Formalism.FockGram.FockGramProofs.CovolGram

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

section Alg

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem norm_embedding_le_trace (a : K) (ha : ∀ σ : K →ₐ[ℚ] ℂ, ∃ r : ℝ, 0 ≤ r ∧ σ a = (r : ℂ)) (φ : K →+* ℂ) :
    ‖φ a‖ ≤ ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
  classical
  choose r hr0 hr using ha
  have htr : ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, r σ := by
    apply Complex.ofReal_injective
    have h1 := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
    rw [show ((((Algebra.trace ℚ K a : ℚ) : ℝ)) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ K a) by simp, h1]
    push_cast
    exact Finset.sum_congr rfl fun σ _ => hr σ
  rw [htr]
  have hφ : φ a = ((r φ.toRatAlgHom : ℝ) : ℂ) := hr φ.toRatAlgHom
  rw [hφ, Complex.norm_of_nonneg (hr0 _)]
  exact Finset.single_le_sum (fun σ _ => hr0 σ) (Finset.mem_univ _)

theorem abs_det_trace_form_eq_discr (hK : IsCMUnram K) :
    |(Matrix.of fun j j' : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      ((Algebra.trace ℚ K (star (integralBasis K j) * integralBasis K j') : ℚ) : ℝ)).det| = |(discr K : ℝ)| := by
  classical
  set B := integralBasis K with hB
  let s : K →ₗ[ℚ] K := (starRingEnd K).toRatAlgHom.toLinearMap
  have hs : ∀ x, s x = star x := fun x => rfl
  let A := LinearMap.toMatrix B B s
  let Mq : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ :=
    Matrix.of fun j j' => Algebra.trace ℚ K (star (B j) * B j')
  have hM : Mq = A.transpose * Algebra.traceMatrix ℚ B := by
    ext j j'
    rw [Matrix.mul_apply]
    simp only [Mq, A, Matrix.of_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    conv_lhs => rw [← B.sum_repr (star (B j))]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul, hs]
  have hA : A * A = 1 := by
    have hss : s ∘ₗ s = LinearMap.id := by
      ext x
      simp [hs]
    rw [← LinearMap.toMatrix_comp, hss, LinearMap.toMatrix_id]
  have hdet : A.det * A.det = 1 := by
    rw [← Matrix.det_mul, hA, Matrix.det_one]
  have hdet' : |A.det| = 1 := by
    rcases mul_self_eq_one_iff.1 hdet with h | h <;> simp [h]
  have hcast : (Matrix.of fun j j' : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      ((Algebra.trace ℚ K (star (integralBasis K j) * integralBasis K j') : ℚ) : ℝ)).det = ((Mq.det : ℚ) : ℝ) := by
    rw [show ((Mq.det : ℚ) : ℝ) = Rat.castHom ℝ Mq.det from rfl, RingHom.map_det]
    congr 1
  rw [hcast, hM, Matrix.det_mul, Matrix.det_transpose, ← Algebra.discr_def, ← NumberField.coe_discr]
  rw [show (((A.det * (discr K : ℚ) : ℚ)) : ℝ) = ((A.det : ℚ) : ℝ) * ((discr K : ℤ) : ℝ) by push_cast; rfl]
  rw [abs_mul]
  have : |((A.det : ℚ) : ℝ)| = 1 := by
    rw [← Rat.cast_abs, hdet', Rat.cast_one]
  rw [this, one_mul]

end Alg

section Frame

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inner_sum_orthonormal_pair (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (a c : Fin 2 → K) :
    h (∑ i, a i • e i) (∑ j, c j • e j) = ∑ i, star (a i) * c i := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, he]
  simp [Fin.sum_univ_two]
  ring

theorem exists_coords_basis_fin_two (e : Fin 2 → V) (hli : LinearIndependent K e) (hsp : Submodule.span K (Set.range e) = ⊤) (x : V) :
    ∃ a : Fin 2 → K, x = ∑ i, a i • e i := by
  have hx : x ∈ Submodule.span K (Set.range e) := hsp ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
  exact ⟨a, ha.symm⟩

theorem conj_inner_self_nonneg (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hli : LinearIndependent K e)
    (hsp : Submodule.span K (Set.range e) = ⊤) (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V)
    (σ : K →ₐ[ℚ] ℂ) : ∃ r : ℝ, 0 ≤ r ∧ σ (h x x) = (r : ℂ) := by
  obtain ⟨a, rfl⟩ := exists_coords_basis_fin_two e hli hsp x
  rw [inner_sum_orthonormal_pair h e he a a]
  refine ⟨∑ i, ‖σ (a i)‖ ^ 2, by positivity, ?_⟩
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  have hst := hK.2.1 (σ : K →+* ℂ) (a i)
  simp only [RingHom.coe_coe] at hst
  rw [hst, Complex.conj_mul']

theorem trace_inner_pos_of_orthonormal_pair (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hli : LinearIndependent K e)
    (hsp : Submodule.span K (Set.range e) = ⊤) (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V)
    (hx : x ≠ 0) : 0 < Algebra.trace ℚ K (h x x) := by
  obtain ⟨a, rfl⟩ := exists_coords_basis_fin_two e hli hsp x
  rw [inner_sum_orthonormal_pair h e he a a]
  have hi : ∃ i, a i ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply hx
    simp [hne]
  obtain ⟨i, hi⟩ := hi
  have htr : ((Algebra.trace ℚ K (∑ i, star (a i) * a i) : ℚ) : ℝ) =
      ∑ σ : K →ₐ[ℚ] ℂ, ∑ i, ‖σ (a i)‖ ^ 2 := by
    apply Complex.ofReal_injective
    have h1 := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := ∑ i, star (a i) * a i)
    rw [show ((((Algebra.trace ℚ K (∑ i, star (a i) * a i) : ℚ) : ℝ)) : ℂ) =
      algebraMap ℚ ℂ (Algebra.trace ℚ K (∑ i, star (a i) * a i)) by simp, h1]
    push_cast
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    have hst := hK.2.1 (σ : K →+* ℂ) (a j)
    simp only [RingHom.coe_coe] at hst
    rw [hst, Complex.conj_mul']
  have hreal : (0 : ℝ) < ((Algebra.trace ℚ K (∑ i, star (a i) * a i) : ℚ) : ℝ) := by
    rw [htr]
    apply Finset.sum_pos' (fun σ _ => Finset.sum_nonneg fun j _ => by positivity)
    refine ⟨IsAlgClosed.lift, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun j _ => by positivity)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    have hne : (IsAlgClosed.lift : K →ₐ[ℚ] ℂ) (a i) ≠ 0 := (map_ne_zero _).2 hi
    exact pow_pos (norm_pos_iff.2 hne) 2
  exact_mod_cast hreal

end Frame

section Covol

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem covolume_trace_lattice (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hli : LinearIndependent K e)
    (hsp : Submodule.span K (Set.range e) = ⊤) (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0)
    (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    [DiscreteTopology (zmap ι (Submodule.span (𝓞 K) (Set.range e)))]
    [IsZLattice ℝ (zmap ι (Submodule.span (𝓞 K) (Set.range e)))] :
    ZLattice.covolume (zmap ι (Submodule.span (𝓞 K) (Set.range e))) = |(discr K : ℝ)| ∧ N = 2 * finrank ℚ K := by
  classical
  let v : Free.ChooseBasisIndex ℤ (𝓞 K) × Fin 2 → EuclideanSpace ℝ (Fin N) :=
    fun p => ι (integralBasis K p.1 • e p.2)
  let A : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ :=
    Matrix.of fun j j' => ((Algebra.trace ℚ K (star (integralBasis K j) * integralBasis K j') : ℚ) : ℝ)
  have hAdet : |A.det| = |(discr K : ℝ)| := abs_det_trace_form_eq_discr hK
  have hspan : zmap ι (Submodule.span (𝓞 K) (Set.range e)) = Submodule.span ℤ (Set.range v) := by
    apply le_antisymm
    · rintro w ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hx
      rw [map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← (RingOfIntegers.basis K).sum_repr (c i), Finset.sum_smul, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [smul_assoc, map_zsmul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k, i), ?_⟩)
      simp only [v, integralBasis_apply, algebraMap_smul]
    · rw [Submodule.span_le]
      rintro _ ⟨⟨k, i⟩, rfl⟩
      have hmem : integralBasis K k • e i ∈ Submodule.span (𝓞 K) (Set.range e) := by
        rw [integralBasis_apply, algebraMap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      exact AddSubgroup.mem_map_of_mem ι hmem
  have hG : Matrix.gram ℝ v = Matrix.blockDiagonal (fun _ : Fin 2 => A) := by
    ext ⟨k, i⟩ ⟨k', i'⟩
    rw [Matrix.gram_apply, Matrix.blockDiagonal_apply]
    simp only [v, A, hι, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply,
      he, Matrix.of_apply]
    split_ifs with hii
    · simp [hii]
      exact congrArg _ (mul_comm _ _)
    · simp [hii]
  have hdetG : (Matrix.gram ℝ v).det = A.det * A.det := by
    rw [hG, Matrix.det_blockDiagonal, Fin.prod_univ_two]
  have hA0 : A.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hAdet
    exact NumberField.discr_ne_zero K (by exact_mod_cast (abs_eq_zero.1 hAdet.symm))
  have hli' : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hmv : Matrix.mulVec (Matrix.gram ℝ v) g = 0 := by
      ext p
      have hp := congrArg (fun w => inner ℝ (v p) w) hg
      simp only [inner_sum, inner_smul_right, inner_zero_right] at hp
      simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply, Pi.zero_apply]
      rw [← hp]
      exact Finset.sum_congr rfl fun q _ => mul_comm _ _
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hdetG]; exact mul_ne_zero hA0 hA0) hmv
    intro p
    exact congrFun h0 p
  have hsp' : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    have htop : Submodule.span ℝ ((zmap ι (Submodule.span (𝓞 K) (Set.range e)) : Submodule ℤ _) :
        Set (EuclideanSpace ℝ (Fin N))) = ⊤ := IsZLattice.span_top
    rw [hspan, Submodule.span_span_of_tower] at htop
    exact htop.ge
  let bb := Module.Basis.mk hli' hsp'
  have hbb : ⇑bb = v := Module.Basis.coe_mk hli' hsp'
  have hcovG := Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) (Free.ChooseBasisIndex ℤ (𝓞 K) × Fin 2) bb
  rw [hbb] at hcovG
  refine ⟨?_, ?_⟩
  · rw [hspan, hcovG, hdetG, Real.sqrt_mul_self_eq_abs, hAdet]
  · have h1 := Module.finrank_eq_card_basis bb
    rw [finrank_euclideanSpace_fin, Fintype.card_prod, Fintype.card_fin] at h1
    have h2 := Module.finrank_eq_card_basis (integralBasis K)
    rw [h1, h2]
    ring

end Covol

section Mink

open MeasureTheory

theorem minkowski_discriminant_ineq (n : ℕ) (hn : 1 ≤ n) (Δ rd : ℝ) (hΔ : 0 < Δ) (hrd : rd ^ n = Δ) (hrd0 : 0 < rd) :
    Δ * 2 ^ (2 * n) < Real.sqrt (2 * n * rd) ^ (2 * n) * (√Real.pi ^ (2 * n) / Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1)) := by
  have hpi : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have e1 : Real.sqrt (2 * n * rd) ^ (2 * n) = (2 * n * rd) ^ n := by
    rw [pow_mul, Real.sq_sqrt (by positivity)]
  have e2 : √Real.pi ^ (2 * n) = Real.pi ^ n := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have e3 : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
    rw [show (((2 * n : ℕ) : ℝ) / 2 + 1) = (n : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  rw [e1, e2, e3, mul_pow, mul_pow, hrd]
  have hf : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2pi : (2 : ℝ) ^ n < Real.pi ^ n := pow_lt_pow_left₀ hpi (by norm_num) (by omega)
  have k1 : (2 : ℝ) ^ n * n.factorial < Real.pi ^ n * (n : ℝ) ^ n :=
    calc (2 : ℝ) ^ n * n.factorial ≤ 2 ^ n * (n : ℝ) ^ n := by gcongr
      _ < Real.pi ^ n * (n : ℝ) ^ n := by gcongr
  rw [← mul_div_assoc, lt_div_iff₀ hfpos]
  have q1 : Δ * 2 ^ (2 * n) * n.factorial = (Δ * 2 ^ n) * (2 ^ n * n.factorial) := by
    rw [two_mul, pow_add]; ring
  have q2 : 2 ^ n * (n : ℝ) ^ n * Δ * Real.pi ^ n = (Δ * 2 ^ n) * (Real.pi ^ n * (n : ℝ) ^ n) := by ring
  rw [q1, q2]
  exact mul_lt_mul_of_pos_left k1 (by positivity)

theorem exists_short_vector_minkowski (N : ℕ) (hN : 1 ≤ N) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (R : ℝ) (hR : 0 ≤ R)
    (hvol : ZLattice.covolume Λ * 2 ^ N < R ^ N * (√Real.pi ^ N / Real.Gamma ((N : ℝ) / 2 + 1))) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ‖v‖ < R := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let b := Module.Free.chooseBasis ℤ Λ
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℝ (Fin N)))
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hF
  have hfin : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  haveI : Countable Λ.toAddSubgroup := Countable.of_equiv _ b.equivFun.toEquiv.symm
  have hc0 : 0 ≤ ZLattice.covolume Λ := by rw [hcov]; exact measureReal_nonneg
  have hvolF : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) = ENNReal.ofReal (ZLattice.covolume Λ) := by
    rw [hcov, measureReal_def, ENNReal.ofReal_toReal hfin]
  have hq : 0 < R ^ N * (√Real.pi ^ N / Real.Gamma ((N : ℝ) / 2 + 1)) :=
    lt_of_le_of_lt (mul_nonneg hc0 (by positivity)) hvol
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := Λ.toAddSubgroup) (s := Metric.ball (0 : EuclideanSpace ℝ (Fin N)) R) hF
    (fun x hx => by simpa using hx) (convex_ball 0 R) (by
      rw [EuclideanSpace.volume_ball, finrank_euclideanSpace_fin, Fintype.card_fin, hvolF]
      have h2 : (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) := by
        rw [ENNReal.ofReal_pow (by norm_num)]; simp
      rw [h2, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (by positivity)]
      exact (ENNReal.ofReal_lt_ofReal_iff hq).2 hvol)
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), by simpa using hxs⟩

end Mink

theorem short_vector_every_place (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) :
    ShortVectorEveryPlace K (2 * (finrank ℚ K : ℝ) * rootDiscriminant K) := by
  intro V _ _ _ _ h L hsymm hL M hM
  obtain ⟨e, hli, hsp, rfl, he⟩ := hL
  haveI : FiniteDimensional K V := Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)
  have hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := fun x hx => trace_inner_pos_of_orthonormal_pair hK h e hli hsp he x hx
  obtain ⟨N, ι, hι, -, hlat⟩ := Formalism.HermitianLatticesTheory.final_traceReal K V h hsymm hpos
  have hLlat : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range e)) :=
    ⟨Submodule.fg_span (Set.finite_range e), by rw [Submodule.span_span_of_tower]; exact hsp⟩
  obtain ⟨iL1, iL2⟩ := hlat _ hLlat
  obtain ⟨familyMassRatio, familyMassSecondLine⟩ := hlat M hM.1
  have hcov := Formalism.HermitianLatticesTheory.final_genusCovol K V h hsymm hpos N ι hι _ M hLlat hM
  obtain ⟨hcL, hN⟩ := covolume_trace_lattice hK h e hli hsp he N ι hι
  set n := Module.finrank ℚ K with hn_def
  subst hN
  have hn : 1 ≤ n := Module.finrank_pos
  have hΔ : 0 < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero K))
  have hrd0 : 0 < rootDiscriminant K := Real.rpow_pos_of_pos hΔ _
  have hrdn : rootDiscriminant K ^ n = |(discr K : ℝ)| := by
    rw [rootDiscriminant, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), ← hn_def, one_div,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (by omega)), Real.rpow_one]
  have hB0 : 0 ≤ 2 * (n : ℝ) * rootDiscriminant K := mul_nonneg (by positivity) hrd0.le
  obtain ⟨v, hvM, hv0, hvR⟩ := exists_short_vector_minkowski (2 * n) (by omega) (zmap ι M) (Real.sqrt (2 * n * rootDiscriminant K))
    (Real.sqrt_nonneg _) (by rw [hcov, hcL]; exact minkowski_discriminant_ineq n hn _ _ hΔ hrdn hrd0)
  obtain ⟨x, hxM, rfl⟩ := hvM
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hv0 (map_zero ι)
  refine ⟨x, hxM, hx0, fun φ => ?_⟩
  have h1 := norm_embedding_le_trace (h x x) (conj_inner_self_nonneg hK h e hli hsp he x) φ
  have h2 : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ‖ι x‖ ^ 2 := by
    rw [← hι x x, real_inner_self_eq_norm_sq]
  have h3 : ‖ι x‖ ^ 2 < 2 * n * rootDiscriminant K := by
    have := pow_lt_pow_left₀ hvR (norm_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt hB0] at this
  linarith

end Formalism.MainNotions.BridgeLemma₂

end
