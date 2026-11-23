import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

open Topology Filter

namespace GlobalTheory.PowerImageOpen

variable {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  {O : Type} [CommRing O] [Algebra O LL]

def powImage (l : ℕ) (LL O : Type) [Field LL] [CommRing O] [Algebra O LL] (n : ℕ) : Set LL :=
  (fun y => (l : LL) ^ n * y) '' Set.range (algebraMap O LL)

omit [TopologicalSpace LL] in
lemma natCast_ne_zero' : (l : LL) ≠ 0 := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rw [← map_natCast (algebraMap ℚ_[l] LL) l]
  exact (map_ne_zero (algebraMap ℚ_[l] LL)).2 hl

omit [TopologicalSpace LL] in
lemma pow_mul_eq_smul (n : ℕ) (y : LL) : (l : LL) ^ n * y = (l : ℚ_[l]) ^ n • y := by
  rw [Algebra.smul_def, map_pow, map_natCast]

omit [Fact l.Prime] [Algebra ℚ_[l] LL] [TopologicalSpace LL] in
lemma mem_powImage_iff (hinj : Function.Injective (algebraMap O LL)) (n : ℕ) (o : O) :
    algebraMap O LL o ∈ powImage l LL O n ↔ o ∈ Ideal.span {(l : O) ^ n} := by
  simp only [powImage, Set.mem_image, Set.mem_range, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, hp⟩
    refine ⟨p, hinj ?_⟩
    rw [map_mul, map_pow, map_natCast]
    exact hp.symm
  · rintro ⟨p, rfl⟩
    exact ⟨algebraMap O LL p, ⟨p, rfl⟩, by rw [map_mul, map_pow, map_natCast]⟩

lemma isOpen_powImage [IsTopologicalRing LL] (ho : IsOpen (Set.range (algebraMap O LL))) (n : ℕ) :
    IsOpen (powImage l LL O n) := by
  have hc : ((l : LL) ^ n) ≠ 0 := pow_ne_zero _ (natCast_ne_zero' (l := l) (LL := LL))
  exact (Homeomorph.mulLeft₀ _ hc).isOpenMap _ ho

omit [Fact l.Prime] [Algebra ℚ_[l] LL] in
lemma isClosed_range [IsTopologicalRing LL] (ho : IsOpen (Set.range (algebraMap O LL))) :
    IsClosed (Set.range (algebraMap O LL)) := by
  have hopen : IsOpen ((algebraMap O LL).range.toAddSubgroup : Set LL) := by
    simpa [RingHom.coe_range] using ho
  simpa [RingHom.coe_range] using AddSubgroup.isClosed_of_isOpen _ hopen

lemma isClosed_powImage [IsTopologicalRing LL] (ho : IsOpen (Set.range (algebraMap O LL))) (n : ℕ) :
    IsClosed (powImage l LL O n) := by
  have hc : ((l : LL) ^ n) ≠ 0 := pow_ne_zero _ (natCast_ne_zero' (l := l) (LL := LL))
  exact (Homeomorph.mulLeft₀ _ hc).isClosedMap _ (isClosed_range ho)

lemma norm_l_lt_one : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one

lemma padicInt_mem_range [IsModuleTopology ℚ_[l] LL] [IsTopologicalRing LL]
    (ho : IsOpen (Set.range (algebraMap O LL))) (z : ℤ_[l]) :
    algebraMap ℚ_[l] LL (algebraMap ℤ_[l] ℚ_[l] z) ∈ Set.range (algebraMap O LL) := by
  have h1 : Continuous (algebraMap ℚ_[l] LL) := by
    have h2 : Continuous fun x : ℚ_[l] => x • (1 : LL) := continuous_id.smul continuous_const
    convert h2 using 1
    funext x
    exact Algebra.algebraMap_eq_smul_one x
  have hf : Continuous fun z : ℤ_[l] => algebraMap ℚ_[l] LL (algebraMap ℤ_[l] ℚ_[l] z) :=
    h1.comp (continuous_subtype_val : Continuous fun z : ℤ_[l] => (z : ℚ_[l]))
  have hS : IsClosed {z : ℤ_[l] | algebraMap ℚ_[l] LL (algebraMap ℤ_[l] ℚ_[l] z) ∈ Set.range (algebraMap O LL)} :=
    (isClosed_range ho).preimage hf
  have hN : Set.range (Nat.cast : ℕ → ℤ_[l]) ⊆
      {z : ℤ_[l] | algebraMap ℚ_[l] LL (algebraMap ℤ_[l] ℚ_[l] z) ∈ Set.range (algebraMap O LL)} := by
    rintro _ ⟨k, rfl⟩
    exact ⟨(k : O), by simp⟩
  exact hS.closure_subset_iff.2 hN (PadicInt.denseRange_natCast z)

lemma not_isUnit_l [IsDomain O] [IsDiscreteValuationRing O] [IsModuleTopology ℚ_[l] LL]
    (hinj : Function.Injective (algebraMap O LL))
    (ho : IsOpen (Set.range (algebraMap O LL))) : ¬ IsUnit (l : O) := by
  intro hu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : algebraMap O LL ϖ ≠ 0 := by
    intro h0
    exact hϖ.ne_zero (hinj (h0.trans (map_zero _).symm))
  set y : LL := (algebraMap O LL ϖ)⁻¹ with hy
  have hT : Tendsto (fun k : ℕ => (l : ℚ_[l]) ^ k • y) atTop (𝓝 0) := by
    have h3 := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_l_lt_one (l := l))).smul_const y
    simpa using h3
  obtain ⟨k, q, hq⟩ := (hT.eventually (ho.mem_nhds ⟨0, map_zero _⟩)).exists
  obtain ⟨u, hu'⟩ := hu
  have hul : algebraMap O LL (↑u⁻¹ : O) * (l : LL) = 1 := by
    rw [← map_natCast (algebraMap O LL) l, ← hu', ← map_mul, Units.inv_mul, map_one]
  have hyR : y = algebraMap O LL ((↑u⁻¹ : O) ^ k * q) := by
    rw [map_mul, hq, map_pow, ← pow_mul_eq_smul, ← mul_assoc, ← mul_pow, hul, one_pow, one_mul]
  apply hϖ.not_isUnit
  refine IsUnit.of_mul_eq_one ((↑u⁻¹ : O) ^ k * q) (hinj ?_)
  rw [map_mul, ← hyR, hy, mul_inv_cancel₀ hne, map_one]

omit [TopologicalSpace LL] [Algebra ℚ_[l] LL] [Fact l.Prime] in
lemma eq_zero_of_forall_mem [IsDomain O] [IsDiscreteValuationRing O] (hl : ¬ IsUnit (l : O))
    (o : O) (h : ∀ n, o ∈ Ideal.span {(l : O) ^ n}) : o = 0 := by
  have hI : Ideal.span {(l : O)} ≠ ⊤ := fun h' => hl (Ideal.span_singleton_eq_top.1 h')
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {(l : O)}) hI
  have hmem : o ∈ ⨅ i : ℕ, Ideal.span {(l : O)} ^ i :=
    (Submodule.mem_iInf _).2 fun i => by
      rw [Ideal.span_singleton_pow]
      exact h i
  rw [hK] at hmem
  exact (Submodule.mem_bot O).1 hmem

lemma exists_coords [FiniteDimensional ℚ_[l] LL] [IsModuleTopology ℚ_[l] LL] [IsTopologicalRing LL] :
    ∃ (d : ℕ) (e : LL ≃ₗ[ℚ_[l]] (Fin d → ℚ_[l])), Continuous e ∧ Continuous e.symm := by
  let b := Module.finBasis ℚ_[l] LL
  refine ⟨Module.finrank ℚ_[l] LL, b.equivFun, ?_, ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  · exact IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap

lemma isCompact_ball {d : ℕ} (e : LL ≃ₗ[ℚ_[l]] (Fin d → ℚ_[l])) (he' : Continuous e.symm) (r : ℝ) :
    IsCompact {y : LL | ‖e y‖ ≤ r} := by
  have hEq : {y : LL | ‖e y‖ ≤ r} = e.symm '' Metric.closedBall 0 r := by
    ext y
    constructor
    · intro hy
      exact ⟨e y, by simpa using hy, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  rw [hEq]
  exact (isCompact_closedBall 0 r).image he'

lemma bounded [IsDomain O] [IsDiscreteValuationRing O] [IsModuleTopology ℚ_[l] LL]
    [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (ho : IsOpen (Set.range (algebraMap O LL)))
    {d : ℕ} (e : LL ≃ₗ[ℚ_[l]] (Fin d → ℚ_[l])) (he : Continuous e) (he' : Continuous e.symm) :
    ∃ n : ℕ, ∀ x ∈ Set.range (algebraMap O LL), ‖(l : ℚ_[l])‖ ^ n * ‖e x‖ ≤ 1 := by
  set c : ℝ := ‖(l : ℚ_[l])‖ with hc
  have hc0 : 0 < c := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hc1 : c < 1 := norm_l_lt_one
  set K : Set LL := {y | ‖e y‖ ≤ 1} ∩ {y | c ≤ ‖e y‖} with hKdef
  have hK : IsCompact K :=
    (isCompact_ball e he' 1).inter_right (isClosed_le continuous_const (continuous_norm.comp he))
  have hl : ¬ IsUnit (l : O) := not_isUnit_l hinj ho
  have hempty : K ∩ ⋂ j, powImage l LL O j = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
    intro hyK hy
    obtain ⟨_, ⟨o, rfl⟩, hoy⟩ := hy 0
    have hyo : y = algebraMap O LL o := by simpa using hoy.symm
    subst hyo
    have ho0 : o = 0 := eq_zero_of_forall_mem hl o fun j => (mem_powImage_iff hinj j o).1 (hy j)
    have hge : c ≤ ‖e (algebraMap O LL o)‖ := hyK.2
    rw [ho0, map_zero, map_zero, norm_zero] at hge
    exact absurd hge (not_le.2 hc0)
  have hanti : Antitone fun j : ℕ => powImage l LL O j := by
    intro i j hij y hy
    obtain ⟨_, ⟨p, rfl⟩, rfl⟩ := hy
    refine ⟨algebraMap O LL ((l : O) ^ (j - i) * p), ⟨_, rfl⟩, ?_⟩
    show (l : LL) ^ i * algebraMap O LL ((l : O) ^ (j - i) * p) = (l : LL) ^ j * algebraMap O LL p
    rw [map_mul, map_pow, map_natCast, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hij]
  obtain ⟨J, hJ⟩ := hK.elim_directed_family_closed (fun j => powImage l LL O j)
    (fun j => isClosed_powImage ho j) hempty hanti.directed_ge
  refine ⟨J, ?_⟩
  rintro x ⟨p, rfl⟩
  by_cases hx1 : ‖e (algebraMap O LL p)‖ ≤ 1
  · calc c ^ J * ‖e (algebraMap O LL p)‖ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hc0.le hc1.le) hx1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [not_le] at hx1
    set N := ‖e (algebraMap O LL p)‖ with hN
    have hex : ∃ j : ℕ, c ^ j * N ≤ 1 := by
      have ht : Tendsto (fun j : ℕ => c ^ j * N) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1).mul_const N
      exact (ht.eventually (ge_mem_nhds zero_lt_one)).exists
    classical
    set j := Nat.find hex with hjdef
    have hj : c ^ j * N ≤ 1 := Nat.find_spec hex
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hj
      linarith
    have hjm : ¬ c ^ (j - 1) * N ≤ 1 := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hj0) one_pos)
    by_contra hcon
    rw [not_le] at hcon
    have hJj : J ≤ j := by
      by_contra hlt
      rw [not_le] at hlt
      have h3 : c ^ J ≤ c ^ j := pow_le_pow_of_le_one hc0.le hc1.le hlt.le
      have h4 : c ^ J * N ≤ c ^ j * N := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      linarith
    have hnorm : ‖e ((l : LL) ^ j * algebraMap O LL p)‖ = c ^ j * N := by
      rw [pow_mul_eq_smul, map_smul, norm_smul, norm_pow]
    have hyK : (l : LL) ^ j * algebraMap O LL p ∈ K := by
      refine ⟨?_, ?_⟩
      · show ‖e _‖ ≤ 1
        rw [hnorm]
        exact hj
      · show c ≤ ‖e _‖
        rw [hnorm]
        have h1 : 1 < c ^ (j - 1) * N := not_le.1 hjm
        have h2 : c ^ j * N = c * (c ^ (j - 1) * N) := by
          rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
        rw [h2]
        nlinarith
    have hyJ : (l : LL) ^ j * algebraMap O LL p ∈ powImage l LL O J :=
      hanti hJj (show _ ∈ powImage l LL O j from ⟨_, ⟨p, rfl⟩, rfl⟩)
    have hmem : (l : LL) ^ j * algebraMap O LL p ∈ K ∩ powImage l LL O J := ⟨hyK, hyJ⟩
    rw [hJ] at hmem
    exact hmem

lemma integral_of_bounded [IsModuleTopology ℚ_[l] LL] [IsTopologicalRing LL]
    (ho : IsOpen (Set.range (algebraMap O LL)))
    {d : ℕ} (e : LL ≃ₗ[ℚ_[l]] (Fin d → ℚ_[l])) (n : ℕ)
    (hb : ∀ x ∈ Set.range (algebraMap O LL), ‖(l : ℚ_[l])‖ ^ n * ‖e x‖ ≤ 1)
    (x : LL) (hx : x ∈ Set.range (algebraMap O LL)) :
    ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem x := by
  let _ : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  have hsmul : ∀ (z : ℤ_[l]) (w : LL), z • w = (z : ℚ_[l]) • w := fun z w => by
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  let v : Fin d → LL := fun i => e.symm (((l : ℚ_[l]) ^ n)⁻¹ • Pi.single i 1)
  let M : Submodule ℤ_[l] LL := Submodule.span ℤ_[l] (Set.range v)
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range v)
  have hRM : ∀ y ∈ Set.range (algebraMap O LL), y ∈ M := by
    intro y hy
    have hcoord : ∀ i, ‖(l : ℚ_[l]) ^ n * e y i‖ ≤ 1 := fun i => by
      rw [norm_mul, norm_pow]
      exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm (e y) i) (pow_nonneg (norm_nonneg _) _)).trans (hb y hy)
    let z : Fin d → ℤ_[l] := fun i => ⟨(l : ℚ_[l]) ^ n * e y i, hcoord i⟩
    have hy' : y = ∑ i, z i • v i := by
      apply e.injective
      simp only [hsmul, v, map_sum, map_smul, LinearEquiv.apply_symm_apply]
      ext j
      simp [z, Finset.sum_apply, Pi.single_apply, smul_smul]
      rw [mul_comm ((l : ℚ_[l]) ^ n) (e y j), mul_inv_cancel_right₀ (pow_ne_zero _ hl0)]
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let SR : Subalgebra ℤ_[l] LL :=
    { (algebraMap O LL).range with
      algebraMap_mem' := fun z => padicInt_mem_range ho z }
  have hsub : Subalgebra.toSubmodule (Algebra.adjoin ℤ_[l] {x}) ≤ M := fun w hw =>
    hRM w (Algebra.adjoin_le (show {x} ⊆ (SR : Set LL) from Set.singleton_subset_iff.2 hx) hw)
  have : IsNoetherian ℤ_[l] M := isNoetherian_of_fg_of_noetherian M hMfg
  have : IsNoetherian ℤ_[l] (Subalgebra.toSubmodule (Algebra.adjoin ℤ_[l] {x})) := isNoetherian_of_le hsub
  exact isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ_[l] {x}) ‹_› x (Algebra.subset_adjoin (Set.mem_singleton x))

lemma mem_of_integral [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    [IsModuleTopology ℚ_[l] LL] [IsTopologicalRing LL]
    (ho : IsOpen (Set.range (algebraMap O LL))) (x : LL)
    (hx : ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem x) :
    x ∈ Set.range (algebraMap O LL) := by
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have hf : ∀ z : ℤ_[l], ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) z ∈ (algebraMap O LL).range :=
    fun z => padicInt_mem_range ho z
  let e₁ : O ≃+* (algebraMap O LL).range :=
    RingEquiv.ofBijective (algebraMap O LL).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap O LL).rangeRestrict_surjective⟩
  let g : ℤ_[l] →+* O := e₁.symm.toRingHom.comp (((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).codRestrict _ hf)
  have hg : (algebraMap O LL).comp g = (algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l]) := by
    ext z
    exact congrArg Subtype.val
      (e₁.apply_symm_apply (((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).codRestrict _ hf z))
  obtain ⟨p, hpm, hp⟩ := hx
  have hint : IsIntegral O x := ⟨p.map g, hpm.map g, by rw [Polynomial.eval₂_map, hg]; exact hp⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := LL)).1 hint
  exact ⟨y, hy⟩

lemma finite_quotient [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (ho : IsOpen (Set.range (algebraMap O LL))) (hc : IsCompact (Set.range (algebraMap O LL)))
    (n : ℕ) : Finite (O ⧸ Ideal.span {(l : O) ^ n}) := by
  let tO : TopologicalSpace O := TopologicalSpace.induced (algebraMap O LL) ‹TopologicalSpace LL›
  have hemb : Topology.IsEmbedding (algebraMap O LL) := ⟨⟨rfl⟩, hinj⟩
  have : IsTopologicalAddGroup O := topologicalAddGroup_induced (algebraMap O LL)
  have : CompactSpace O := ⟨hemb.isCompact_iff.2 (by simpa [Set.image_univ] using hc)⟩
  have hopen : IsOpen ((Ideal.span {(l : O) ^ n} : Ideal O) : Set O) :=
    isOpen_induced_iff.2 ⟨powImage l LL O n, isOpen_powImage ho n, by
      ext o
      exact mem_powImage_iff hinj n o⟩
  exact AddSubgroup.quotient_finite_of_isOpen (Ideal.span {(l : O) ^ n}).toAddSubgroup hopen

lemma adicComplete [IsDomain O] [IsDiscreteValuationRing O] [IsModuleTopology ℚ_[l] LL]
    [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (ho : IsOpen (Set.range (algebraMap O LL))) (hc : IsCompact (Set.range (algebraMap O LL))) :
    IsAdicComplete (Ideal.span {(l : O)}) O := by
  have hsm : ∀ n : ℕ, (Ideal.span {(l : O)} ^ n • ⊤ : Submodule O O) = Ideal.span {(l : O) ^ n} := fun n => by
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have hl : ¬ IsUnit (l : O) := not_isUnit_l hinj ho
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    refine eq_zero_of_forall_mem hl x fun n => ?_
    have h1 := hx n
    rw [hsm, SModEq.sub_mem, sub_zero] at h1
    exact h1
  · intro f hf
    obtain ⟨a, ⟨L, rfl⟩, hcl⟩ := hc.exists_clusterPt (f := Filter.map (fun k => algebraMap O LL (f k)) atTop)
      (Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' fun k => ⟨f k, rfl⟩)))
    refine ⟨L, fun n => ?_⟩
    rw [hsm, SModEq.sub_mem]
    have hC : IsClosed {y : LL | y - algebraMap O LL (f n) ∈ powImage l LL O n} :=
      (isClosed_powImage ho n).preimage (continuous_id.sub continuous_const)
    have hev : {y : LL | y - algebraMap O LL (f n) ∈ powImage l LL O n} ∈
        Filter.map (fun k => algebraMap O LL (f k)) atTop := by
      rw [Filter.mem_map]
      filter_upwards [eventually_ge_atTop n] with k hk
      have h2 := hf hk
      rw [hsm, SModEq.sub_mem] at h2
      show algebraMap O LL (f k) - algebraMap O LL (f n) ∈ powImage l LL O n
      rw [← map_sub]
      have h3 : f k - f n ∈ Ideal.span {(l : O) ^ n} := by
        have h4 := (Ideal.neg_mem_iff (I := Ideal.span {(l : O) ^ n})).2 h2
        rwa [neg_sub] at h4
      exact (mem_powImage_iff hinj n _).2 h3
    have hL := hC.closure_subset (hcl.mem_closure_of_mem _ hev)
    have hL' : L - f n ∈ Ideal.span {(l : O) ^ n} := by
      apply (mem_powImage_iff hinj n _).1
      rw [map_sub]
      exact hL
    have h5 := (Ideal.neg_mem_iff (I := Ideal.span {(l : O) ^ n})).2 hL'
    rwa [neg_sub] at h5

theorem main (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL] (h : Formalism.MainNotions.N.GoodO (Qp := ℚ_[l]) LL O) :
    (∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔
      ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem x) ∧
    IsCompact (Set.range (algebraMap O LL)) ∧
    (∀ n : ℕ, Finite (O ⧸ Ideal.span {(l : O) ^ n})) ∧
    IsAdicComplete (Ideal.span {(l : O)}) O := by
  obtain ⟨⟨hD, hDVR, hFr⟩, hfd, hmt, htr, ho⟩ := h
  have := hD
  have := hDVR
  have := hFr
  have := hfd
  have := hmt
  have := htr
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  obtain ⟨d, e, he, he'⟩ := exists_coords (l := l) (LL := LL)
  obtain ⟨n, hb⟩ := bounded hinj ho e he he'
  have hpos : 0 < ‖(l : ℚ_[l])‖ ^ n :=
    pow_pos (norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) n
  have hsub : Set.range (algebraMap O LL) ⊆ {y : LL | ‖e y‖ ≤ 1 / ‖(l : ℚ_[l])‖ ^ n} := by
    intro y hy
    show ‖e y‖ ≤ 1 / ‖(l : ℚ_[l])‖ ^ n
    rw [le_div_iff₀ hpos, mul_comm]
    exact hb y hy
  have hcpt : IsCompact (Set.range (algebraMap O LL)) :=
    (isCompact_ball e he' _).of_isClosed_subset (isClosed_range ho) hsub
  exact ⟨fun x => ⟨fun hx => integral_of_bounded ho e n hb x hx, fun hx => mem_of_integral ho x hx⟩, hcpt,
    fun k => finite_quotient hinj ho hcpt k, adicComplete hinj ho hcpt⟩

end GlobalTheory.PowerImageOpen
