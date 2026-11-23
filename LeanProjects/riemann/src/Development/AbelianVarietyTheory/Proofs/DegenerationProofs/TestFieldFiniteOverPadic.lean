import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.FieldOfTest

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open IntermediateField in
variable (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [NormedField F] [Algebra (FractionRing V) F] in
variable (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [NormedField F] [Algebra (FractionRing V) F] in
private lemma norm_uniformizer_pos_and_lt_one
    (h : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) {ϖ : V} (hϖ : Irreducible ϖ) :
    0 < ‖algebraMap _ F (algebraMap V (FractionRing V) ϖ)‖ ∧
      ‖algebraMap _ F (algebraMap V (FractionRing V) ϖ)‖ < 1 := by
  have h0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  refine ⟨norm_pos_iff.2 ((map_ne_zero _).2 h0), lt_of_not_ge fun hge => hϖ.not_isUnit ?_⟩
  have hle : ‖algebraMap _ F (algebraMap V (FractionRing V) ϖ)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, norm_inv]
    exact inv_le_one_of_one_le₀ hge
  obtain ⟨z, hz⟩ := (h _).1 hle
  refine IsUnit.of_mul_eq_one z ?_
  apply IsFractionRing.injective V (FractionRing V)
  rw [map_mul, map_one, hz]
  exact mul_inv_cancel₀ h0

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open IntermediateField in
variable (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [NormedField F] [Algebra (FractionRing V) F] in
variable (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [NormedField F] [Algebra (FractionRing V) F] in
private lemma dvd_of_norm_le_pow
    (h : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) {ϖ : V} (hϖ : Irreducible ϖ) (n : ℕ) (x : V)
    (hx : ‖algebraMap _ F (algebraMap V (FractionRing V) x)‖ ≤
      ‖algebraMap _ F (algebraMap V (FractionRing V) ϖ)‖ ^ n) : ϖ ^ n ∣ x := by
  have h0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  have hpos := (norm_uniformizer_pos_and_lt_one V F h hϖ).1
  have hle : ‖algebraMap _ F (algebraMap V (FractionRing V) x /
      algebraMap V (FractionRing V) ϖ ^ n)‖ ≤ 1 := by
    rw [map_div₀, norm_div, map_pow, norm_pow]
    exact div_le_one_of_le₀ hx (by positivity)
  obtain ⟨z, hz⟩ := (h _).1 hle
  refine ⟨z, IsFractionRing.injective V (FractionRing V) ?_⟩
  rw [map_mul, map_pow, hz, mul_div_cancel₀ _ (pow_ne_zero _ h0)]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open IntermediateField in

theorem _root_.GlobalTheory.ZH.FieldOfTest.isComplete_range_fractionRing (V F : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [NormedField F] [Algebra (FractionRing V) F]
    (h : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) :
    IsComplete (Set.range (algebraMap (FractionRing V) F)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  set ιV := algebraMap V (FractionRing V) with hιV
  set φ := algebraMap (FractionRing V) F with hφ
  obtain ⟨hc0, hc1⟩ := norm_uniformizer_pos_and_lt_one V F h hϖ
  set c := ‖φ (ιV ϖ)‖ with hc
  have h0 : ιV ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  have hnorm_dvd : ∀ (n : ℕ) (y : V), ϖ ^ n ∣ y → ‖φ (ιV y)‖ ≤ c ^ n := by
    rintro n y ⟨z, rfl⟩
    rw [map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow]
    exact mul_le_of_le_one_right (by positivity) ((h _).2 ⟨z, rfl⟩)
  rw [← completeSpace_coe_iff_isComplete]
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  set v : ℕ → F := fun n => (u n : F) with hv
  have hvc : CauchySeq v := uniformContinuous_subtype_val.comp_cauchySeq hu
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 hvc.isBounded_range
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (|B| + 1) by positivity) hc1
  have hw : ∀ n, ∃ x : V, φ (ιV x) = φ (ιV ϖ) ^ k * v n := by
    intro n
    obtain ⟨t, ht⟩ := (u n).2
    have hle' : ‖φ (ιV ϖ ^ k * t)‖ ≤ 1 := by
      rw [map_mul, norm_mul, map_pow, norm_pow, ht]
      have hBn : ‖v n‖ ≤ |B| + 1 := (hB _ ⟨n, rfl⟩).trans (by linarith [le_abs_self B])
      calc c ^ k * ‖v n‖ ≤ c ^ k * (|B| + 1) := by gcongr
        _ ≤ 1 / (|B| + 1) * (|B| + 1) := by gcongr
        _ = 1 := by field_simp
    obtain ⟨x, hx⟩ := (h _).1 hle'
    exact ⟨x, by rw [hx, map_mul, map_pow, ht]⟩
  choose x hx using hw
  have hxc : ∀ m : ℕ, ∃ N, ∀ a ≥ N, ∀ b ≥ N, ϖ ^ m ∣ x a - x b := by
    intro m
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hvc (c ^ m / c ^ k) (by positivity)
    refine ⟨N, fun a ha b hb => dvd_of_norm_le_pow V F h hϖ m _ ?_⟩
    have hd := hN a ha b hb
    rw [dist_eq_norm] at hd
    rw [map_sub, map_sub, hx, hx, ← mul_sub, norm_mul, norm_pow]
    have := (lt_div_iff₀' (by positivity : (0:ℝ) < c ^ k)).1 hd
    exact this.le
  choose N hN using hxc
  set M : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup N + m with hM
  have hMN : ∀ m, N m ≤ M m := fun m =>
    (Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_self m))).trans (Nat.le_add_right _ _)
  have hMmono : StrictMono M := by
    refine strictMono_nat_of_lt_succ fun m => ?_
    have : (Finset.range (m + 1)).sup N ≤ (Finset.range (m + 1 + 1)).sup N :=
      Finset.sup_mono (Finset.range_mono (Nat.le_succ _))
    simp only [hM]
    omega
  obtain ⟨ℓ, hℓ⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal V) (M := V)
    IsAdicComplete.toIsPrecomplete (f := fun m => x (M m)) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hϖ.maximalIdeal_eq,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hN m _ (hMN m) _ ((hMN m).trans (hMmono.monotone hmn)))
  have hlim : Filter.Tendsto (fun m => v (M m)) Filter.atTop
      (nhds (φ (ιV ℓ) / φ (ιV ϖ) ^ k)) := by
    have hdiff : Filter.Tendsto (fun m => φ (ιV (x (M m)))) Filter.atTop (nhds (φ (ιV ℓ))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1)
      rw [← map_sub, ← map_sub]
      apply hnorm_dvd
      have := hℓ m
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hϖ.maximalIdeal_eq,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
      exact this
    have hk0 : φ (ιV ϖ) ^ k ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 h0)
    refine (hdiff.div_const (φ (ιV ϖ) ^ k)).congr fun m => ?_
    simp only [hx]
    field_simp
  refine ⟨⟨φ (ιV ℓ / ιV ϖ ^ k), ιV ℓ / ιV ϖ ^ k, rfl⟩, ?_⟩
  rw [tendsto_subtype_rng]
  have := tendsto_nhds_of_cauchySeq_of_subseq hvc hMmono.tendsto_atTop hlim
  simpa [map_div₀, map_pow] using this

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open IntermediateField in
private lemma finrank_le_of_le_of_adjoin_finrank_le {K E : Type} [Field K] [Field E] [Algebra K E]
    [CharZero K] (N : ℕ) (F : IntermediateField K E)
    (h : ∀ x ∈ F, Module.finrank K K⟮x⟯ ≤ N) (E' : IntermediateField K E) (hE' : E' ≤ F)
    [FiniteDimensional K E'] : Module.finrank K E' ≤ N := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E'
  have hint : IsIntegral K α := IsIntegral.of_finite K α
  have h1 : Module.finrank K E' = (minpoly K α).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top']
  have h2 : (minpoly K α).natDegree = Module.finrank K K⟮(α : E)⟯ := by
    have hint' : IsIntegral K (α : E) := hint.map E'.val
    rw [IntermediateField.adjoin.finrank hint', IntermediateField.minpoly_eq]
  rw [h1, h2]
  exact h _ (hE' α.2)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open IntermediateField in
private lemma finiteDimensional_of_finrank_adjoin_le {K E : Type} [Field K] [Field E] [Algebra K E]
    [CharZero K] (N : ℕ) (F : IntermediateField K E) (halg : ∀ x ∈ F, IsIntegral K x)
    (h : ∀ x ∈ F, Module.finrank K K⟮x⟯ ≤ N) : FiniteDimensional K F := by
  classical
  let P : ℕ → Prop := fun d => ∃ E' : IntermediateField K E, E' ≤ F ∧
    FiniteDimensional K E' ∧ Module.finrank K E' = d
  have hP1 : P 1 := ⟨⊥, bot_le, inferInstance, IntermediateField.finrank_bot⟩
  have hbound : ∀ d, P d → d ≤ N := by
    rintro d ⟨E', hE'F, hfin, rfl⟩
    exact finrank_le_of_le_of_adjoin_finrank_le N F h E' hE'F
  obtain ⟨E', hE'F, hfin, hE'd⟩ := Nat.findGreatest_spec (hbound 1 hP1) hP1
  have hmax : ∀ E'' : IntermediateField K E, E'' ≤ F → FiniteDimensional K E'' →
      Module.finrank K E'' ≤ Module.finrank K E' := by
    intro E'' hE'' hfin''
    rw [hE'd]
    exact Nat.le_findGreatest (hbound _ ⟨E'', hE'', hfin'', rfl⟩) ⟨E'', hE'', hfin'', rfl⟩
  have hFE : F ≤ E' := by
    intro x hx
    have hfx : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional (halg x hx)
    have hle : E' ≤ E' ⊔ K⟮x⟯ := le_sup_left
    have heq : E' = E' ⊔ K⟮x⟯ := IntermediateField.eq_of_le_of_finrank_le hle
      (hmax _ (sup_le hE'F ((IntermediateField.adjoin_simple_le_iff).2 hx)) inferInstance)
    rw [heq]
    exact (le_sup_right : K⟮x⟯ ≤ E' ⊔ K⟮x⟯) (IntermediateField.mem_adjoin_simple_self K x)
  obtain rfl : F = E' := le_antisymm hFE hE'F
  exact hfin

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open IntermediateField in

theorem _root_.GlobalTheory.ZH.FieldOfTest.exists_finiteDimensional_of_isComplete (p : ℕ) [Fact p.Prime]
    (L : Subfield (PadicAlgCl p)) (hL : IsComplete (L : Set (PadicAlgCl p))) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      (K : Set (PadicAlgCl p)) = L := by
  classical
  have hQ : ∀ a : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) a ∈ L := by
    intro a
    have hcl : IsClosed (L : Set (PadicAlgCl p)) := hL.isClosed
    have hmem := map_mem_closure (continuous_algebraMap ℚ_[p] (PadicAlgCl p))
      (Padic.denseRange_ratCast (p := p) a) (t := (L : Set (PadicAlgCl p))) (by
        rintro _ ⟨q, rfl⟩
        simpa using SubfieldClass.ratCast_mem L q)
    rwa [hcl.closure_eq] at hmem
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) := { L with algebraMap_mem' := hQ }
  haveI : CompleteSpace L := hL.completeSpace_coe
  have hc : Continuous (fun z : ℤ_[p] => algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])) :=
    (continuous_algebraMap ℚ_[p] (PadicAlgCl p)).comp continuous_subtype_val
  let A : ℕ → Set L := fun n => {x | ∃ c : Fin (n + 1) → ℤ_[p], (∃ i, ‖c i‖ = 1) ∧
    ∑ i, algebraMap ℚ_[p] (PadicAlgCl p) (c i : ℚ_[p]) * (x : PadicAlgCl p) ^ (i : ℕ) = 0}
  have hAclosed : ∀ n, IsClosed (A n) := by
    intro n
    have hA : A n = Prod.snd '' {q : (Fin (n + 1) → ℤ_[p]) × L | (∃ i, ‖q.1 i‖ = 1) ∧
        ∑ i, algebraMap ℚ_[p] (PadicAlgCl p) (q.1 i : ℚ_[p]) * (q.2 : PadicAlgCl p) ^ (i : ℕ)
          = 0} := by
      ext x
      simp [A]
    rw [hA]
    apply isClosedMap_snd_of_compactSpace
    apply IsClosed.inter
    · have hset : {q : (Fin (n + 1) → ℤ_[p]) × L | ∃ i, ‖q.1 i‖ = 1} =
          ⋃ i, {q : (Fin (n + 1) → ℤ_[p]) × L | ‖q.1 i‖ = 1} := by
        ext q
        simp
      have hcl : IsClosed {q : (Fin (n + 1) → ℤ_[p]) × L | ∃ i, ‖q.1 i‖ = 1} := by
        rw [hset]
        exact isClosed_iUnion_of_finite fun i =>
          isClosed_eq (continuous_norm.comp ((continuous_apply i).comp continuous_fst))
            continuous_const
      exact hcl
    · exact isClosed_eq (continuous_finset_sum _ fun i _ =>
        (hc.comp ((continuous_apply i).comp continuous_fst)).mul
          ((continuous_subtype_val.comp continuous_snd).pow _)) continuous_const
  have hcover : ⋃ n, A n = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨f, hf0, hfx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[p]) (x : PadicAlgCl p)
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.range (f.natDegree + 1))
      (fun i => ‖f.coeff i‖) ⟨f.natDegree, by simp⟩
    have hc0 : f.coeff i₀ ≠ 0 := by
      intro h0
      apply hf0
      have := hmax f.natDegree (by simp)
      rw [h0, norm_zero] at this
      exact Polynomial.leadingCoeff_eq_zero.1 (norm_le_zero_iff.1 this)
    let c : Fin (f.natDegree + 1) → ℤ_[p] := fun i => ⟨f.coeff i / f.coeff i₀, by
      rw [norm_div]
      exact div_le_one_of_le₀ (hmax i (Finset.mem_range.2 i.2)) (norm_nonneg _)⟩
    refine ⟨f.natDegree, c, ⟨⟨i₀, Finset.mem_range.1 hi₀⟩, ?_⟩, ?_⟩
    · show ‖f.coeff i₀ / f.coeff i₀‖ = 1
      rw [div_self hc0, norm_one]
    · have hsum : ∑ i : Fin (f.natDegree + 1), algebraMap ℚ_[p] (PadicAlgCl p) (c i : ℚ_[p]) *
          (x : PadicAlgCl p) ^ (i : ℕ) = (algebraMap ℚ_[p] (PadicAlgCl p) (f.coeff i₀))⁻¹ *
          ∑ i ∈ Finset.range (f.natDegree + 1),
            algebraMap ℚ_[p] (PadicAlgCl p) (f.coeff i) * (x : PadicAlgCl p) ^ i := by
        rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        show algebraMap ℚ_[p] (PadicAlgCl p) (f.coeff i / f.coeff i₀) * _ = _
        rw [map_div₀, div_eq_inv_mul, _root_.mul_assoc]
      rw [hsum, Polynomial.aeval_eq_sum_range] at *
      simp only [Algebra.smul_def] at hfx
      rw [hfx, mul_zero]
  obtain ⟨n, a, ha⟩ := nonempty_interior_of_iUnion_of_closed hAclosed hcover
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior a ha
  have hdeg : ∀ y : L, y ∈ A n → (minpoly ℚ_[p] (y : PadicAlgCl p)).natDegree ≤ n := by
    rintro y ⟨c, ⟨i, hi⟩, hsum⟩
    let g : Polynomial ℚ_[p] :=
      ∑ j : Fin (n + 1), Polynomial.C (c j : ℚ_[p]) * Polynomial.X ^ (j : ℕ)
    have hgi : g.coeff i = c i := by
      simp [g, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj]
    have hg0 : g ≠ 0 := by
      intro h0
      rw [h0, Polynomial.coeff_zero] at hgi
      have : ‖c i‖ = 0 := by
        show ‖(c i : ℚ_[p])‖ = 0
        rw [← hgi, norm_zero]
      rw [hi] at this
      exact one_ne_zero this
    have hgy : Polynomial.aeval (y : PadicAlgCl p) g = 0 := by
      simpa [g, map_sum] using hsum
    have hgdeg : g.natDegree ≤ n :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ =>
        (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 j.2)
    exact (Polynomial.natDegree_le_natDegree
      (minpoly.degree_le_of_ne_zero ℚ_[p] _ hg0 hgy)).trans hgdeg
  have hint : ∀ z : PadicAlgCl p, IsIntegral ℚ_[p] z := fun z => Algebra.IsIntegral.isIntegral z
  have hfr : ∀ y : L, y ∈ A n → Module.finrank ℚ_[p] ℚ_[p]⟮(y : PadicAlgCl p)⟯ ≤ n := by
    intro y hy
    rw [IntermediateField.adjoin.finrank (hint _)]
    exact hdeg y hy
  refine ⟨K, ?_, rfl⟩
  refine finiteDimensional_of_finrank_adjoin_le (n * n) K (fun x _ => hint x) fun x hx => ?_
  have hp1 : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < r / (‖x‖ + 1) by positivity) hp1
  let b : L := a + ⟨(p : PadicAlgCl p) ^ j * x, L.mul_mem (L.pow_mem (_root_.natCast_mem L p) j) hx⟩
  have hb : b ∈ A n := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    show ‖(a : PadicAlgCl p) + (p : PadicAlgCl p) ^ j * x - a‖ < r
    rw [add_sub_cancel_left, norm_mul, norm_pow]
    calc ‖(p : PadicAlgCl p)‖ ^ j * ‖x‖ ≤ r / (‖x‖ + 1) * ‖x‖ := by gcongr
      _ < r := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg x]
  have ha' : a ∈ A n := interior_subset ha
  haveI := IntermediateField.adjoin.finiteDimensional (hint (a : PadicAlgCl p))
  haveI := IntermediateField.adjoin.finiteDimensional (hint (b : PadicAlgCl p))
  have hxmem : x ∈ ℚ_[p]⟮(a : PadicAlgCl p)⟯ ⊔ ℚ_[p]⟮(b : PadicAlgCl p)⟯ := by
    have hpj : ((p : PadicAlgCl p) ^ j) ≠ 0 := pow_ne_zero _ (by
      have := (Fact.out : p.Prime).ne_zero
      exact_mod_cast this)
    have hx' : x = ((b : PadicAlgCl p) - a) / (p : PadicAlgCl p) ^ j := by
      show x = ((a : PadicAlgCl p) + (p : PadicAlgCl p) ^ j * x - a) / _
      field_simp
      ring
    rw [hx']
    refine div_mem (sub_mem ((le_sup_right : ℚ_[p]⟮(b : PadicAlgCl p)⟯ ≤ _)
      (IntermediateField.mem_adjoin_simple_self _ _))
      ((le_sup_left : ℚ_[p]⟮(a : PadicAlgCl p)⟯ ≤ _)
      (IntermediateField.mem_adjoin_simple_self _ _))) (pow_mem (_root_.natCast_mem _ p) j)
  calc Module.finrank ℚ_[p] ℚ_[p]⟮x⟯
      ≤ Module.finrank ℚ_[p] ↥(ℚ_[p]⟮(a : PadicAlgCl p)⟯ ⊔ ℚ_[p]⟮(b : PadicAlgCl p)⟯) :=
        IntermediateField.finrank_le_of_le_right
          ((IntermediateField.adjoin_simple_le_iff).2 hxmem)
    _ ≤ Module.finrank ℚ_[p] ℚ_[p]⟮(a : PadicAlgCl p)⟯ *
          Module.finrank ℚ_[p] ℚ_[p]⟮(b : PadicAlgCl p)⟯ :=
        IntermediateField.finrank_sup_le _ _
    _ ≤ n * n := Nat.mul_le_mul (hfr a ha') (hfr b hb)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open IntermediateField in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.ZH.FieldOfTest.fractionRing_finite_over_padic : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    [_root_.GlobalTheory.ZH.ArithBase o Ω] (S : _root_.GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real)
    (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p)
    (u : ρ.UTest p y₀),
    CharZero u.V ∧ IsLocalHom u.j ∧
      Function.Injective u.j ∧
      ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
        (K : Set (PadicAlgCl p)) =
          Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u
  have hinj : Function.Injective u.j := by
    intro x y hxy
    have h := congrArg (fun z : _root_.GlobalTheory.ZH.OO p => (z : PadicAlgCl p)) hxy
    simp only [_root_.GlobalTheory.ZH.ThetaSys.Real.UTest.j] at h
    exact IsFractionRing.injective _ (FractionRing u.V)
      ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective h)
  refine ⟨?_, ?_, hinj, ?_⟩
  · have : CharZero (_root_.GlobalTheory.ZH.OO p) := inferInstance
    exact (RingHom.charZero_iff hinj).2 this
  · refine ⟨fun x hx => ?_⟩
    set F := FractionRing u.V
    set φ := algebraMap F (PadicAlgCl p)
    set y : F := algebraMap u.V F x
    have hjx : ((u.j x : _root_.GlobalTheory.ZH.OO p) :
        PadicAlgCl p) = φ y := rfl
    have hge : 1 ≤ ‖φ y‖ := by
      have := (_root_.GlobalTheory.ZH.not_isUnit_OO_iff (u.j x)).not.1 (not_not.2 hx)
      rw [hjx] at this
      exact not_lt.1 this
    have hy0 : y ≠ 0 := by
      rintro h0
      rw [h0, map_zero, norm_zero] at hge
      exact absurd hge (by norm_num)
    have hle : ‖φ y⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨z, hz⟩ := (u.norm_le y⁻¹).1 hle
    refine IsUnit.of_mul_eq_one z ?_
    apply IsFractionRing.injective u.V F
    rw [map_mul, map_one, hz]
    exact mul_inv_cancel₀ hy0
  · haveI := u.complete
    obtain ⟨K, hK, hKL⟩ := _root_.GlobalTheory.ZH.FieldOfTest.exists_finiteDimensional_of_isComplete p
      (algebraMap (FractionRing u.V) (PadicAlgCl p)).fieldRange
      (by
        rw [RingHom.coe_fieldRange]
        exact _root_.GlobalTheory.ZH.FieldOfTest.isComplete_range_fractionRing _ _ u.norm_le)
    exact ⟨K, hK, by rw [hKL, RingHom.coe_fieldRange]⟩

end GlobalTheory.ZH.FieldOfTest
