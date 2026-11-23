import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Lat
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

omit [NumberField E] in
theorem mem_detSet (M : Submodule (𝓞 E) (Fin n → E)) (d : E) :
    d ∈ detSet M ↔ ∃ v : Matrix (Fin n) (Fin n) E, (∀ i, v i ∈ M) ∧ d = v.det := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, Matrix.det_transpose (Matrix.of v)⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (Matrix.det_transpose v).symm⟩

def detSpan (M : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) E := Submodule.span (𝓞 E) (detSet M)

omit [NumberField E] in
theorem det_mem {M : Submodule (𝓞 E) (Fin n → E)} (v : Matrix (Fin n) (Fin n) E) (hv : ∀ i, v i ∈ M) :
    v.det ∈ detSpan M := Submodule.subset_span ((mem_detSet M _).2 ⟨v, hv, rfl⟩)

omit [NumberField E] in
theorem row_update_mem {M : Submodule (𝓞 E) (Fin n → E)} (v : Matrix (Fin n) (Fin n) E) (hv : ∀ i, v i ∈ M)
    (j : Fin n) (m : Fin n → E) (hm : m ∈ M) (i : Fin n) : v.updateRow j m i ∈ M := by
  by_cases h : i = j
  · subst h; rwa [Matrix.updateRow_self]
  · rw [Matrix.updateRow_ne h]; exact hv i

omit [NumberField E] in
theorem smul_det_mem (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E) (a : 𝓞 E) (ha : a • m ∈ M')
    (w : Matrix (Fin n) (Fin n) E) (hw : ∀ i, w i ∈ M' ⊔ Submodule.span (𝓞 E) {m}) :
    a • w.det ∈ detSpan M' := by
  classical
  have dec : ∀ x ∈ M' ⊔ Submodule.span (𝓞 E) {m}, ∃ v ∈ M', ∃ t : 𝓞 E, x = v + t • m := by
    intro x hx
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨v, hv, t, rfl⟩
  have key : ∀ s : Finset (Fin n), ∀ w : Matrix (Fin n) (Fin n) E,
      (∀ i, w i ∈ M' ⊔ Submodule.span (𝓞 E) {m}) → (∀ i, i ∉ s → w i ∈ M') → a • w.det ∈ detSpan M' := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro w _ h; exact Submodule.smul_mem _ _ (det_mem w fun i => h i (by simp))
    | insert j s hj ih =>
      intro w hw h
      choose v hv t ht using fun i => dec _ (hw i)
      have e1 : w.det = (w.updateRow j (v j)).det + (t j : E) * (w.updateRow j m).det := by
        conv_lhs => rw [← Matrix.updateRow_eq_self w j, ht j]
        rw [Matrix.det_updateRow_add, ← Matrix.det_updateRow_smul]
        rfl
      have e2 : (w.updateRow j m).det = ((Matrix.of v).updateRow j m).det := by
        apply Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => if i = j then 0 else (t i : E)) j (by simp)
        intro i k
        by_cases hi : i = j
        · subst hi; simp
        · simp only [Matrix.updateRow_ne hi, hi, if_false, Matrix.updateRow_self, Matrix.of_apply]
          rw [ht i]; rfl
      rw [e1, smul_add]
      refine Submodule.add_mem _ (ih _ (row_update_mem w hw j _ (Submodule.mem_sup_left (hv j))) ?_) ?_
      · intro i hi
        by_cases hij : i = j
        · subst hij; rw [Matrix.updateRow_self]; exact hv i
        · rw [Matrix.updateRow_ne hij]; exact h i (by simp [hij, hi])
      · have e3 : a • ((t j : E) * (w.updateRow j m).det) =
            ((Matrix.of v).updateRow j (t j • a • m)).det := by
          rw [e2]
          change (a : E) * _ = ((Matrix.of v).updateRow j ((t j : E) • (a : E) • m)).det
          rw [Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]; ring
        rw [e3]
        exact det_mem _ (row_update_mem _ hv j _ (M'.smul_mem _ ha))
  exact key Finset.univ w hw (fun i hi => absurd (Finset.mem_univ i) hi)

omit [NumberField E] in
theorem cramer_rows (v : Matrix (Fin n) (Fin n) E) (m : Fin n → E) :
    v.det • m = ∑ i, (v.updateRow i m).det • v i := by
  have h := Matrix.mulVec_cramer v.transpose m
  rw [Matrix.det_transpose] at h
  rw [← h]
  ext k
  simp [Matrix.mulVec, dotProduct, Matrix.cramer_transpose_apply, Finset.sum_apply, mul_comm]

omit [NumberField E] in
theorem detSpan_mono {M' M : Submodule (𝓞 E) (Fin n → E)} (h : M' ≤ M) : detSpan M' ≤ detSpan M := by
  apply Submodule.span_mono
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, fun i => h (hv i), rfl⟩

def Bdd (M : Submodule (𝓞 E) (Fin n → E)) : Prop := ∃ k : 𝓞 E, k ≠ 0 ∧ ∀ v ∈ M, k • v ∈ stdLat E n

omit [NumberField E] in
theorem mem_std (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = v j := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]

omit [NumberField E] in
theorem frac_of_bdd {M : Submodule (𝓞 E) (Fin n → E)} (h : Bdd M) :
    IsFractional (nonZeroDivisors (𝓞 E)) (detSpan M) := by
  obtain ⟨k, hk, h⟩ := h
  apply FractionalIdeal.isFractional_span_iff.2
  refine ⟨k ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hk), ?_⟩
  intro d hd
  obtain ⟨v, hv, rfl⟩ := (mem_detSet M d).1 hd
  choose b hb using fun i => (mem_std _).1 (h _ (hv i))
  refine ⟨(Matrix.of b).det, ?_⟩
  rw [RingHom.map_det]
  have : (algebraMap (𝓞 E) E).mapMatrix (Matrix.of b) = (k : E) • v := by
    ext i j
    exact hb i j
  rw [this, Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]

theorem detSpan_cyclic (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E)
    (hb : Bdd (M' ⊔ Submodule.span (𝓞 E) {m})) :
    detSpan M' = (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) •
      detSpan (M' ⊔ Submodule.span (𝓞 E) {m}) := by
  set M := M' ⊔ Submodule.span (𝓞 E) {m} with hM
  have hle : M' ≤ M := le_sup_left
  have hm : m ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self m)
  apply le_antisymm
  · by_cases h0 : detSpan M = ⊥
    · exact (detSpan_mono hle).trans (h0.le.trans bot_le)
    let I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨detSpan M, frac_of_bdd hb⟩
    have hI : I ≠ 0 := fun h => h0 (by
      have := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (J : Submodule (𝓞 E) E)) h
      simp only [FractionalIdeal.coe_zero] at this
      exact this)
    have h1 : detSpan M * ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) = 1 := by
      have := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (J : Submodule (𝓞 E) E))
        (mul_inv_cancel₀ hI)
      simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at this
      exact this
    generalize ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) = J at h1
    have hint : ∀ x ∈ detSpan M, ∀ y ∈ J, ∃ b : 𝓞 E, (b : E) = x * y := by
      intro x hx y hy
      have := Submodule.mul_mem_mul hx hy
      rw [h1] at this
      exact Submodule.mem_one.1 this
    apply Submodule.span_le.2
    intro d hd
    obtain ⟨v, hv, rfl⟩ := (mem_detSet M' d).1 hd
    have h1m : (1 : E) ∈ detSpan M * J := by rw [h1]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    have : ∀ z ∈ detSpan M * J, v.det * z ∈
        (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) • detSpan M := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro x hx y hy
        obtain ⟨b, hb⟩ := hint _ (det_mem v fun i => hle (hv i)) y hy
        have e : v.det * (x * y) = b • x := by
          change _ = (b : E) * x
          rw [hb]; ring
        rw [e]
        refine Submodule.smul_mem_smul ?_ hx
        change b • m ∈ M'
        have e2 : b • m = y • (v.det • m) := by
          change (b : E) • m = _
          rw [hb, smul_smul, mul_comm]
        rw [e2, cramer_rows, Finset.smul_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨b', hb'⟩ := hint _ (det_mem _ (row_update_mem v (fun i => hle (hv i)) i m hm)) y hy
        rw [smul_smul, mul_comm, ← hb']
        exact M'.smul_mem b' (hv i)
      · intro x y hx hy
        rw [mul_add]; exact Submodule.add_mem _ hx hy
    simpa using this 1 h1m
  · apply Submodule.smul_le.2
    intro a ha x hx
    have : detSpan M ≤ (detSpan M').comap (LinearMap.lsmul (𝓞 E) E a) := by
      apply Submodule.span_le.2
      intro d hd
      obtain ⟨v, hv, rfl⟩ := (mem_detSet M d).1 hd
      exact smul_det_mem M' m a ha v hv
    exact this hx

theorem index_cyclic (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E) :
    Ideal.absNorm (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) =
      M'.toAddSubgroup.relIndex (M' ⊔ Submodule.span (𝓞 E) {m}).toAddSubgroup := by
  rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, LinearMap.span_singleton_eq_range,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact AddSubgroup.index_comap M'.toAddSubgroup (LinearMap.toSpanSingleton (𝓞 E) _ m).toAddMonoidHom

theorem exists_index_ideal (M' M : Submodule (𝓞 E) (Fin n → E)) (hle : M' ≤ M) (hb : Bdd M)
    (ht : ∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') :
    ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan M' = 𝔞 • detSpan M ∧
      Ideal.absNorm 𝔞 = M'.toAddSubgroup.relIndex M.toAddSubgroup := by
  classical
  have key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ M) →
      ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan M' = 𝔞 • detSpan (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        Ideal.absNorm 𝔞 = M'.toAddSubgroup.relIndex
          (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))).toAddSubgroup := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨⊤, by simp, by simp, by simp⟩
    | insert m s _ ih =>
      intro hs
      obtain ⟨𝔞, h0, h1, h2⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      set N := M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hN
      have hm : m ∈ M := hs m (Finset.mem_insert_self _ _)
      have e : M' ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          N ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hN, sup_assoc, sup_comm (Submodule.span _ {m})]
      have hNM : N ⊔ Submodule.span (𝓞 E) {m} ≤ M := by
        rw [← e]
        exact sup_le hle (Submodule.span_le.2 fun x hx => hs x hx)
      have hb' : Bdd (N ⊔ Submodule.span (𝓞 E) {m}) := by
        obtain ⟨k, hk, h⟩ := hb
        exact ⟨k, hk, fun v hv => h v (hNM hv)⟩
      rw [e]
      refine ⟨𝔞 * (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_⟩
      · refine mul_ne_zero h0 ?_
        obtain ⟨a, ha, ham⟩ := ht m hm
        exact (Submodule.ne_bot_iff _).2 ⟨a, (le_sup_left : M' ≤ N) ham, ha⟩
      · rw [h1, Submodule.mul_smul, ← detSpan_cyclic N m hb']
      · rw [map_mul, h2, index_cyclic]
        exact AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left)
          (Submodule.toAddSubgroup_mono le_sup_left)
  have hfg : M.FG := by
    obtain ⟨k, hk, h⟩ := hb
    have hs : (stdLat E n).FG := Submodule.fg_pi fun _ => by
      rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
    apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k)
      (fun x y hxy => smul_right_injective _ hk hxy)
    exact hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
  obtain ⟨s, rfl⟩ := hfg
  have := key s fun x hx => Submodule.subset_span hx
  rwa [sup_eq_right.2 hle] at this

theorem exists_smul_std (v : Fin n → E) : ∃ a : 𝓞 E, a ≠ 0 ∧ a • v ∈ stdLat E n := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) v
  exact ⟨d, nonZeroDivisors.ne_zero d.2, (mem_std _).2 fun j => hd j⟩

theorem bdd_of_unimod [IsCMField E] (Λ : GenLat E n) (h : Λ.Unimod) : Bdd Λ.La := by
  classical
  have hfull : Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let u : Fin n → E := fun j => IsCMField.complexConj E (f (Pi.single j 1))
    have hu : ∀ w, ∑ j, IsCMField.complexConj E (u j) * w j = f w := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ f w]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [u, IsCMField.complexConj_apply_apply, smul_eq_mul, mul_comm]
      congr 2
      ext k; simp [Pi.single_apply, eq_comm]
    have hk : ∀ w ∈ Λ.La, f w = 0 := fun w hw => hf (Submodule.subset_span hw)
    have huL : u ∈ Λ.La := (h u).2 fun w hw => by rw [hu, hk w hw]; exact zero_mem _
    have h0 := hu u
    rw [hk u huL] at h0
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 := congrArg φ h0
    simp only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero,
      ← Complex.normSq_eq_conj_mul_self] at h1
    have h2 : ∑ j, Complex.normSq (φ (u j)) = 0 := by exact_mod_cast h1
    have h3 : ∀ j, u j = 0 := fun j => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 j (Finset.mem_univ j)
      simpa using this
    apply hf0
    ext w
    simp [← hu, h3]
  have hmul : ∀ x : Fin n → E, ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ Λ.La := by
    intro x
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E
      (Λ.La : Set (Fin n → E)) x (by rw [hfull]; trivial)
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  choose a ha0 ha using fun j : Fin n => hmul (Pi.single j 1)
  have hA : ∀ j, (∏ i, a i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := by
    intro j
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_comm, mul_smul]
    exact Λ.La.smul_mem _ (ha j)
  refine ⟨IsCMField.ringOfIntegersComplexConj E (∏ i, a i), ?_, fun v hv => (mem_std _).2 fun j => ?_⟩
  · rw [Ne, map_eq_zero_iff _ (AlgEquiv.injective _)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => ha0 i
  · obtain ⟨b, hb⟩ := (h _).1 (hA j) v hv
    refine ⟨b, ?_⟩
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)] at hb
    change _ = ((IsCMField.ringOfIntegersComplexConj E (∏ i, a i) : 𝓞 E) : E) * v j
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    simpa [Algebra.smul_def] using hb

end Lat

section Push
variable {E F : Type} [Field E] [Field F] (φ : E →+* F)

theorem map_smul_int (b : 𝓞 E) (x : E) : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
  change φ ((b : E) * x) = _
  rw [map_mul]; rfl

theorem span_image_span (S : Set E) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 E) S : Set E)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx => rw [map_smul_int]; exact Submodule.smul_mem _ _ hx

theorem span_image_smul (𝔞 : Ideal (𝓞 E)) (N : Submodule (𝓞 E) E) :
    Submodule.span (𝓞 F) (φ '' ((𝔞 • N : Submodule (𝓞 E) E) : Set E)) =
      Submodule.span (𝓞 F) ((φ.comp (algebraMap (𝓞 E) E)) '' (𝔞 : Set (𝓞 E))) *
        Submodule.span (𝓞 F) (φ '' (N : Set E)) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y hy
      rw [Algebra.smul_def, map_mul]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨y, hy, rfl⟩)
    · intro x y hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨a • y, Submodule.smul_mem_smul ha hy, by rw [Algebra.smul_def, map_mul]; rfl⟩

end Push

theorem betaExists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (n bad : ℕ), Formalism.L2.Pj.BetaExists (Dw := Dw) c n bad := by
  intro E _ _ _ H Dw l c n bad hK Λ hU _
  obtain ⟨𝔞, h0, h1, h2⟩ := exists_index_ideal Λ.Ln Λ.La inf_le_left (bdd_of_unimod Λ hU) (fun m hm => by
    obtain ⟨a, ha, h⟩ := exists_smul_std m
    exact ⟨a, ha, Λ.La.smul_mem a hm, h⟩)
  obtain ⟨β, hβ0, hβ1, hβ2⟩ := hK 𝔞 h0
  refine ⟨β, hβ0, ?_, fun σ => ?_⟩
  · have e : ∀ τ, idealAt c Λ.Ln τ =
        Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c Λ.La τ := by
      intro τ
      unfold idealAt
      rw [← span_image_span (embF c τ) (detSet Λ.Ln), ← span_image_span (embF c τ) (detSet Λ.La)]
      have := span_image_smul (embF c τ) 𝔞 (detSpan Λ.La)
      rw [← h1] at this
      exact this
    unfold BetaIs
    simp only [e, mul_pow, Finset.prod_mul_distrib, hβ1]
  · rw [hβ2, h2]; rfl

end GlobalTheory.BetaEx
