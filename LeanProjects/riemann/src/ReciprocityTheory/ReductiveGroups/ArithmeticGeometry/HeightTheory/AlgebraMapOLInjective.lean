import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValPl

open IsDedekindDomain WithZero IsLocalRing

theorem wt_add_eq_zero {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe b =>
      have ha' : (0 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (0 : ℤ) ≤ b := by exact_mod_cast hb
      have h' : a + b = 0 := by exact_mod_cast h
      have ha0 : a = 0 := by omega
      rw [ha0]
      first | rfl | exact WithTop.coe_zero | simp

section
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)

variable (L) in
open Classical in

noncomputable def addv : AddValuation L (WithTop ℤ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else (((-log (v.valuation L x) : ℤ)) : WithTop ℤ))
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      rw [← WithTop.coe_min, WithTop.coe_le_coe]
      have hx' : v.valuation L x ≠ 0 := by simpa using hx
      have hy' : v.valuation L y ≠ 0 := by simpa using hy
      have hxy' : v.valuation L (x + y) ≠ 0 := by simpa using hxy
      have h := (v.valuation L).map_add x y
      rcases le_max_iff.mp h with h | h
      · have := (log_le_log hxy' hx').mpr h
        rw [min_le_iff]; left; omega
      · have := (log_le_log hxy' hy').mpr h
        rw [min_le_iff]; right; omega)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      have hx' : v.valuation L x ≠ 0 := by simpa using hx
      have hy' : v.valuation L y ≠ 0 := by simpa using hy
      simp only [hx, hy, mul_eq_zero, or_self, ite_false, map_mul, log_mul hx' hy']
      rw [← WithTop.coe_add]; congr 1; ring)

theorem addv_apply {x : L} (hx : x ≠ 0) :
    addv L v x = (((-log (v.valuation L x) : ℤ)) : WithTop ℤ) := by
  first
  | (unfold addv; rw [AddValuation.of_apply, if_neg hx])
  | simp [addv, AddValuation.of_apply, hx]

theorem addv_nonneg (s : S) : 0 ≤ addv L v (algebraMap S L s) := by
  by_cases hs : s = 0
  · subst hs
    simp
  have hx : algebraMap S L s ≠ 0 := by
    intro h
    apply hs
    apply IsFractionRing.injective S L
    rw [h, map_zero]
  have hv : v.valuation L (algebraMap S L s) ≠ 0 := by simpa using hx
  rw [addv_apply v hx]
  have h1 := (log_le_log hv one_ne_zero).mpr (v.valuation_le_one s)
  rw [log_one] at h1
  have h2 : (0 : ℤ) ≤ -log (v.valuation L (algebraMap S L s)) := by omega
  exact_mod_cast h2

theorem addv_pos_iff (s : S) : 0 < addv L v (algebraMap S L s) ↔ s ∈ v.asIdeal := by
  by_cases hs : s = 0
  · subst hs
    rw [map_zero, AddValuation.map_zero]
    exact iff_of_true (WithTop.coe_lt_top 0) (Submodule.zero_mem _)
  have hx : algebraMap S L s ≠ 0 := by
    intro h
    apply hs
    apply IsFractionRing.injective S L
    rw [h, map_zero]
  have hv : v.valuation L (algebraMap S L s) ≠ 0 := by simpa using hx
  rw [addv_apply v hx, ← v.valuation_lt_one_iff_mem (K := L) s]
  have h1 : v.valuation L (algebraMap S L s) < 1 ↔
      ¬ (log (1 : WithZero (Multiplicative ℤ)) ≤ log (v.valuation L (algebraMap S L s))) := by
    rw [log_le_log one_ne_zero hv, not_le]
  rw [h1, log_one, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  constructor <;> intro h <;> omega

theorem eq_addv (w : AddValuation L (WithTop ℤ)) (hw : IsNormDiscrete w)
    (h0 : ∀ s : S, 0 ≤ w (algebraMap S L s))
    (hQ : ∀ s : S, 0 < w (algebraMap S L s) ↔ s ∈ v.asIdeal) : w = addv L v := by
  have hunit : ∀ d : S, d ∉ v.asIdeal → w (algebraMap S L d) = 0 := fun d hd =>
    le_antisymm (not_lt.1 (mt (hQ d).1 hd)) (h0 d)
  have hint : ∀ x : L, v.valuation L x ≤ 1 → 0 ≤ w x := by
    intro x hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := v) x hx
    have h := congrArg w hnd
    rw [AddValuation.map_mul, hunit d d.2, add_zero] at h
    rw [h]; exact h0 n
  have heq1 : ∀ x : L, x ≠ 0 → v.valuation L x = 1 → w x = 0 := by
    intro x hx h1
    have h2 : v.valuation L x⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
    have hs : w x + w x⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]
    exact wt_add_eq_zero (hint x h1.le) (hint _ h2.le) hs
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  set p := algebraMap S L π with hp_def
  have hp : v.valuation L p = exp (-1 : ℤ) := by rw [hp_def, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hp; exact exp_ne_zero hp.symm
  have hπQ : π ∈ v.asIdeal := by
    rw [← v.intValuation_lt_one_iff_mem, hπ, ← exp_zero, exp_lt_exp]; omega
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℤ, w p = a0 := WithTop.ne_top_iff_exists.mp (hw.1 p hp0) |>.imp
    fun _ h => h.symm
  have hpinv : w p⁻¹ = ((-a0 : ℤ) : WithTop ℤ) := by
    have hs : w p + w p⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hp0, AddValuation.map_one]
    have hne : w p⁻¹ ≠ ⊤ := hw.1 _ (inv_ne_zero hp0)
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hb] at hs ⊢
    rw [ha0] at hs
    have : a0 + b = 0 := by exact_mod_cast hs
    congr 1; omega
  have hzpow : ∀ n : ℤ, w (p ^ n) = ((n * a0 : ℤ) : WithTop ℤ) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one₀ hp0, AddValuation.map_mul, ih, ha0, ← WithTop.coe_add]; congr 1; ring
    | pred n ih =>
      rw [zpow_sub_one₀ hp0, AddValuation.map_mul, ih, hpinv, ← WithTop.coe_add]; congr 1; ring
  have hform : ∀ x : L, x ≠ 0 → w x = (((-log (v.valuation L x)) * a0 : ℤ) : WithTop ℤ) := by
    intro x hx
    have hvx : v.valuation L x ≠ 0 := by simpa using hx
    set k := log (v.valuation L x)
    have hy : v.valuation L (x * p ^ k) = 1 := by
      rw [map_mul, map_zpow₀, hp, ← exp_log hvx, ← exp_zsmul, ← exp_add]
      simp [k]
    have hy0 : x * p ^ k ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hp0)
    have h := heq1 _ hy0 hy
    rw [AddValuation.map_mul, hzpow] at h
    have hne : w x ≠ ⊤ := hw.1 x hx
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hb] at h ⊢
    have : b + k * a0 = 0 := by exact_mod_cast h
    congr 1; linarith
  have ha1 : a0 = 1 := by
    obtain ⟨z, hz⟩ := hw.2
    have hz0 : z ≠ 0 := by
      intro h; rw [h, AddValuation.map_zero] at hz; exact WithTop.top_ne_coe hz
    rw [hform z hz0] at hz
    have h1 : (-log (v.valuation L z)) * a0 = 1 := by exact_mod_cast hz
    have hpos : 0 < a0 := by
      have := (hQ π).mpr hπQ
      rw [← hp_def, ha0] at this; exact_mod_cast this
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  apply AddValuation.ext
  intro x
  by_cases hx : x = 0
  · subst hx; simp
  rw [hform x hx, addv_apply v hx, ha1, mul_one]

end

def PlacesOver (O L : Type*) [CommRing O] [IsLocalRing O] [Field L] [Algebra O L] :
    Set (AddValuation L (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ x : O, 0 ≤ w (algebraMap O L x) ∧
    (0 < w (algebraMap O L x) ↔ x ∈ maximalIdeal O)}

theorem placesOver_iff_loc {R O L : Type*} [CommRing R] [CommRing O] [IsLocalRing O] [Field L]
    [Algebra R O] [Algebra R L] [Algebra O L] [IsScalarTower R O L] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime O P] (w : AddValuation L (WithTop ℤ)) :
    (∀ x : R, 0 ≤ w (algebraMap R L x) ∧ (0 < w (algebraMap R L x) ↔ x ∈ P)) ↔
      (∀ x : O, 0 ≤ w (algebraMap O L x) ∧ (0 < w (algebraMap O L x) ↔ x ∈ maximalIdeal O)) := by
  constructor
  · intro h x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have hsP : (s : R) ∉ P := s.2
    have hs0 : w (algebraMap R L s) = 0 := by
      obtain ⟨h1, h2⟩ := h s
      exact le_antisymm (not_lt.mp fun hp => hsP (h2.mp hp)) h1
    have hspec : algebraMap O L (IsLocalization.mk' O r s) * algebraMap R L s =
        algebraMap R L r := by
      rw [IsScalarTower.algebraMap_apply R O L (s : R), IsScalarTower.algebraMap_apply R O L r,
        ← map_mul, IsLocalization.mk'_spec]
    have hw : w (algebraMap O L (IsLocalization.mk' O r s)) = w (algebraMap R L r) := by
      rw [← hspec, AddValuation.map_mul, hs0, add_zero]
    rw [hw]
    first
    | (rw [IsLocalization.AtPrime.mk'_mem_maximal_iff O P]; exact h r)
    | (rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (S := O) (I := P)]; exact h r)
    | (rw [IsLocalization.AtPrime.mk'_mem_maximal_iff O]; exact h r)
  · intro h x
    have hx := h (algebraMap R O x)
    rw [← IsScalarTower.algebraMap_apply R O L x] at hx
    first
    | rwa [IsLocalization.AtPrime.to_map_mem_maximal_iff (S := O) (I := P)] at hx
    | (rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O P] at hx; exact hx)

section DVR

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

include F in
theorem algebraMap_OL_injective : Function.Injective (algebraMap O L) := by
  rw [IsScalarTower.algebraMap_eq O F L]
  first
  | exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  | (rw [RingHom.coe_comp]; exact (algebraMap F L).injective.comp (IsFractionRing.injective O F))

variable (O F L) in
include F in

theorem exists_heightOne (Q : Ideal (integralClosure O L)) (hQ : Q.IsMaximal) :
    ∃ v : HeightOneSpectrum (integralClosure O L), v.asIdeal = Q := by
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro a b hab
    first
    | exact algebraMap_OL_injective (F := F) (congrArg Subtype.val hab)
    | (apply algebraMap_OL_injective (F := F)
       rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L a,
         IsScalarTower.algebraMap_apply O (integralClosure O L) L b, hab])
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hB : IsField (integralClosure O L) := Ring.isField_iff_maximal_bot.mpr hQ
    have hO : IsField O := isField_of_isIntegral_of_isField hinj hB
    have hmax : (⊥ : Ideal O).IsMaximal := Ring.isField_iff_maximal_bot.mp hO
    exact absurd (IsLocalRing.eq_maximalIdeal hmax).symm IsDiscreteValuationRing.not_a_field'
  exact ⟨⟨Q, hQ.isPrime, hne⟩, rfl⟩

theorem addv_mem_placesOver (v : HeightOneSpectrum (integralClosure O L)) :
    addv L v ∈ PlacesOver O L := by
  rw [PlacesOver, Set.mem_setOf_eq, IsNormDiscrete]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a ha
    rw [addv_apply v ha]
    exact WithTop.coe_ne_top
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact absurd hπ.symm (by simp)
    refine ⟨π, ?_⟩
    rw [addv_apply v hπ0, hπ, log_exp]
    simp
  · intro x
    haveI := v.isMaximal
    have hcomap : v.asIdeal.comap (algebraMap O (integralClosure O L)) = maximalIdeal O := by
      apply IsLocalRing.eq_maximalIdeal
      first
      | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
      | exact Ideal.IsMaximal.under O v.asIdeal
      | infer_instance
    rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L x, ← hcomap, Ideal.mem_comap]
    exact ⟨addv_nonneg v _, addv_pos_iff v _⟩

variable (O F L) in
include F in

theorem placesOver_bij : ∃ e : HeightOneSpectrum (integralClosure O L) ≃ PlacesOver O L,
    ∀ v, (e v : AddValuation L (WithTop ℤ)) = addv L v := by
  classical
  let f : HeightOneSpectrum (integralClosure O L) → PlacesOver O L :=
    fun v => ⟨addv L v, addv_mem_placesOver v⟩
  have hinj : Function.Injective f := by
    intro v v' hvv
    have h : addv L v = addv L v' := congrArg Subtype.val hvv
    ext b
    rw [← addv_pos_iff (L := L) v, ← addv_pos_iff (L := L) v', h]
  have hsurj : Function.Surjective f := by
    rintro ⟨w, hw⟩
    have h0 : ∀ b : integralClosure O L, 0 ≤ w (algebraMap (integralClosure O L) L b) := by
      intro b
      have hb : IsIntegral O (algebraMap (integralClosure O L) L b) := b.2
      letI : Algebra O (vRing w) :=
        ((algebraMap O L).codRestrict (vRing w) (fun x => (hw.2 x).1)).toAlgebra
      haveI : IsScalarTower O (vRing w) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hb' : IsIntegral (vRing w) (algebraMap (integralClosure O L) L b) := hb.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
      rw [← hy]
      exact y.2
    let Qw : Ideal (integralClosure O L) :=
      { carrier := {b | 0 < w (algebraMap (integralClosure O L) L b)}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
          exact lt_of_lt_of_le (lt_min ha hb) (w.map_add _ _)
        zero_mem' := by simp
        smul_mem' := fun c b hb => by
          simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢
          exact lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 c)) }
    have hprime : Qw.IsPrime := by
      refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
      · have h1 : (1 : integralClosure O L) ∈ Qw := htop ▸ Submodule.mem_top
        simp [Qw] at h1
      · change 0 < w (algebraMap _ L (a * b)) at hab
        rw [map_mul, AddValuation.map_mul] at hab
        by_contra hno
        rw [not_or] at hno
        have ha : w (algebraMap _ L a) = 0 :=
          le_antisymm (not_lt.1 (hno.1 : ¬ 0 < w (algebraMap _ L a))) (h0 a)
        have hb : w (algebraMap _ L b) = 0 :=
          le_antisymm (not_lt.1 (hno.2 : ¬ 0 < w (algebraMap _ L b))) (h0 b)
        rw [ha, hb, add_zero] at hab
        exact lt_irrefl _ hab
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hne : Qw ≠ ⊥ := by
      intro hbot
      have hmem : algebraMap O (integralClosure O L) ϖ ∈ Qw := by
        show 0 < w (algebraMap (integralClosure O L) L (algebraMap O _ ϖ))
        rw [← IsScalarTower.algebraMap_apply]
        exact ((hw.2 ϖ).2).2 hϖ.not_isUnit
      rw [hbot, Ideal.mem_bot] at hmem
      have : (algebraMap O L) ϖ = 0 := by
        rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L, hmem, map_zero]
      exact hϖ.ne_zero (algebraMap_OL_injective (F := F) (by rw [this, map_zero]))
    refine ⟨⟨Qw, hprime, hne⟩, Subtype.ext ?_⟩
    exact (eq_addv _ w hw.1 h0 (fun s => Iff.rfl)).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun v => rfl⟩

theorem addv_count (v : HeightOneSpectrum (integralClosure O L)) (b : integralClosure O L)
    (hb : b ≠ 0) :
    addv L v (algebraMap (integralClosure O L) L b) =
      ((Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) : ℕ) : WithTop ℤ) := by
  have hx : algebraMap (integralClosure O L) L b ≠ 0 := by
    intro h
    apply hb
    apply IsFractionRing.injective (integralClosure O L) L
    rw [h, map_zero]
  have hI : Ideal.span {b} ≠ 0 := by
    first
    | (rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb)
    | simpa using hb
  have hc := Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot
  have hval : v.valuation L (algebraMap (integralClosure O L) L b) = v.intValuation b := by
    first
    | exact v.valuation_of_algebraMap b
    | exact HeightOneSpectrum.valuation_of_algebraMap v b
    | simp
  rw [addv_apply v hx, hval, v.intValuation_if_neg hb, log_exp, neg_neg, hc]
  first
  | (norm_cast; done)
  | (norm_cast; convert rfl; done)
  | (push_cast; convert rfl; done)
  | (congr 1; convert rfl)

include F in

theorem addv_uniformizer (v : HeightOneSpectrum (integralClosure O L)) {ϖ : O}
    (hϖ : Irreducible ϖ) :
    addv L v (algebraMap O L ϖ) = ((v.asIdeal.ramificationIdx O : ℕ) : WithTop ℤ) := by
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro a b hab
    first
    | exact algebraMap_OL_injective (F := F) (congrArg Subtype.val hab)
    | (apply algebraMap_OL_injective (F := F)
       rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L a,
         IsScalarTower.algebraMap_apply O (integralClosure O L) L b, hab])
  have hb : algebraMap O (integralClosure O L) ϖ ≠ 0 := by
    intro h
    apply hϖ0
    apply hinj
    rw [h, map_zero]
  rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ, addv_count v _ hb]
  have hmax : maximalIdeal O = Ideal.span {ϖ} := by
    first
    | exact hϖ.maximalIdeal_eq
    | exact IsDiscreteValuationRing.Irreducible.maximalIdeal_eq hϖ
    | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {algebraMap O (integralClosure O L) ϖ} =
      (maximalIdeal O).map (algebraMap O (integralClosure O L)) := by
    rw [hmax, Ideal.map_span, Set.image_singleton]
  have hund : v.asIdeal.under O = maximalIdeal O := by
    haveI := v.isMaximal
    apply IsLocalRing.eq_maximalIdeal
    first
    | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
    | exact Ideal.IsMaximal.under O v.asIdeal
    | infer_instance
  have hmap : Ideal.map (algebraMap O (integralClosure O L)) (v.asIdeal.under O) ≠ ⊥ := by
    rw [hund, ← hspan, Ne, Ideal.span_singleton_eq_bot]
    exact hb
  rw [hspan]
  norm_cast
  rw [← hund]
  first
  | (rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count, hmap, v.ne_bot]; done)
  | (rw [Ideal.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.ramificationIdx_eq_normalizedFactors_count, hmap, v.ne_bot]; done)
  | (rw [Ideal.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.ramificationIdx_eq_count_normalizedFactors, hmap, v.ne_bot]; done)
  | (rw [Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors, hmap, v.ne_bot]; done)
  | (rw [Ideal.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.count_normalizedFactors_eq_ramificationIdx, hmap, v.ne_bot]; done)
  | (rw [Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx, hmap, v.ne_bot]; done)
  | (rw [Ideal.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.ramificationIdx_eq_factors_count, hmap, v.ne_bot]; done)
  | (rw [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count, hmap, v.ne_bot]; done)
  | skip
  done

end DVR

end ValPl

end ReciprocityTheory.ChartRestriction.G.T0
