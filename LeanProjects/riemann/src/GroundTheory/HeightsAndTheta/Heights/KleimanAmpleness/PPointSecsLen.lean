import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PointSecsLenSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RingKrullDimRangeCompAddOneLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace CycleSplit.PointSecs

variable {S : Type u} [CommRing S] {K : Type w} [Field K] [Algebra S K] {N : ℕ} {y : Fin (N + 1) → K}

variable (S y) in

def dehomAt (j : Fin (N + 1)) : Poly S N →ₐ[S] K :=
  ((Polynomial.aeval (y j)⁻¹ : Polynomial K →ₐ[K] K).restrictScalars S).comp (cone (S := S) y)

theorem dehomAt_of_isHomogeneous (j : Fin (N + 1)) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    dehomAt S y j f = aeval y f / y j ^ e := by
  change ((Polynomial.aeval (y j)⁻¹ : Polynomial K →ₐ[K] K).restrictScalars S) (cone (S := S) y f) = _
  rw [cone_of_isHomogeneous y hf, AlgHom.restrictScalars_apply, map_mul, map_pow, Polynomial.aeval_C,
    Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, inv_pow, div_eq_mul_inv]

theorem isField_dehomAt_range (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) : IsField (dehomAt S y j).range := by
  have h1 : ringKrullDim (cone (S := S) y).range ≤ 1 := by
    rw [primeOf_eq] at hdim
    rwa [← ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (cone (S := S) y)).toRingEquiv]
  have hne : cone (S := S) y (X j - 1) ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p 0) h
    simp [cone_eq, coneGen] at this
  have hkill : ((Polynomial.aeval (y j)⁻¹ : Polynomial K →ₐ[K] K).restrictScalars S)
      (cone (S := S) y (X j - 1)) = 0 := by
    simp [cone_eq, coneGen, hj]
  have key := SectionsOverLocalization.ringKrullDim_range_comp_add_one_le (cone (S := S) y)
    ((Polynomial.aeval (y j)⁻¹ : Polynomial K →ₐ[K] K).restrictScalars S) (X j - 1) hne hkill
  have key2 : ringKrullDim (dehomAt S y j).range + 1 ≤ 1 := key.trans h1
  have hle : ringKrullDim (dehomAt S y j).range ≤ 0 :=
    SectionsOverLocalization.le_zero_of_add_natCast_le (n := 1) (by simpa using key2)
  have : Ring.KrullDimLE 0 (dehomAt S y j).range := Ring.krullDimLE_iff.mpr (by simpa using hle)
  exact Ring.KrullDimLE.isField_of_isDomain

theorem dehomAt_range_le (j : Fin (N + 1)) (hj : y j ≠ 0) :
    (dehomAt S y j).range ≤ chartRing S y (singleChart hj) := by
  have : dehomAt S y j = (chartRing S y (singleChart hj)).val.comp (aeval (ratio (S := S) hj)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [dehomAt, cone_eq, coneGen, ratio, div_eq_mul_inv]
  rw [this]
  exact (AlgHom.range_comp_le_range _ _).trans (Subalgebra.range_val _).le

theorem chartRing_le_dehomAt_range (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1)
    {j : Fin (N + 1)} (hj : y j ≠ 0) (I : Chart y) : chartRing S y I ≤ (dehomAt S y j).range := by
  have hF := isField_dehomAt_range hdim hj
  rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hje : y j ^ e ≠ 0 := pow_ne_zero _ hj
  have hb : (⟨dehomAt S y j s, AlgHom.mem_range_self _ _⟩ : (dehomAt S y j).range) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simp only [dehomAt_of_isHomogeneous j hse, ZeroMemClass.coe_zero] at this
    exact div_ne_zero hs0 hje this
  obtain ⟨c, hc⟩ := hF.mul_inv_cancel hb
  have hc' : (c : K) = aeval y (X j ^ e : Poly S N) / aeval y s := by
    have := congrArg Subtype.val hc
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, dehomAt_of_isHomogeneous j hse] at this
    simp only [map_pow, aeval_X]
    field_simp at this ⊢
    linear_combination this
  have : aeval y f / aeval y s = dehomAt S y j f * c := by
    rw [hc', dehomAt_of_isHomogeneous j hf]
    simp only [map_pow, aeval_X]
    field_simp
  rw [this]
  exact mul_mem (AlgHom.mem_range_self _ _) c.2

theorem mem_chartRing_iff (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) (I : Chart y) (z : K) : z ∈ chartRing S y I ↔ z ∈ chartRing S y (singleChart hj) := by
  obtain ⟨i, hi⟩ := I.2.1
  have hyi : y i ≠ 0 := (mem_support y).mp (I.2.2 hi)
  refine ⟨fun hz => dehomAt_range_le j hj (chartRing_le_dehomAt_range hdim hj I hz), fun hz => ?_⟩
  exact chartRing_mono (x := y) (I := singleChart hyi) (J := I) (Finset.singleton_subset_iff.mpr hi)
    (dehomAt_range_le i hyi (chartRing_le_dehomAt_range hdim hyi _ hz))

theorem chart_inv_mem (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) {z : K} (hz : z ∈ chartRing S y (singleChart hj)) : z⁻¹ ∈ chartRing S y (singleChart hj) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [inv_zero]
    exact zero_mem _
  have hF := isField_dehomAt_range hdim hj
  have hb : (⟨z, chartRing_le_dehomAt_range hdim hj _ hz⟩ : (dehomAt S y j).range) ≠ 0 :=
    fun h => hz0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := hF.mul_inv_cancel hb
  have : (c : K) = z⁻¹ := by
    have := congrArg Subtype.val hc
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact (eq_inv_of_mul_eq_one_right this)
  rw [← this]
  exact dehomAt_range_le j hj c.2

theorem twist_sub_line (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) (Q : LineBundle S y) (c : ℤ) (I : Chart y) :
    ∃ f : K, f ≠ 0 ∧ ∀ z, z ∈ (Q.twist (twistSys S y c)).sub I ↔
      ∃ a ∈ chartRing S y (singleChart hj), z = a * f := by
  have hI := mem_chartRing_iff hdim hj I
  obtain ⟨Q', hQ'⟩ := Q.invertible I
  have h1 : (1 : K) ∈ Q.sub I * Q' := by
    rw [hQ', Submodule.mem_one]
    exact ⟨1, map_one _⟩
  have hex : ∃ m ∈ Q.sub I, ∃ n ∈ Q', m * n ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : Q.sub I * Q' ≤ ⊥ := Submodule.mul_le.mpr fun m hm n hn => by
      rw [Submodule.mem_bot]; exact hcon m hm n hn
    exact one_ne_zero ((Submodule.mem_bot _).mp (hle h1))
  obtain ⟨m0, hm0, n, hn, hmn⟩ := hex
  have hqn : ∀ q ∈ Q.sub I, q * n ∈ chartRing S y (singleChart hj) := by
    intro q hq
    have := Submodule.mul_mem_mul hq hn
    rw [hQ', Submodule.mem_one] at this
    obtain ⟨a, ha⟩ := this
    rw [← ha]
    exact (hI _).mp a.2
  obtain ⟨i, hi⟩ := I.2.1
  have hyi : y i ≠ 0 := (mem_support y).mp (I.2.2 hi)
  have hm0' : m0 ≠ 0 := left_ne_zero_of_mul hmn
  have hn0 : n ≠ 0 := right_ne_zero_of_mul hmn
  have hinv := chart_inv_mem hdim hj (hqn m0 hm0)
  have hyic : y i ^ c ≠ 0 := zpow_ne_zero _ hyi
  refine ⟨y i ^ c * m0, mul_ne_zero hyic hm0', fun z => ⟨fun hz => ?_, ?_⟩⟩
  · refine Submodule.span_induction (p := fun z _ => ∃ a ∈ chartRing S y (singleChart hj), z = a * (y i ^ c * m0))
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, x, hx, rfl⟩
      change q ∈ twistMod S y c I at hq
      rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨b, rfl⟩ := hq
      refine ⟨b * (x * n) * (m0 * n)⁻¹, mul_mem (mul_mem ((hI _).mp b.2) (hqn x hx)) hinv, ?_⟩
      rw [chartRing_smul_def, smul_eq_mul]
      field_simp
    · exact ⟨0, zero_mem _, by simp⟩
    · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_mem ha hb, by ring⟩
    · rintro b _ _ ⟨a, ha, rfl⟩
      exact ⟨b * a, mul_mem ((hI _).mp b.2) ha, by rw [chartRing_smul_def]; ring⟩
  · rintro ⟨a, ha, rfl⟩
    have hyc : y i ^ c ∈ (twistSys S y c).sub I := by
      change y i ^ c ∈ twistMod S y c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    have hgen : y i ^ c * m0 ∈ (Q.twist (twistSys S y c)).sub I :=
      Submodule.subset_span ⟨y i ^ c, hyc, m0, hm0, rfl⟩
    have := Submodule.smul_mem _ (⟨a, (hI a).mpr ha⟩ : chartRing S y I) hgen
    rwa [chartRing_smul_def] at this

theorem secs_line (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) (Q : LineBundle S y) (c : ℤ) :
    ∃ f : K, f ≠ 0 ∧ ∀ z, z ∈ (Q.twist (twistSys S y c)).secs ↔
      ∃ a ∈ chartRing S y (singleChart hj), z = a * f := by
  obtain ⟨f, hf, hL⟩ := twist_sub_line hdim hj Q c (singleChart hj)
  refine ⟨f, hf, fun z => ⟨fun hz => (hL z).mp ?_, fun hz => ?_⟩⟩
  · rw [SubSystem.secs, Submodule.mem_iInf] at hz
    exact hz (singleChart hj)
  · rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    change z ∈ (Q.twist (twistSys S y c)).sub I
    let U : Chart y := ⟨(singleChart hj).1 ∪ I.1, I.2.1.mono Finset.subset_union_right,
      Finset.union_subset (singleChart hj).2.2 I.2.2⟩
    obtain ⟨g, hg, hLU⟩ := twist_sub_line hdim hj Q c U
    obtain ⟨h, hh, hLI⟩ := twist_sub_line hdim hj Q c I
    obtain ⟨b, hb, hfb⟩ := (hLU f).mp ((Q.twist (twistSys S y c)).mono _ U Finset.subset_union_left f
      ((hL f).mpr ⟨1, one_mem _, (one_mul f).symm⟩))
    obtain ⟨d, hd, hhd⟩ := (hLU h).mp ((Q.twist (twistSys S y c)).mono I U Finset.subset_union_right h
      ((hLI h).mpr ⟨1, one_mem _, (one_mul h).symm⟩))
    obtain ⟨a, ha, rfl⟩ := hz
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hhd
      exact hh hhd
    refine (hLI _).mpr ⟨a * b * d⁻¹, mul_mem (mul_mem ha hb) (chart_inv_mem hdim hj hd), ?_⟩
    rw [hfb, hhd]
    field_simp

theorem length_secs (hdim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1) {j : Fin (N + 1)}
    (hj : y j ≠ 0) (Q : LineBundle S y) (c : ℤ) :
    Module.length S (Q.twist (twistSys S y c)).secs = Module.length S (chartRing S y (singleChart hj)) := by
  obtain ⟨f, hf, hline⟩ := secs_line hdim hj Q c
  let φ : chartRing S y (singleChart hj) →ₗ[S] (Q.twist (twistSys S y c)).secs :=
    { toFun := fun a => ⟨(a : K) * f, (hline _).mpr ⟨a, a.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (by simp [add_mul])
      map_smul' := fun s a => Subtype.ext (by simp) }
  have hbij : Function.Bijective φ := by
    refine ⟨fun a b hab => Subtype.ext (mul_right_cancel₀ hf (congrArg Subtype.val hab)), fun z => ?_⟩
    obtain ⟨a, ha, hz⟩ := (hline z).mp z.2
    exact ⟨⟨a, ha⟩, Subtype.ext hz.symm⟩
  exact ((LinearEquiv.ofBijective φ hbij).length_eq).symm

end CycleSplit.PointSecs

theorem CycleSplit.PointSecs.proof : CycleSplit.PointSecs.Statement.{u, w} := by
  intro S _ K _ _ N y ⟨j, hj⟩ hdim Q₁ Q₂ c₁ c₂
  have hyj : y j ≠ 0 := fun h =>
    hj ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X S j)).mpr (by rw [aeval_X, h]))
  rw [CycleSplit.PointSecs.length_secs hdim hyj, CycleSplit.PointSecs.length_secs hdim hyj]

end

end GroundTheory.Heights₂.Heights.Kleiman
