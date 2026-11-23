import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaExtensionEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WLeOneOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WAddLeMax
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieSmooth

open scoped nonZeroDivisors

section IdealSup

variable {K : Type} [Field K] [NumberField K]

theorem exists_ideal_mem_iff_of_fg (𝔞 : Submodule (𝓞 K) K) (hfg : 𝔞.FG) :
    ∃ (d : 𝓞 K) (I : Ideal (𝓞 K)), d ≠ 0 ∧ ∀ x : K, x ∈ 𝔞 ↔ ∃ y ∈ I, (y : K) = (d : K) * x := by
  obtain ⟨d, hd, h⟩ := FractionalIdeal.isFractional_of_fg (S := (𝓞 K)⁰) hfg
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  refine ⟨d, 𝔞.comap (LinearMap.toSpanSingleton (𝓞 K) K (d : K)⁻¹), hd0, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨y, hy⟩ := h x hx
    have hy' : (y : K) = (d : K) * x := by
      rw [Algebra.smul_def] at hy
      exact hy
    refine ⟨y, ?_, hy'⟩
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
    change (y : K) * _ ∈ 𝔞
    rw [hy', mul_comm (d : K), mul_assoc, mul_inv_cancel₀ hdK, mul_one]
    exact hx
  · rintro ⟨y, hy, hy'⟩
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Algebra.smul_def] at hy
    change (y : K) * _ ∈ 𝔞 at hy
    rwa [hy', mul_comm (d : K), mul_assoc, mul_inv_cancel₀ hdK, mul_one] at hy

theorem exists_pow_eq_span_of_ne_bot (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ (h : ℕ) (b : 𝓞 K), h ≠ 0 ∧ b ≠ 0 ∧ I ^ h = Ideal.span {b} := by
  let J : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩
  have h1 : ClassGroup.mk0 (J ^ classNumber K) = 1 := by
    rw [map_pow, classNumber, Fintype.card_eq_nat_card]
    exact pow_card_eq_one'
  obtain ⟨a, ha⟩ := ((ClassGroup.mk0_eq_one_iff (J ^ classNumber K).2).mp h1).principal
  have ha' : I ^ classNumber K = Ideal.span {a} := by
    rw [SubmonoidClass.coe_pow] at ha
    exact ha
  refine ⟨classNumber K, a, (classNumber_pos K).ne', ?_, ha'⟩
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.mpr rfl] at ha'
  exact pow_ne_zero _ hI ha'

omit [NumberField K] in

theorem abv_le_pow_of_mem_pow (u : AbsoluteValue K ℝ) (hu : ∀ x y, u (x + y) ≤ max (u x) (u y))
    (h1 : ∀ x : 𝓞 K, u x ≤ 1) (I : Ideal (𝓞 K)) {T : ℝ} (hT : ∀ y ∈ I, u y ≤ T) (h : ℕ) :
    ∀ y ∈ I ^ h, u y ≤ T ^ h := by
  have hT0 : 0 ≤ T := by simpa using hT 0 I.zero_mem
  induction h with
  | zero => intro y _; simpa using h1 y
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun m hm r hr => ?_) (fun x y hx hy => ?_)
    · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, pow_succ]
      exact mul_le_mul (ih m hm) (hT r hr) (u.nonneg _) (pow_nonneg hT0 _)
    · rw [RingOfIntegers.coe_eq_algebraMap, map_add]
      exact (hu _ _).trans (max_le hx hy)

omit [NumberField K] in

theorem log_iSup_abv_eq (u : AbsoluteValue K ℝ) (hu : ∀ x y, u (x + y) ≤ max (u x) (u y))
    (h1 : ∀ x : 𝓞 K, u x ≤ 1) (𝔞 : Submodule (𝓞 K) K) {d b : 𝓞 K} {I : Ideal (𝓞 K)} {h : ℕ} (hd : d ≠ 0)
    (hI : ∀ x : K, x ∈ 𝔞 ↔ ∃ y ∈ I, (y : K) = (d : K) * x) (hh : h ≠ 0) (hb : b ≠ 0)
    (hIb : I ^ h = Ideal.span {b}) :
    Real.log (⨆ a : 𝔞, u a) = (h : ℝ)⁻¹ * Real.log (u b) - Real.log (u d) := by
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
  have hud : 0 < u d := u.pos hdK
  have hub : 0 < u b := u.pos hbK
  set r : ℝ := (u b) ^ ((h : ℝ)⁻¹) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hub _
  have hrh : r ^ h = u b := Real.rpow_inv_natCast_pow hub.le hh
  have hup : ∀ a : 𝔞, u a ≤ r / u d := by
    intro a
    obtain ⟨y, hy, hy'⟩ := (hI a).1 a.2
    have hm : y ^ h ∈ Ideal.span {b} := hIb ▸ Ideal.pow_mem_pow hy h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    have h2 : u y ^ h ≤ r ^ h := by
      have hc' : (c : K) * (b : K) = (y : K) ^ h := by exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) hc
      rw [hrh, ← map_pow, ← hc', map_mul]
      exact mul_le_of_le_one_left hub.le (h1 c)
    have h3 : u y ≤ r := (pow_le_pow_iff_left₀ (u.nonneg _) hr0.le hh).1 h2
    rw [le_div_iff₀ hud, mul_comm, ← map_mul, ← hy']
    exact h3
  have hbdd : BddAbove (Set.range fun a : 𝔞 => u a) := ⟨r / u d, by rintro _ ⟨a, rfl⟩; exact hup a⟩
  have hS : (⨆ a : 𝔞, u a) = r / u d := by
    refine le_antisymm (ciSup_le hup) ?_
    have hT : ∀ y ∈ I, u y ≤ (⨆ a : 𝔞, u a) * u d := by
      intro y hy
      have hm : (d : K)⁻¹ * y ∈ 𝔞 := (hI _).2 ⟨y, hy, by rw [mul_inv_cancel_left₀ hdK]⟩
      have := le_ciSup hbdd ⟨_, hm⟩
      simp only [map_mul, map_inv₀] at this
      rwa [inv_mul_le_iff₀ hud, mul_comm] at this
    have h4 := abv_le_pow_of_mem_pow u hu h1 I hT h b (hIb ▸ Ideal.mem_span_singleton_self b)
    rw [← hrh] at h4
    have hT0 : 0 ≤ (⨆ a : 𝔞, u a) * u d := by simpa using hT 0 I.zero_mem
    rw [div_le_iff₀ hud]
    exact (pow_le_pow_iff_left₀ hr0.le hT0 hh).1 h4
  rw [hS, Real.log_div hr0.ne' hud.ne', hr, Real.log_rpow hub]

theorem sum_log_norm_eq_log_absNorm (z : 𝓞 K) (hz : z ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ z‖ = Real.log (Ideal.absNorm (Ideal.span {z}) : ℝ) := by
  have hzK : (z : K) ≠ 0 := by exact_mod_cast hz
  rw [sum_log_norm_embeddings_eq_log_norm _ hzK, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem idealLog_eq_of_pow_eq_span (𝔞 : Submodule (𝓞 K) K) (h𝔞 : 𝔞 ≠ ⊥) {d b : 𝓞 K} {I : Ideal (𝓞 K)} {h : ℕ}
    (hd : d ≠ 0) (hI : ∀ x : K, x ∈ 𝔞 ↔ ∃ y ∈ I, (y : K) = (d : K) * x) (hh : h ≠ 0) (hb : b ≠ 0)
    (hIb : I ^ h = Ideal.span {b}) :
    idealLog 𝔞 = (h : ℝ)⁻¹ * (-∑ σ : K →+* ℂ, Real.log ‖σ b‖) - -∑ σ : K →+* ℂ, Real.log ‖σ d‖ := by
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have ha : ∃ a ∈ 𝔞, a ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  rw [idealLog, dif_pos ha]
  obtain ⟨ha1, ha0⟩ := ha.choose_spec
  generalize ha.choose = a at ha1 ha0
  obtain ⟨y, hy, hy'⟩ := (hI a).1 ha1
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hdK ha0 (by simpa using hy'.symm)
  let f : 𝓞 K →+ K := (AddMonoidHom.mulLeft (d : K)⁻¹).comp (algebraMap (𝓞 K) K).toAddMonoidHom
  have hf (x : 𝓞 K) : f x = (d : K)⁻¹ * (x : K) := rfl
  have hfi : Function.Injective f := fun x x' hx => by
    rw [hf, hf] at hx
    exact RingOfIntegers.ext (mul_left_cancel₀ (inv_ne_zero hdK) hx)
  have e1 : 𝔞.toAddSubgroup = I.toAddSubgroup.map f := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, hI, hf]
    refine exists_congr fun z => and_congr_right fun _ => ?_
    rw [inv_mul_eq_iff_eq_mul₀ hdK]
  have e2 : (Submodule.span (𝓞 K) {a}).toAddSubgroup = (Ideal.span {y}).toAddSubgroup.map f := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, hf, Ideal.mem_span_singleton',
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨c * y, ⟨c, rfl⟩, ?_⟩
      rw [Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap (c * y), map_mul, ← RingOfIntegers.coe_eq_algebraMap y, hy']
      field_simp
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨c, ?_⟩
      rw [Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap (c * y), map_mul, ← RingOfIntegers.coe_eq_algebraMap y, hy']
      field_simp
  have hle : (Ideal.span {y}).toAddSubgroup ≤ I.toAddSubgroup := (Ideal.span_singleton_le_iff_mem I).2 hy
  have h1 := AddSubgroup.relIndex_mul_index hle
  have hN (J : Ideal (𝓞 K)) : J.toAddSubgroup.index = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [hN, hN] at h1
  have hy1 : Ideal.absNorm (Ideal.span {y}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hy0
  rw [← h1] at hy1
  have h2 : Real.log (Ideal.absNorm (Ideal.span {y}) : ℝ) =
      Real.log ((Ideal.span {y}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) + Real.log (Ideal.absNorm I : ℝ) := by
    rw [← h1, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.2 (left_ne_zero_of_mul hy1))
      (Nat.cast_ne_zero.2 (right_ne_zero_of_mul hy1))]
  have h3 : ∑ σ : K →+* ℂ, Real.log ‖σ b‖ = h * Real.log (Ideal.absNorm I : ℝ) := by
    rw [sum_log_norm_eq_log_absNorm b hb, ← hIb, map_pow, Nat.cast_pow, Real.log_pow]
  have h4 : ∑ σ : K →+* ℂ, Real.log ‖σ y‖ =
      ∑ σ : K →+* ℂ, Real.log ‖σ d‖ + ∑ σ : K →+* ℂ, Real.log ‖σ a‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hy', map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero σ).2 hdK))
      (norm_ne_zero_iff.2 ((map_ne_zero σ).2 ha0))]
  rw [sum_log_norm_eq_log_absNorm y hy0, h2] at h4
  have hh' : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  rw [e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ hfi, h3, mul_neg, inv_mul_cancel_left₀ hh']
  linarith

end IdealSup

theorem finsum_sum_log_iSup_eq_idealLog : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (φ : F →+* K) (𝔞 : Submodule (𝓞 K) K), 𝔞.FG → 𝔞 ≠ ⊥ → (Function.support fun v : HeightOneSpectrum (𝓞 F) => ∑ θ : EmbOver φ, Real.log (⨆ a : 𝔞, (extOf v).w (θ.1 a))).Finite ∧ ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ, Real.log (⨆ a : 𝔞, (extOf v).w (θ.1 a)) = idealLog 𝔞 := by
  intro F _ _ K _ _ φ 𝔞 hfg h𝔞
  obtain ⟨d, I, hd, hI⟩ := exists_ideal_mem_iff_of_fg 𝔞 hfg
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
    obtain ⟨y, hy, hy'⟩ := (hI a).1 ha
    rw [Ideal.mem_bot] at hy
    subst hy
    exact mul_ne_zero hdK ha0 (by simpa using hy'.symm)
  obtain ⟨h, b, hh, hb, hIb⟩ := exists_pow_eq_span_of_ne_bot I hI0
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => ∑ θ : EmbOver φ, Real.log (⨆ a : 𝔞, (extOf v).w (θ.1 a))) =
      fun v => (h : ℝ)⁻¹ * (∑ θ : EmbOver φ, Real.log ((extOf v).w (θ.1 b))) -
        ∑ θ : EmbOver φ, Real.log ((extOf v).w (θ.1 d)) := by
    funext v
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    exact log_iSup_abv_eq ((extOf v).w.comp θ.1.injective)
      (fun x y => by
        change (extOf v).w (θ.1 (x + y)) ≤ max ((extOf v).w (θ.1 x)) ((extOf v).w (θ.1 y))
        rw [map_add]
        exact TrueGeo.Ext.w_add_le_max F v _ _ _)
      (fun x => (extOf v).w_le_one_of_isIntegral (x.isIntegral_coe.map θ.1.toIntAlgHom)) 𝔞 hd hI hh hb hIb
  obtain ⟨b1, b2⟩ := finsum_sum_log_embOver_eq φ (b : K) hbK
  obtain ⟨d1, d2⟩ := finsum_sum_log_embOver_eq φ (d : K) hdK
  have b3 : (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      (h : ℝ)⁻¹ * ∑ θ : EmbOver φ, Real.log ((extOf v).w (θ.1 b))).Finite :=
    b1.subset (Function.support_mul_subset_right _ _)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (b3.union d1).subset (Function.support_sub _ _)
  · rw [hfun, finsum_sub_distrib b3 d1, ← mul_finsum, b2, d2, idealLog_eq_of_pow_eq_span 𝔞 h𝔞 hd hI hh hb hIb]

end GlobalTheory.LieSmooth

end
