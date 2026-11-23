import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchInt
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LibFresh

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.DivisorSumOrder

variable {F : Type} [Field F] [NumberField F]

theorem ordI_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) : ordI v w.asIdeal = 0 := by
  by_contra h0
  have h1 := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).1 h0
  exact h (HeightOneSpectrum.ext (associated_iff_eq.1 ((v.prime.dvd_prime_iff_associated w.prime).1 h1)))

theorem ordI_top (v : HeightOneSpectrum (𝓞 F)) : ordI v (⊤ : Ideal (𝓞 F)) = 0 := by
  by_contra h0
  have h1 := (Associates.count_ne_zero_iff_dvd top_ne_bot v.irreducible).1 h0
  exact v.isPrime.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 h1))

open Classical in
theorem ordI_pow (v w : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    ordI v (w.asIdeal ^ k) = if v = w then k else 0 := by
  induction k with
  | zero => rw [pow_zero, Ideal.one_eq_top, ordI_top]; split_ifs <;> rfl
  | succ k ih =>
    rw [pow_succ, Fresh.ordI_mul_of_ne_bot v (pow_ne_zero _ w.ne_bot) w.ne_bot, ih]
    by_cases h : v = w
    · rw [if_pos h, if_pos h, h, Fresh.ordI_asIdeal_self]
    · rw [if_neg h, if_neg h, ordI_ne h]

theorem prodS_ne_bot (T : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F) → ℕ) :
    (∏ w ∈ T, w.asIdeal ^ p w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro w _
  exact pow_ne_zero _ w.ne_bot

open Classical in
theorem ordI_prodS (T : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F) → ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : ordI v (∏ w ∈ T, w.asIdeal ^ p w) = if v ∈ T then p v else 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top, ordI_top]; simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Fresh.ordI_mul_of_ne_bot v (pow_ne_zero _ a.ne_bot) (prodS_ne_bot T p), ordI_pow, ih]
    by_cases h1 : v = a
    · subst h1
      simp [ha]
    · by_cases h2 : v ∈ T
      · simp [h1, h2]
      · simp [h1, h2]

theorem eq_of_ordI {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ w : HeightOneSpectrum (𝓞 F), ordI w I = ordI w J) :
    I = J := by
  classical
  have key : Associates.mk I = Associates.mk J := by
    refine Associates.eq_of_eq_counts (Associates.mk_ne_zero.2 hI) (Associates.mk_ne_zero.2 hJ) fun p hp => ?_
    obtain ⟨P, rfl⟩ := Associates.exists_rep p
    have hP : Irreducible P := Associates.irreducible_mk.1 hp
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, Ideal.isPrime_of_prime hP.prime, hP.ne_zero⟩
    have := h v
    unfold ordI at this
    convert this using 2
  exact associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 key)

theorem ordI_le_of_dvd {r m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (h : r ∣ m) (w : HeightOneSpectrum (𝓞 F)) :
    ordI w r ≤ ordI w m := by
  obtain ⟨s, rfl⟩ := h
  have hr : r ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.bot_mul])
  have hs : s ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.mul_bot])
  rw [Fresh.ordI_mul_of_ne_bot w hr hs]
  exact Nat.le_add_right _ _

theorem dvd_fin {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) : {r : Ideal (𝓞 F) | r ∣ m}.Finite := by
  have := UniqueFactorizationMonoid.fintypeSubtypeDvd m hm
  exact Set.finite_coe_iff.1 (Finite.of_fintype {r // r ∣ m})

open Classical in

def ext (S : Finset (HeightOneSpectrum (𝓞 F))) (p : S → ℕ) (w : HeightOneSpectrum (𝓞 F)) : ℕ :=
  if h : w ∈ S then p ⟨w, h⟩ else 0

theorem ordI_prod_ext (S : Finset (HeightOneSpectrum (𝓞 F))) (p : S → ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    ordI v (∏ w ∈ S, w.asIdeal ^ ext S p w) = ext S p v := by
  classical
  rw [ordI_prodS]
  unfold ext
  split_ifs <;> rfl

theorem divS_eq (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ w ∉ S, ordI w m = 0) :
    divS ω c m = ∏ w ∈ S, ∑ j ∈ Finset.range (ordI w m + 1), L4.chiW ω c w ^ j := by
  classical
  rw [← Finset.prod_coe_sort S, Finset.prod_univ_sum]
  unfold divS
  rw [finsum_mem_eq_finite_toFinset_sum _ (dvd_fin hm)]
  symm
  refine Finset.sum_nbij' (fun p => ∏ w ∈ S, w.asIdeal ^ ext S p w) (fun r => fun w : S => ordI w.1 r) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have hp' : ∀ w : S, p w ≤ ordI w.1 m := fun w => by
      have := Fintype.mem_piFinset.1 hp w
      rw [Finset.mem_range] at this
      omega
    refine ⟨∏ w ∈ S, w.asIdeal ^ (ordI w m - ext S p w), ?_⟩
    have hne : (∏ w ∈ S, w.asIdeal ^ ext S p w) * (∏ w ∈ S, w.asIdeal ^ (ordI w m - ext S p w)) ≠ ⊥ := by
      rw [Ne, Ideal.mul_eq_bot, not_or]
      exact ⟨prodS_ne_bot _ _, prodS_ne_bot _ _⟩
    refine eq_of_ordI hm hne fun v => ?_
    rw [Fresh.ordI_mul_of_ne_bot v (prodS_ne_bot _ _) (prodS_ne_bot _ _), ordI_prod_ext, ordI_prodS]
    by_cases hv : v ∈ S
    · rw [if_pos hv]
      have h1 : ext S p v = p ⟨v, hv⟩ := by unfold ext; rw [dif_pos hv]
      have h2 : p ⟨v, hv⟩ ≤ ordI v m := hp' ⟨v, hv⟩
      rw [h1]
      omega
    · rw [if_neg hv, hS v hv]
      unfold ext
      rw [dif_neg hv]
  · intro r hr
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hr
    rw [Fintype.mem_piFinset]
    intro w
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (ordI_le_of_dvd hm hr w)
  · intro p _
    funext w
    rw [ordI_prod_ext]
    unfold ext
    rw [dif_pos w.2]
  · intro r hr
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hr
    have hr0 : r ≠ ⊥ := fun h0 => hm (by rw [h0] at hr; exact zero_dvd_iff.1 hr)
    refine eq_of_ordI (prodS_ne_bot _ _) hr0 fun v => ?_
    rw [ordI_prod_ext]
    unfold ext
    split_ifs with hv
    · rfl
    · have := ordI_le_of_dvd hm hr v
      rw [hS v hv] at this
      omega
  · intro p _
    unfold chiI
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [ordI_prod_ext]
      unfold ext L4.chiW
      rw [dif_pos w.2]
    · intro v hv
      by_contra hvS
      apply hv
      beta_reduce
      rw [ordI_prod_ext]
      unfold ext
      rw [dif_neg fun h => hvS (Finset.mem_coe.2 h), pow_zero]

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.DivisorSumOrder

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open DivisorSumOrder

theorem coefficient_divisor_holds : CoefDiv := by
  intro F _ _ _ ω c z m S hz hS
  classical
  unfold coefAt
  by_cases hpos : ∀ w ∈ S, 0 ≤ m w
  · rw [if_pos hpos]
    have hex : ∃ 𝔪, GenD z 𝔪 := by
      refine ⟨∏ w ∈ S, w.asIdeal ^ (m w).toNat, prodS_ne_bot _ _, fun w => ?_⟩
      rw [hz w, ordI_prodS]
      congr 1
      by_cases hw : w ∈ S
      · rw [if_pos hw, Int.toNat_of_nonneg (hpos w hw)]; rfl
      · rw [if_neg hw, hS w hw]; rfl
    rw [dif_pos hex]
    have hspec := hex.choose_spec
    set 𝔪 := hex.choose
    have hord : ∀ w, (ordI w 𝔪 : ℤ) = m w := by
      intro w
      have h := (hspec.2 w).symm.trans (hz w)
      rw [WithZero.exp_inj] at h
      unfold dd at h
      omega
    rw [divS_eq ω c hspec.1 S fun w hw => by have := hord w; rw [hS w hw] at this; omega]
    refine Finset.prod_congr rfl fun w _ => ?_
    congr 2
    have := hord w
    omega
  · rw [if_neg hpos, dif_neg]
    rintro ⟨𝔪, -, h𝔪⟩
    apply hpos
    intro w _
    have h := (h𝔪 w).symm.trans (hz w)
    rw [WithZero.exp_inj] at h
    unfold dd at h
    omega

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
