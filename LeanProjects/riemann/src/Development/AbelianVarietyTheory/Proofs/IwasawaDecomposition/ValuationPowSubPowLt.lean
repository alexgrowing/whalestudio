import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassHost

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal
open GlobalTheory.AntiRamConj GlobalTheory.Mem.Chr GlobalTheory.AntiLAdic
open scoped Pointwise

namespace GlobalTheory.GalToHecke

section Tame

variable {L : Type} [Field L] [NumberField L]

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

theorem locK_eq_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (x y : Lˣ)
    (hxy : v.valuation L ((y : L) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (x : L)) :
    χ.locK v y = χ.locK v x := by
  have hx0 : v.valuation L (x : L) ≠ 0 := by simp
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have h1 : v.valuation L (((y * x⁻¹ : Lˣ) : L) - 1) ≤ WithZero.exp (-1 : ℤ) := by
    have : ((y * x⁻¹ : Lˣ) : L) - 1 = ((y : L) - x) * (x : L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, _root_.sub_mul, mul_inv_cancel₀ x.ne_zero]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hx0)]
    exact hxy
  have h2 : v.valuation L ((y * x⁻¹ : Lˣ) : L) = 1 := by
    have := Valuation.map_one_add_of_lt (v.valuation L) (h1.trans_lt exp_neg_one_lt_one)
    rwa [add_sub_cancel] at this
  have h3 : χ.locK v (y * x⁻¹) = 1 := by
    refine h (atFin v (y * x⁻¹)) ?_ ?_
    · exact (hval _).trans h2
    · have : ((atFin v (y * x⁻¹) : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
          algebraMap L (v.adicCompletion L) (((y * x⁻¹ : Lˣ) : L) - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this, hval]
      simpa using h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at h3

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, v.intValuation (t v) = WithZero.exp (-(n : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg (ht v)⟩
  choose n hn using hn
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun v => n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
  have e1 : v.valuation L ((y : L) - (t v : L)) = v.intValuation (y - t v) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := L)]; simp
  have e2 : v.valuation L (t v : L) = v.intValuation (t v) := HeightOneSpectrum.valuation_of_algebraMap (K := L) v _
  rw [e1, e2, hn, ← WithZero.exp_add]
  convert h1 using 2
  push_cast; ring

end Tame

section Basic

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Ideles E →* Gab E Ω}

def IsHeckeOf (art : Ideles E →* Gab E Ω) (r : G E Ω →* ℂˣ) (χ : HChar E) : Prop :=
  ∀ (x : Ideles E) (σ : G E Ω), art x = toAb E Ω σ → χ.1 x = r σ

def heckeOf (ha : IsGlobalArtin art) (r : G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (G E Ω))) : HChar E :=
  ⟨(liftAb r (continuous_of_isOpen_ker' r hr)).comp art,
    (continuous_liftAb r (continuous_of_isOpen_ker' r hr)).comp ha.quot.continuous, fun k => by
      have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one]⟩

theorem isHeckeOf_heckeOf (ha : IsGlobalArtin art) (r : G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (G E Ω))) :
    IsHeckeOf art r (heckeOf ha r hr) := fun x σ h => by
  show liftAb r (continuous_of_isOpen_ker' r hr) (art x) = r σ
  rw [h, liftAb_toAb]

variable {r : G E Ω →* ℂˣ} {χ : HChar E} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem IsHeckeOf.unique (h : IsHeckeOf art r χ) {χ' : HChar E} (h' : IsHeckeOf art r χ') : χ = χ' :=
  Subtype.ext (MonoidHom.ext fun x => by
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    rw [h x σ hσ.symm, h' x σ hσ.symm])

theorem IsHeckeOf.orderDvd (h : IsHeckeOf art r χ) {m : ℕ} (hm : ∀ σ, r σ ^ m = 1) : χ.OrderDvd m :=
  Subtype.ext (MonoidHom.ext fun x => by
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    show χ.1 x ^ m = 1
    rw [h x σ hσ.symm, hm])

theorem IsHeckeOf.unr_iff (ha : IsGlobalArtin art) (h : IsHeckeOf art r χ) (hA : IsPlaceOver A v) :
    χ.UnrAt v ↔ ∀ σ ∈ Ine (F := E) A, r σ = 1 := by
  constructor
  · intro H σ hσ
    obtain ⟨x, hx, e⟩ := (ha.ine v A hA _).2 ⟨σ, hσ, rfl⟩
    rw [← h _ σ e]
    exact H x hx
  · intro H x hx
    obtain ⟨σ, hσ, e⟩ := (ha.ine v A hA _).1 ⟨x, hx, rfl⟩
    exact (h _ σ e.symm).trans (H σ hσ)

theorem IsHeckeOf.val_eq (ha : IsGlobalArtin art) (h : IsHeckeOf art r χ) (hu : χ.UnrAt v) (hA : IsPlaceOver A v)
    {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) : χ.val v = (r σ)⁻¹ := by
  obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).2 ⟨σ, hσ, rfl⟩
  rw [← χ.val_eq hu x hx, ← map_inv]
  exact h _ _ e

theorem IsHeckeOf.loc_eq_one (ha : IsGlobalArtin art) (h : IsHeckeOf art r χ) (hA : IsPlaceOver A v)
    (H : ∀ σ ∈ Dec (F := E) A, r σ = 1) (x : (v.adicCompletion E)ˣ) : χ.loc v x = 1 := by
  have hm : art (localIdele E v x) ∈ (Dec (F := E) A).map (toAb E Ω) := by
    rw [← ha.dec v A hA]
    exact Subgroup.le_topologicalClosure _ ⟨x, rfl⟩
  obtain ⟨σ, hσ, e⟩ := hm
  exact (h _ σ e.symm).trans (H σ hσ)

theorem tameAt_of_orderDvd {l k : ℕ} (hl : l.Prime) (h : χ.OrderDvd (l ^ k)) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    χ.TameAt v := by
  intro x _ hx
  have h1 : ∀ y, χ.1 y ^ (l ^ k) = 1 := fun y => congrArg (fun ξ : HChar E => ξ.1 y) h
  have ho := isOpen_ker_of_pow χ.1 χ.2.1 (pow_pos hl.pos k) h1
  let θ : (v.adicCompletion E)ˣ →* rootsOfUnity (l ^ k) ℂ := (χ.loc v).codRestrict _ fun y => h1 _
  have := GlobalTheory.RingCls.tame hl (B := rootsOfUnity (l ^ k) ℂ) (fun z => ⟨k, Subtype.ext z.2⟩) hv θ (by
    convert ho.preimage (Determ.continuous_localIdele v) using 1
    ext y
    exact Subtype.ext_iff) x (hx.trans_lt (by simpa using exp_neg_one_lt_one))
  exact congrArg Subtype.val this

theorem locInf_eq_one [IsTotallyComplex E] {m : ℕ} (hm : 0 < m) (h : χ.OrderDvd m) (w : InfinitePlace E)
    (y : (w.Completion)ˣ) : χ.locInf w y = 1 := by
  have h1 : ∀ y, χ.1 y ^ m = 1 := fun y => congrArg (fun ξ : HChar E => ξ.1 y) h
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e y) hm
  have hy : e.symm z ^ m = y := e.injective (by rw [map_pow, e.apply_symm_apply, hz])
  have h0 : e.symm z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm.ne'] at hy
    exact y.ne_zero hy.symm
  have e1 : y = Units.mk0 _ h0 ^ m := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy.symm)
  rw [e1, map_pow]
  exact h1 _

end Basic

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_aboveF {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  simp [aboveF]

theorem valuation_up (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (P : HeightOneSpectrum (𝓞 E)) (x : F) :
    P.valuation E (algebraMap F E x) = (P.under (𝓞 F)).valuation F x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := hr P (Units.mk0 x hx)
  unfold ordF at h
  have h1 : P.valuation E (algebraMap F E x) ≠ 0 := by simpa using hx
  have h2 : (P.under (𝓞 F)).valuation F x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h1, ← WithZero.exp_log h2]
  exact congrArg WithZero.exp (neg_injective h)

theorem resFin_eq (χ : HChar E) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    χ.resFin v k = ∏ P ∈ aboveF (L := E) F v, χ.locK P (upF F k) := by
  rw [HChar.resFin, MonoidHom.finsetProd_apply]
  rfl

theorem trivOn_of_cofinite (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (χ : HChar E) (htame : ∀ P, χ.TameAt P) (hinf : ∀ w y, χ.locInf w y = 1) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hu : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ T → χ.UnrAt P)
    (hv : ∀ v, v ∉ T → ∏ P ∈ aboveF (L := E) F v, χ.val P = 1) : χ.TrivOn F := by
  classical
  have h0 : ∀ v, v ∉ T → ∀ k, χ.resFin v k = 1 := fun v hvT k => by
    rw [resFin_eq, Finset.prod_congr rfl (g := fun P => χ.val P ^ ordF v k) fun P hP => by
      have e := mem_aboveF.1 hP
      rw [GlobalTheory.HeckeProduct.locK_unr χ (hu P (e ▸ hvT)), hr, e], Finset.prod_zpow, hv v hvT, one_zpow]
  have h1 : ∀ k : Fˣ, ∏ v ∈ T, χ.resFin v k = 1 := fun k => by
    let T' := T ∪ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset
    have hS : ∀ P : HeightOneSpectrum (𝓞 E), P ∈ T'.biUnion (aboveF (L := E) F) ↔ P.under (𝓞 F) ∈ T' := fun P => by
      simp [Finset.mem_biUnion, mem_aboveF, -Finset.mem_union]
    have h := GlobalTheory.HeckeProduct.productRule χ (T'.biUnion (aboveF (L := E) F))
      (fun P hP => hu P fun hm => hP ((hS P).2 (Finset.mem_union_left _ hm))) (upF F k)
    have hi : χ.inf (upF F k) = 1 := by
      show χ.1 (infDiag _) = 1
      rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
      exact Finset.prod_eq_one fun w _ => hinf w _
    have hf : (∏ᶠ (P : HeightOneSpectrum (𝓞 E)) (_ : P ∉ T'.biUnion (aboveF (L := E) F)),
        χ.val P ^ ordF P (upF F k)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun P => ?_
      by_cases hP : P ∈ T'.biUnion (aboveF (L := E) F)
      · exact finprod_eq_if.trans (if_neg (not_not.2 hP))
      rw [finprod_eq_if, if_pos hP]
      have : ordF (P.under (𝓞 F)) k = 0 := by
        by_contra hne
        exact hP ((hS P).2 (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 hne)))
      rw [hr, this, zpow_zero]
    rw [hi, hf, one_mul, mul_one, Finset.prod_biUnion (fun v _ v' _ hne => Finset.disjoint_left.2 fun P h1 h2 =>
      hne ((mem_aboveF.1 h1).symm.trans (mem_aboveF.1 h2)))] at h
    rw [← h]
    simp only [← resFin_eq]
    exact Finset.prod_subset Finset.subset_union_left fun v _ hvT => h0 v hvT k
  have h2 : ∀ v (x y : Fˣ), v.valuation F ((y : F) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation F (x : F) →
      χ.resFin v y = χ.resFin v x := fun v x y hxy => by
    rw [resFin_eq, resFin_eq]
    refine Finset.prod_congr rfl fun P hP => locK_eq_of_tame χ (htame P) _ _ ?_
    change P.valuation E (algebraMap F E y - algebraMap F E x) ≤ _ * P.valuation E (algebraMap F E x)
    rw [← map_sub, valuation_up hr, valuation_up hr, mem_aboveF.1 hP]
    exact hxy
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · by_cases hvT : v ∈ T
    swap
    · exact h0 v hvT k
    have key : ∀ (a : 𝓞 F) (ha : (a : F) ≠ 0), χ.resFin v (Units.mk0 (a : F) ha) = 1 := by
      intro a ha
      have ha' : a ≠ 0 := fun h => ha (by simp [h])
      obtain ⟨y, hy⟩ := exists_approx T (fun u => if u = v then a else 1)
        (fun u => by split_ifs; exacts [ha', one_ne_zero])
      have hP := hy v hvT
      simp only [if_true] at hP
      have hy0 : (y : F) ≠ 0 := by
        intro h0
        rw [h0, zero_sub, Valuation.map_neg] at hP
        have hpos : 0 < v.valuation F (a : F) := zero_lt_iff.2 (by simpa using ha')
        have := mul_lt_mul_of_pos_right exp_neg_one_lt_one hpos
        rw [one_mul] at this
        exact absurd hP (not_le.2 this)
      rw [← h2 v (Units.mk0 (a : F) ha) (Units.mk0 (y : F) hy0) hP, ← h1 (Units.mk0 (y : F) hy0)]
      symm
      refine Finset.prod_eq_single_of_mem v hvT fun u hu hne => ?_
      have h3 := hy u hu
      simp only [if_neg hne] at h3
      rw [h2 u 1 _ (by simpa using h3), map_one]
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 F) (k : F)
    have hb0 : (b : F) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
    have ha0 : (a : F) ≠ 0 := by
      intro h
      apply k.ne_zero
      rw [← hab]
      change (a : F) / _ = 0
      rw [h, zero_div]
    have hx : k = Units.mk0 (a : F) ha0 * (Units.mk0 (b : F) hb0)⁻¹ := by
      apply Units.ext
      rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]; rfl
    rw [hx, map_mul, map_inv, key, key, inv_one, mul_one]
  · rw [HChar.resInf, MonoidHom.finsetProd_apply]
    exact Finset.prod_eq_one fun w' _ => hinf w' _

end Adelic

section Galois

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field Ω] [Algebra E Ω]

theorem normV_eq (v : HeightOneSpectrum (𝓞 E)) : normV v = Ideal.absNorm v.asIdeal := rfl

theorem normV_inert (h2 : Module.finrank F E = 2)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    {P : HeightOneSpectrum (𝓞 E)} (hP : ∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → P' = P) :
    normV P = normV (P.under (𝓞 F)) ^ 2 := by
  set v := P.under (𝓞 F) with hv
  have := P.isPrime
  have := v.isMaximal
  have : P.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : v.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have h := HeightOneSpectrum.valuation_liesOver E v P π
    rw [valuation_up hr, ← hv, hπ, ← WithZero.exp_nsmul, WithZero.exp_inj] at h
    simpa using h
  have hs := Ideal.sum_ramification_inertia (𝓞 E) F E v.ne_bot
  have hset : IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) = {P.asIdeal} := by
    ext Q
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset v.ne_bot, Finset.mem_singleton]
    constructor
    · rintro ⟨hQ, hl⟩
      exact congrArg HeightOneSpectrum.asIdeal
        (hP ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩ (HeightOneSpectrum.ext hl.over.symm))
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  rw [hset, Finset.sum_singleton, he, one_mul, h2] at hs
  rw [normV_eq, normV_eq, ← hs]
  exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal v.asIdeal v.isPrime v.ne_bot

theorem not_forall_pow_sub_mem {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} (hq : normV P = q ^ 2) :
    ¬ ∀ x : 𝓞 E, x ^ q - x ∈ P.asIdeal := by
  intro h
  classical
  have := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  have hc : Fintype.card (𝓞 E ⧸ P.asIdeal) = q ^ 2 := by rw [← hq, ← Nat.card_eq_fintype_card]; rfl
  have h1 : 1 < q := by
    have : 1 < q ^ 2 := hc ▸ Fintype.one_lt_card
    exact (Nat.one_lt_pow_iff two_ne_zero).1 this
  have h3 := Polynomial.card_le_degree_of_subset_roots
    (p := (Polynomial.X ^ q - Polynomial.X : Polynomial (𝓞 E ⧸ P.asIdeal))) (Z := Finset.univ) (fun z _ => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ h1)]
      simpa using Ideal.Quotient.eq_zero_iff_mem.2 (h x))
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ h1, Finset.card_univ, hc] at h3
  nlinarith

theorem valuation_pow_sub_pow_lt (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1)
    (h : A.valuation (a - b) < 1) (q : ℕ) : A.valuation (a ^ q - b ^ q) < 1 := by
  rw [A.valuation_le_one_iff] at ha hb
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨a, ha⟩ : A) ⟨b, hb⟩ q
  have e : a ^ q - b ^ q = (a - b) * c := congrArg Subtype.val hc
  rw [e, map_mul]
  exact (mul_le_of_le_one_right' (A.valuation_le_one c)).trans_lt h

theorem exists_frob_inert [IsAlgClosure E Ω] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hne : c ≠ 1)
    (hinv : ∀ x, c (c x) = x)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (cc : Ω ≃+* Ω) (hcc : ∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) (hcc2 : ∀ x, cc (cc x) = x)
    {P : HeightOneSpectrum (𝓞 E)} (hP : ∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → P' = P)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A P) :
    ∃ g g' : G E Ω, (∀ x, g' x = cc (g (cc.symm x))) ∧ IsFrob (F := E) A (normV P) (g * g') := by
  letI : Algebra F Ω := ((algebraMap E Ω).comp (algebraMap F E)).toAlgebra
  haveI : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  have : IsGalois F E := inferInstance
  have hall : ∀ σ : E ≃ₐ[F] E, σ = 1 ∨ σ = c := by
    intro σ
    have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
    by_cases h : σ = 1
    · exact Or.inl h
    · exact Or.inr ((hy σ h).trans (hy c hne).symm)
  have hAv : IsPlaceOver A (P.under (𝓞 F)) := fun x => hA (algebraMap (𝓞 F) (𝓞 E) x)
  obtain ⟨τ, hτ⟩ := exists_isFrob hAv
  have hq := normV_inert h2 hr hP
  set q := normV (P.under (𝓞 F))
  have hτd : τ ∈ Dec (F := F) A := hτ.1
  have hres : ∀ x : E, τ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormal τ E x) := fun x =>
    (AlgEquiv.restrictNormal_commutes τ E x).symm
  rcases hall (AlgEquiv.restrictNormal τ E) with h | h
  · exfalso
    refine not_forall_pow_sub_mem hq fun x => (hA _).1 ?_
    have hx : A.valuation (algebraMap E Ω (x : E)) ≤ 1 := by
      exact Valuation.Integers.mem_of_integral (Valuation.valuationSubring.integers A.valuation)
        (((RingOfIntegers.isIntegral_coe x).map (algebraMap E Ω).toIntAlgHom).tower_top)
    have h1 := hτ.2 _ hx
    rw [hres, h, ← Valuation.map_neg, neg_sub] at h1
    simpa using h1
  · have hs : ∀ x, cc.symm x = cc x := fun x => by rw [RingEquiv.symm_apply_eq, hcc2]
    let g : G E Ω := { cc.trans (τ : Ω ≃+* Ω) with
      commutes' := fun x => by
        show τ (cc (algebraMap E Ω x)) = _
        rw [hcc, hres, h, hinv] }
    let g' : G E Ω := { (τ : Ω ≃+* Ω).trans cc with
      commutes' := fun x => by
        show cc (τ (algebraMap E Ω x)) = _
        rw [hres, h, hcc, hinv] }
    have e : ∀ x, (g * g') x = τ (τ x) := fun x => by
      show τ (cc (cc (τ x))) = _
      rw [hcc2]
    refine ⟨g, g', fun x => ?_, ?_, fun x hx => ?_⟩
    · show cc (τ x) = cc (τ (cc (cc.symm x)))
      rw [cc.apply_symm_apply]
    · show g * g' ∈ Dec (F := E) A
      rw [mem_Dec]
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
      obtain ⟨z, rfl⟩ := (g * g').surjective x
      have h1 : ((g * g')⁻¹ : G E Ω) ((g * g') z) = z := (g * g').symm_apply_apply z
      rw [h1, e, apply_mem_iff_of_mem_Dec hτd, apply_mem_iff_of_mem_Dec hτd]
    · have hx' : A.valuation (τ x) ≤ 1 := by
        rw [A.valuation_le_one_iff] at hx ⊢
        exact (apply_mem_iff_of_mem_Dec hτd x).2 hx
      have e2 : (g * g') x - x ^ normV P = (τ (τ x) - τ x ^ q) + (τ x ^ q - (x ^ q) ^ q) := by
        rw [e, hq, sq, pow_mul]; ring
      rw [e2]
      exact Valuation.map_add_lt _ (hτ.2 _ hx')
        (valuation_pow_sub_pow_lt A hx' (by rw [map_pow]; exact pow_le_one' hx q) (hτ.2 x hx) q)

theorem IsHeckeOf.trivOn [IsAlgClosure E Ω] [IsTotallyComplex E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hne : c ≠ 1)
    (hinv : ∀ x, c (c x) = x)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (cc : Ω ≃+* Ω) (hcc : ∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) (hcc2 : ∀ x, cc (cc x) = x)
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {r : G E Ω →* ℂˣ} {χ : HChar E} (h : IsHeckeOf art r χ)
    (hanti : AntiHom cc r) {m : ℕ} (hm : 0 < m) (ho : χ.OrderDvd m) (htame : ∀ P, χ.TameAt P) : χ.TrivOn F := by
  classical
  have hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y := fun x =>
    ⟨c x, by rw [RingEquiv.symm_apply_eq, hcc, hinv]⟩
  have hu : ∀ P : HeightOneSpectrum (𝓞 E),
      P.under (𝓞 F) ∉ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset.image (fun P => P.under (𝓞 F)) → χ.UnrAt P := by
    intro P hP
    by_contra hn
    exact hP (Finset.mem_image.2 ⟨P, by simpa using hn, rfl⟩)
  refine trivOn_of_cofinite hr χ htame (locInf_eq_one hm ho) _ hu fun v hv => ?_
  rcases (aboveF (L := E) F v).eq_empty_or_nonempty with h0 | ⟨P, hP⟩
  · rw [h0, Finset.prod_empty]
  obtain rfl := mem_aboveF.1 hP
  obtain ⟨P', hP'⟩ := (existsUnique_conjPl c.toRingEquiv P).exists
  have hs : aboveF (L := E) F (P.under (𝓞 F)) = {P, P'} := by
    ext Q
    rw [mem_aboveF, under_eq_iff_conjPl c h2 hne P Q, Finset.mem_insert, Finset.mem_singleton]
    refine or_congr Iff.rfl ⟨fun h' => (existsUnique_conjPl _ P).unique h' hP', ?_⟩
    rintro rfl
    exact hP'
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω P
  by_cases e : P = P'
  · subst e
    rw [Finset.pair_eq_singleton] at hs
    obtain ⟨g, g', hg, hσ⟩ := exists_frob_inert c h2 hne hinv hr cc hcc hcc2
      (fun Q hQ => Finset.mem_singleton.1 (hs ▸ mem_aboveF.2 hQ)) hA
    rw [hs, Finset.prod_singleton, h.val_eq ha (hu P hv) hA hσ, map_mul, hanti g g' hg, mul_inv_cancel, inv_one]
  · obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have hA' := isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) hcc hP' hA
    have hσ' := isFrob_conjHom cc hc hσ
    rw [← normV_conjPl hP'] at hσ'
    have hu' : χ.UnrAt P' := hu P' (by
      rwa [mem_aboveF.1 (hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self P') : P' ∈ aboveF F (P.under (𝓞 F)))])
    rw [hs, Finset.prod_pair e, h.val_eq ha (hu P hv) hA hσ, h.val_eq ha hu' hA' hσ',
      hanti σ _ (conjHom_apply cc hc σ), inv_inv, inv_mul_cancel]

end Galois

end GlobalTheory.GalToHecke

end
