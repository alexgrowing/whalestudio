import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotMemOfNonZeroDivisor
import GroundTheory.HeightsAndTheta.Heights.Intersections.PHorizNotMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace RegularityFunctionFieldNumber

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

section Chain

variable [DecidableEq K] {E : Type*} [Field E]

def cS (E : Type*) [Field E] (S : Finset K) (k : K) : MvPolynomial K E :=
  if k ∈ S then 0 else MvPolynomial.X k

def specMap (ψ : MRing ι →+* E) (S : Finset K) : MRing ι →ₐ[ℤ] MvPolynomial K E :=
  aeval fun p => cS E S p.1 * MvPolynomial.C (ψ (X p))

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem specMap_X (ψ : MRing ι →+* E) (S : Finset K) (p : Σ k, ι k) :
    specMap ψ S (X p) = cS E S p.1 * MvPolynomial.C (ψ (X p)) := aeval_X _ _

theorem specMap_form (ψ : MRing ι →+* E) (S : Finset K) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) :
    specMap ψ S g = (∏ k, cS E S k ^ a k) * MvPolynomial.C (ψ g) := by
  have e : (aeval fun p => MvPolynomial.C (ψ (X p)) : MRing ι →ₐ[ℤ] MvPolynomial K E) =
      ((MvPolynomial.C : E →+* MvPolynomial K E).comp ψ).toIntAlgHom :=
    MvPolynomial.algHom_ext fun p => by rw [aeval_X]; rfl
  rw [specMap, regularityLocalResidue_holds.aeval_blockScale_int hg, e]
  rfl

theorem card_add_two_le [CharZero E] (ψ : MRing ι →+* E) (j : ∀ k, ι k) (hj : ∀ k, ψ (X ⟨k, j k⟩) = 1)
    {P : Ideal (MRing ι)} [P.IsPrime] (hPh : IsMultiHomogIdeal P)
    (hPψ : ∀ (g : MRing ι) (a : K → ℕ), IsMultiHomog g a → g ∈ P → ψ g = 0)
    {u : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a) (huP : u ∉ P) (hψu : ψ u = 0) :
    ((Fintype.card K + 2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ P) := by
  let Q : Finset K → Ideal (MRing ι) := fun S => RingHom.ker (specMap ψ S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => RingHom.ker_isPrime _
  have hmem : ∀ S g, g ∈ Q S ↔ specMap ψ S g = 0 := fun S g => RingHom.mem_ker

  have hPQ : P < Q ∅ := by
    obtain ⟨T, hT, hPT⟩ := hPh
    refine SetLike.lt_iff_le_and_exists.mpr ⟨?_, u, ?_, huP⟩
    · rw [hPT, Ideal.span_le]
      intro g hg
      obtain ⟨b, hb⟩ := hT g hg
      rw [SetLike.mem_coe, hmem, specMap_form ψ ∅ hb, hPψ g b hb (hPT ▸ Ideal.subset_span hg), map_zero,
        mul_zero]
    · rw [hmem, specMap_form ψ ∅ hu, hψu, map_zero, mul_zero]

  have hstep : ∀ S k, k ∉ S → Q S < Q (insert k S) := by
    intro S k hk
    let ρ : MvPolynomial K E →+* MvPolynomial K E :=
      (aeval fun k' => if k' = k then (0 : MvPolynomial K E) else MvPolynomial.X k').toRingHom
    have e : ρ.comp (specMap ψ S).toRingHom = (specMap ψ (insert k S)).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun n => by simp) fun q => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, specMap_X, map_mul]
      congr 1
      · by_cases h1 : q.1 ∈ S
        · simp [ρ, cS, h1]
        · by_cases h2 : q.1 = k
          · subst h2
            simp [ρ, cS, h1]
          · simp [ρ, cS, h1, h2]
      · simp [ρ]
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, X ⟨k, j k⟩, ?_, ?_⟩
    · rw [hmem] at hg ⊢
      have := congrArg (fun f => f g) e
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
      rw [← this, hg, map_zero]
    · rw [hmem, specMap_X]
      simp [cS]
    · rw [hmem, specMap_X, hj, map_one, mul_one]
      simp only [cS, if_neg hk]
      exact MvPolynomial.X_ne_zero k

  let Qt : Ideal (MRing ι) := RingHom.ker ((Int.castRingHom (ZMod 2)).comp MvPolynomial.constantCoeff)
  have hQt : Qt.IsPrime := RingHom.ker_isPrime _
  have huniv : ∀ g, specMap ψ Finset.univ g = MvPolynomial.C ((MvPolynomial.constantCoeff g : ℤ) : E) := by
    intro g
    have e : (specMap ψ Finset.univ).toRingHom =
        (MvPolynomial.C : E →+* MvPolynomial K E).comp ((Int.castRingHom E).comp MvPolynomial.constantCoeff) :=
      MvPolynomial.ringHom_ext (fun n => by simp) fun q => by simp [specMap_X, cS]
    exact congrArg (fun f => f g) e
  have hc2 : MvPolynomial.constantCoeff (2 : MRing ι) = 2 := by
    rw [show (2 : MRing ι) = MvPolynomial.C 2 from (map_ofNat MvPolynomial.C 2).symm, constantCoeff_C]
  have hlast : Q Finset.univ < Qt := by
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, 2, ?_, ?_⟩
    · rw [hmem, huniv, MvPolynomial.C_eq_zero, Int.cast_eq_zero] at hg
      simp [Qt, RingHom.mem_ker, hg]
    · rw [RingHom.mem_ker, RingHom.comp_apply, hc2, map_ofNat]
      rfl
    · intro h
      rw [hmem, huniv, MvPolynomial.C_eq_zero, Int.cast_eq_zero, hc2] at h
      exact two_ne_zero h

  have chain : ∀ S : Finset K, (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) ≤
      ringKrullDim (MRing ι ⧸ Q ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have : (Q (insert k S)).IsPrime := hQp _
      have h1 := HorizNotMem.ringKrullDim_quotient_add_one_le (hstep S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + (ringKrullDim (MRing ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) := by gcongr
        _ ≤ _ := ih
  have : (Q ∅).IsPrime := hQp _
  have : (Q Finset.univ).IsPrime := hQp _
  have h0 := HorizNotMem.ringKrullDim_quotient_add_one_le hPQ
  have h2 := HorizNotMem.ringKrullDim_quotient_add_one_le hlast
  have hc := chain Finset.univ
  have : IsDomain (MRing ι ⧸ Qt) := Ideal.Quotient.isDomain _
  have h3 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ Qt) := ringKrullDim_nonneg_of_nontrivial
  rw [Finset.card_univ] at hc
  calc ((Fintype.card K + 2 : ℕ) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + (0 + 1) + 1 := by
        push_cast; simp [add_assoc]; rfl
    _ ≤ (Fintype.card K : WithBot ℕ∞) + (ringKrullDim (MRing ι ⧸ Qt) + 1) + 1 := by gcongr
    _ ≤ (Fintype.card K : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q Finset.univ) + 1 := by gcongr
    _ ≤ ringKrullDim (MRing ι ⧸ Q ∅) + 1 := by gcongr
    _ ≤ _ := h0

end Chain

theorem funField_le_locRing (P : Ideal (MRing ι)) [P.IsPrime] : funField P ≤ locRing P P := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
  exact Subring.subset_closure ⟨u, v, a, hv,
    fun h => nonZeroDivisors.ne_zero hv (Ideal.Quotient.eq_zero_iff_mem.mpr h), hu, hva, rfl⟩

end RegularityFunctionFieldNumber

open regularityEmbedding_holds in

theorem RegularityFunctionFieldNumber.proof : RegularityFunctionFieldNumber.Statement := by
  intro K _ ι _ P hP
  classical
  obtain ⟨-, ⟨hPp, hPh, hPr⟩, hhor, hdim⟩ := hP
  have := hPp
  have hfrac : ∀ x ∈ funField P, ∃ (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ P ∧
      x * toFrac P v = toFrac P u := fun x hx =>
    LocRingFrac.proof K ι P P hPp hPp le_rfl x (RegularityFunctionFieldNumber.funField_le_locRing P hx)
  have hv0 : ∀ v : MRing ι, v ∉ P → toFrac P v ≠ 0 := fun v hv h => hv (toFrac_eq_zero.mp h)

  have hF : IsField (funField P) := by
    refine ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩, mul_comm, fun {x} hx => ?_⟩
    obtain ⟨u, v, a, hu, hv, hvP, hx'⟩ := hfrac x x.2
    have huP : u ∉ P := fun h => by
      rw [toFrac_eq_zero.mpr h] at hx'
      exact hx (Subtype.ext ((mul_eq_zero.mp hx').resolve_right (hv0 v hvP)))
    obtain ⟨y, hy⟩ := exists_funField_mul_eq hv hu huP
    have hy' : (y : FractionRing (MRing ι ⧸ P)) * toFrac P u = toFrac P v := hy
    refine ⟨y, Subtype.ext ?_⟩
    have e : ((x : FractionRing (MRing ι ⧸ P)) * y) * toFrac P u = 1 * toFrac P u := by
      rw [mul_assoc, hy', one_mul]
      exact hx'
    exact mul_right_cancel₀ (hv0 u huP) e
  refine ⟨hF, ?_⟩

  have hY : ∀ n : ℕ, (n : FractionRing (MRing ι ⧸ P)) = 0 → n = 0 := by
    intro n hn
    have h1 : toFrac P (n : MRing ι) = 0 := by rw [map_natCast]; exact hn
    have h3 : ((n : ℤ)) ∈ P.comap (MvPolynomial.C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact toFrac_eq_zero.mp h1
    rw [show P.comap (MvPolynomial.C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h3
    exact_mod_cast h3
  have : CharZero (FractionRing (MRing ι ⧸ P)) := charZero_of_inj_zero hY

  choose j hj using hPr
  have hr : ∀ p : Σ k, ι k, ∃ x : funField P,
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, j p.1⟩) = toFrac P (X p) := fun p =>
    exists_funField_mul_eq (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 (j p.1)) (hj p.1)
  choose r hr using hr
  let ρ : (Σ k, ι k) → FractionRing (MRing ι ⧸ P) := fun p => r p
  let φ : MRing ι →+* FractionRing (MRing ι ⧸ P) := eval₂Hom (Int.castRingHom _) ρ
  have hφ : ∀ (g : MRing ι) (a : K → ℕ), IsMultiHomog g a →
      φ g * toFrac P (∏ k, (X ⟨k, j k⟩ : MRing ι) ^ a k) = toFrac P g := fun g a hg => by
    rw [← chartHom_mul j r hr hg, chartHom_coe]
  have hφr : ∀ (g v : MRing ι) (a : K → ℕ), IsMultiHomog g a → IsMultiHomog v a →
      ∀ x : FractionRing (MRing ι ⧸ P), x * toFrac P v = toFrac P g → φ g = x * φ v := by
    intro g v a hg hv x hx
    apply mul_right_cancel₀ (toFrac_prod_ne_zero j hj a)
    rw [hφ g a hg, mul_assoc, hφ v a hv, hx]

  let D : Subalgebra ℚ (FractionRing (MRing ι ⧸ P)) := Algebra.adjoin ℚ (Set.range ρ)
  have hφD : ∀ g, φ g ∈ D := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C n =>
      rw [eval₂Hom_C, eq_intCast]
      exact intCast_mem D n
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f p hf =>
      rw [map_mul]
      refine mul_mem hf ?_
      rw [eval₂Hom_X']
      exact Algebra.subset_adjoin ⟨p, rfl⟩
  have hDF : ∀ x ∈ D, x ∈ funField P := by
    intro x hx
    have hx' : x ∈ D.toSubring := hx
    rw [Algebra.adjoin_eq_ring_closure] at hx'
    refine (Subring.closure_le.mpr (Set.union_subset ?_ ?_)) hx'
    · rintro _ ⟨q, rfl⟩
      have hden : ((q.den : funField P)) ≠ 0 := fun h => by
        have := congrArg Subtype.val h
        simp only [Subring.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this
        exact q.den_ne_zero this
      obtain ⟨w, hw⟩ := hF.mul_inv_cancel hden
      have hw' : ((q.den : FractionRing (MRing ι ⧸ P))) * w = 1 := by
        have := congrArg Subtype.val hw
        simpa using this
      rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right hw']
      exact mul_mem (intCast_mem _ _) w.2
    · rintro _ ⟨p, rfl⟩
      exact (r p).2

  have hunit : ∀ d ∈ D, d ≠ 0 → d⁻¹ ∈ D := by
    intro d hdD hd0
    by_contra hinv
    let d' : D := ⟨d, hdD⟩
    have hnu : ¬ IsUnit d' := by
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
      apply hinv
      have e : d * (w : FractionRing (MRing ι ⧸ P)) = 1 := congrArg Subtype.val hw
      rw [← eq_inv_of_mul_eq_one_right e]
      exact w.2
    obtain ⟨m, hm, hdm⟩ := Ideal.exists_le_maximal (Ideal.span {d'})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    let _ : Field (D ⧸ m) := Ideal.Quotient.field m
    have hcz : CharZero (D ⧸ m) := charZero_of_inj_zero fun n hn => by
      by_contra hn0
      have hu : IsUnit (n : D) := isUnit_iff_exists_inv.mpr ⟨algebraMap ℚ D (n : ℚ)⁻¹, by
        rw [← map_natCast (algebraMap ℚ D) n, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn0), map_one]⟩
      have hmem : (n : D) ∈ m := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
        exact hn
      exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
    let ψ : MRing ι →+* D ⧸ m := (Ideal.Quotient.mk m).comp (φ.codRestrict D hφD)
    have hψ : ∀ g, ψ g = Ideal.Quotient.mk m ⟨φ g, hφD g⟩ := fun g => rfl
    obtain ⟨u, v, a, hu, hv, hvP, hdu⟩ := hfrac d (hDF d hdD)
    have huP : u ∉ P := fun h => by
      rw [toFrac_eq_zero.mpr h] at hdu
      exact hd0 ((mul_eq_zero.mp hdu).resolve_right (hv0 v hvP))
    have key := RegularityFunctionFieldNumber.card_add_two_le (E := D ⧸ m) ψ j (fun k => ?_) hPh (fun g b hg hgP => ?_)
      hu huP ?_
    · rw [hdim] at key
      have h' : Fintype.card K + 2 ≤ 1 + Fintype.card K := by exact_mod_cast key
      omega
    · have e1 : φ (X ⟨k, j k⟩) = 1 := by
        rw [eval₂Hom_X']
        exact mul_right_cancel₀ (hv0 _ (hj k)) ((hr ⟨k, j k⟩).trans (one_mul _).symm)
      rw [hψ]
      have e2 : (⟨φ (X ⟨k, j k⟩), hφD _⟩ : D) = 1 := Subtype.ext e1
      rw [e2, map_one]
    · have e1 : φ g = 0 := by
        have := hφ g b hg
        rw [toFrac_eq_zero.mpr hgP] at this
        exact (mul_eq_zero.mp this).resolve_right (toFrac_prod_ne_zero j hj b)
      rw [hψ]
      have e2 : (⟨φ g, hφD _⟩ : D) = 0 := Subtype.ext e1
      rw [e2, map_zero]
    · rw [hψ, Ideal.Quotient.eq_zero_iff_mem]
      have e : (⟨φ u, hφD u⟩ : D) = d' * ⟨φ v, hφD v⟩ := Subtype.ext (hφr u v a hu hv d hdu)
      rw [e]
      exact Ideal.mul_mem_right _ _ (hdm (Ideal.subset_span rfl))

  have hFD : ∀ x ∈ funField P, x ∈ D := by
    intro x hx
    obtain ⟨u, v, a, hu, hv, hvP, hx'⟩ := hfrac x hx
    have hφv : φ v ≠ 0 := fun h => hv0 v hvP (by
      have := hφ v a hv
      rw [h, zero_mul] at this
      exact this.symm)
    have e : x = φ u * (φ v)⁻¹ := by
      rw [hφr u v a hu hv x hx', mul_assoc, mul_inv_cancel₀ hφv, mul_one]
    rw [e]
    exact mul_mem (hφD u) (hunit _ (hφD v) hφv)

  have hDft : Algebra.FiniteType ℚ D := (Subalgebra.fg_iff_finiteType D).mp
    ⟨Finset.univ.image ρ, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩

  let _ : Field (funField P) := hF.toField
  have : CharZero (funField P) := charZero_of_inj_zero fun n hn => hY n (by
    have := congrArg Subtype.val hn
    simpa using this)
  let e : funField P ≃+* D :=
    { toFun := fun x => ⟨x, hFD x x.2⟩
      invFun := fun y => ⟨y, hDF y y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

  have : Algebra.FiniteType ℚ (funField P) := hDft.equiv e.symm.toRatAlgEquiv
  have : Module.Finite ℚ (funField P) := finite_of_finite_type_of_isJacobsonRing ℚ (funField P)
  exact ⟨⟩

end

end GroundTheory.Heights₂.Heights.Inter
