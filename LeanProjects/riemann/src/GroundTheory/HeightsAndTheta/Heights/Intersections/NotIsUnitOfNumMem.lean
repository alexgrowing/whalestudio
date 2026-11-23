import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace regularityLocalResidue_holds

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add' {R : Type*} [CommRing R] {f g : MRingOver R ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_neg' {R : Type*} [CommRing R] {f : MRingOver R ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem isMultiHomog_zero' {R : Type*} [CommRing R] (a : K → ℕ) : IsMultiHomog (0 : MRingOver R ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {f : MRingOver R ι}
    {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (map φ f) a :=
  fun m hm => hf m (support_map_subset φ f hm)

theorem aeval_blockScale_int {A : Type*} [CommRing A] [Algebra ℤ A] {g : MRing ι} {a : K → ℕ}
    (hg : IsMultiHomog g a) (c : K → A) (z : (Σ k, ι k) → A) :
    aeval (fun p => c p.1 * z p) g = (∏ k, c k ^ a k) * aeval z g := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h1 : ∏ p, (c p.1 * z p) ^ d p = (∏ p, c p.1 ^ d p) * ∏ p, z p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [mul_pow]
  have h2 : ∏ p : (Σ k, ι k), c p.1 ^ d p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  rw [h1, h2]
  ring

def quotEquivMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hI : RingHom.ker f ≤ I) : R ⧸ I ≃+* S ⧸ I.map f :=
  (Ideal.quotEquivOfEq (by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hI])).trans
    (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk (I.map f)).comp f)
      (Ideal.Quotient.mk_surjective.comp hf))

theorem comap_map_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hI : RingHom.ker f ≤ I) : (I.map f).comap f = I := by
  rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hI]

theorem chart_field_card {W : Ideal (MRing ι)} [W.IsPrime] (hWmh : IsMultiHomogIdeal W) {T : ∀ k, ι k}
    (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : ℕ) [Fact p.Prime] (hp : (C (p : ℤ) : MRing ι) ∈ W) :
    IsField (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1))) ∧
      Finite (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1))) ∧
      Nat.card (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1))) =
        p ^ (Module.length ℤ (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1)))).toNat := by
  classical
  set J := W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1) with hJ
  let π : MRing ι →+* MRingOver (ZMod p) ι := MvPolynomial.map (Int.castRingHom (ZMod p))
  have hπ : Function.Surjective π := MvPolynomial.map_surjective _ ZMod.intCast_surjective
  have hker : RingHom.ker π ≤ W := by
    rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hp
  set Wb := W.map π
  have hWbp : Wb.IsPrime := Ideal.map_isPrime_of_surjective hπ hker
  have hXb : ∀ k, (X ⟨k, T k⟩ : MRingOver (ZMod p) ι) ∉ Wb := by
    intro k h
    have h' : π (X ⟨k, T k⟩) ∈ Wb := by rwa [show π (X ⟨k, T k⟩) = X ⟨k, T k⟩ from map_X _ _]
    have := Ideal.mem_comap.mpr h'
    rw [comap_map_eq π hπ W hker] at this
    exact hT k this
  have hWb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF Wb 0 := by
    refine ⟨⟨hWbp, ?_, fun k => ⟨T k, hXb k⟩⟩, ?_⟩
    · obtain ⟨S, hS, hWS⟩ := hWmh
      refine ⟨π '' S, ?_, ?_⟩
      · rintro _ ⟨f, hf, rfl⟩
        obtain ⟨a, ha⟩ := hS f hf
        exact ⟨a, isMultiHomog_map _ ha⟩
      · show W.map π = _
        rw [hWS, Ideal.map_span]
    · rw [← ringKrullDim_eq_of_ringEquiv (quotEquivMap π hπ W hker), hdim]
  have hmapJ : J.map π = ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T := by
    rw [hJ, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
    unfold ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal
    have e : (⇑π ∘ fun k => (X ⟨k, T k⟩ : MRing ι) - 1) = fun k => (X ⟨k, T k⟩ : MRingOver (ZMod p) ι) - 1 := by
      funext k
      simp [π]
    rw [e]
  let eC : MRing ι ⧸ J ≃+* MRingOver (ZMod p) ι ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T :=
    (quotEquivMap π hπ J (hker.trans le_sup_left)).trans (Ideal.quotEquivOfEq hmapJ)
  have hF := ReciprocityTheory.ChartRestriction.G.AI.I1.chart_isField hWb (j := T) hXb
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.I1.chart_finite hWb (j := T) hXb
  have : Finite (MRingOver (ZMod p) ι ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T) := Module.finite_of_finite (ZMod p)
  refine ⟨MulEquiv.isField hF eC.toMulEquiv, Finite.of_equiv _ eC.symm.toEquiv, ?_⟩
  have hlen : Module.length ℤ (MRing ι ⧸ J) =
      Module.finrank (ZMod p) (MRingOver (ZMod p) ι ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T) := by
    rw [LinearEquiv.length_eq eC.toAddEquiv.toIntLinearEquiv,
      Module.length_eq_of_surjective (R := ZMod p) ZMod.intCast_surjective, Module.length_eq_finrank]
  haveI := Fintype.ofFinite (MRingOver (ZMod p) ι ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal Wb T)
  rw [hlen, ENat.toNat_natCast, Nat.card_congr eC.toEquiv, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

section Loc

variable (P : Ideal (MRing ι))

def frHom : MRing ι →+* FractionRing (MRing ι ⧸ P) :=
  (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))).comp (Ideal.Quotient.mk P)

variable {P} [P.IsPrime]

theorem frHom_eq_zero_iff {f : MRing ι} : frHom P f = 0 ↔ f ∈ P := by
  rw [frHom, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem exists_rep {W : Ideal (MRing ι)} (hW : W.IsPrime) {x : FractionRing (MRing ι ⧸ P)}
    (hx : x ∈ locRing P W) :
    ∃ (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧ x * frHom P v = frHom P u := by
  have h1 : (1 : MRing ι) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, a, hv, hvW, hu, hva, rfl⟩ := hx
    exact ⟨u, v, a, hu, hva, hvW, IsLocalization.mk'_spec _ _ _⟩
  | zero => exact ⟨0, 1, 0, isMultiHomog_zero' 0, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | one => exact ⟨1, 1, 0, AvoidRing.isMultiHomog_one, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * v' + u' * v, v * v', a + a',
      isMultiHomog_add' (AvoidRing.isMultiHomog_mul hu hv') (by rw [add_comm]; exact AvoidRing.isMultiHomog_mul hu' hv),
      AvoidRing.isMultiHomog_mul hv hv', fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    rw [map_mul, map_add, map_mul, map_mul, ← e, ← e']
    ring
  | neg x _ hx =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    exact ⟨-u, v, a, isMultiHomog_neg' hu, hv, hvW, by rw [map_neg, ← e]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * u', v * v', a + a', AvoidRing.isMultiHomog_mul hu hu', AvoidRing.isMultiHomog_mul hv hv',
      fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    rw [map_mul, map_mul, ← e, ← e']
    ring

theorem not_isUnit_of_num_mem {W : Ideal (MRing ι)} (hW : W.IsPrime) (hPW : P ≤ W) {x : locRing P W}
    {u v : MRing ι} (hx : (x : FractionRing (MRing ι ⧸ P)) * frHom P v = frHom P u) (hu : u ∈ W) (hv : v ∉ W) :
    ¬ IsUnit x := by
  intro hxu
  obtain ⟨y, hy⟩ := hxu.exists_right_inv
  obtain ⟨u', v', a', -, -, hv', e'⟩ := exists_rep hW y.2
  have hxy : (x : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) = 1 := by
    rw [← Subring.coe_mul, hy, Subring.coe_one]
  have h1 : frHom P (u * u') = frHom P (v * v') := by
    rw [map_mul, map_mul, ← hx, ← e']
    calc _ = ((x : FractionRing (MRing ι ⧸ P)) * y) * (frHom P v * frHom P v') := by ring
      _ = _ := by rw [hxy, one_mul]
  have h2 : u * u' - v * v' ∈ P := by rw [← frHom_eq_zero_iff, map_sub, h1, sub_self]
  have h3 : v * v' ∈ W := by
    have := W.sub_mem (W.mul_mem_right u' hu) (hPW h2)
    rwa [sub_sub_cancel] at this
  exact (hW.mem_or_mem h3).elim hv hv'

theorem mem_locRing_of_form {W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (hvW : v ∉ W) :
    frHom P u * (frHom P v)⁻¹ ∈ locRing P W := by
  have hv0 : Ideal.Quotient.mk P v ≠ 0 := fun h => hvW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hnz : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := mem_nonZeroDivisors_of_ne_zero hv0
  refine Subring.subset_closure ⟨u, v, a, hnz, hvW, hu, hv, ?_⟩
  rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv]
  rfl

def chartMap {W : Ideal (MRing ι)} (hPW : P ≤ W) (T : ∀ k, ι k) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W) :
    MRing ι →+* locRing P W :=
  eval₂Hom (Int.castRingHom _) fun p =>
    ⟨frHom P (X p) * (frHom P (X ⟨p.1, T p.1⟩))⁻¹, by
      classical
      exact mem_locRing_of_form hPW (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (T p.1)) (hT p.1)⟩

theorem coe_chartMap {W : Ideal (MRing ι)} (hPW : P ≤ W) {T : ∀ k, ι k} (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W)
    (f : MRing ι) : (chartMap hPW T hT f : FractionRing (MRing ι ⧸ P)) =
      aeval (fun p => (frHom P (X ⟨p.1, T p.1⟩))⁻¹ * frHom P (X p)) f := by
  have e : (locRing P W).subtype.comp (chartMap hPW T hT) =
      (aeval (fun p => (frHom P (X ⟨p.1, T p.1⟩))⁻¹ * frHom P (X p)) :
        MRing ι →ₐ[ℤ] FractionRing (MRing ι ⧸ P)).toRingHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by
      simp [chartMap, mul_comm]
  exact DFunLike.congr_fun e f

theorem frHom_X_ne_zero {W : Ideal (MRing ι)} (hPW : P ≤ W) {T : ∀ k, ι k}
    (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W) (k : K) : frHom P (X ⟨k, T k⟩) ≠ 0 :=
  fun h => hT k (hPW (frHom_eq_zero_iff.mp h))

theorem chartMap_form {W : Ideal (MRing ι)} (hPW : P ≤ W) {T : ∀ k, ι k}
    (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    (chartMap hPW T hT f : FractionRing (MRing ι ⧸ P)) * frHom P (∏ k, (X ⟨k, T k⟩ : MRing ι) ^ a k) =
      frHom P f := by
  have hz : (aeval fun p => frHom P (X p) : MRing ι →ₐ[ℤ] FractionRing (MRing ι ⧸ P)).toRingHom = frHom P :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp
  have hz' : (aeval fun p => frHom P (X p) : MRing ι →ₐ[ℤ] FractionRing (MRing ι ⧸ P)) f = frHom P f :=
    DFunLike.congr_fun hz f
  rw [coe_chartMap, aeval_blockScale_int hf (fun k => (frHom P (X ⟨k, T k⟩))⁻¹) (fun p => frHom P (X p)), hz', map_prod, mul_comm, ← mul_assoc,
    ← Finset.prod_mul_distrib]
  simp_rw [map_pow, ← mul_pow, mul_inv_cancel₀ (frHom_X_ne_zero hPW hT _), one_pow, Finset.prod_const_one,
    one_mul]

end Loc

end regularityLocalResidue_holds

open regularityLocalResidue_holds in

theorem regularityLocalResidue_holds.proof : regularityLocalResidue_holds.Statement := by
  intro K _ ι _ P s a W b hP hs hsP hW _
  classical
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨hWmin, hWrel⟩ := hW
  have : P.IsPrime := hPp
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have h1 := dim_quot_minimal_add_one P W s hsP hWmin
    rw [hPdim] at h1
    exact withBot_eq_of_add_one (by rw [h1, show 1 + Fintype.card K = 0 + Fintype.card K + 1 by omega])
  have hvert : ¬ IsHorizontal W := fun hh => arithVarZero K ι W ⟨hK, ⟨hWp, hWmh, hWrel⟩, hh, hdim⟩
  have : Fact (charOf W).Prime := ⟨charOf_prime hWp hvert⟩
  have hp : (C ((charOf W : ℕ) : ℤ) : MRing ι) ∈ W := by
    have hgen := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))
    have : ((charOf W : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
      unfold charOf
      rw [Int.natCast_natAbs]
      rcases abs_choice (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))) with h | h <;> rw [h]
      · exact hgen
      · exact neg_mem hgen
    exact Ideal.mem_comap.mp this
  set T : ∀ k, ι k := fun k => (hWrel k).choose with hTdef
  have hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W := fun k => (hWrel k).choose_spec
  set J := W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1) with hJ
  have hgeo : geoNum 0 W b = ((Module.length ℤ (MRing ι ⧸ J)).toNat : ℤ) := by
    rw [geoNum, dif_pos hWrel]
  obtain ⟨hCf, hCfin, hCcard⟩ := chart_field_card hWmh hT hdim (charOf W) hp
  letI : Field (MRing ι ⧸ J) := hCf.toField
  let g := chartMap hPW T hT
  let χ := (IsLocalRing.residue (locRing P W)).comp g
  have hJχ : J ≤ RingHom.ker χ := by
    refine sup_le ?_ (Ideal.span_le.mpr ?_)
    · obtain ⟨S, hS, hWS⟩ := hWmh
      intro f hf
      rw [hWS] at hf
      refine (Ideal.span_le.mpr ?_) hf
      intro f hfS
      obtain ⟨a', ha'⟩ := hS f hfS
      have hfW : f ∈ W := hWS ▸ Ideal.subset_span hfS
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact not_isUnit_of_num_mem hWp hPW (chartMap_form hPW hT ha') hfW (AvoidRing.coordProd_not_mem hWp T hT a')
    · rintro _ ⟨k, rfl⟩
      have h1 : g (X ⟨k, T k⟩) = 1 := Subtype.ext (by
        rw [coe_chartMap, aeval_X, Subring.coe_one, inv_mul_cancel₀ (frHom_X_ne_zero hPW hT k)])
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, RingHom.comp_apply, h1, map_one, sub_self]
  let χb : MRing ι ⧸ J →+* IsLocalRing.ResidueField (locRing P W) := Ideal.Quotient.lift J χ fun f hf => hJχ hf
  have hχb : ∀ f, χb (Ideal.Quotient.mk J f) = χ f := fun f => Ideal.Quotient.lift_mk _ _ _
  have hsurj : Function.Surjective χb := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨u, v, a', hu, hv, hvW, e⟩ := exists_rep hWp x.2
    have hTa : frHom P (∏ k, (X ⟨k, T k⟩ : MRing ι) ^ a' k) ≠ 0 :=
      fun h => AvoidRing.coordProd_not_mem hWp T hT a' (hPW (frHom_eq_zero_iff.mp h))
    have hv0 : frHom P v ≠ 0 := fun h => hvW (hPW (frHom_eq_zero_iff.mp h))
    have hunit : IsUnit (g v) := by
      refine IsUnit.of_mul_eq_one ⟨_, mem_locRing_of_form hPW (AvoidRing.isMultiHomog_coordProd T a') hv hvW⟩
        (Subtype.ext ?_)
      show (g v : FractionRing (MRing ι ⧸ P)) * (frHom P _ * (frHom P v)⁻¹) = 1
      rw [← mul_assoc, chartMap_form hPW hT hv, mul_inv_cancel₀ hv0]
    have hxg : x * g v = g u := Subtype.ext (by
      refine mul_right_cancel₀ hTa ?_
      rw [Subring.coe_mul, mul_assoc, chartMap_form hPW hT hv, chartMap_form hPW hT hu, e])
    have hχv : χ v ≠ 0 := (hunit.map (IsLocalRing.residue (locRing P W))).ne_zero
    refine ⟨Ideal.Quotient.mk J u * (Ideal.Quotient.mk J v)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hχb, hχb, mul_inv_eq_iff_eq_mul₀ hχv]
    show _ = IsLocalRing.residue (locRing P W) x * IsLocalRing.residue (locRing P W) (g v)
    rw [← map_mul, hxg]
    rfl
  let eK : MRing ι ⧸ J ≃+* IsLocalRing.ResidueField (locRing P W) :=
    RingEquiv.ofBijective χb ⟨χb.injective, hsurj⟩
  refine ⟨Finite.of_equiv _ eK.toEquiv, ?_⟩
  rw [← Nat.card_congr eK.toEquiv, hCcard, hgeo, Int.toNat_natCast]

end

end GroundTheory.Heights₂.Heights.Inter
