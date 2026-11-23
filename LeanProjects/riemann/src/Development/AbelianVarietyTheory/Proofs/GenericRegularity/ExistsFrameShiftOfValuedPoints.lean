import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralFramesModelInvertiblePushforwardStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericFrameIntegralOffFinitelyManyFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.ExistsCompleteDiscreteValuationRingOfIsNormDiscr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

namespace FrameShift

open ReciprocityTheory.ChartRestriction.G.T0

theorem vV_algebraMap {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (x : V) (n : ℕ) (hx : IsDiscreteValuationRing.addVal V x = n) :
    vV V (algebraMap V K x) = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [IsDiscreteValuationRing.addVal_zero] at hx
    exact ENat.top_ne_coe n hx
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ m] at hx
  obtain rfl : m = n := by exact_mod_cast hx
  have h1 : (IsDiscreteValuationRing.maximalIdeal V).intValuation (u : V) = 1 :=
    HeightOneSpectrum.intValuation_eq_one_iff.2 fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm u.isUnit
  have h2 : (IsDiscreteValuationRing.maximalIdeal V).intValuation ϖ = WithZero.exp (-1 : ℤ) :=
    HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq
  simp only [vV, valV, HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow, h1, h2, _root_.one_mul]
  rw [← WithZero.exp_nsmul, WithZero.log_exp]
  simp

theorem exists_cdvr (Ω : Type) [Field Ω] [CharZero Ω] (v : AddValuation Ω (WithTop ℤ)) (hv : IsNormDiscrete v) :
    ∃ (T : CDVR) (ψ : Ω →+* T.Fr), (∀ a : Ω, 0 ≤ v a → ∃ x : T.V, algebraMap T.V T.Fr x = ψ a) ∧
      ∀ a : Ω, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a := by
  obtain ⟨V, K', _, _, _, _, _, _, f, hc, hmem, hval, -⟩ :=
    GlobalTheory.exists_complete_discreteValuationRing_of_isNormDiscrete Ω v hv
  haveI : CharZero K' := (RingHom.charZero_iff f.injective).1 inferInstance
  haveI : CharZero V := (algebraMap V K').charZero
  let T : CDVR := CDVR.mk V
  let e : FractionRing V ≃ₐ[V] K' := FractionRing.algEquiv V K'
  let ψ : Ω →+* FractionRing V := e.symm.toAlgHom.toRingHom.comp f
  have hψ : ∀ (a : Ω) (x : V), algebraMap V K' x = f a → algebraMap V (FractionRing V) x = ψ a := by
    intro a x hx
    show _ = e.symm (f a)
    rw [← hx, AlgEquiv.commutes]
  have hnn : ∀ a : Ω, a ≠ 0 → 0 ≤ v a → ((vV V (ψ a) : ℤ) : WithTop ℤ) = v a := by
    intro a ha h0
    obtain ⟨x, hx⟩ := (hmem a).2 h0
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (hv.1 a ha)
    have hk0 : 0 ≤ k := by rw [← hk] at h0; exact_mod_cast h0
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    rw [← hψ a x hx, vV_algebraMap x n ((hval n a x hx).2 hk.symm), hk]
  refine ⟨T, ψ, fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨x, hx⟩ := (hmem a).2 ha
    exact ⟨x, hψ a x hx⟩
  · by_cases h0 : 0 ≤ v a
    · exact hnn a ha h0
    · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (hv.1 a ha)
      obtain ⟨k', hk'⟩ := WithTop.ne_top_iff_exists.1 (hv.1 a⁻¹ (inv_ne_zero ha))
      have hs : k + k' = 0 := by
        have := v.map_mul a a⁻¹
        rw [mul_inv_cancel₀ ha, v.map_one, ← hk, ← hk'] at this
        exact_mod_cast this.symm
      have hneg : ¬ 0 ≤ k := fun h => h0 (by rw [← hk]; exact_mod_cast h)
      have h1 := hnn a⁻¹ (inv_ne_zero ha) (by rw [← hk']; exact_mod_cast (by omega : 0 ≤ k'))
      rw [← hk'] at h1
      have h1' : vV V (ψ a⁻¹) = k' := by exact_mod_cast h1
      have h2 := vV_mul (V := V) ((map_ne_zero ψ).2 ha) ((map_ne_zero ψ).2 (inv_ne_zero ha))
      rw [← map_mul, mul_inv_cancel₀ ha, map_one] at h2
      have h3 : vV V (1 : FractionRing V) = 0 := by simp [vV]
      rw [← hk]
      show ((vV V (ψ a) : ℤ) : WithTop ℤ) = _
      exact_mod_cast (by omega : vV V (ψ a) = k)

theorem integer_nonneg {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : AddValuation Ω (WithTop ℤ)) (a : 𝓞 K) : 0 ≤ v (algebraMap K Ω (a : K)) := by
  have h1 : IsIntegral ℤ (algebraMap K Ω (a : K)) :=
    (RingOfIntegers.isIntegral_coe a).map (algebraMap K Ω).toIntAlgHom
  have h2 : IsIntegral (vRing v) (algebraMap K Ω (a : K)) := h1.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := vRing v) (K := Ω)).mp h2
  rw [← hy]
  exact y.2

theorem exists_place_nonneg {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : AddValuation Ω (WithTop ℤ)) (hv : (∃ la, IsOver (K := K) v la) ∨ IsTrivOn K v) :
    ∃ la : HeightOneSpectrum (𝓞 K), ∀ a : K, a ∈ (la.valuation K).valuationSubring → 0 ≤ v (algebraMap K Ω a) := by
  rcases hv with ⟨la, hla⟩ | ht
  · refine ⟨la, fun a ha => ?_⟩
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer la a ha
    have hd : v (algebraMap K Ω ((d : 𝓞 K) : K)) = 0 :=
      le_antisymm (not_lt.1 fun h => d.2 ((hla d).1 h)) (integer_nonneg v (d : 𝓞 K))
    have hn := integer_nonneg (K := K) v n
    have : (n : K) = a * ((d : 𝓞 K) : K) := hnd.symm
    rwa [this, map_mul, v.map_mul, hd, add_zero] at hn
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
    refine ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩,
      fun a _ => ?_⟩
    by_cases ha : a = 0
    · rw [ha, map_zero, v.map_zero]; exact le_top
    · exact (ht a ha).ge

theorem vV_wchar {J : Type} [Fintype J] (T : CDVR) (e : J → ℕ) (t : J → T.Frˣ) :
    wchar e t ≠ 0 ∧ vV T.V (wchar e t) = ∑ i, (e i : ℤ) * vV T.V ((t i : T.Frˣ) : T.Fr) := by
  classical
  unfold wchar
  induction (Finset.univ : Finset J) using Finset.induction_on with
  | empty => simp [vV]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have h0 : ((t i : T.Frˣ) : T.Fr) ^ e i ≠ 0 := pow_ne_zero _ (t i).ne_zero
    refine ⟨mul_ne_zero h0 ih.1, ?_⟩
    rw [vV_mul h0 ih.1, ih.2]
    congr 1
    simp only [vV, map_pow, WithZero.log_pow]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def algOf {Z : Comp Xo c} {T : CDVR} (ψ : Om Z →+* T.Fr) :
    letI := (ψ.comp (algebraMap c.F (Om Z))).toAlgebra
    Om Z →ₐ[c.F] T.Fr :=
  letI := (ψ.comp (algebraMap c.F (Om Z))).toAlgebra
  { ψ with commutes' := fun _ => rfl }

theorem exists_valued_point (hIF : IntFramesSt Xo c) (hbc : FrBC Xo c) (hM : ∀ la, ModelAt Xo c la)
    (h : GenFrEx Xo c) (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)) (hv : IsNormDiscrete v)
    (ho : (∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) :
    ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))) (t : Ix Dw → T.Frˣ),
      (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧
      letI := (ψ.comp (algebraMap c.F (Om Z))).toAlgebra
      ∃ z : FrPt Xo c T.Fr, FrMap (algOf ψ) (genFr h Z) z ∧ FrBor t z y.1 := by
  haveI : CharZero (Om Z) := charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  obtain ⟨T, ψ, hmem, hval⟩ := exists_cdvr (Om Z) v hv
  obtain ⟨la, hla⟩ := exists_place_nonneg v ho
  obtain ⟨Y, hY⟩ := hM la
  letI := (ψ.comp (algebraMap c.F (Om Z))).toAlgebra
  obtain ⟨z, hz⟩ := hbc _ _ (algOf ψ) (genFr h Z)
  have hinj := IsFractionRing.injective T.V T.Fr
  let g : (la.valuation c.F).valuationSubring →+* T.Fr :=
    (ψ.comp (algebraMap c.F (Om Z))).comp (la.valuation c.F).valuationSubring.subtype
  have hg : ∀ a, g a ∈ (algebraMap T.V T.Fr).range := fun a => hmem _ (hla a a.2)
  let e : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
    ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
  let b : (la.valuation c.F).valuationSubring →+* T.V := e.symm.toRingHom.comp (g.codRestrict _ hg)
  have hb : (algebraMap T.V T.Fr).comp b = g := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (g.codRestrict _ hg a))
  obtain ⟨y, t, hyt⟩ := intFr_of_model hIF T _ Y hY b hb z
  exact ⟨T, ψ, y, t, hval, z, hz, hyt⟩

end FrameShift

open FrameShift in

theorem exists_frameShift_of_valued_points : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → (∀ la, ModelAt Xo c la) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (h : GenFrEx Xo c), ∃ δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ, (∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v → ((∃ la, ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) v la) ∨ ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn c.F v) → ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))), (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → (evI y f = 0 ↔ evC h Z f = 0) ∧ (evC h Z f ≠ 0 → ordC (δ Z v) v (wtZ a n) (valC h a n f Z) = vV T.V (evI y f))) ∧ ∀ Z : Comp Xo c, ∃ S : Finset (Om Z), (∀ s ∈ S, s ≠ 0) ∧ ∀ v : AddValuation (Om Z) (WithTop ℤ), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v → ((∃ la, ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) v la) ∨ ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn c.F v) → (∀ s ∈ S, v s = 0) → δ Z v = 0 := by
  intro hT E _ _ _ H Dw l Xo c hL hU hM Y h
  classical
  have hIF : IntFramesSt Xo c := GlobalTheory.T.exists_integralFrames_model_invertible_pushforward GlobalTheory.abelianSchemeLaws_all.1.secBaseChange hT E H Dw l Xo c
  have key := fun Z v hv ho => exists_valued_point hIF hL.bc hM h Z v hv ho
  choose T ψ y t hval z hz hb using key
  refine ⟨fun Z v i => if hh : T0.IsNormDiscrete v ∧ ((∃ la, T0.IsOver (K := c.F) v la) ∨ T0.IsTrivOn c.F v) then
    vV (T Z v hh.1 hh.2).V ((t Z v hh.1 hh.2 i : (T Z v hh.1 hh.2).Frˣ) : (T Z v hh.1 hh.2).Fr) else 0, ?_, ?_⟩
  · intro Z v hv ho
    refine ⟨T Z v hv ho, ψ Z v hv ho, y Z v hv ho, hval Z v hv ho, fun a n f hf => ?_⟩
    letI := ((ψ Z v hv ho).comp (algebraMap c.F (Om Z))).toAlgebra
    have h1 : evI (y Z v hv ho) f = wchar (ex Dw a n) (t Z v hv ho) * evR Xo c f (z Z v hv ho) :=
      hL.wt a n f hf _ (t Z v hv ho) (z Z v hv ho) (y Z v hv ho).1 (hL.test _ _) (y Z v hv ho).2.1 (hb Z v hv ho)
    have h2 : evR Xo c f (z Z v hv ho) = ψ Z v hv ho (evC h Z f) :=
      GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf _ _ (algOf (ψ Z v hv ho)) _ _ (hz Z v hv ho)
    obtain ⟨hw0, hw⟩ := vV_wchar (T Z v hv ho) (ex Dw a n) (t Z v hv ho)
    rw [h1, h2]
    refine ⟨by rw [mul_eq_zero, map_eq_zero]; exact or_iff_right hw0, fun hne => ?_⟩
    apply WithTop.coe_injective
    rw [valC, ordC_single _ _ _ hne, vV_mul hw0 ((map_ne_zero _).2 hne), hw, ← hval Z v hv ho _ hne,
      ← WithTop.coe_add, add_comm]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    beta_reduce
    rw [exZ_wtZ, dif_pos ⟨hv, ho⟩]
  · intro Z
    obtain ⟨S, hS0, hS⟩ := GlobalTheory.T.genericFrame_integral_off_finitelyMany_functions hT E H Dw l Xo c hL.bc Y h Z
    refine ⟨S, hS0, fun v hv ho hs => ?_⟩
    letI := ((ψ Z v hv ho).comp (algebraMap c.F (Om Z))).toAlgebra
    have hint := hS (T Z v hv ho) _ (algOf (ψ Z v hv ho)) (fun s hs' => by
      have := hval Z v hv ho s (hS0 s hs')
      rw [hs s hs'] at this
      exact_mod_cast this) (z Z v hv ho) (hz Z v hv ho)
    funext i
    have := hU (T Z v hv ho) _ ⟨z Z v hv ho, hL.test _ _, hint⟩ (y Z v hv ho) (t Z v hv ho) (hb Z v hv ho) i
    beta_reduce
    rw [dif_pos ⟨hv, ho⟩]
    simp [vV, this]

end GlobalTheory.Reg
