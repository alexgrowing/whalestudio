import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsModelPushInvertibleOverCompleteDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralFramesModelInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NoCommonZeroOfFiniteValues
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjOfSecondTyping
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.CubeMapTripleProductUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTopBaseModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfNoTwoTorsion

set_option synthInstance.maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

namespace GlobalTheory.SupFinite

section Algebra

theorem fg_of_separating {K V : Type} [Field K] [AddCommGroup V] [Module K V] (O : Subring K) [IsNoetherianRing O]
    (W : Submodule K V) [FiniteDimensional K W] (S : Submodule O V) (hS : ∀ g ∈ S, g ∈ W)
    (h : ∀ f ∈ W, f ≠ 0 → ∃ ψ : V →ₗ[K] K, ψ f ≠ 0 ∧ ∀ g ∈ S, ψ g ∈ O) : S.FG := by
  classical
  let N : Finset (V →ₗ[K] K) → Submodule K W := fun t => ⨅ ψ ∈ t, (LinearMap.ker ψ).comap W.subtype
  have hN : ∀ t (x : W), x ∈ N t ↔ ∀ ψ ∈ t, ψ x = 0 := fun t x => by simp [N, Submodule.mem_iInf]
  obtain ⟨_, ⟨t, ht, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule K W)).has_min
    (N '' {t | ∀ ψ ∈ t, ∀ g ∈ S, ψ g ∈ O}) ⟨N ∅, ∅, by simp, rfl⟩
  have hsep : ∀ f ∈ W, (∀ ψ ∈ t, ψ f = 0) → f = 0 := by
    intro f hf h0
    by_contra hne
    obtain ⟨ψ, hψ, hψS⟩ := h f hf hne
    refine hmin (N (insert ψ t)) ⟨_, ?_, rfl⟩ (lt_of_le_of_ne ?_ ?_)
    · intro χ hχ
      rcases Finset.mem_insert.1 hχ with rfl | hχ
      · exact hψS
      · exact ht χ hχ
    · intro x hx
      exact (hN _ _).2 fun χ hχ => (hN _ _).1 hx χ (Finset.mem_insert_of_mem hχ)
    · intro e
      have : (⟨f, hf⟩ : W) ∈ N (insert ψ t) := e ▸ (hN _ _).2 h0
      exact hψ ((hN _ _).1 this ψ (Finset.mem_insert_self _ _))
  let Φ : S →ₗ[O] (t → O) :=
    { toFun := fun g ψ => ⟨ψ.1 g, ht ψ.1 ψ.2 g g.2⟩
      map_add' := fun g g' => by ext ψ; simp
      map_smul' := fun a g => by
        ext ψ
        exact ψ.1.map_smul (a : K) g.1 }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    exact Subtype.ext (hsep g (hS g g.2) fun ψ hψ => congrArg Subtype.val (congrFun hg ⟨ψ, hψ⟩))
  have : Module.Finite O S := Module.Finite.of_injective Φ hΦ
  exact Module.Finite.iff_fg.1 this

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (la : HeightOneSpectrum (𝓞 K))

omit [NumberField K] in

theorem exists_denominator (y : L)
    (hy : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver la.asIdeal → w.valuation L y ≤ 1) :
    ∃ s : 𝓞 K, s ∉ la.asIdeal ∧ ∃ z : 𝓞 L, algebraMap K L s * y = z := by
  let J : Ideal (𝓞 L) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 L) L y)
    (LinearMap.range (Algebra.linearMap (𝓞 L) L))
  by_contra hcon
  push Not at hcon
  have hJ : J.comap (algebraMap (𝓞 K) (𝓞 L)) ≤ la.asIdeal := by
    intro s hs
    by_contra hn
    obtain ⟨z, hz⟩ := hs
    refine hcon s hn z ?_
    have : (z : L) = (algebraMap (𝓞 K) (𝓞 L) s : L) * y := by
      simpa [Algebra.smul_def] using hz
    rw [this]; rfl
  have := la.isPrime
  obtain ⟨Q, hJQ, hQ, hQl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral la.asIdeal J hJ
  have hlo : Q.LiesOver la.asIdeal := ⟨hQl.symm⟩
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot la.ne_bot Q⟩
  obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer y (hy w hlo)
  refine d.2 (hJQ ⟨n, ?_⟩)
  simp [Algebra.smul_def, ← hnd, mul_comm]

theorem exists_bound (X : Set L)
    (hX : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver la.asIdeal →
      ∃ d : L, d ≠ 0 ∧ ∀ x ∈ X, w.valuation L (d * x) ≤ 1) (ℓ : L →ₗ[K] K) :
    ∃ d : K, d ≠ 0 ∧ ∀ x ∈ X, la.valuation K (d * ℓ x) ≤ 1 := by
  classical
  have h1 : ∀ w : HeightOneSpectrum (𝓞 L), ∃ a : 𝓞 L, a ≠ 0 ∧ (w.asIdeal.LiesOver la.asIdeal →
      ∀ x ∈ X, w.valuation L (a * x) ≤ 1) := by
    intro w
    by_cases hw : w.asIdeal.LiesOver la.asIdeal
    · obtain ⟨d, hd, hx⟩ := hX w hw
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) d
      have hb0 : algebraMap (𝓞 L) L b ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
      refine ⟨a, by rintro rfl; simp at hd, fun _ x hxX => ?_⟩
      have e : (a : L) * x = algebraMap (𝓞 L) L b * (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L b * x) := by
        field_simp
      rw [e, map_mul]
      exact mul_le_one' (w.valuation_le_one b) (hx x hxX)
    · exact ⟨1, one_ne_zero, fun h => absurd h hw⟩
  choose a ha0 ha using h1
  have hfin : {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.LiesOver la.asIdeal}.Finite := by
    have := la.isMaximal
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite la.asIdeal (𝓞 L)).subset ?_) fun _ _ _ _ h => HeightOneSpectrum.ext h
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, hw⟩
  let D : 𝓞 L := ∏ w ∈ hfin.toFinset, a w
  have hD0 : (D : L) ≠ 0 := by
    have : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => ha0 w
    simpa using this
  have hD : ∀ x ∈ X, ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver la.asIdeal → w.valuation L (D * x) ≤ 1 := by
    intro x hx w hw
    obtain ⟨r, hr⟩ : a w ∣ D := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hw)
    have e : (D : L) * x = algebraMap (𝓞 L) L r * (a w * x) := by
      rw [hr]; push_cast; simp only [RingOfIntegers.coe_eq_algebraMap]; ring
    rw [e, map_mul]
    exact mul_le_one' (w.valuation_le_one r) (ha w hw x hx)
  let b := RingOfIntegers.basis L
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun j => ℓ ((D : L)⁻¹ * (b j : L)))
  have hz : ∀ z : 𝓞 L, la.valuation K (((d : 𝓞 K) : K) * ℓ ((D : L)⁻¹ * z)) ≤ 1 := by
    intro z
    have hz : z ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      obtain ⟨o, ho⟩ := hd j
      rw [Algebra.smul_def] at ho
      exact le_of_eq_of_le (congrArg _ ho.symm) (la.valuation_le_one o)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [RingOfIntegers.coe_eq_algebraMap (x + y), map_add, mul_add, map_add, mul_add]
      exact Valuation.map_add_le _ hx hy
    | smul n x _ hx =>
      have e : ((d : 𝓞 K) : K) * ℓ ((D : L)⁻¹ * ((n • x : 𝓞 L) : L)) =
          algebraMap (𝓞 K) K n * (((d : 𝓞 K) : K) * ℓ ((D : L)⁻¹ * x)) := by
        rw [RingOfIntegers.coe_eq_algebraMap (n • x), map_zsmul, mul_smul_comm, map_zsmul, mul_smul_comm, zsmul_eq_mul,
          map_intCast]
      rw [e, map_mul]
      exact mul_le_one' (la.valuation_le_one _) hx
  refine ⟨((d : 𝓞 K) : K), by simp, fun x hx => ?_⟩
  obtain ⟨s, hs, z, hsz⟩ := exists_denominator la _ (hD x hx)
  have hv : la.valuation K (s : K) = 1 := (la.valuation_eq_one_iff_notMem).2 hs
  have e : (D : L)⁻¹ * z = (s : K) • x := by
    rw [← hsz, Algebra.smul_def]; field_simp
  have := hz z
  rwa [e, map_smul, smul_eq_mul, mul_left_comm, map_mul, hv, one_mul] at this

end Algebra

section Geometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

open GlobalTheory.Models GlobalTheory.Models.RankZero in

theorem exists_model_rank_zero (hD : Dw.p + Dw.q = 0) {O : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [IsNoetherianRing O] (β : O →+* c.F) : ∃ Y : Model Xo c β, PushInvertible Y.t.G Y.t.PP.L := by
  have hX := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  have := hX.1
  let oF := zeroObj hD l (Limits.pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have zo : IsIso oF.t.G.hom := isIso_zeroTriple _
  let C := pointCpt (c := Limits.pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance
    zo β (ZJ.isNormalScheme_sp O)
  obtain ⟨m₀⟩ := nonempty_objMap zo hX.2 (Limits.pullback.fst _ _)
  have hz := isIso_zeroTriple (H := H) (Sp O)
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, oF, m₀, C.m, C.ab_gen⟩,
    PushInv.pushInvertible_any allSixLaws.2.1.secBaseChangeAny allSixLaws.1.globalSectionsRank _
      (GenericPol.toPolAV (Inhab.zeroTriple H (Sp O)) 0 inferInstance (Inhab.isProper_zeroTriple _)
        (ReciprocityTheory.ChartRestriction.G.Out.Inh.zeroPolAV _).ample fun _ _ _ _ _ => hom_unique hz _ _)⟩

theorem exists_intFr {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} (hp : p.Prime) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal)
    (hg : l.GoodAt p) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (z : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), (letI := io.toAlgebra; FrBor t z y.1) := by
  have hIF := GlobalTheory.intFrames_of_laws GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.abelianSchemeLaws_all.2.secTwist
    E H Dw l Xo c
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · obtain ⟨Y, hY⟩ := exists_model_rank_zero Xo c hD (la.valuation c.F).valuationSubring.subtype
    obtain ⟨b, hb⟩ := GlobalTheory.Reg.exists_valuationSubring_hom_of_overLa la T io e ho
    exact intFr_of_model hIF T io Y hY b hb z
  · have hm : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
      rw [← GlobalTheory.PlaceCompletion.valV_algebraMap_lt_one_iff (K' := T.Fr), map_natCast, ← map_natCast io,
        GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho]
      refine pow_lt_one₀ zero_le ?_ ho.1.ne'
      rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
      exact (la.valuation_lt_one_iff_mem _).2 hpl
    obtain ⟨O, _, β, Y, hY, b, hb⟩ := GlobalTheory.exists_model_pushInvertible_under_cdvr GlobalTheory.partI_closed
      GlobalTheory.Moduli.moduli_scheme_exists E H Dw l Xo c hD T io p hp hm hg
    exact intFr_of_model hIF T io Y hY b hb z

theorem exists_bound_values {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} (hp : p.Prime)
    (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hg : l.GoodAt p) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {L : Type} [Field L] [NumberField L] [Algebra c.F L] (y : FrPt Xo c L)
    (w : HeightOneSpectrum (𝓞 L)) (hw : w.asIdeal.LiesOver la.asIdeal) :
    ∃ d : L, d ≠ 0 ∧ ∀ g ∈ sec Xo c a n, BddAll Xo c la 1 g → w.valuation L (d * evR Xo c g y) ≤ 1 := by
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨T, κ, e, ho, hfin⟩ := GlobalTheory.locFld L L (RingHom.id L) w
  rw [RingHom.comp_id] at ho
  have hκ := GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho
  let io : c.F →+* T.Fr := κ.comp (algebraMap c.F L)
  have he2 : la.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot
  have ho' : OverLa la T.V io (e * la.asIdeal.ramificationIdx' w.asIdeal) := by
    refine ⟨Nat.mul_pos ho.1 (Nat.pos_of_ne_zero he2), fun x => ?_⟩
    show vV T.V (κ (algebraMap c.F L x)) = _
    rw [ho.2]
    simp only [vLa]
    rw [← HeightOneSpectrum.valuation_liesOver L la w x, WithZero.log_pow]
    push_cast
    simp [mul_assoc]
  let _ : Algebra c.F T.Fr := io.toAlgebra
  let ψ : L →ₐ[c.F] T.Fr := { κ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := hL.bc L T.Fr ψ y
  obtain ⟨y', t, hb⟩ := exists_intFr Xo c hp hpl hg T io _ ho' z
  have hu : valV T.V (wchar (ex Dw a n) t : T.Fr) ≠ 0 :=
    valV_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero)
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  let m : ℤ := WithZero.log (valV T.V (wchar (ex Dw a n) t : T.Fr))
  have hd : valV T.V (κ (π ^ m.natAbs)) ≤ valV T.V (wchar (ex Dw a n) t : T.Fr) := by
    rw [hκ, map_pow, hπ, ← pow_mul, ← WithZero.exp_nsmul, ← WithZero.exp_log hu, WithZero.exp_le_exp]
    have h1 : (m.natAbs : ℤ) * 1 ≤ m.natAbs * e :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast ho.1) (Int.natCast_nonneg _)
    have h2 : -(m.natAbs : ℤ) ≤ m := by omega
    simp only [nsmul_eq_mul, Nat.cast_mul]
    change _ ≤ m
    linarith
  refine ⟨π ^ m.natAbs, pow_ne_zero _ hπ0, fun g hgs hgb => ?_⟩
  obtain ⟨v, hv⟩ := hgb T io _ ho' y' hfin
  have h1 : evI y' g = wchar (ex Dw a n) t * κ (evR Xo c g y) := by
    have := hL.wt a n g hgs T.Fr t z y'.1 (hL.test _ z) y'.2.1 hb
    rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n g hgs L T.Fr ψ y z hz] at this
    exact this
  rw [map_one, one_mul, h1] at hv
  have h2 : valV T.V (κ (π ^ m.natAbs * evR Xo c g y)) ≤ 1 := by
    refine le_trans ?_ (GlobalTheory.PlaceCompletion.valV_algebraMap_le_one (K' := T.Fr) v)
    rw [hv, map_mul, map_mul, map_mul]
    exact mul_le_mul_left hd _
  rw [hκ] at h2
  exact (pow_le_one_iff_of_nonneg zero_le ho.1.ne').1 h2

theorem exists_value_ne_zero {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (h0 : f ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra c.F L) (y : FrPt Xo c L), evR Xo c f y ≠ 0 := by
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hq
  have : IsReduced q.R := (Ideal.isRadical_iff_quotient_reduced q.I).1 q.rad
  have hev : evR Xo c f y = f q y := by
    have hT := hL.test q.R y
    unfold evR evalAt
    rw [dif_pos hT]
    exact (hf.1 _ _ _ _ _ hT.choose_spec.choose_spec.choose_spec).symm
  have hM : ∃ M : Ideal q.R, M.IsMaximal ∧ f q y ∉ M := by
    by_contra hcon
    push Not at hcon
    have h1 : f q y ∈ (⊥ : Ideal q.R).jacobson := Ideal.mem_sInf.2 fun M hM => hcon M hM.2
    rw [IsJacobsonRing.out inferInstance (Ideal.isRadical_bot (R := q.R))] at h1
    exact hy h1
  obtain ⟨M, hMmax, hM⟩ := hM
  let _ : Field (q.R ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite c.F (q.R ⧸ M) := finite_of_finite_type_of_isJacobsonRing c.F (q.R ⧸ M)
  have : NumberField (q.R ⧸ M) := NumberField.of_module_finite c.F (q.R ⧸ M)
  obtain ⟨z, hz⟩ := hL.bc q.R (q.R ⧸ M) (Ideal.Quotient.mkₐ c.F M) y
  refine ⟨q.R ⧸ M, inferInstance, inferInstance, inferInstance, z, ?_⟩
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf _ _ _ y z hz, hev]
  exact fun h => hM (Ideal.Quotient.eq_zero_iff_mem.1 h)

def supModule (la : HeightOneSpectrum (𝓞 c.F)) (W : Submodule c.F (Rul Xo c)) :
    Submodule (la.valuation c.F).valuationSubring.toSubring (Rul Xo c) where
  carrier := supSet Xo c la W
  zero_mem' := ⟨W.zero_mem, fun T io e ho y hy => by
    rw [(isEval_evI y).zero (), mul_zero]; exact zero_mem _⟩
  add_mem' := fun {f g} hf hg => ⟨W.add_mem hf.1 hg.1, fun T io e ho y hy => by
    rw [evI_add, mul_add]; exact add_mem (hf.2 T io e ho y hy) (hg.2 T io e ho y hy)⟩
  smul_mem' := fun o f hf => ⟨W.smul_mem (o : c.F) hf.1, fun T io e ho y hy => by
    obtain ⟨b, hb⟩ := GlobalTheory.Reg.exists_valuationSubring_hom_of_overLa la T io e ho
    show InV T (io 1 * evI y ((o : c.F) • f))
    rw [evI_smul, mul_left_comm]
    exact mul_mem ⟨b o, RingHom.congr_fun hb o⟩ (hf.2 T io e ho y hy)⟩

theorem supModule_fg {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} (hp : p.Prime)
    (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hg : l.GoodAt p) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (W : Submodule c.F (Rul Xo c)) (hW : W ≤ sec Xo c a n) [FiniteDimensional c.F W] :
    (supModule Xo c la W).FG := by
  have : IsNoetherianRing (la.valuation c.F).valuationSubring.toSubring :=
    inferInstanceAs (IsNoetherianRing (la.valuation c.F).valuationSubring)
  refine fg_of_separating _ W _ (fun g hg => hg.1) fun f hf h0 => ?_
  obtain ⟨L, _, _, _, y, hy⟩ := exists_value_ne_zero Xo c (hW hf) h0
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : L →ₗ[c.F] c.F, ℓ (evR Xo c f y) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy ((Module.forall_dual_apply_eq_zero_iff c.F _).1 hcon)
  obtain ⟨d, hd, hX⟩ := exists_bound la ((fun g => evR Xo c g y) '' supSet Xo c la W) (fun w hw => by
    obtain ⟨d, hd, h⟩ := exists_bound_values Xo c hp hpl hg a n y w hw
    refine ⟨d, hd, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact h g (hW hg.1) hg.2) ℓ
  refine ⟨d • ℓ.comp (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y),
    mul_ne_zero hd hℓ, fun g hg => ?_⟩
  exact hX _ ⟨g, hg, rfl⟩

end Geometry

theorem supSet_finitelyGenerated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n) → ∃ (m : ℕ) (g : Fin m → Rul Xo c), (∀ i, g i ∈ supSet Xo c la (cusp Xo c U a n)) ∧ ∀ f ∈ supSet Xo c la (cusp Xo c U a n), ∃ o : Fin m → c.F, (∀ i, la.valuation c.F (o i) ≤ 1) ∧ f = ∑ i, o i • g i := by
  intro E _ _ _ H Dw l Xo c r U _ la p hp hpl hg a n _ hfd
  obtain ⟨m, g, hspan⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (supModule_fg Xo c hp hpl hg (cusp Xo c U a n) (cusp_le_sec Xo c U a n))
  refine ⟨m, g, fun i => ?_, fun f hf => ?_⟩
  · have : g i ∈ supModule Xo c la (cusp Xo c U a n) := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
    exact this
  · have hf' : f ∈ supModule Xo c la (cusp Xo c U a n) := hf
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hf'
    obtain ⟨o, ho⟩ := hf'
    exact ⟨fun i => o i, fun i => (o i).2, ho.symm⟩

end GlobalTheory.SupFinite
