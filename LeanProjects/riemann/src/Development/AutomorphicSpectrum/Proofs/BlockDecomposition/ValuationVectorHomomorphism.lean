import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.VKMap

variable {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K} {v : Pl}

theorem ord_eq_zero_of_valued (x : Qv v) (hx : Valued.v x = 1) : ord x = 0 := by
  have hE := ValuativeRel.isEquiv (ValuativeRel.valuation (Qv v)) (Valued.v : Valuation (Qv v) _)
  have h1 : ValuativeRel.valuation (Qv v) x = ValuativeRel.valuation (Qv v) 1 := by
    rw [map_one]; exact hE.eq_one_iff_eq_one.2 hx
  have h2 := (normalizedValuation_eq_iff (K := Qv v)).2 h1
  simp [ord, h2]

theorem ord_one_Qv : ord (1 : Qv v) = 0 := ord_eq_zero_of_valued 1 (map_one _)

theorem valued_le_one_of_integral (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] (x : Qv v) (y : K)
    (hy : IsIntegral ℤ y) (h : algebraMap (Qv v) (Kv K w) x = algebraMap K (Kv K w) y) :
    Valued.v x ≤ 1 := by
  obtain ⟨p, hp, hev⟩ := hy
  set φ := algebraMap (Qv v) (Kv K w) with hφ
  set ψ := algebraMap K (Kv K w) with hψ
  have h1 : p.eval₂ (Int.castRingHom (Qv v)) x = 0 := by
    apply φ.injective
    rw [Polynomial.hom_eval₂, h, map_zero]
    have e : φ.comp (Int.castRingHom (Qv v)) = ψ.comp (algebraMap ℤ K) := RingHom.ext_int _ _
    rw [e, ← Polynomial.hom_eval₂, hev, map_zero]
  have h3 : IsIntegral (Valued.v : Valuation (Qv v) _).integer x := by
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (Valued.v : Valuation (Qv v) _).integer (Qv v)).comp (Int.castRingHom _) =
        Int.castRingHom (Qv v) := RingHom.ext_int _ _
    rw [e, h1]
  exact (Valuation.integer.integers _).mem_of_integral h3

theorem exists_int_mul_integral (y : K) : ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : K) * y) := by
  obtain ⟨d, hd, h⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic y))
  exact ⟨d, hd, by simpa [zsmul_eq_mul] using h⟩

theorem valued_int_eq (v : Pl) (d : ℤ) :
    Valued.v (d : Qv v) = HeightOneSpectrum.valuation ℚ v (d : ℚ) := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (d : 𝓞 ℚ)
  simpa using this

theorem finite_int (d : ℤ) (hd : d ≠ 0) : {v : Pl | Valued.v (d : Qv v) ≠ 1}.Finite := by
  refine (HeightOneSpectrum.Support.finite (𝓞 ℚ) ((d : ℚ)⁻¹)).subset ?_
  intro v hv
  have hv' : HeightOneSpectrum.valuation ℚ v (d : ℚ) ≠ 1 := by
    rw [← valued_int_eq]; exact hv
  have hle : HeightOneSpectrum.valuation ℚ v (d : ℚ) ≤ 1 := by
    have := HeightOneSpectrum.valuation_le_one (K := ℚ) v (d : 𝓞 ℚ)
    simpa using this
  have hlt := lt_of_le_of_ne hle hv'
  have h0 : HeightOneSpectrum.valuation ℚ v (d : ℚ) ≠ 0 := by
    simpa using hd
  show 1 < HeightOneSpectrum.valuation ℚ v ((d : ℚ)⁻¹)
  rw [map_inv₀]
  exact (one_lt_inv₀ (zero_lt_iff.2 h0)).2 hlt

theorem degreeOneEmbedding_algebraMap_split (hK : Module.finrank ℚ K = 2) (w₁ w₂ : PlK K)
    [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal] (hne : w₁ ≠ w₂) (ξ : K) :
    algebraMap (Qv v) (Kv K w₁) (dg1 v w₁ ξ) = algebraMap K (Kv K w₁) ξ :=
  (GlobalTheory.T.split_place_embedding_properties K hK v w₁ w₂ hne).1 ξ

theorem firstEmbedding_ne_zero (hK : Module.finrank ℚ K = 2) (L : LM c v) (hL : L.ok) {ξ : K} (hξ : ξ ≠ 0) :
    e1 L ξ ≠ 0 := by
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    intro h
    have h' : dg1 v w₁ ξ = 0 := h
    have := degreeOneEmbedding_algebraMap_split (v := v) hK w₁ w₂ hL.1 ξ
    rw [h', map_zero] at this
    exact hξ ((algebraMap K (Kv K w₁)).injective (by rw [← this, map_zero]))
  | ns w σ η Φ => exact one_ne_zero

theorem firstEmbedding_mul (hK : Module.finrank ℚ K = 2) (L : LM c v) (hL : L.ok) (a b : K) :
    e1 L (a * b) = e1 L a * e1 L b := by
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    show dg1 v w₁ (a * b) = dg1 v w₁ a * dg1 v w₁ b
    apply (algebraMap (Qv v) (Kv K w₁)).injective
    rw [map_mul, degreeOneEmbedding_algebraMap_split hK w₁ w₂ hL.1, degreeOneEmbedding_algebraMap_split hK w₁ w₂ hL.1, degreeOneEmbedding_algebraMap_split hK w₁ w₂ hL.1, map_mul]
  | ns w σ η Φ => exact (one_mul 1).symm

theorem unitCoordinate_eq_firstEmbedding (hK : Module.finrank ℚ K = 2) (L : LM c v) (hL : L.ok) (κ : Kˣ) :
    ((k1 L κ : (Qv v)ˣ) : Qv v) = e1 L (κ : K) := by
  rw [k1, dif_neg (firstEmbedding_ne_zero hK L hL κ.ne_zero)]
  rfl

theorem order_unitCoordinate_mul (hK : Module.finrank ℚ K = 2) (L : LM c v) (hL : L.ok) (a b : Kˣ) :
    ord ((k1 L (a * b) : (Qv v)ˣ) : Qv v) =
      ord ((k1 L a : (Qv v)ˣ) : Qv v) + ord ((k1 L b : (Qv v)ˣ) : Qv v) := by
  rw [unitCoordinate_eq_firstEmbedding hK L hL, unitCoordinate_eq_firstEmbedding hK L hL, unitCoordinate_eq_firstEmbedding hK L hL, Units.val_mul, firstEmbedding_mul hK L hL]
  exact ord_mul (firstEmbedding_ne_zero hK L hL a.ne_zero) (firstEmbedding_ne_zero hK L hL b.ne_zero)

theorem order_unitCoordinate_field_datum (hK : Module.finrank ℚ K = 2) (L : LM c v) (hL : L.ok) (hs : ¬ L.IsSp) (κ : Kˣ) :
    ord ((k1 L κ : (Qv v)ˣ) : Qv v) = 0 := by
  rw [unitCoordinate_eq_firstEmbedding hK L hL]
  cases L with
  | sp w₁ w₂ Φ => exact absurd trivial hs
  | ns w σ η Φ => exact ord_one_Qv

theorem order_unitCoordinate_of_integral (hK : Module.finrank ℚ K = 2) (L : LM c v) (hL : L.ok) (κ : Kˣ) {d e : ℤ}
    (hd : IsIntegral ℤ ((d : K) * (κ : K))) (he : IsIntegral ℤ ((e : K) * ((κ⁻¹ : Kˣ) : K)))
    (hdv : Valued.v (d : Qv v) = 1) (hev : Valued.v (e : Qv v) = 1) :
    ord ((k1 L κ : (Qv v)ˣ) : Qv v) = 0 := by
  rw [unitCoordinate_eq_firstEmbedding hK L hL]
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    have hm := degreeOneEmbedding_algebraMap_split (v := v) hK w₁ w₂ hL.1
    show ord (dg1 v w₁ (κ : K)) = 0
    apply ord_eq_zero_of_valued
    have a1 : Valued.v (dg1 v w₁ (κ : K)) ≤ 1 := by
      have := valued_le_one_of_integral w₁ ((d : Qv v) * dg1 v w₁ (κ : K)) _ hd
        (by rw [map_mul, map_mul, hm, map_intCast, map_intCast])
      rwa [map_mul, hdv, one_mul] at this
    have a2 : Valued.v (dg1 v w₁ ((κ⁻¹ : Kˣ) : K)) ≤ 1 := by
      have := valued_le_one_of_integral w₁ ((e : Qv v) * dg1 v w₁ ((κ⁻¹ : Kˣ) : K)) _ he
        (by rw [map_mul, map_mul, hm, map_intCast, map_intCast])
      rwa [map_mul, hev, one_mul] at this
    have a3 : dg1 v w₁ (κ : K) * dg1 v w₁ ((κ⁻¹ : Kˣ) : K) = 1 := by
      apply (algebraMap (Qv v) (Kv K w₁)).injective
      rw [map_mul, hm, hm, ← map_mul, Units.mul_inv, map_one, map_one]
    have a4 : Valued.v (dg1 v w₁ (κ : K)) * Valued.v (dg1 v w₁ ((κ⁻¹ : Kˣ) : K)) = 1 := by
      rw [← map_mul, a3, map_one]
    refine le_antisymm a1 ?_
    calc (1 : _) = Valued.v (dg1 v w₁ (κ : K)) * Valued.v (dg1 v w₁ ((κ⁻¹ : Kˣ) : K)) := a4.symm
      _ ≤ Valued.v (dg1 v w₁ (κ : K)) * 1 := mul_le_mul_right a2 _
      _ = _ := mul_one _
  | ns w σ η Φ => exact ord_one_Qv

theorem support_ord_finite (hK : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (κ : Kˣ) :
    (Function.support fun v : Pl => ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v)).Finite := by
  obtain ⟨d, hd0, hd⟩ := exists_int_mul_integral (κ : K)
  obtain ⟨e, he0, he⟩ := exists_int_mul_integral ((κ⁻¹ : Kˣ) : K)
  refine ((finite_int d hd0).union (finite_int e he0)).subset ?_
  intro v hv
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
  exact hv (order_unitCoordinate_of_integral hK (M v) (hM.1 v) κ hd he hc.1 hc.2)

theorem vK_apply (hK : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (κ : Kˣ) (v : Pl) :
    vK M κ v = ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v) := by
  rw [vK, dif_pos (support_ord_finite hK M hM κ)]
  rfl

theorem vK_valuation_map : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
  ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
    (∀ (κ : Kˣ) (v : Pl), vK M κ v = ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v)) ∧ (∀ κ : Kˣ, vK M κ ∈ Tm M) ∧
      ∀ a b : Kˣ, vK M (a * b) = vK M a + vK M b := by
  intro K _ _ hK c M hM
  refine ⟨vK_apply hK M hM, ?_, ?_⟩
  · intro κ v hv
    by_contra hs
    exact hv ((vK_apply hK M hM κ v).trans (order_unitCoordinate_field_datum hK (M v) (hM.1 v) hs κ))
  · intro a b
    ext v
    rw [Finsupp.add_apply, vK_apply hK M hM, vK_apply hK M hM, vK_apply hK M hM]
    exact order_unitCoordinate_mul hK (M v) (hM.1 v) a b

end GlobalTheory.CompanionTheory.FexTheta.VKMap
