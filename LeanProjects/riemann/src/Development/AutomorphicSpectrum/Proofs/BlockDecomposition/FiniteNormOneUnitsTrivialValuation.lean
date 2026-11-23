import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaValueIndicator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralBasisLocalIntegrality
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.Stab

variable {K : Type} [Field K] [NumberField K]

theorem eq_one_of_le_of_inv_le {a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (h1 : a ≤ 1) (h2 : a⁻¹ ≤ 1) : a = 1 :=
  le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 ha)).1 h2)

theorem ord_eq_zero_iff (w : PlK K) {y : Kv K w} (hy : y ≠ 0) : ord y = 0 ↔ Valued.v y = 1 := by
  have hO : ∀ z : Kv K w, normalizedValuation (Kv K w) z ≤ 1 ↔ Valued.v z ≤ 1 := fun z => by
    rw [normalizedValuation_le_one_iff]
    exact GlobalTheory.CompanionTheory.IntCoord.mem_O_iff w z
  have hnv : ord y = 0 ↔ normalizedValuation (Kv K w) y = 1 := by
    rw [normalizedValuation_eq_exp_ord hy]
    constructor
    · intro h
      simp [h]
    · intro h
      have h' : WithZero.exp (-ord y) = WithZero.exp (0 : ℤ) := by simpa using h
      have := WithZero.exp_inj.1 h'
      omega
  rw [hnv]
  constructor
  · intro h
    refine eq_one_of_le_of_inv_le (by simpa using hy) ((hO y).1 h.le) ?_
    rw [← map_inv₀]
    exact (hO _).1 (by rw [map_inv₀, h, inv_one])
  · intro h
    refine eq_one_of_le_of_inv_le (by simpa using hy) ((hO y).2 h.le) ?_
    rw [← map_inv₀]
    exact (hO _).2 (by rw [map_inv₀, h, inv_one])

theorem alg_ne_zero (w : PlK K) (κ : Kˣ) : algebraMap K (Kv K w) (κ : K) ≠ 0 := by
  simp

theorem ord_alg_eq_zero_iff (w : PlK K) (κ : Kˣ) :
    ord (algebraMap K (Kv K w) (κ : K)) = 0 ↔ w.valuation K (κ : K) = 1 := by
  rw [ord_eq_zero_iff w (alg_ne_zero w κ), GlobalTheory.CompanionTheory.IntCoord.val_alg]

theorem algebraMap_degreeOneEmbedding_inverse (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h1 : Module.finrank (Qv v) (Kv K w) = 1) (ξ : K) :
    algebraMap (Qv v) (Kv K w) (dg1 v w ξ) = algebraMap K (Kv K w) ξ :=
  Function.rightInverse_invFun (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.algebraMap_bijective v w h1).2 _

theorem degreeOneEmbedding_ne_zero (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h1 : Module.finrank (Qv v) (Kv K w) = 1) (κ : Kˣ) : dg1 v w (κ : K) ≠ 0 := by
  intro h
  have := algebraMap_degreeOneEmbedding_inverse v w h1 (κ : K)
  rw [h, map_zero] at this
  exact alg_ne_zero w κ this.symm

theorem ord_alg_eq (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h1 : Module.finrank (Qv v) (Kv K w) = 1) (ξ : K) :
    ord (algebraMap K (Kv K w) ξ) = ramificationIndex (Qv v) (Kv K w) * ord (dg1 v w ξ) := by
  rw [← algebraMap_degreeOneEmbedding_inverse v w h1, ord_algebraMap]

theorem order_degreeOneEmbedding_eq_zero_iff (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h1 : Module.finrank (Qv v) (Kv K w) = 1) (ξ : K) :
    ord (dg1 v w ξ) = 0 ↔ ord (algebraMap K (Kv K w) ξ) = 0 := by
  have he : (ramificationIndex (Qv v) (Kv K w) : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIndex_pos (Qv v) (Kv K w)).ne'
  rw [ord_alg_eq v w h1, mul_eq_zero, or_iff_right he]

variable {c : HeckeCharacter K} {v : Pl}

theorem order_unit_field_datum_zero (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] (σ : Kv K w ≃ₐ[Qv v] Kv K w) (η : (Qv v)ˣ →* ℂˣ)
    (Φ : Kv K w → ℂ) (κ : Kˣ) : ord ((k1 (LM.ns (c := c) w σ η Φ) κ : (Qv v)ˣ) : Qv v) = 0 := by
  have h : e1 (LM.ns (c := c) w σ η Φ) (κ : K) ≠ 0 := by simp [e1]
  simp [k1, h, e1, ord]

theorem split_datum_unit_coordinate (w₁ w₂ : PlK K) [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal]
    (Φ : Qv v × Qv v → ℂ) (κ : Kˣ) (h : dg1 v w₁ (κ : K) ≠ 0) :
    ((k1 (LM.sp (c := c) w₁ w₂ Φ) κ : (Qv v)ˣ) : Qv v) = dg1 v w₁ (κ : K) := by
  have h' : e1 (LM.sp (c := c) w₁ w₂ Φ) (κ : K) ≠ 0 := h
  simp only [k1, dif_neg h']
  rfl

def pl : LM c v → PlK K
  | LM.sp w₁ _ _ => w₁
  | LM.ns w .. => w

theorem pl_liesOver (L : LM c v) : (pl L).asIdeal.LiesOver v.asIdeal := by
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ => exact i₁
  | @ns w i σ η Φ => exact i

theorem order_unit_coordinate_of_valuation_one (h2 : Module.finrank ℚ K = 2) (L : LM c v) (hok : L.ok) (κ : Kˣ)
    (h : (pl L).valuation K (κ : K) = 1) : ord ((k1 L κ : (Qv v)ˣ) : Qv v) = 0 := by
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    obtain ⟨-, d₁, -⟩ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_split h2 v w₁ w₂ hok.1
    rw [split_datum_unit_coordinate w₁ w₂ Φ κ (degreeOneEmbedding_ne_zero v w₁ d₁ κ), order_degreeOneEmbedding_eq_zero_iff v w₁ d₁, ord_alg_eq_zero_iff]
    exact h
  | @ns w i σ η Φ => exact order_unit_field_datum_zero w σ η Φ κ

theorem ord_norm_alg (u : PlK K) [u.asIdeal.LiesOver v.asIdeal] (y : Kv K u) :
    ord (Algebra.norm (Qv v) y) = residueDegree (Qv v) (Kv K u) * ord y :=
  ord_norm y

theorem val_eq_one (h2 : Module.finrank ℚ K = 2) (L : LM c v) (hok : L.ok) (κ : Kˣ)
    (hN : Algebra.norm ℚ (κ : K) = 1) (h0 : ord ((k1 L κ : (Qv v)ˣ) : Qv v) = 0)
    (w : PlK K) (hw : w.asIdeal.LiesOver v.asIdeal) : w.valuation K (κ : K) = 1 := by
  classical
  have hprod := SemiLocal.algebraMap_norm_eq_prod (K := ℚ) (L := K) v (κ : K)
  rw [hN, map_one] at hprod
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    obtain ⟨hall, d₁, d₂⟩ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_split h2 v w₁ w₂ hok.1
    rw [split_datum_unit_coordinate w₁ w₂ Φ κ (degreeOneEmbedding_ne_zero v w₁ d₁ κ), order_degreeOneEmbedding_eq_zero_iff v w₁ d₁] at h0
    have hu : (⟨w₁, i₁⟩ : SemiLocal.PlacesOver K v) ≠ ⟨w₂, i₂⟩ :=
      fun h => hok.1 (congrArg Subtype.val h)
    have huniv : (Finset.univ : Finset (SemiLocal.PlacesOver K v)) = {⟨w₁, i₁⟩, ⟨w₂, i₂⟩} := by
      ext u
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases hall u.1 u.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    rw [huniv, Finset.prod_pair hu] at hprod
    replace hprod : (1 : Qv v) = Algebra.norm (Qv v) (algebraMap K (Kv K w₁) (κ : K)) *
        Algebra.norm (Qv v) (algebraMap K (Kv K w₂) (κ : K)) := hprod
    have hn₁ : Algebra.norm (Qv v) (algebraMap K (Kv K w₁) (κ : K)) ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]; exact alg_ne_zero w₁ κ
    have hn₂ : Algebra.norm (Qv v) (algebraMap K (Kv K w₂) (κ : K)) ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]; exact alg_ne_zero w₂ κ
    have ho := congrArg ord hprod
    rw [ord_mul hn₁ hn₂, ord_norm_alg, ord_norm_alg, h0] at ho
    have h1 : ord (1 : Qv v) = 0 := by simp [ord]
    rw [h1] at ho
    have h02 : ord (algebraMap K (Kv K w₂) (κ : K)) = 0 := by
      simpa [(residueDegree_pos (Qv v) (Kv K w₂)).ne'] using ho.symm
    rcases hall w hw with rfl | rfl
    · exact (ord_alg_eq_zero_iff _ κ).1 h0
    · exact (ord_alg_eq_zero_iff _ κ).1 h02
  | @ns w₀ i σ η Φ =>
    obtain ⟨hall, -⟩ := hok
    obtain rfl := hall w hw
    have huniv : (Finset.univ : Finset (SemiLocal.PlacesOver K v)) = {⟨w, i⟩} := by
      ext u
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subtype.ext (hall u.1 u.2)
    rw [huniv, Finset.prod_singleton] at hprod
    replace hprod : (1 : Qv v) = Algebra.norm (Qv v) (algebraMap K (Kv K w) (κ : K)) := hprod
    have ho := congrArg ord hprod
    rw [ord_norm_alg] at ho
    have h1 : ord (1 : Qv v) = 0 := by simp [ord]
    rw [h1] at ho
    have h02 : ord (algebraMap K (Kv K w) (κ : K)) = 0 := by
      simpa [(residueDegree_pos (Qv v) (Kv K w)).ne'] using ho.symm
    exact (ord_alg_eq_zero_iff _ κ).1 h02

theorem pl_injective (M : ∀ v : Pl, LM c v) : Function.Injective (fun v => pl (M v)) := by
  intro a b h
  have ha := pl_liesOver (M a)
  have hb := pl_liesOver (M b)
  simp only at h
  rw [h] at ha
  apply HeightOneSpectrum.ext
  rw [ha.over, hb.over]

theorem support_finite (h2 : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (hok : ∀ v, (M v).ok) (κ : Kˣ) :
    (Function.support fun v : Pl => ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v)).Finite := by
  have hS : {w : PlK K | w.valuation K (κ : K) ≠ 1}.Finite := by
    refine ((HeightOneSpectrum.Support.finite (𝓞 K) (κ : K)).union
      (HeightOneSpectrum.Support.finite (𝓞 K) ((κ : K)⁻¹))).subset ?_
    intro w hw
    rcases lt_or_gt_of_ne hw with h | h
    · right
      show 1 < w.valuation K (κ : K)⁻¹
      rw [map_inv₀]
      exact (one_lt_inv₀ (zero_lt_iff.2 (by simp))).2 h
    · left
      exact h
  refine (hS.preimage (pl_injective M).injOn).subset ?_
  intro v hv h
  exact hv (order_unit_coordinate_of_valuation_one h2 (M v) (hok v) κ h)

theorem val_eq_one_all (h2 : Module.finrank ℚ K = 2) (M : ∀ v : Pl, LM c v) (hok : ∀ v, (M v).ok) (κ : Kˣ)
    (hN : Algebra.norm ℚ (κ : K) = 1) (h0 : vK M κ = 0) (w : PlK K) : w.valuation K (κ : K) = 1 := by
  let v : Pl := ⟨w.asIdeal.under (𝓞 ℚ), inferInstance, Ideal.under_ne_bot _ w.ne_bot⟩
  have hw : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  refine val_eq_one h2 (M v) (hok v) κ hN ?_ w hw
  have h := DFunLike.congr_fun h0 v
  rw [vK, dif_pos (support_finite h2 M hok κ)] at h
  exact h

theorem finite_units (h2 : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K) : Finite (𝓞 K)ˣ := by
  haveI := hc
  have hr : NumberField.Units.rank K = 0 := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h3 : InfinitePlace.nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
    have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    unfold NumberField.Units.rank
    omega
  haveI : IsEmpty (Fin (NumberField.Units.rank K)) := by
    rw [hr]
    infer_instance
  refine Finite.of_surjective (fun ζ : NumberField.Units.torsion K => (ζ : (𝓞 K)ˣ)) fun x => ?_
  obtain ⟨⟨ζ, e⟩, h, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K x
  exact ⟨ζ, by simpa using h.symm⟩

end GlobalTheory.CompanionTheory.FexTheta.Stab

namespace GlobalTheory.CompanionTheory.FexTheta

open GlobalTheory.CompanionTheory.FexTheta.Stab in

theorem finite_stabiliser : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M → Finite {κ : K1 K // vK M (κ : Kˣ) = 0} := by
  intro K _ _ h2 hc c M hM
  haveI := finite_units h2 hc
  have hmem : ∀ κ : {κ : K1 K // vK M (κ : Kˣ) = 0},
      (κ.1 : Kˣ) ∈ Set.range (Units.map (algebraMap (𝓞 K) K).toMonoidHom) := by
    intro κ
    have hN : Algebra.norm ℚ ((κ.1 : Kˣ) : K) = 1 := by
      have h : Units.map (Algebra.norm ℚ : K →* ℚ) (κ.1 : Kˣ) = 1 := MonoidHom.mem_ker.1 κ.1.2
      exact congrArg Units.val h
    have hv := val_eq_one_all h2 M hM.1 (κ.1 : Kˣ) hN κ.2
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
      (((κ.1 : Kˣ) : K)) (fun w => (hv w).le)
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
      (((κ.1 : Kˣ) : K)⁻¹) (fun w => by rw [map_inv₀, hv w, inv_one])
    have hab : a * b = 1 := by
      apply RingOfIntegers.ext
      have : (algebraMap (𝓞 K) K a) * (algebraMap (𝓞 K) K b) = 1 := by
        rw [ha, hb]
        exact mul_inv_cancel₀ (Units.ne_zero _)
      simpa using this
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, Units.ext ha⟩
  refine Finite.of_injective
    (fun κ : {κ : K1 K // vK M (κ : Kˣ) = 0} =>
      (⟨(κ.1 : Kˣ), hmem κ⟩ : Set.range (Units.map (algebraMap (𝓞 K) K).toMonoidHom))) ?_
  intro a b h
  have h' : ((a.1 : K1 K) : Kˣ) = ((b.1 : K1 K) : Kˣ) :=
    congrArg (fun x : Set.range (Units.map (algebraMap (𝓞 K) K).toMonoidHom) => (x : Kˣ)) h
  exact Subtype.ext (Subtype.ext h')

end GlobalTheory.CompanionTheory.FexTheta
