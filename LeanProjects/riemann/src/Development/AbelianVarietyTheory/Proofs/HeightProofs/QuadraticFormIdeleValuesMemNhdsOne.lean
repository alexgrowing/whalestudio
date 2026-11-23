import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitNormFormAtOddPlace

open NumberField IsDedekindDomain
open scoped Topology

namespace GlobalTheory.QNorm

namespace NormOpen

variable {F : Type} [Field F] [NumberField F]

theorem eventually_isSquare_finite (v : HeightOneSpectrum (𝓞 F)) :
    ∀ᶠ x in 𝓝 (1 : v.adicCompletion F), IsSquare x := by
  have h2eq : ((2 : F) : v.adicCompletion F) = 2 := by
    rw [show (2 : F) = 1 + 1 from one_add_one_eq_two.symm,
      show (2 : v.adicCompletion F) = 1 + 1 from one_add_one_eq_two.symm,
      HeightOneSpectrum.adicCompletion.coe_add, HeightOneSpectrum.adicCompletion.coe_one]
  have h2v : Valued.v (2 : v.adicCompletion F) ≠ 0 := by
    rw [← h2eq, HeightOneSpectrum.adicCompletion.valued_coe]
    exact (Valuation.ne_zero_iff _).2 two_ne_zero
  have h2le : Valued.v (2 : v.adicCompletion F) ≤ 1 := by
    rw [← one_add_one_eq_two]
    exact (Valued.v.map_add 1 1).trans (by simp)
  set m : ℤ := WithZero.log (Valued.v (2 : v.adicCompletion F)) with hm
  have hexp : WithZero.exp m = Valued.v (2 : v.adicCompletion F) := WithZero.exp_log h2v
  have hm0 : m ≤ 0 := by
    rw [← WithZero.exp_le_exp, hexp, WithZero.exp_zero]
    exact h2le
  set e : ℕ := (-m).toNat with he_def
  have he : Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    rw [← hexp, he_def, this, neg_neg]
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set c : v.adicCompletion F := ((π : F) : v.adicCompletion F) ^ (2 * e + 1) with hc_def
  have hc : Valued.v c = WithZero.exp (-((2 * e + 1 : ℕ) : ℤ)) := by
    rw [hc_def, map_pow, HeightOneSpectrum.adicCompletion.valued_coe, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have hc1 : Valued.v c < 1 := by
    rw [hc, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from rfl, WithZero.exp_lt_exp]
    omega
  have hN : {x : v.adicCompletion F | (x - 1) * c⁻¹ ∈ (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).integer} ∈
      𝓝 (1 : v.adicCompletion F) := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)
    · simp [Valuation.mem_integer_iff]
  filter_upwards [hN] with x hx
  rw [Valuation.mem_integer_iff] at hx
  have hle : Valued.v (x - 1) ≤ Valued.v c :=
    calc Valued.v (x - 1) = Valued.v ((x - 1) * c⁻¹) * Valued.v c := by
          rw [← map_mul, inv_mul_cancel_right₀ hc0]
      _ ≤ 1 * Valued.v c := by gcongr
      _ = Valued.v c := one_mul _
  have hvx : Valued.v x = 1 := by
    have : x = 1 + (x - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ (hle.trans_lt hc1)
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hvx
    exact zero_ne_one hvx
  have hu : Units.mk0 x hx0 ∈ hiUnits (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (2 * e + 1) :=
    ⟨hvx, hc ▸ hle⟩
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 (hiUnits_le_sqs_hiUnits F v e he hu)
  have hy' := congrArg Units.val hy
  simp only [powMonoidHom_apply, Units.val_mk0, pow_two] at hy'
  exact ⟨y, hy'.symm⟩

omit [NumberField F] in

theorem eventually_isSquare_infinite (w : InfinitePlace F) :
    ∀ᶠ x in 𝓝 (1 : w.Completion), IsSquare x := by
  rcases w.isReal_or_isComplex with hw | hw
  · let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hφ : Continuous φ := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
    have hpos : ∀ᶠ x in 𝓝 (1 : w.Completion), 0 < φ x := by
      have h := hφ.tendsto 1
      rw [map_one] at h
      exact h.eventually (lt_mem_nhds one_pos)
    filter_upwards [hpos] with x hx
    have hs : IsSquare (φ x) := ⟨Real.sqrt (φ x), (Real.mul_self_sqrt hx.le).symm⟩
    simpa using hs.map φ.symm
  · let φ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (φ x)
    simpa using IsSquare.map φ.symm (⟨z, hz⟩ : IsSquare (φ x))

theorem eventually_integral :
    ∀ᶠ a in 𝓝 (1 : FiniteAdeleRing (𝓞 F) F), ∀ v, a v ∈ v.adicCompletionIntegers F := by
  have ho : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a.1 v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  exact ho.mem_nhds (fun v => (one_mem (v.adicCompletionIntegers F) : _))

theorem continuous_eval (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (fun a : FiniteAdeleRing (𝓞 F) F => a v) := by
  exact RestrictedProduct.continuous_eval v

end NormOpen

open NormOpen in

theorem norm_form_mem_nhds_one : ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → {a : (AdeleRing (𝓞 F) F)ˣ | ∃ x y : AdeleRing (𝓞 F) F, (a : AdeleRing (𝓞 F) F) = x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) := by
  intro F _ _ δ hδ
  set S : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v.valuation F (2 : F) ≠ 1} ∪ {v | v.valuation F δ ≠ 1} with hS
  have hSfin : S.Finite := by
    have h2 := finite_valuation_ne_one F (Units.mk0 (2 : F) two_ne_zero)
    have hd := finite_valuation_ne_one F (Units.mk0 δ hδ)
    simp only [Units.val_mk0] at h2 hd
    exact h2.union hd
  set U : Set (AdeleRing (𝓞 F) F) := {b | (∀ w, IsSquare (b.1 w)) ∧
    ((∀ v, b.2 v ∈ v.adicCompletionIntegers F) ∧ ∀ v ∈ S, IsSquare (b.2 v))} with hU_def
  have hU : U ∈ 𝓝 (1 : AdeleRing (𝓞 F) F) := by
    have h1 : ∀ᶠ b in 𝓝 (1 : InfiniteAdeleRing F), ∀ w, IsSquare (b w) := by
      have h : ∀ᶠ b in 𝓝 (1 : (w : InfinitePlace F) → w.Completion), ∀ w, IsSquare (b w) := by
        rw [nhds_pi]
        exact Filter.eventually_pi fun w => NormOpen.eventually_isSquare_infinite w
      exact h
    have h2 : ∀ᶠ b in 𝓝 (1 : FiniteAdeleRing (𝓞 F) F), ∀ v ∈ S, IsSquare (b v) := by
      refine (Filter.eventually_all_finite hSfin).2 fun v _ => ?_
      exact ((NormOpen.continuous_eval v).tendsto 1).eventually (NormOpen.eventually_isSquare_finite v)
    have h3 : ∀ᶠ z in 𝓝 ((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)),
        (∀ w, IsSquare (z.1 w)) ∧ ((∀ v, z.2 v ∈ v.adicCompletionIntegers F) ∧ ∀ v ∈ S, IsSquare (z.2 v)) :=
      h1.prod_nhds (NormOpen.eventually_integral.and h2)
    exact h3
  have hV : ∀ᶠ a : (AdeleRing (𝓞 F) F)ˣ in 𝓝 1,
      (a : AdeleRing (𝓞 F) F) ∈ U ∧ ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ U := by
    have hc1 : Filter.Tendsto (fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F))
        (𝓝 1) (𝓝 1) := by
      simpa using Units.continuous_val.tendsto (1 : (AdeleRing (𝓞 F) F)ˣ)
    have hc2 : Filter.Tendsto
        (fun a : (AdeleRing (𝓞 F) F)ˣ => ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
        (𝓝 1) (𝓝 1) := by
      simpa using Units.continuous_coe_inv.tendsto (1 : (AdeleRing (𝓞 F) F)ˣ)
    exact (hc1.eventually hU).and (hc2.eventually hU)
  filter_upwards [hV] with a ha
  obtain ⟨⟨hAinf, hAint, hAS⟩, ⟨-, hBint, -⟩⟩ := ha
  set A : AdeleRing (𝓞 F) F := (a : AdeleRing (𝓞 F) F) with hA_def
  set B : AdeleRing (𝓞 F) F := ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) with hB_def
  have hAB : A * B = 1 := a.mul_inv
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ p : v.adicCompletion F × v.adicCompletion F,
      A.2 v = p.1 ^ 2 - (algebraMap F (AdeleRing (𝓞 F) F) δ).2 v * p.2 ^ 2 ∧
      (v ∉ S → p.1 ∈ v.adicCompletionIntegers F ∧ p.2 ∈ v.adicCompletionIntegers F) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨r, hr⟩ := hAS v hv
      exact ⟨(r, 0), by rw [hr]; ring, fun h => absurd hv h⟩
    · have hv2 : v.valuation F (2 : F) = 1 := by
        by_contra h; exact hv (Or.inl h)
      have hvδ : v.valuation F δ = 1 := by
        by_contra h; exact hv (Or.inr h)
      have h2eq : ((2 : F) : v.adicCompletion F) = 2 := by
        rw [show (2 : F) = 1 + 1 from one_add_one_eq_two.symm,
          show (2 : v.adicCompletion F) = 1 + 1 from one_add_one_eq_two.symm,
          HeightOneSpectrum.adicCompletion.coe_add, HeightOneSpectrum.adicCompletion.coe_one]
      have h2 : Valued.v (2 : v.adicCompletion F) = 1 := by
        rw [← h2eq, HeightOneSpectrum.adicCompletion.valued_coe, hv2]
      have hδv : Valued.v ((algebraMap F (AdeleRing (𝓞 F) F) δ).2 v) = 1 := by
        change Valued.v ((δ : F) : v.adicCompletion F) = 1
        rw [HeightOneSpectrum.adicCompletion.valued_coe, hvδ]
      have hprod : A.2 v * B.2 v = 1 := by
        have := congrArg (fun z : AdeleRing (𝓞 F) F => z.2 v) hAB
        exact this
      have hAle : Valued.v (A.2 v) ≤ 1 := hAint v
      have hBle : Valued.v (B.2 v) ≤ 1 := hBint v
      have hAv : Valued.v (A.2 v) = 1 := by
        have hmul : Valued.v (A.2 v) * Valued.v (B.2 v) = 1 := by
          rw [← map_mul, hprod, map_one]
        refine le_antisymm hAle ?_
        calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (A.2 v) * Valued.v (B.2 v) := hmul.symm
          _ ≤ Valued.v (A.2 v) * 1 := by gcongr
          _ = Valued.v (A.2 v) := mul_one _
      obtain ⟨x, hx, y, hy, hxy⟩ :=
        exists_integral_sq_sub_mul_sq_of_unit F v _ (A.2 v) h2 hδv hAv
      exact ⟨(x, y), hxy, fun _ => ⟨hx, hy⟩⟩
  choose p hp using hloc
  choose r hr using hAinf
  have hx : ∀ᶠ v in Filter.cofinite, (p v).1 ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_cofinite.2 (hSfin.subset fun v hv => ?_)
    by_contra h
    exact hv ((hp v).2 h).1
  have hy : ∀ᶠ v in Filter.cofinite, (p v).2 ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_cofinite.2 (hSfin.subset fun v hv => ?_)
    by_contra h
    exact hv ((hp v).2 h).2
  let X : AdeleRing (𝓞 F) F :=
    ((fun w => r w : InfiniteAdeleRing F), RestrictedProduct.mk (fun v => (p v).1) hx)
  let Y : AdeleRing (𝓞 F) F :=
    ((0 : InfiniteAdeleRing F), RestrictedProduct.mk (fun v => (p v).2) hy)
  refine ⟨X, Y, ?_⟩
  refine Prod.ext ?_ ?_
  · funext w
    change A.1 w = r w ^ 2 - (algebraMap F (AdeleRing (𝓞 F) F) δ).1 w * (0 : w.Completion) ^ 2
    rw [hr w]
    ring
  · refine RestrictedProduct.ext _ _ fun v => ?_
    change A.2 v = (p v).1 ^ 2 - (algebraMap F (AdeleRing (𝓞 F) F) δ).2 v * (p v).2 ^ 2
    exact (hp v).1

end GlobalTheory.QNorm
