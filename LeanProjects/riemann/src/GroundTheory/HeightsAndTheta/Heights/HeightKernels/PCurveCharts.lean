import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsClosedPointChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain

noncomputable section

namespace CurveAffineCharts

variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

theorem exists_chart (hy : IsArithVar (mCoordIdeal y) 1) : ∃ t : T, y ⟨(), t⟩ ≠ 0 := by
  obtain ⟨t, ht⟩ := hy.2.1.2.2 ()
  refine ⟨t, fun h0 => ht ?_⟩
  simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]

omit [Fintype T] in

theorem mem_integer_of_mem_chartRingZ [NumberField K'] (v : HeightOneSpectrum (𝓞 K')) (t : T)
    (ht : ∀ u, v.valuation K' (y ⟨(), u⟩) ≤ v.valuation K' (y ⟨(), t⟩)) {b : K'}
    (hb : b ∈ chartRingZ y (fun _ => t)) : b ∈ (v.valuation K').integer := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    rw [Valuation.mem_integer_iff, map_div₀]
    rcases eq_or_ne (v.valuation K' (y ⟨(), t⟩)) 0 with h0 | h0
    · simp [h0]
    · exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (ht u)
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem mem_integralClosure_of_mem_curveRing [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1)
    {b : K'} (hb : b ∈ curveRing y) : b ∈ integralClosure ℤ K' := by
  obtain ⟨t0, ht0⟩ := exists_chart y hy
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' b ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' b hv
    rw [← hr]
    exact r.2
  intro v
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  exact mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _))
    (mem_curveRing.mp hb (fun _ => t) (fun _ => hyt))

theorem finite [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) : Module.Finite ℤ (curveRing y) := by
  have : Module.Finite ℤ (integralClosure ℤ K') := inferInstanceAs (Module.Finite ℤ (𝓞 K'))
  let f : curveRing y →ₗ[ℤ] integralClosure ℤ K' :=
    { toFun := fun b => ⟨b, mem_integralClosure_of_mem_curveRing y hy b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h => Subtype.ext (congrArg (fun z : integralClosure ℤ K' => (z : K')) h)

theorem mem_blockFnField_of_mem_curveRing [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1)
    {b : K'} (hb : b ∈ curveRing y) : b ∈ blockFnField y := by
  obtain ⟨t, ht⟩ := exists_chart y hy
  have hbt := mem_curveRing.mp hb (fun _ => t) (fun _ => ht)
  clear hb
  induction hbt using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem exists_nat_mul_mem_adjoin [CharZero K'] {S : Set K'} {x : K'} (hx : x ∈ Algebra.adjoin ℚ S) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ Algebra.adjoin ℤ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_nz, ?_⟩
    have hq : (q.den : K') * algebraMap ℚ K' q = (q.num : K') := by
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [hq]
    exact intCast_mem _ _
  | add x z _ _ hx hz =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : K') * (x + z) = (m : K') * ((n : K') * x) + (n : K') * ((m : K') * z) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ m) hnx) (mul_mem (natCast_mem _ n) hmz)
  | mul x z _ _ hx hz =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : K') * (x * z) = ((n : K') * x) * ((m : K') * z) := by
      push_cast; ring
    rw [e]
    exact mul_mem hnx hmz

omit [Fintype T] in

theorem mem_adjoin_of_mem_blockFnField [NumberField K'] (t : T) (ht : y ⟨(), t⟩ ≠ 0) {x : K'}
    (hx : x ∈ blockFnField y) :
    x ∈ Algebra.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)]
  have hle : blockFnField y ≤
      IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, -, rfl⟩
    have hp : y p / y ⟨(), t⟩ ∈
        IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) :=
      IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨(), t⟩ ∈
        IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) :=
      IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    rw [← div_div_div_cancel_right₀ ht]
    exact div_mem hp hq
  exact hle hx

theorem exists_nat_mul_mem_curveRing [NumberField K'] {x : K'} (hx : x ∈ blockFnField y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ curveRing y := by
  classical
  have key : ∀ t : T, ∃ n : ℕ, n ≠ 0 ∧ (y ⟨(), t⟩ ≠ 0 → (n : K') * x ∈ chartRingZ y (fun _ => t)) := by
    intro t
    by_cases ht : y ⟨(), t⟩ = 0
    · exact ⟨1, one_ne_zero, fun h => (h ht).elim⟩
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin (mem_adjoin_of_mem_blockFnField y t ht hx)
      exact ⟨n, hn, fun _ => h⟩
  choose N hN0 hN using key
  refine ⟨∏ t, N t, Finset.prod_ne_zero_iff.mpr (fun t _ => hN0 t), ?_⟩
  rw [mem_curveRing]
  intro c hc
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  have h1 := hN (c ()) (hc ())
  rw [← hc'] at h1
  have e : ((∏ t, N t : ℕ) : K') * x =
      ((∏ t ∈ Finset.univ.erase (c ()), N t : ℕ) : K') * ((N (c ()) : K') * x) := by
    rw [← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ (c ()))]
    push_cast; ring
  rw [e]
  exact mul_mem (natCast_mem _ _) h1

theorem finrank_eq [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) :
    Module.finrank ℤ (curveRing y) = Module.finrank ℚ (blockFnField y) := by
  have := finite y hy
  let b := Module.finBasis ℤ (curveRing y)
  let ι : curveRing y →ₗ[ℤ] K' := (curveRing y).subtype.toAddMonoidHom.toIntLinearMap
  have hliZ : LinearIndependent ℤ (ι ∘ b) :=
    b.linearIndependent.map' ι (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ (ι ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hspan : Submodule.span ℚ (Set.range (ι ∘ b)) =
      Subalgebra.toSubmodule (blockFnField y).toSubalgebra := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact mem_blockFnField_of_mem_curveRing y hy (b i).2
    · intro x hx
      obtain ⟨n, hn, hnx⟩ := exists_nat_mul_mem_curveRing y hx
      have h1 : (⟨_, hnx⟩ : curveRing y) ∈ Submodule.span ℤ (Set.range b) := by
        rw [b.span_eq]; trivial
      have h2 : (n : K') * x ∈ Submodule.span ℤ (Set.range (ι ∘ b)) := by
        rw [Set.range_comp, ← Submodule.map_span]
        exact Submodule.mem_map_of_mem h1
      have h3 : (n : K') * x ∈ Submodule.span ℚ (Set.range (ι ∘ b)) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ h2
      have h4 : x = (n : ℚ)⁻¹ • ((n : K') * x) := by
        rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]
      rw [h4]
      exact Submodule.smul_mem _ _ h3
  rw [← IntermediateField.finrank_eq_finrank_subalgebra, ← Subalgebra.finrank_toSubmodule, ← hspan,
    finrank_span_eq_card hliQ, Fintype.card_fin]

end CurveAffineCharts

theorem CurveCharts.proof (hc : ClosedPointChart.Statement) : CurveCharts.Statement :=
  fun T _ K' _ _ y hy =>
    ⟨CurveAffineCharts.finite y hy, CurveAffineCharts.finrank_eq y hy, hc T K' y hy⟩

end

end GroundTheory.Heights₂.Heights
