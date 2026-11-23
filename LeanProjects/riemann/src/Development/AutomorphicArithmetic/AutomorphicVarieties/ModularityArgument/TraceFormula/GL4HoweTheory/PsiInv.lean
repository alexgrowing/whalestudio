import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.GalIsom
import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private theorem UpperTheory.V.Z.Tf.L4.psiInv_exists_zpow (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (ϖ : Eˣ) (hϖ : valuation E (ϖ : E) = uniformizer E) (x : Eˣ) :
    ∃ d : ℤ, valuation E (x : E) = valuation E (ϖ : E) ^ d := by
  have h1 : ord E ϖ = 1 := ord_eq_one hϖ
  have hz : ∀ d : ℤ, ord E (ϖ ^ d) = d := by
    intro d
    cases d with
    | ofNat n => simp [DiscreteGroups.sglob.DzType.ord_pow_bis, h1]
    | negSucc n =>
      rw [zpow_negSucc, DiscreteGroups.sglob.DzType.ord_inv_eq_neg_ord, DiscreteGroups.sglob.DzType.ord_pow_bis, h1, Int.negSucc_eq]
      push_cast; ring
  refine ⟨ord E x, ?_⟩
  rw [← map_zpow₀, ← Units.val_zpow_eq_zpow_val]
  exact le_antisymm ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))
    ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))

private theorem UpperTheory.V.Z.Tf.L4.psiInv_shift {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {ψ : AddChar E Circle} {c c' : Eˣ} (h : HasConductor ψ c) (s : E) (hs : s ≠ 0)
    (hc : valuation E s * valuation E (c' : E) = valuation E (c : E)) : HasConductor (ψ.mulShift s) c' := by
  intro x
  have hv : 0 < valuation E s := by simpa [zero_lt_iff] using hs
  have h2 : valuation E x ≤ valuation E (c' : E) ↔ valuation E (s * x) ≤ valuation E (c : E) := by
    rw [← hc, map_mul, mul_le_mul_iff_right₀ hv]
  rw [h2, ← h (s * x)]
  constructor
  · intro H y hy
    have := H (s⁻¹ * y) (by
      rw [map_mul, map_inv₀, inv_mul_le_iff₀ hv, ← map_mul]; exact hy)
    simpa [AddChar.mulShift_apply, hs] using this
  · intro H y hy
    rw [AddChar.mulShift_apply]
    apply H
    rw [map_mul, map_mul]
    gcongr

theorem UpperTheory.V.Z.Tf.L4.psiInv :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∃ c : ℤ, ∀ a₀ : ℤ, ∃ a ≥ a₀, ∃ ψ : AddChar E Circle,
      HasConductor ψ (ϖ ^ (2 * a - c)) ∧ ∀ (σ : E ≃ₐ[k] E) (x : E), ψ (σ x) = ψ x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ
  obtain ⟨ψ₀, hψ₀⟩ := exists_hasConductor_one k
  let Ψ : AddChar E Circle := ψ₀.compAddMonoidHom (Algebra.trace k E).toAddMonoidHom
  have hΨ : ∀ x, Ψ x = ψ₀ (Algebra.trace k E x) := fun _ => rfl
  have hle : ∀ a b : k, valuation k a ≤ valuation k b ↔
      valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) := fun a b => by
    rw [← Valuation.vle_iff_le, ← Valuation.vle_iff_le, ValuativeExtension.vle_iff_vle]
  have htriv : ∀ y : E, valuation E y ≤ 1 → Ψ y = 1 := fun y hy => by
    rw [hΨ]
    refine (hψ₀ 1).2 (by simp) _ ?_
    rw [hle, map_one, map_one, trace_eq_sum_automorphisms]
    refine Valuation.map_sum_le _ fun σ _ => ?_
    rw [UpperTheory.V.Z.Tf.L4.galIsom k E σ y]
    exact hy
  have hcont : Continuous Ψ := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_)
    have : (fun z => -x + z) ⁻¹' cball (1 : Eˣ) ∈ nhds x :=
      ((isOpen_cball (1 : Eˣ)).preimage (by fun_prop)).mem_nhds (by simp [cball])
    filter_upwards [this] with z hz
    have h1 : Ψ (-x + z) = 1 := htriv _ (by simpa [cball] using hz)
    calc Ψ z = Ψ (x + (-x + z)) := by simp
      _ = Ψ x := by rw [AddChar.map_add_eq_mul, h1, mul_one]
  have hne : Ψ ≠ 1 := by
    intro h
    apply hψ₀.ne_one
    ext y
    obtain ⟨x, rfl⟩ := Algebra.trace_surjective k E y
    rw [← hΨ, h]; simp
  obtain ⟨c₀, hc₀⟩ := DiscreteGroups.sglob.DzType.exists_hasConductor_of_continuous_ne_one Ψ hcont hne
  obtain ⟨d, hd⟩ := psiInv_exists_zpow E ϖ hϖ c₀
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have hR0 : algebraMap k E r ≠ 0 := by simpa using hr0
  have hR1 : valuation E (algebraMap k E r) < 1 := by
    have := (hle 1 r).not
    simp only [map_one, not_le] at this
    exact this.1 hr1
  obtain ⟨e, he⟩ := psiInv_exists_zpow E ϖ hϖ (Units.mk0 _ hR0)
  rw [Units.val_mk0] at he
  have hϖ0 : 0 < valuation E (ϖ : E) := by simp [zero_lt_iff]
  have hϖ1 : valuation E (ϖ : E) < 1 := hϖ ▸ uniformizer_lt_one
  have he0 : 0 < e := by
    rw [he] at hR1
    exact (zpow_lt_one_iff_right_of_lt_one₀ hϖ0 hϖ1).1 hR1
  refine ⟨-d, fun a₀ => ⟨e * |a₀|, ?_, Ψ.mulShift (algebraMap k E (r ^ (-(2 * |a₀|)))), ?_, ?_⟩⟩
  · have := le_abs_self a₀
    have := abs_nonneg a₀
    nlinarith
  · refine psiInv_shift hc₀ _ (by simp [zpow_ne_zero, hr0]) ?_
    rw [hd, map_zpow₀, map_zpow₀, he, Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_mul, ← zpow_add₀ hϖ0.ne']
    congr 1
    ring
  · intro σ x
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply, hΨ, hΨ, ← σ.commutes, ← map_mul, σ.commutes,
      Algebra.trace_eq_of_algEquiv]
