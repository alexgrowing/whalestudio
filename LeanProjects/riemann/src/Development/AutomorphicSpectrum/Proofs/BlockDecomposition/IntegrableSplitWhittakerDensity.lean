import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS.DenInt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_periodic {Ψ : F × F → ℂ} (h : IsSB Ψ) :
    ∃ n : ℤ, ∀ (x y t : F), t ∈ valBall F n → Ψ (x, y + t) = Ψ (x, y) := by
  obtain ⟨hl, hc⟩ := h
  have h1 : IsLocallyConstant (Ψ ∘ fun p : (F × F) × F => (p.1.1, p.1.2 + p.2)) :=
    hl.comp_continuous (by fun_prop)
  have h2 : IsLocallyConstant (Ψ ∘ fun p : (F × F) × F => p.1) :=
    hl.comp_continuous continuous_fst
  have hopen := (h1.sub h2).isOpen_fiber 0
  obtain ⟨U, V, -, hV, hKU, h0V, hUV⟩ := generalized_tube_lemma hc.isCompact
    (isCompact_singleton (x := (0 : F))) hopen (by
      rintro ⟨p, t⟩ ⟨-, ht⟩
      have ht0 : t = 0 := ht
      subst ht0
      simp)
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp
    (hV.mem_nhds (h0V (Set.mem_singleton (0 : F))))
  have key : ∀ p ∈ tsupport Ψ, ∀ t ∈ valBall F n, Ψ (p.1, p.2 + t) = Ψ p := by
    intro p hp t ht
    have := hUV (Set.mk_mem_prod (hKU hp) (hn ht))
    simpa [sub_eq_zero] using this
  refine ⟨n, fun x y t ht => ?_⟩
  by_cases h1 : (x, y) ∈ tsupport Ψ
  · exact key _ h1 t ht
  by_cases h2 : (x, y + t) ∈ tsupport Ψ
  · have := key _ h2 (-t) (neg_mem ht)
    simpa using this.symm
  · rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem exists_bdd {Ψ : F × F → ℂ} (h : IsSB Ψ) :
    ∃ m : ℤ, ∀ x y : F, Ψ (x, y) ≠ 0 → x ∈ valBall F m ∧ y ∈ valBall F m := by
  obtain ⟨-, hc⟩ := h
  obtain ⟨k, hk⟩ := hc.isCompact.elim_directed_cover
    (fun k : ℤ => (valBall F (-k) : Set F) ×ˢ (valBall F (-k) : Set F))
    (fun k => (isOpen_valBall _).prod (isOpen_valBall _))
    (by
      rintro ⟨x, y⟩ -
      refine Set.mem_iUnion.mpr ⟨max (-ord x) (-ord y), ?_, ?_⟩
      · exact valBall_antitone (by omega) (mem_valBall_ord (x := x))
      · exact valBall_antitone (by omega) (mem_valBall_ord (x := y)))
    (fun a b => ⟨max a b,
      Set.prod_mono (valBall_antitone (by omega)) (valBall_antitone (by omega)),
      Set.prod_mono (valBall_antitone (by omega)) (valBall_antitone (by omega))⟩)
  exact ⟨-k, fun x y hxy => hk (subset_tsupport _ hxy)⟩

variable [MeasurableSpace F] [BorelSpace F]

theorem inn_eq_zero_of_lt {χ : AddChar F Circle} {Ψ : F × F → ℂ} {m : ℤ}
    (hm : ∀ x y : F, Ψ (x, y) ≠ 0 → x ∈ valBall F m) (u : Fˣ) (hu : ord (u : F) < m) :
    inn χ Ψ u = 0 := by
  have h0 : ∀ y : F, Ψ ((u : F), (u : F) * y) = 0 := by
    intro y
    by_contra hne
    have := (mem_valBall_iff_le_ord u.ne_zero).mp (hm _ _ hne)
    omega
  simp [inn, h0]

theorem inn_eq_zero_of_gt {χ : AddChar F Circle} (hχ : IsStd χ) {Ψ : F × F → ℂ} {n : ℤ}
    (hp : ∀ (x y t : F), t ∈ valBall F n → Ψ (x, y + t) = Ψ (x, y)) (u : Fˣ)
    (hu : n + 1 ≤ ord (u : F)) : inn χ Ψ u = 0 := by
  have hnot := not_isTrivialOn_addCharConductor_sub_one hχ.1 hχ.2.1
  rw [hχ.2.2] at hnot
  obtain ⟨y₀, hy₀, hne⟩ : ∃ y₀ ∈ valBall F (-1), χ y₀ ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hnot fun x hx => hcon x (by simpa using hx)
  set f : F → ℂ := fun y => Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ) with hf
  have hu' : (u : F) * (-y₀) ∈ valBall F n :=
    valBall_antitone (by omega : n ≤ ord (u : F) + -1)
      (mul_mem_valBall (mem_valBall_ord (x := (u : F))) (neg_mem hy₀))
  have ht : ∀ y, f (y + -y₀) = (χ y₀ : ℂ) * f y := by
    intro y
    simp only [hf]
    rw [mul_add, hp _ _ _ hu', neg_add, neg_neg, AddChar.map_add_eq_mul]
    push_cast
    ring
  have hI : ∫ y, f y ∂selfDualMeasure χ = (χ y₀ : ℂ) * ∫ y, f y ∂selfDualMeasure χ := by
    rw [← integral_const_mul]
    conv_lhs => rw [← integral_add_right_eq_self f (-y₀)]
    simp_rw [ht]
  have hne' : (χ y₀ : ℂ) ≠ 1 := fun h => hne (Circle.ext (by simpa using h))
  have h1 : (1 - (χ y₀ : ℂ)) * ∫ y, f y ∂selfDualMeasure χ = 0 := by linear_combination hI
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hne'.symm)

theorem continuous_inn {χ : AddChar F Circle} (hχ : Continuous χ) {Ψ : F × F → ℂ} (h : IsSB Ψ) :
    Continuous (inn χ Ψ) := by
  obtain ⟨m, hm⟩ := exists_bdd h
  have hΨ := h.1.continuous
  obtain ⟨C, hC⟩ := h.2.exists_bound_of_continuous hΨ
  rw [continuous_iff_continuousAt]
  intro u₀
  set k := ord ((u₀⁻¹ : Fˣ) : F) with hk
  have hnb : ∀ᶠ u : Fˣ in 𝓝 u₀, ((u⁻¹ : Fˣ) : F) ∈ valBall F k := by
    have hcont : Continuous fun u : Fˣ => ((u⁻¹ : Fˣ) : F) := Units.continuous_val.comp continuous_inv
    exact hcont.continuousAt.eventually_mem
      ((isOpen_valBall k).mem_nhds (mem_valBall_ord (x := ((u₀⁻¹ : Fˣ) : F))))
  have hint : Integrable ((valBall F (k + m) : Set F).indicator fun _ => C) (selfDualMeasure χ) :=
    (integrableOn_const (isCompact_valBall (k + m)).measure_lt_top.ne).integrable_indicator
      (measurableSet_valBall (k + m))
  have hcy : ∀ y : F, Continuous fun u : Fˣ => Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ) := by
    intro y
    have : Continuous fun u : Fˣ => (((u : F), (u : F) * y) : F × F) :=
      Units.continuous_val.prodMk (Units.continuous_val.mul continuous_const)
    exact (hΨ.comp this).mul continuous_const
  refine continuousAt_of_dominated (bound := (valBall F (k + m) : Set F).indicator fun _ => C)
    (Eventually.of_forall fun u => ?_) ?_ hint (ae_of_all _ fun y => (hcy y).continuousAt)
  · have hc : Continuous fun y : F => Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ) := by
      have h1 : Continuous fun y : F => (((u : F), (u : F) * y) : F × F) := by fun_prop
      have h2 : Continuous fun y : F => (χ (-y) : ℂ) :=
        continuous_subtype_val.comp (hχ.comp continuous_neg)
      exact (hΨ.comp h1).mul h2
    exact hc.aestronglyMeasurable
  · filter_upwards [hnb] with u hu
    refine ae_of_all _ fun y => ?_
    by_cases h0 : Ψ ((u : F), (u : F) * y) = 0
    · have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0, 0))
      simp only [h0, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hC0) _
    · have hy : y ∈ valBall F (k + m) := by
        have := mul_mem_valBall hu (hm _ _ h0).2
        simpa using this
      rw [Set.indicator_of_mem (by exact hy)]
      rw [norm_mul, Circle.norm_coe, mul_one]
      exact hC _

theorem continuous_den {χ : AddChar F Circle} (hχ : Continuous χ) {c₁ c₂ : Fˣ →* ℂˣ}
    (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂) {Ψ : F × F → ℂ} (h : IsSB Ψ) :
    Continuous (den χ c₁ c₂ Ψ) := by
  have e1 : Continuous fun u => ((c₁ u : ℂˣ) : ℂ) := Units.continuous_val.comp h₁.1
  have e2 : Continuous fun u => (((c₂ u)⁻¹ : ℂˣ) : ℂ) := Units.continuous_val.comp h₂.1.inv
  have e3 : Continuous fun u : Fˣ => mp u 1 := by
    have : (fun u : Fˣ => mp u 1) = fun u : Fˣ => ((modulus (u : F) : ℝ) : ℂ) := by
      funext u
      simp [mp]
    rw [this]
    exact Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  exact ((e1.mul e2).mul e3).mul (continuous_inn hχ h)

theorem isCompact_ord_between (a b : ℤ) : IsCompact {u : Fˣ | a ≤ ord (u : F) ∧ ord (u : F) ≤ b} := by
  have hA : IsCompact ((valBall F a : Set F) \ (valBall F (b + 1) : Set F)) :=
    (isCompact_valBall a).diff (isOpen_valBall (b + 1))
  have hsub : (valBall F a : Set F) \ (valBall F (b + 1) : Set F) ⊆ Set.range (Units.val : Fˣ → F) := by
    rintro x ⟨-, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (zero_mem _)
    exact ⟨Units.mk0 x hx0, rfl⟩
  have himg : Units.val '' {u : Fˣ | a ≤ ord (u : F) ∧ ord (u : F) ≤ b} =
      (valBall F a : Set F) \ (valBall F (b + 1) : Set F) := by
    rw [← Set.image_preimage_eq_of_subset hsub]
    congr 1
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      mem_valBall_iff_le_ord u.ne_zero]
    omega
  rw [isOpenEmbedding_units_val.isEmbedding.isCompact_iff, himg]
  exact hA

theorem multHaar_ord_between_ne_top (a b : ℤ) :
    multHaar F {u : Fˣ | a ≤ ord (u : F) ∧ ord (u : F) ≤ b} ≠ ⊤ := by
  have hsub : {u : Fˣ | a ≤ ord (u : F) ∧ ord (u : F) ≤ b} ⊆
      ⋃ k ∈ Finset.Icc a b, ordShell F k := by
    intro u hu
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_Icc.mpr hu)) rfl
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  exact (measure_biUnion_lt_top (Finset.finite_toSet _) fun k _ => by
    rw [multHaar_ordShell]; exact ENNReal.one_lt_top).ne

end GlobalTheory.CompanionTheory.WS.DenInt

namespace GlobalTheory.CompanionTheory.WS

open GlobalTheory.CompanionTheory.WS.DenInt in

theorem integrable_den : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle),
    IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → ∀ Ψ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Ψ →
      Integrable (GlobalTheory.CompanionTheory.WS.den χ c₁ c₂ Ψ) (multHaar F) := by
  intro F _ _ _ _ _ _ χ hχ c₁ c₂ h₁ h₂ Ψ h
  obtain ⟨m, hm⟩ := exists_bdd h
  obtain ⟨n, hn⟩ := exists_periodic h
  have hc := continuous_den hχ.1 h₁ h₂ h
  have hsupp : Function.support (den χ c₁ c₂ Ψ) ⊆
      {u : Fˣ | m ≤ ord (u : F) ∧ ord (u : F) ≤ n} := by
    intro u hu
    have hinn : inn χ Ψ u ≠ 0 := fun h0 => hu (by simp [den, h0])
    refine ⟨?_, ?_⟩
    · by_contra hlt
      exact hinn (inn_eq_zero_of_lt (fun x y hxy => (hm x y hxy).1) u (not_le.mp hlt))
    · by_contra hgt
      exact hinn (inn_eq_zero_of_gt hχ hn u (by omega))
  obtain ⟨M, hM⟩ := (isCompact_ord_between (F := F) m n).exists_bound_of_continuousOn hc.continuousOn
  refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
  exact Measure.integrableOn_of_bounded (multHaar_ord_between_ne_top m n) hc.aestronglyMeasurable
    ((ae_restrict_iff' (isCompact_ord_between m n).measurableSet).mpr (ae_of_all _ hM))

end GlobalTheory.CompanionTheory.WS
