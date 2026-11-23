import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRationalStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.FourierComplete

open scoped Pointwise

section Gen

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem exists_descent (Λ : AddSubgroup V) (f : V → ℂ) (hf : Continuous f)
    (hp : ∀ x, ∀ l ∈ Λ, f (x + l) = f x) :
    ∃ h : C(V ⧸ Λ, ℂ), ∀ x, h (QuotientAddGroup.mk x) = f x := by
  let p : C(V, V ⧸ Λ) := ⟨QuotientAddGroup.mk, continuous_quotient_mk'⟩
  have hq : Topology.IsQuotientMap p := QuotientAddGroup.isQuotientMap_mk Λ
  have hfac : Function.FactorsThrough (⟨f, hf⟩ : C(V, ℂ)) p := by
    intro a b hab
    have h1 : -a + b ∈ Λ := QuotientAddGroup.eq.1 hab
    have h2 := hp a _ h1
    simpa using h2.symm
  refine ⟨hq.lift ⟨f, hf⟩ hfac, fun x => ?_⟩
  exact DFunLike.congr_fun (hq.lift_comp ⟨f, hf⟩ hfac) x

theorem compactSpace_quotient (Λ : AddSubgroup V) {K : Set V} (hK : IsCompact K)
    (hc : ∀ x, ∃ l ∈ Λ, x - l ∈ K) : CompactSpace (V ⧸ Λ) := by
  refine ⟨?_⟩
  have himg : (QuotientAddGroup.mk '' K : Set (V ⧸ Λ)) = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨l, hl, hx⟩ := hc x
    refine ⟨x - l, hx, ?_⟩
    rw [QuotientAddGroup.eq]
    have h1 : -(x - l) + x = l := by abel
    rwa [h1]
  rw [← himg]
  exact hK.image continuous_quotient_mk'

theorem mem_closure_span {X : Type*} [TopologicalSpace X] [CompactSpace X] {T : Type*} [AddCommGroup T]
    (c : T → C(X, ℂ)) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hstar : ∀ t, star (c t) = c (-t)) (hsep : ∀ x y, x ≠ y → ∃ t, c t x ≠ c t y) (f : C(X, ℂ)) :
    f ∈ closure ((Submodule.span ℂ (Set.range c) : Submodule ℂ C(X, ℂ)) : Set C(X, ℂ)) := by
  set S : Submodule ℂ C(X, ℂ) := Submodule.span ℂ (Set.range c) with hS
  have hcS : ∀ t, c t ∈ S := fun t => Submodule.subset_span ⟨t, rfl⟩
  have h1 : (1 : C(X, ℂ)) ∈ S := h0 ▸ hcS 0
  have hmul : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S := by
    intro x y hx hy
    have hle : S * S ≤ S := by
      rw [hS, Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
      show c s * c t ∈ _
      rw [← hadd]
      exact hcS _
    exact hle (Submodule.mul_mem_mul hx hy)
  have hst : ∀ x ∈ S, star x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => obtain ⟨t, rfl⟩ := h; rw [hstar]; exact hcS _
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  let A : StarSubalgebra ℂ C(X, ℂ) :=
    { toSubalgebra := S.toSubalgebra h1 hmul, star_mem' := fun {a} ha => hst a ha }
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨t, ht⟩ := hsep x y hxy
    exact ⟨c t, ⟨c t, hcS t, rfl⟩, ht⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  have hf : f ∈ (A.topologicalClosure : Set C(X, ℂ)) := by
    rw [htop]
    trivial
  rwa [StarSubalgebra.topologicalClosure_coe] at hf

theorem eq_zero_of_coeffs_vanish [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (Λ : AddSubgroup V) [Countable Λ] (μ : Measure V) [μ.IsAddHaarMeasure] {D : Set V}
    (hD : IsAddFundamentalDomain Λ D μ) {K : Set V} (hK : IsCompact K)
    (hc : ∀ x, ∃ l ∈ Λ, x - l ∈ K) {T : Type*} [AddCommGroup T] (χ : T → V → ℂ)
    (hχc : ∀ t, Continuous (χ t)) (hχp : ∀ t x, ∀ l ∈ Λ, χ t (x + l) = χ t x)
    (h0 : ∀ x, χ 0 x = 1) (hadd : ∀ s t x, χ (s + t) x = χ s x * χ t x)
    (hconj : ∀ t x, star (χ t x) = χ (-t) x)
    (hsep : ∀ x y, (∀ t, χ t x = χ t y) → -x + y ∈ Λ)
    (g : V → ℂ) (hg : Continuous g) (hgp : ∀ x, ∀ l ∈ Λ, g (x + l) = g x)
    (hF : ∀ t, ∫ b in D, g b * χ (-t) b ∂μ = 0) (x : V) : g x = 0 := by
  haveI : CompactSpace (V ⧸ Λ) := compactSpace_quotient Λ hK hc
  choose c hcχ using fun t => exists_descent Λ (χ t) (hχc t) (hχp t)
  obtain ⟨gb, hgb⟩ := exists_descent Λ g hg hgp
  have hext : ∀ a b : C(V ⧸ Λ, ℂ),
      (∀ x : V, a (QuotientAddGroup.mk x) = b (QuotientAddGroup.mk x)) → a = b := by
    intro a b h
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h x
  have hc0 : c 0 = 1 := hext _ _ fun x => by
    rw [hcχ, h0]; rfl
  have hcadd : ∀ s t, c (s + t) = c s * c t := fun s t => hext _ _ fun x => by
    rw [hcχ, hadd, ContinuousMap.mul_apply, hcχ, hcχ]
  have hcstar : ∀ t, star (c t) = c (-t) := fun t => hext _ _ fun x => by
    rw [ContinuousMap.star_apply, hcχ, hcχ, hconj]
  have hsepc : ∀ p q : V ⧸ Λ, p ≠ q → ∃ t, c t p ≠ c t q := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    by_contra hcon
    push Not at hcon
    apply hpq
    rw [QuotientAddGroup.eq]
    exact hsep a b fun t => by simpa [hcχ] using hcon t
  have hfin : μ D < ⊤ := Formalism.IndefR.Tow.fd_measure_lt_top hD hK (fun y => by
    obtain ⟨l, hl, hy⟩ := hc y
    refine ⟨-l, Λ.neg_mem hl, ?_⟩
    have h1 : -l + y = y - l := by abel
    rwa [h1])
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using hfin⟩
  let L : C(V ⧸ Λ, ℂ) → ℂ := fun s => ∫ b in D, g b * s (QuotientAddGroup.mk b) ∂μ
  have hbd : ∀ (s : C(V ⧸ Λ, ℂ)) (b : V), ‖g b * s (QuotientAddGroup.mk b)‖ ≤ ‖gb‖ * ‖s‖ := by
    intro s b
    rw [norm_mul, ← hgb b]
    exact mul_le_mul (gb.norm_coe_le_norm _) (s.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  have hint : ∀ s : C(V ⧸ Λ, ℂ),
      Integrable (fun b => g b * s (QuotientAddGroup.mk b)) (μ.restrict D) := by
    intro s
    have hcont : Continuous fun b => g b * s (QuotientAddGroup.mk b) :=
      hg.mul (s.continuous.comp continuous_quotient_mk')
    exact Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ * ‖s‖) (ae_of_all _ (hbd s))
  have hLc : Continuous L := by
    have hl : LipschitzWith (Real.toNNReal (‖gb‖ * (μ.restrict D).real Set.univ)) L := by
      refine LipschitzWith.of_dist_le' fun s s' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : L s - L s' = ∫ b in D, g b * (s - s') (QuotientAddGroup.mk b) ∂μ := by
        show (∫ b in D, _ ∂μ) - (∫ b in D, _ ∂μ) = _
        rw [← integral_sub (hint s) (hint s')]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp [mul_sub]
      rw [h1]
      have h2 := norm_integral_le_of_norm_le_const (μ := μ.restrict D)
        (ae_of_all _ (hbd (s - s')))
      calc _ ≤ _ := h2
        _ = _ := by ring
    exact hl.continuous
  have hz : ∀ s ∈ Submodule.span ℂ (Set.range c), L s = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem s h =>
      obtain ⟨t, rfl⟩ := h
      have h1 := hF (-t)
      rw [neg_neg] at h1
      show ∫ b in D, g b * c t (QuotientAddGroup.mk b) ∂μ = 0
      simpa only [hcχ] using h1
    | zero => simp [L]
    | add s s' _ _ hs hs' =>
      have h1 : L (s + s') = L s + L s' := by
        show _ = (∫ b in D, _ ∂μ) + (∫ b in D, _ ∂μ)
        rw [← integral_add (hint s) (hint s')]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp [mul_add]
      rw [h1, hs, hs', add_zero]
    | smul a s _ hs =>
      have h1 : L (a • s) = a * L s := by
        show _ = a * ∫ b in D, _ ∂μ
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [h1, hs, mul_zero]
  have hL0 : L (star gb) = 0 := by
    have hsub : ((Submodule.span ℂ (Set.range c) : Submodule ℂ C(V ⧸ Λ, ℂ)) : Set C(V ⧸ Λ, ℂ)) ⊆
        {s | L s = 0} := fun s hs => hz s hs
    exact closure_minimal hsub (isClosed_eq hLc continuous_const)
      (mem_closure_span c hc0 hcadd hcstar hsepc (star gb))
  have hpt : ∀ b, g b * (star gb) (QuotientAddGroup.mk b) = ((‖g b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [ContinuousMap.star_apply, hgb]
    simpa using Complex.mul_conj' (g b)
  have hR : ∫ b in D, ‖g b‖ ^ 2 ∂μ = 0 := by
    have h1 : ((∫ b in D, ‖g b‖ ^ 2 ∂μ : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal, ← hL0]
      exact integral_congr_ae (ae_of_all _ fun b => (hpt b).symm)
    exact_mod_cast h1
  have hRint : Integrable (fun b => ‖g b‖ ^ 2) (μ.restrict D) := by
    have hcont : Continuous fun b => ‖g b‖ ^ 2 := hg.norm.pow 2
    refine Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ ^ 2) (ae_of_all _ fun b => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← hgb b]
    exact pow_le_pow_left₀ (norm_nonneg _) (gb.norm_coe_le_norm _) 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun b => by positivity) hRint).1 hR
  let Z : Set V := {y | g y ≠ 0}
  have hZo : IsOpen Z := isOpen_ne_fun hg continuous_const
  have hZD : μ (Z ∩ D) = 0 := by
    rw [← Measure.restrict_apply hZo.measurableSet]
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
    have hy' : g y ≠ 0 := hy
    simpa using hy'
  have hZinv : ∀ l : Λ, l +ᵥ Z = Z := by
    intro l
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have h1 : g (-l +ᵥ y) = g y := by
      have h2 := hgp y (-(l : V)) (Λ.neg_mem l.2)
      rw [← h2, add_comm]
      rfl
    show g (-l +ᵥ y) ≠ 0 ↔ g y ≠ 0
    rw [h1]
  have hZ0 := hD.measure_zero_of_invariant Z hZinv hZD
  have hZe : Z = ∅ := (hZo.measure_eq_zero_iff μ).1 hZ0
  by_contra hx
  have hxZ : x ∈ Z := hx
  rw [hZe] at hxZ
  exact hxZ

end Gen

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

end GlobalTheory.CompanionTheory.FourierComplete
