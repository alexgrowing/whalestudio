import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrigPolynomialIndicatorAwayFromPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothBumpWithTrigonometricExpansionStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.OffVLocalWeights

theorem sq_lintegral_lt_top : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ < ⊤ := by
  intro F _ _ κ _ Φ hΦ μ hμ
  letI : MeasurableSpace (κ → AF F) := borel _
  have h := (GlobalTheory.WeilM.schA_memLp_two F κ μ hμ Φ hΦ).integrable_norm_pow two_ne_zero
  have h2 := h.2
  simp only [HasFiniteIntegral, enorm_pow, enorm_norm] at h2
  exact h2

theorem continuous_and_compact_finite_support : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    Continuous Φ ∧ ∃ K : Set (κ → Af F), IsCompact K ∧ ∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ K := by
  intro F _ _ κ _ Φ hΦ
  let j : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hd := GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (GlobalTheory.RestrSchA.mem_schA_comp_extend F j j.injective Φ hΦ)
  have e : ∀ x : κ → AF F, Φ x = Φ (Function.extend j (x ∘ j) 0) := fun x => by
    congr 1
    funext i
    obtain ⟨k, rfl⟩ := j.surjective i
    rw [j.injective.extend_apply]
    rfl
  have hr : Continuous (fun x : κ → AF F => x ∘ j) := continuous_pi fun i => continuous_apply _
  obtain ⟨hc, ⟨K, hK, hK0⟩, -⟩ := hd
  refine ⟨?_, (fun u : Fin (Fintype.card κ) → Af F => u ∘ j.symm) '' K,
    hK.image (continuous_pi fun i => continuous_apply _), fun x hx => ?_⟩
  · have : Φ = (fun y => Φ (Function.extend j y 0)) ∘ (fun x : κ → AF F => x ∘ j) := funext e
    rw [this]
    exact hc.comp hr
  · refine ⟨GlobalTheory.SWQ.fin (x ∘ j), ?_, ?_⟩
    · by_contra h
      exact hx ((e x).trans (hK0 _ h))
    · funext i
      simp only [GlobalTheory.SWQ.fin, Function.comp_apply, Equiv.apply_symm_apply]
      rfl

theorem exists_box_nhds : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (O : Set (κ → AF F)) (y : κ → AF F),
    IsOpen O → y ∈ O → ∃ (U : Set (κ → Ainf F)) (V : Set (κ → Af F)), IsOpen U ∧ IsOpen V ∧
      (fun i => (y i).1) ∈ U ∧ (fun i => (y i).2) ∈ V ∧
      ∀ x : κ → AF F, (fun i => (x i).1) ∈ U → (fun i => (x i).2) ∈ V → x ∈ O := by
  intro F _ _ κ _ O y hO hy
  have hp : Continuous (fun q : (κ → Ainf F) × (κ → Af F) => (fun i => ((q.1 i, q.2 i) : AF F))) :=
    continuous_pi fun i => ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  obtain ⟨U, V, hU, hV, hyU, hyV, hUV⟩ :=
    isOpen_prod_iff.1 (hO.preimage hp) (fun i => (y i).1) (fun i => (y i).2) (by exact hy)
  exact ⟨U, V, hU, hV, hyU, hyV, fun x hx1 hx2 => hUV (Set.mk_mem_prod hx1 hx2)⟩

theorem exists_finite_indicator_poly : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ K : Set (κ → Af F), IsCompact K → ∀ (y : κ → AF F) (V : Set (κ → Af F)), IsOpen V → (fun i => (y i).2) ∈ V →
    ∃ (A : Set (κ → Af F)) (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ),
      IsOpen A ∧ (fun i => (y i).2) ∈ A ∧ (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
      (∀ x z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z →
        ((fun i => ((x + z) i).2) ∈ A ↔ (fun i => (x i).2) ∈ A)) ∧
      (∀ x : κ → AF F, (fun i => (x i).2) ∈ A →
        (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) ∈ V) ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ K →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = A.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2) := by
  first | exact @GlobalTheory.T.exists_trigPolynomial_indicator_awayFromPlace | exact GlobalTheory.T.exists_trigPolynomial_indicator_awayFromPlace

theorem exists_arch_bump_poly : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.T.archimedean_smooth_bump_with_trigonometric_expansion | exact GlobalTheory.T.archimedean_smooth_bump_with_trigonometric_expansion

theorem exists_trig_prod : ∀ {X B : Type} [AddCommMonoid B] [DecidableEq B] (χ : B → X → ℂ),
    (∀ b b' x, χ (b + b') x = χ b x * χ b' x) → ∀ (s₁ s₂ : Finset B) (c₁ c₂ : B → ℂ),
    ∃ (s : Finset B) (c : B → ℂ), (∀ b ∈ s, ∃ b₁ ∈ s₁, ∃ b₂ ∈ s₂, b = b₁ + b₂) ∧
      ∀ x, ∑ b ∈ s, c b * χ b x = (∑ b ∈ s₁, c₁ b * χ b x) * (∑ b ∈ s₂, c₂ b * χ b x) := by
  intro X B _ _ χ hχ s₁ s₂ c₁ c₂
  refine ⟨Finset.image (fun p : B × B => p.1 + p.2) (s₁ ×ˢ s₂),
    fun b => ∑ p ∈ (s₁ ×ˢ s₂).filter (fun p => p.1 + p.2 = b), c₁ p.1 * c₂ p.2, ?_, ?_⟩
  · intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    exact ⟨p.1, h1, p.2, h2, rfl⟩
  · intro x
    have hb : ∀ b, (∑ p ∈ (s₁ ×ˢ s₂).filter (fun p => p.1 + p.2 = b), c₁ p.1 * c₂ p.2) * χ b x =
        ∑ p ∈ (s₁ ×ˢ s₂).filter (fun p => p.1 + p.2 = b), c₁ p.1 * c₂ p.2 * χ (p.1 + p.2) x := by
      intro b
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2]
    simp_rw [hb]
    rw [Finset.sum_fiberwise_of_maps_to (g := fun p : B × B => p.1 + p.2)
      (fun p hp => Finset.mem_image_of_mem _ hp), Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hχ]
    ring

theorem lintegral_weight_eq_of_approx : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (f g h : X → ENNReal) (m : ℕ → X → ℂ) (C : ℝ),
    Measurable f → Measurable g → (∀ n, Measurable (m n)) → ∫⁻ x, f x ∂μ < ⊤ → ∫⁻ x, g x ∂μ < ⊤ →
    (∀ n, ∫⁻ x, ‖m n x‖ₑ ^ 2 * f x ∂μ = ∫⁻ x, ‖m n x‖ₑ ^ 2 * g x ∂μ) →
    (∀ n x, (f x ≠ 0 ∨ g x ≠ 0) → ‖m n x‖ ≤ C) →
    (∀ x, (f x ≠ 0 ∨ g x ≠ 0) → Filter.Tendsto (fun n => ‖m n x‖ₑ ^ 2) Filter.atTop (nhds (h x))) →
    ∫⁻ x, h x * f x ∂μ = ∫⁻ x, h x * g x ∂μ := by
  intro X _ μ f g h m C hf hg hm hfi hgi heq hb hlim
  have key : ∀ u : X → ENNReal, Measurable u → ∫⁻ x, u x ∂μ < ⊤ → (∀ x, u x ≠ 0 → (f x ≠ 0 ∨ g x ≠ 0)) →
      Filter.Tendsto (fun n => ∫⁻ x, ‖m n x‖ₑ ^ 2 * u x ∂μ) Filter.atTop (nhds (∫⁻ x, h x * u x ∂μ)) := by
    intro u hu hui hsupp
    refine tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal C ^ 2 * u x)
      (fun n => ((hm n).enorm.pow_const 2).mul hu) (fun n => Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · by_cases hx : u x = 0
      · simp [hx]
      · have h1 : ‖m n x‖ₑ ≤ ENNReal.ofReal C := by
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (hb n x (hsupp x hx))
        show ‖m n x‖ₑ ^ 2 * u x ≤ ENNReal.ofReal C ^ 2 * u x
        gcongr
    · rw [lintegral_const_mul _ hu]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hui.ne
    · filter_upwards [ae_lt_top hu hui.ne] with x hx
      by_cases h0 : u x = 0
      · simp [h0]
      · exact ENNReal.Tendsto.mul_const (hlim x (hsupp x h0)) (Or.inr hx.ne)
  exact tendsto_nhds_unique ((key f hf hfi fun x hx => Or.inl hx).congr fun n => heq n)
    (key g hg hgi fun x hx => Or.inr hx)

theorem liftV_mul_fst {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (a : AF F) :
    (GlobalTheory.LatVac.liftV v 1 * a).1 = 0 := by
  change (0 : Ainf F) * a.1 = 0
  exact zero_mul _

theorem exists_localizing_weight : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
    (∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ) →
    ∀ (y : κ → AF F) (O : Set (κ → AF F)), IsOpen O → y ∈ O →
    ∃ h : (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, GlobalTheory.LatVac.liftV v 1 • z = z → h (x + z) = h x) ∧
      (∀ x, h x ≠ 0 → x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x) ∈ O) ∧
      (∃ O' : Set (κ → AF F), IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ v ψ hψ hnt μ hμ Φ hΦ Ψ hΨ hyp y O hO hyO
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨hΦc, KΦ, hKΦ, hΦK⟩ := continuous_and_compact_finite_support Φ hΦ
  obtain ⟨hΨc, KΨ, hKΨ, hΨK⟩ := continuous_and_compact_finite_support Ψ hΨ
  obtain ⟨U, V, hU, hV, hyU, hyV, hbox⟩ := exists_box_nhds O y hO hyO
  obtain ⟨A, sf, cf, hA, hyA, hsf, hAinv, hAV, hfK⟩ :=
    exists_finite_indicator_poly v ψ hψ hnt (KΦ ∪ KΨ) (hKΦ.union hKΨ) y V hV hyV
  obtain ⟨β, hβc, hβ01, hβy, hβU, sa, ca, C, hsa, hCb, hlim⟩ := exists_arch_bump_poly ψ hψ U y hU hyU
  have hmul : ∀ (b b' : κ → AF F) (x : κ → AF F), ψ (x ⬝ᵥ (b + b')) = ψ (x ⬝ᵥ b) * ψ (x ⬝ᵥ b') :=
    fun b b' x => by rw [dotProduct_add, AddChar.map_add_eq_mul]
  choose s c hs hsc using fun n => exists_trig_prod (fun b x => ψ (x ⬝ᵥ b)) hmul sf (sa n) cf (ca n)
  have hfinc : Continuous (fun x : κ → AF F => fun i => (x i).2) :=
    continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  have hinfc : Continuous (fun x : κ → AF F => fun i => (x i).1) :=
    continuous_pi fun i => continuous_fst.comp (continuous_apply i)
  have hgc : Continuous (fun x : κ → AF F => ‖((β (fun i => (x i).1) : ℝ) : ℂ)‖ₑ ^ 2) :=
    (ENNReal.continuous_pow 2).comp (continuous_enorm.comp (Complex.continuous_ofReal.comp (hβc.comp hinfc)))
  have hz1 : ∀ z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z → ∀ i, (z i).1 = 0 := by
    intro z hz i
    have := congrArg Prod.fst (congrFun hz i)
    rw [← this]
    exact liftV_mul_fst v (z i)
  have hβle : ∀ u, ‖((β u : ℝ) : ℂ)‖ₑ ^ 2 ≤ 1 := by
    intro u
    refine pow_le_one₀ zero_le' ?_
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ01 u).1]
    exact ENNReal.ofReal_le_one.2 (hβ01 u).2
  refine ⟨fun x => if (fun i => (x i).2) ∈ A then ‖((β (fun i => (x i).1) : ℝ) : ℂ)‖ₑ ^ 2 else 0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Measurable.ite (p := {x : κ → AF F | (fun i => (x i).2) ∈ A})
      (hA.preimage hfinc).measurableSet hgc.measurable measurable_const
  · intro x
    dsimp only
    split_ifs
    · exact hβle _
    · exact zero_le'
  · intro x z hz
    dsimp only
    have h1 : (fun i => ((x + z) i).1) = fun i => (x i).1 := by
      funext i
      change (x i).1 + (z i).1 = (x i).1
      rw [hz1 z hz i, add_zero]
    simp only [hAinv x z hz, h1]
  · intro x hx
    dsimp only at hx
    by_cases hxA : (fun i => (x i).2) ∈ A
    · rw [if_pos hxA] at hx
      have hβ0 : β (fun i => (x i).1) ≠ 0 := by
        intro h0
        rw [h0] at hx
        simp at hx
      apply hbox
      · have h1 : (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).1) =
            fun i => (x i).1 := by
          funext i
          change (x i).1 + ((GlobalTheory.LatVac.liftV v 1 * y i).1 - (GlobalTheory.LatVac.liftV v 1 * x i).1) = (x i).1
          rw [liftV_mul_fst, liftV_mul_fst, sub_zero, add_zero]
        rw [h1]
        exact hβU _ hβ0
      · exact hAV x hxA
    · rw [if_neg hxA] at hx
      exact absurd rfl hx
  · refine ⟨{x | (fun i => (x i).2) ∈ A} ∩ {x | 1 / 2 < ‖((β (fun i => (x i).1) : ℝ) : ℂ)‖ₑ ^ 2},
      (hA.preimage hfinc).inter (isOpen_lt continuous_const hgc), ⟨hyA, ?_⟩, ?_⟩
    · show 1 / 2 < ‖((β (fun i => (y i).1) : ℝ) : ℂ)‖ₑ ^ 2
      rw [hβy]
      simpa using ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top
    · rintro x ⟨hxA, hx⟩ -
      show 1 / 2 ≤ (if (fun i => (x i).2) ∈ A then ‖((β (fun i => (x i).1) : ℝ) : ℂ)‖ₑ ^ 2 else 0)
      rw [if_pos (show (fun i => (x i).2) ∈ A from hxA)]
      exact le_of_lt hx
  · have hK : ∀ x : κ → AF F, (‖Ψ x‖ₑ ^ 2 ≠ 0 ∨ ‖Φ x‖ₑ ^ 2 ≠ 0) → (fun i => (x i).2) ∈ KΦ ∪ KΨ := by
      intro x hx
      rcases hx with hx | hx
      · refine Or.inr (hΨK x fun h0 => hx ?_)
        rw [h0]; simp
      · refine Or.inl (hΦK x fun h0 => hx ?_)
        rw [h0]; simp
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCb 0 0)
    refine lintegral_weight_eq_of_approx μ (fun x => ‖Ψ x‖ₑ ^ 2) (fun x => ‖Φ x‖ₑ ^ 2) _ (fun n x => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) C
      (hΨc.measurable.enorm.pow_const 2) (hΦc.measurable.enorm.pow_const 2) ?_ (sq_lintegral_lt_top Ψ hΨ μ hμ) (sq_lintegral_lt_top Φ hΦ μ hμ)
      ?_ ?_ ?_
    · intro n
      refine Continuous.measurable (continuous_finset_sum _ fun b _ => continuous_const.mul (hψ.1.comp ?_))
      exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
    · intro n
      have hoff : ∀ b ∈ s n, GlobalTheory.LatVac.liftV v 1 • b = 0 := by
        intro b hb
        obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hs n b hb
        rw [smul_add, hsf b₁ hb₁, hsa n b₂ hb₂ v, add_zero]
      have := hyp (s n) (c n) hoff
      simp only [enorm_mul, mul_pow] at this
      exact this
    · intro n x hx
      rw [hsc n x, hfK x (hK x hx)]
      by_cases hxA : (fun i => (x i).2) ∈ A
      · rw [Set.indicator_of_mem hxA, one_mul]
        exact hCb n x
      · rw [Set.indicator_of_notMem hxA, zero_mul, norm_zero]
        exact hC0
    · intro x hx
      simp only [hsc _ x, hfK x (hK x hx)]
      by_cases hxA : (fun i => (x i).2) ∈ A
      · simp only [Set.indicator_of_mem hxA, one_mul, if_pos hxA]
        exact ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp (hlim x))
      · simp only [Set.indicator_of_notMem hxA, zero_mul, if_neg hxA, enorm_zero]
        simpa using tendsto_const_nhds

end GlobalTheory.OffVLocalWeights
