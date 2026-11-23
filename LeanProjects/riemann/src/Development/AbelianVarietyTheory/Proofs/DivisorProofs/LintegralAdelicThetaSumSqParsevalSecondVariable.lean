import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Pointwise
namespace GlobalTheory.ThetaParsevalInner

theorem setIntegral_eq_zero_of_twist {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddLeftInvariant] (G : AddSubgroup V) [Countable G]
    {s : Set V} (hs : IsAddFundamentalDomain G s μ) {h : V → ℂ} (hper : ∀ g ∈ G, ∀ y, h (g + y) = h y)
    {c : V} {a : ℂ} (hc : ∀ y, h (c + y) = a * h y) (ha : a ≠ 1) : ∫ y in s, h y ∂μ = 0 := by
  have ht : IsAddFundamentalDomain G (c +ᵥ s) μ := hs.vadd_of_comm c
  have e1 : ∫ y in s, h y ∂μ = ∫ y in c +ᵥ s, h y ∂μ := hs.setIntegral_eq ht (fun g y => hper g g.2 y)
  have e2 : ∫ y in c +ᵥ s, h y ∂μ = ∫ y in s, h (c + y) ∂μ := by
    have := (measurePreserving_add_left μ c).setIntegral_preimage_emb (measurableEmbedding_addLeft c) h (c +ᵥ s)
    rw [← this]
    congr 2
    ext y
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e3 : ∫ y in s, h (c + y) ∂μ = a * ∫ y in s, h y ∂μ := by
    simp_rw [hc]
    exact integral_const_mul a _
  have : (1 - a) * ∫ y in s, h y ∂μ = 0 := by rw [sub_mul, one_mul, ← e3, ← e2, ← e1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem lintegral_thetaSum_schr_sq : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
      μ 𝓕₁ ≠ ⊤ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ x : (κ → AF F),
      ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
        μ 𝓕₁ * ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 := by
  intro F _ _ ψ hψ κ _ μ hμ 𝓕₁ hF hfin Φ hΦ x
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : Countable F := countable_numberField F
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  haveI := hμ
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hψ
  obtain ⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (κ → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (κ → AF F) → ℂ, g = fun y => ∑' ξ, a ξ * e ξ y := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have he_norm : ∀ ξ y, ‖e ξ y‖ = 1 := fun ξ y => by rw [he]; exact hnorm _
  have he_cont : ∀ ξ, Continuous (e ξ) := fun ξ => by
    rw [he]; exact hcont.comp (continuous_const.dotProduct continuous_id)
  have hconj : ∀ t, (starRingEnd ℂ) (ψ t) = ψ (-t) := fun t => by
    have h1 : ψ t * (starRingEnd ℂ) (ψ t) = 1 := by rw [Complex.mul_conj', hnorm]; simp
    have h2 : ψ t * ψ (-t) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    have h0 : ψ t ≠ 0 := fun h => by simpa [h] using hnorm t
    exact mul_left_cancel₀ h0 (h1.trans h2.symm)
  have hemb_sub : ∀ ξ η, emb (ξ - η) = emb ξ - emb η := by
    intro ξ η; rw [hemb]; funext i; simp [map_sub]
  have he_sub : ∀ ξ η y, e (ξ - η) y = e ξ y * (starRingEnd ℂ) (e η y) := by
    intro ξ η y
    simp only [he]
    rw [hconj, hemb_sub, sub_dotProduct, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsum_e : ∀ y, Summable fun ξ => ‖a ξ * e ξ y‖ := fun y => by simpa [norm_mul, he_norm] using hsum
  have hg_bd : ∀ y, ‖g y‖ ≤ ∑' ξ, ‖a ξ‖ := fun y => by
    rw [hg]
    refine (norm_tsum_le_tsum_norm (hsum_e y)).trans (le_of_eq ?_)
    congr 1; funext ξ; rw [norm_mul, he_norm, mul_one]
  have hg_cont : Continuous g := by
    rw [hg]
    exact continuous_tsum (fun ξ => continuous_const.mul (he_cont ξ)) hsum
      (fun ξ y => by rw [norm_mul, he_norm, mul_one])
  have h1 : ∀ y, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ = ‖g y‖ₑ := by
    intro y
    have : GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ) = ψ (⅟2 * (x ⬝ᵥ y)) * g y := by
      rw [hg, ← tsum_mul_left]
      unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
      congr 1; funext ξ
      subst ha he hemb
      simp only [AddChar.map_add_eq_mul]; ring
    rw [this, enorm_mul, ← ofReal_norm_eq_enorm (ψ _), hnorm, ENNReal.ofReal_one, one_mul]
  have hgsq_int : Integrable (fun y => ‖g y‖ ^ 2) (μ.restrict 𝓕₁) :=
    Integrable.of_bound (hg_cont.norm.pow 2).aestronglyMeasurable ((∑' ξ, ‖a ξ‖) ^ 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hg_bd y) 2)
  have lhs : ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgsq_int (ae_of_all _ fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [h1, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hcomp : ∀ y, ((‖g y‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : (κ → F) × (κ → F), a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y := by
    intro y
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [hg]
    rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm (hsum_e y) (by simpa [norm_mul, he_norm] using hsum)]
    congr 1; funext p
    rw [he_sub, map_mul]; ring
  have hFint : ∀ p : (κ → F) × (κ → F),
      Integrable (fun y => a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y) (μ.restrict 𝓕₁) := fun p =>
    (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _
  have hnormint : ∀ p : (κ → F) × (κ → F),
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ = ‖a p.1‖ * ‖a p.2‖ * μ.real 𝓕₁ := by
    intro p
    simp only [norm_mul, he_norm, RCLike.norm_conj, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun p : (κ → F) × (κ → F) =>
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ := by
    simp_rw [hnormint]
    exact (hsum.mul_of_nonneg hsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right _
  have horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ y, e 0 y = 1 := fun y => by simp [he, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push_neg at h; exact hζ (funext h)
      haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
        refine Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_
        · exact (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩
        · rintro ⟨r, hr⟩
          obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
          exact ⟨ρ, by subst hemb; rfl⟩
      refine setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_
        (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0
      · intro r hr y
        obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        rw [show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by
          subst hemb; simp [dotProduct, map_sum, map_mul], htriv, one_mul]
      · intro y
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  have hFval : ∀ p : (κ → F) × (κ → F), ∫ y in 𝓕₁, a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y ∂μ =
      if p.1 = p.2 then ((‖a p.1‖ ^ 2 * μ.real 𝓕₁ : ℝ) : ℂ) else 0 := by
    intro p
    rw [integral_const_mul, horth]
    by_cases h : p.1 = p.2
    · rw [if_pos (sub_eq_zero.mpr h), if_pos h, h, Complex.mul_conj']; push_cast; ring
    · rw [if_neg (sub_ne_zero.mpr h), if_neg h, mul_zero]
  have hI : ∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ = (∑' ξ, ‖a ξ‖ ^ 2) * μ.real 𝓕₁ := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp_rw [hcomp]
    rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
    simp_rw [hFval]
    have hinj : Function.Injective (fun ξ : κ → F => (ξ, ξ)) := fun _ _ h => (Prod.ext_iff.1 h).1
    rw [← hinj.tsum_eq]
    · simp only [if_true]
      rw [← tsum_mul_right, Complex.ofReal_tsum]
    · intro p hp
      by_cases h : p.1 = p.2
      · exact ⟨p.1, Prod.ext rfl h⟩
      · exact absurd (if_neg h) hp
  have hsq : Summable fun ξ => ‖a ξ‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun ξ => by
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hsum.le_tsum ξ (fun _ _ => norm_nonneg _)) (norm_nonneg _))
      (hsum.mul_left (∑' ξ, ‖a ξ‖))
  rw [lhs, hI, ENNReal.ofReal_mul (tsum_nonneg fun _ => sq_nonneg _), ofReal_measureReal hfin, mul_comm,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsq]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, ha, hemb]

end GlobalTheory.ThetaParsevalInner
