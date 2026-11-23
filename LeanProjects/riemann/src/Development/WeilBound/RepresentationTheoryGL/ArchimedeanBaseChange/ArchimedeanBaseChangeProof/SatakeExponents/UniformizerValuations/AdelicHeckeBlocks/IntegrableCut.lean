import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousEmbInf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EllFormula2J

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical ENNReal

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Ell

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem th_mul (x y : H E a b) : E1.th (x * y) = E1.th x * E1.th y :=
  Prod.ext (map_mul (thetaA E a) x.1 y.1) (map_mul (thetaA E b) x.2 y.2)

theorem th_mem {δ : H E a b} (hδ : δ ∈ ratH E a b) : E1.th δ ∈ ratH E a b := by
  obtain ⟨γ, rfl⟩ := hδ
  refine ⟨(thetaE E a γ.1, thetaE E b γ.2), ?_⟩
  show (ratGL E a (thetaE E a γ.1), ratGL E b (thetaE E b γ.2)) =
    (thetaA E a (ratGL E a γ.1), thetaA E b (ratGL E b γ.2))
  rw [(E1.thetaBasic_holds E a).2.2 γ.1, (E1.thetaBasic_holds E b).2.2 γ.2]

theorem ker_bound (D : Dom E a b) (τ : ℝ) (φ : H E a b → ℂ) (hφ : IsTestH φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ cutSet E a τ ×ˢ cutSet E b τ, ‖kerH φ x (E1.th x)‖ ≤ M := by
  obtain ⟨-, -, C₁, hC₁, hs₁⟩ := E1.mahler_holds E a τ
  obtain ⟨-, -, C₂, hC₂, hs₂⟩ := E1.mahler_holds E b τ
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  have thc : Continuous (E1.th : H E a b → H E a b) := (E1.cntPair E a b).2.1
  let K : Set (H E a b) := (fun p : H E a b × H E a b × H E a b => p.1 * p.2.1 * (E1.th p.2.2)⁻¹) ''
    ((C₁ ×ˢ C₂) ×ˢ tsupport φ ×ˢ (C₁ ×ˢ C₂))
  have hKc : IsCompact K := ((hC₁.prod hC₂).prod (hφ.2.isCompact.prod (hC₁.prod hC₂))).image
    ((continuous_fst.mul continuous_snd.fst).mul ((thc.comp continuous_snd.snd).inv))
  have hS := E1.proper_ratH E1.ratProper_holds K hKc
  refine ⟨hS.toFinset.card * max B 0, by positivity, fun x hx => ?_⟩
  obtain ⟨_, ⟨γ₁, rfl⟩, c₁, hc₁, hx₁⟩ := hs₁ hx.1
  obtain ⟨_, ⟨γ₂, rfl⟩, c₂, hc₂, hx₂⟩ := hs₂ hx.2
  obtain ⟨δ, hδ⟩ : ∃ δ : ratH E a b, (δ : H E a b) = (ratGL E a γ₁, ratGL E b γ₂) := ⟨⟨_, (γ₁, γ₂), rfl⟩, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ratH E a b, (t : H E a b) = E1.th δ := ⟨⟨_, th_mem δ.2⟩, rfl⟩
  have hx' : x = (δ : H E a b) * (c₁, c₂) := by rw [hδ]; exact Prod.ext hx₁.symm hx₂.symm
  have h1 : ‖kerH φ x (E1.th x)‖ₑ ≤ ∑' γ : ratH E a b, ‖φ (x⁻¹ * (γ : H E a b) * E1.th x)‖ₑ :=
    (E1.kerBasic (E1.ctx E1.ratProper_holds D) φ hφ).2.2.2.2.2 x (E1.th x)
  have h2 : ∑' γ : ratH E a b, ‖φ (x⁻¹ * (γ : H E a b) * E1.th x)‖ₑ =
      ∑' γ : ratH E a b, ‖φ ((c₁, c₂)⁻¹ * (γ : H E a b) * E1.th (c₁, c₂))‖ₑ := by
    rw [← ((Equiv.mulLeft δ).trans (Equiv.mulRight t⁻¹)).tsum_eq]
    refine tsum_congr fun γ => ?_
    simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv, ht]
    rw [hx', th_mul]
    group
  have h3 : ∀ γ : ratH E a b, ‖φ ((c₁, c₂)⁻¹ * (γ : H E a b) * E1.th (c₁, c₂))‖ₑ ≤
      {γ : ratH E a b | (γ : H E a b) ∈ K}.indicator (fun _ => ENNReal.ofReal (max B 0)) γ := by
    intro γ
    by_cases hγ : (γ : H E a b) ∈ K
    · rw [Set.indicator_of_mem (show γ ∈ {γ : ratH E a b | (γ : H E a b) ∈ K} from hγ), ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hB _).trans (le_max_left _ _))
    · have h0 : φ ((c₁, c₂)⁻¹ * (γ : H E a b) * E1.th (c₁, c₂)) = 0 := by
        by_contra hne
        apply hγ
        refine ⟨((c₁, c₂), (c₁, c₂)⁻¹ * (γ : H E a b) * E1.th (c₁, c₂), (c₁, c₂)),
          ⟨⟨hc₁, hc₂⟩, subset_tsupport _ hne, ⟨hc₁, hc₂⟩⟩, ?_⟩
        simp only
        group
      rw [h0]; simp
  have h4 : ∑' γ : ratH E a b, {γ : ratH E a b | (γ : H E a b) ∈ K}.indicator (fun _ => ENNReal.ofReal (max B 0)) γ =
      hS.toFinset.card * ENNReal.ofReal (max B 0) := by
    rw [tsum_eq_sum (s := hS.toFinset) (fun γ hγ => Set.indicator_of_notMem (by simpa using hγ) _)]
    rw [Finset.sum_congr rfl (fun γ hγ => Set.indicator_of_mem ((Set.Finite.mem_toFinset hS).1 hγ) _)]
    rw [Finset.sum_const, nsmul_eq_mul]
  have h5 : ‖kerH φ x (E1.th x)‖ₑ ≤ ENNReal.ofReal (hS.toFinset.card * max B 0) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← h4]
    exact h1.trans (h2.le.trans (ENNReal.tsum_le_tsum h3))
  rw [← ofReal_norm] at h5
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h5

theorem integrable_cut (D : Dom E a b) {τ : ℝ} (hτ : 0 ≤ τ) (φ : H E a b → ℂ) (hφ : IsTestH φ) :
    Integrable (fun x : H E a b => chiT τ x.1 * chiT τ x.2 * kerTw2 φ x x) D.ν := by
  have : BorelSpace (H E a b) := ⟨rfl⟩
  obtain ⟨hcl₁, -, -⟩ := E1.mahler_holds E a τ
  obtain ⟨hcl₂, -, -⟩ := E1.mahler_holds E b τ
  have hms : MeasurableSet (cutSet E a τ ×ˢ cutSet E b τ) := (hcl₁.prod hcl₂).measurableSet
  have heq : (fun x : H E a b => chiT τ x.1 * chiT τ x.2 * kerTw2 φ x x) =
      (cutSet E a τ ×ˢ cutSet E b τ).indicator (fun x => kerH φ x (E1.th x)) := by
    funext x
    simp only [chiT, (E1.cntPair E a b).2.2]
    by_cases h1 : x.1 ∈ cutSet E a τ <;> by_cases h2 : x.2 ∈ cutSet E b τ <;>
      simp [Set.indicator, h1, h2, Set.mem_prod]
  rw [heq, integrable_indicator_iff hms]
  have hk : Continuous (Function.uncurry (kerH φ)) := (E1.kerBasic (E1.ctx E1.ratProper_holds D) φ hφ).2.1
  have hc₀ : Continuous fun x : H E a b => Function.uncurry (kerH φ) (x, E1.th x) :=
    hk.comp (Continuous.prodMk continuous_id (E1.cntPair E a b).2.1)
  have hc : Continuous fun x : H E a b => kerH φ x (E1.th x) := by
    simpa only [Function.uncurry_apply_pair] using hc₀
  obtain ⟨M, -, hM⟩ := ker_bound D τ φ hφ
  have hfin : D.ν (cutSet E a τ ×ˢ cutSet E b τ) ≠ ⊤ := by
    obtain ⟨C, N, -, hC⟩ := E1.cutCount E a b D {1} isCompact_singleton
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ (hC τ hτ))
    rw [← lintegral_indicator_one hms]
    refine lintegral_mono fun x => Set.indicator_le_indicator ?_
    show (1 : ℝ≥0∞) ≤ ∑' γ : ratH E a b, ({1} : Set (H E a b)).indicator 1 (x⁻¹ * (γ : H E a b) * x)
    refine le_trans ?_ (ENNReal.le_tsum (1 : ratH E a b))
    simp
  exact Measure.integrableOn_of_bounded (M := M) hfin hc.aestronglyMeasurable (ae_restrict_of_forall_mem hms hM)

theorem kerTw2_sum (D : Dom E a b) {J : Type} (s : Finset J) (c : J → ℂ) (φ : J → H E a b → ℂ)
    (hφ : ∀ j ∈ s, IsTestH (φ j)) (x y : H E a b) :
    kerTw2 (∑ j ∈ s, c j • φ j) x y = ∑ j ∈ s, c j * kerTw2 (φ j) x y := by
  have hL := (E1.kerLin (E1.ctx E1.ratProper_holds D) s (fun i => φ i) (fun i => c i)
    (fun i => hφ i i.2)).2 x (E1.th y)
  have hL' : kerH (fun z => ∑ i : s, φ i z * c i) x (E1.th y) = ∑ i : s, kerH (φ i) x (E1.th y) * c i := hL
  have he : (∑ j ∈ s, c j • φ j) = fun z => ∑ i : s, φ i z * c i := by
    funext z
    rw [Finset.sum_apply, ← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  simp only [(E1.cntPair E a b).2.2]
  rw [he, hL', ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem cutTrD_sum (D : Dom E a b) {τ : ℝ} (hτ : 0 ≤ τ) {J : Type} (s : Finset J) (c : J → ℂ)
    (φ : J → H E a b → ℂ) (hφ : ∀ j ∈ s, IsTestH (φ j)) :
    cutTrD D τ (∑ j ∈ s, c j • φ j) = ∑ j ∈ s, c j * cutTrD D τ (φ j) := by
  have hk : ∀ x : H E a b, chiT τ x.1 * chiT τ x.2 * kerTw2 (∑ j ∈ s, c j • φ j) x x =
      ∑ j ∈ s, c j * (chiT τ x.1 * chiT τ x.2 * kerTw2 (φ j) x x) := by
    intro x
    rw [kerTw2_sum D s c φ hφ x x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [cutTrD, hk]
  rw [integral_finsetSum s fun j hj => (integrable_cut D hτ (φ j) (hφ j hj)).const_mul (c j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul (c j) _

end Ell

theorem ellLin (h : D4.EllFormula2J) : EllLin := by
  intro E _ _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ J s c φ r hr hφ
  obtain ⟨C, hC, hE⟩ := h E a b
  obtain ⟨F₁, hF₁⟩ := E1.domEx_holds E a μ₁
  obtain ⟨F₂, hF₂⟩ := E1.domEx_holds E b μ₂
  obtain ⟨D, -, hD⟩ := E1.bridge_holds E a b μ₁ μ₂ F₁ F₂ hF₁ hF₂
  have hτ : 0 ≤ C * (1 + r) := mul_nonneg hC (by linarith)
  have hs : D4.IsTest2J (∑ j ∈ s, c j • φ j) r := isTest2J_sum s fun j hj => isTest2J_smul (c j) (hφ j hj)
  rw [← hE μ₁ μ₂ F₁ F₂ (C * (1 + r)) r _ hF₁ hF₂ hs hr le_rfl, ← hD,
    Ell.cutTrD_sum D hτ s c φ fun j hj => ⟨(hφ j hj).cont, (hφ j hj).supp⟩]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hD, hE μ₁ μ₂ F₁ F₂ (C * (1 + r)) r _ hF₁ hF₂ (hφ j hj) hr le_rfl]

theorem ellLin_holds : EllLin := ellLin CV.ellFormula2J

end PositivityTheory.Rg.BcB.F

end
