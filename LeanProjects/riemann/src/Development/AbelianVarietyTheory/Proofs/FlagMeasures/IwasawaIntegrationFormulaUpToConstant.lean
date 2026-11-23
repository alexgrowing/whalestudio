import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLintegralEqOfMeasurable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulusStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.IwasawaShape

theorem gauge_ne_zero_finite {n : ℕ} {ε : Fin n → Bool} (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ)
    (μ : Measure (Formalism.REAL.UJ ε)) (hM : IsClosed (M : Set (Formalism.REAL.UJ ε)))
    (hμ : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ) : μ ≠ 0 ∧ IsFiniteMeasureOnCompacts μ := by
  obtain ⟨h0, hinv, hlim⟩ := hμ
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hr0, hrt⟩ := (hpos.and ((hlim.eventually_ne hL0).and (hlim.eventually_ne hLt))).exists
  set B : Set (Formalism.REAL.UJ ε) := {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} with hB
  have hden0 : ENNReal.ofReal (r ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact pow_pos hr d
  have hB0 : μ B ≠ 0 := by
    intro h; apply hr0; rw [h, ENNReal.zero_div]
  have hBt : μ B ≠ ⊤ := by
    intro h; apply hrt; rw [h]; exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top
  have hf : Continuous fun g : Formalism.REAL.UJ ε => Real.sqrt (Formalism.REAL.hs (uMat g - 1)) := by
    refine Real.continuous_sqrt.comp ?_
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
    refine (Continuous.norm ?_).pow 2
    exact (continuous_apply k).comp ((continuous_apply i).comp
      (GlobalTheory.FlagLeviGroup.continuous_uMat.sub continuous_const))
  have hBm : MeasurableSet B := (isClosed_le hf continuous_const).measurableSet
  have hBn : B ∈ nhds (1 : Formalism.REAL.UJ ε) := by
    have hO : IsOpen {g : Formalism.REAL.UJ ε | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < r} :=
      isOpen_lt hf continuous_const
    refine Filter.mem_of_superset (hO.mem_nhds ?_) fun g hg => by
      rw [hB, Set.mem_ofPred_eq]; rw [Set.mem_ofPred_eq] at hg; exact hg.le
    show Real.sqrt (Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r
    rw [GlobalTheory.FlagLeviGroup.uMat_one, sub_self]
    unfold Formalism.REAL.hs
    simpa using hr
  refine ⟨fun h => hB0 (by rw [h]; rfl), ?_⟩
  exact finiteOnCompacts_of_nhds M μ h0 hM (fun s hs => hinv s hs) B hBm hBn hBt

theorem coe_KG {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) = maxK ε := by
  ext g
  have hJ := GlobalTheory.RealIwasawa.uMat_form g
  change g ∈ Formalism.REAL.KG ε ↔ (uMat g)ᴴ * uMat g = 1
  rw [Formalism.REAL.mem_KG]
  change (uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g) ↔ _
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have h' : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp h
  calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hJ]
    _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * uMat g := by rw [h', Matrix.one_mul]

theorem iwasawa_shape : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN := by
  intro n ε p q _ _ a j hj W hW μN μM μK hN hM hK0 hK1 hKi
  obtain ⟨⟨N, hNs⟩, hNc, -⟩ := GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW
  obtain ⟨⟨M, hMs⟩, hMc, ⟨K, hKs⟩, -, hnorm⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε a W
  obtain ⟨hdec, huniq⟩ := GlobalTheory.RealIwasawa.iwasawa n ε a j W hW
  have eN : ∀ x, x ∈ N ↔ x ∈ flagN ε W := fun x => by rw [← hNs]; rfl
  have eM : ∀ x, x ∈ M ↔ x ∈ flagM ε W := fun x => by rw [← hMs]; rfl
  have eK : ∀ x, x ∈ K ↔ x ∈ maxK ε := fun x => by rw [← hKs]; rfl
  have hKc : IsCompact (K : Set (Formalism.REAL.UJ ε)) := by
    rw [hKs, ← coe_KG]
    exact isCompact_iff_compactSpace.mpr (Formalism.REAL.instCompactKG n ε)
  have hN' : IsGaugeSub (N : Set (Formalism.REAL.UJ ε)) (dimN n j) μN := by rw [hNs]; exact hN
  have hM' : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM := by
    rw [hMs]; exact hM
  have hNc' : IsClosed (N : Set (Formalism.REAL.UJ ε)) := by rw [hNs]; exact hNc
  have hMc' : IsClosed (M : Set (Formalism.REAL.UJ ε)) := by rw [hMs]; exact hMc
  obtain ⟨hN0, hNf⟩ := gauge_ne_zero_finite N _ μN hNc' hN'
  obtain ⟨hM0, hMf⟩ := gauge_ne_zero_finite M _ μM hMc' hM'
  have := hNf
  have := hMf
  have : IsProbabilityMeasure μK := ⟨hK1⟩
  have : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hmod := GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus n ε a j W hj hW μN hN
  obtain ⟨c, hc0, hct, hc⟩ := GlobalTheory.IwasawaShape.exists_lintegral_eq N M K hNc' hMc' hKc
    (fun m hm u hu => (eN _).2 (hnorm m ((eM m).1 hm) u ((eN u).1 hu)))
    (fun u hu m hm hk => huniq u ((eN u).1 hu) m ((eM m).1 hm) ((eK _).1 hk))
    (fun g => by
      obtain ⟨u, hu, m, hm, k, hk, rfl⟩ := hdec g
      exact ⟨u, (eN u).2 hu, m, (eM m).2 hm, k, (eK k).2 hk, rfl⟩)
    (Formalism.REAL.muG ε) μN μM μK (NeZero.ne _) hN0 hM0 hN'.1 hM'.1
    (fun s hs => hN'.2.1 s hs) (fun s hs => hM'.2.1 s hs) (fun s hs => hKi s ((eK s).1 hs))
    (fun m => ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id))
    (fun m hm => hmod m ((eM m).1 hm))
  exact ⟨c, hc0, hct, hc⟩

end GlobalTheory.IwasawaShape
