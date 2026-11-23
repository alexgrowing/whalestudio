import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntMuCD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarHaar

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Pt (ε : Fin n → Bool) := {a : Fin n // ε a = true}

abbrev Qt (ε : Fin n → Bool) := {a : Fin n // ε a = false}

def pOfB (ε : Fin n → Bool) (B : Pt ε → Qt ε → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b =>
    if ha : ε a = true then (if hb : ε b = false then B ⟨a, ha⟩ ⟨b, hb⟩ else 0)
    else (if hb : ε b = true then star (B ⟨b, hb⟩ ⟨a, by simpa using ha⟩) else 0)

open Classical in

def toUJ (ε : Fin n → Bool) (m : Matrix (Fin n) (Fin n) ℂ) : UJ ε :=
  if h : inUJ ε m then
    ⟨⟨m, Jm ε * mᴴ * Jm ε, mul_eq_one_comm.mp (left_inv_of_inUJ ε m h), left_inv_of_inUJ ε m h⟩, h⟩
  else 1

theorem toUJ_toM (ε : Fin n → Bool) (g : UJ ε) : toUJ ε (toM g) = g := by
  unfold toUJ
  split_ifs with h
  · exact Subtype.ext (Units.ext rfl)
  · exact absurd g.2 h

theorem measurable_comp_toUJ (ε : Fin n → Bool) {f : UJ ε → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun m : Fin n → Fin n → ℂ => f (toUJ ε m)) := by
  have hc : Topology.IsClosedEmbedding (intMuCD_eM ε) := isClosedEmbedding_toM ε
  have he : MeasurableEmbedding (intMuCD_eM ε) := hc.measurableEmbedding
  have hinj : Function.Injective (intMuCD_eM ε) := hc.injective
  have heq : (fun m : Fin n → Fin n → ℂ => f (toUJ ε m)) =
      Function.extend (intMuCD_eM ε) f (fun _ => f 1) := by
    funext m
    by_cases h : inUJ ε m
    · obtain ⟨g, rfl⟩ : m ∈ Set.range (fun g : UJ ε => toM g) := by rw [range_toM]; exact h
      show f (toUJ ε (toM g)) = Function.extend (intMuCD_eM ε) f (fun _ => f 1) (intMuCD_eM ε g)
      rw [toUJ_toM, hinj.extend_apply]
    · rw [Function.extend_apply']
      · simp [toUJ, h]
      · rintro ⟨g, hg⟩
        exact h (hg ▸ g.2)
  rw [heq]
  exact he.measurable_extend hf measurable_const

def phiF (ε : Fin n → Bool) (B : Pt ε → Qt ε → ℂ) : PCoord ε → ℂ := fun ab => pOfB ε B ab.1.1 ab.1.2

theorem pOfB_star (ε : Fin n → Bool) (B : Pt ε → Qt ε → ℂ) (a b : Fin n) :
    star (pOfB ε B b a) = pOfB ε B a b := by
  cases ha : ε a <;> cases hb : ε b <;> simp [pOfB, ha, hb]

theorem pOfB_zero (ε : Fin n → Bool) (B : Pt ε → Qt ε → ℂ) {a b : Fin n} (h : ε a = ε b) :
    pOfB ε B a b = 0 := by
  cases ha : ε a <;> cases hb : ε b <;> simp_all [pOfB]

theorem pmat_phiF (ε : Fin n → Bool) (B : Pt ε → Qt ε → ℂ) : pmat (phiF ε B) = pOfB ε B := by
  funext a b
  simp only [pmat]
  split_ifs with h1 h2
  · rfl
  · exact pOfB_star ε B a b
  · refine (pOfB_zero ε B ?_).symm
    by_contra hne
    rcases lt_trichotomy a b with h | h | h
    · exact h2 ⟨h, Ne.symm hne⟩
    · exact hne (h ▸ rfl)
    · exact h1 ⟨h, hne⟩

def phiL (ε : Fin n → Bool) : (Pt ε → Qt ε → ℂ) ≃ₗ[ℝ] (PCoord ε → ℂ) where
  toFun := phiF ε
  invFun z := fun a b => pmat z a.1 b.1
  map_add' B B' := by
    funext ab
    simp only [phiF, pOfB, Matrix.of_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' r B := by
    funext ab
    simp only [phiF, pOfB, Matrix.of_apply, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp
  left_inv B := by
    funext a b
    show pmat (phiF ε B) a.1 b.1 = B a b
    rw [pmat_phiF]
    simp [pOfB, a.2, b.2]
  right_inv z := by
    funext ab
    obtain ⟨⟨a, b⟩, hlt, hne⟩ := ab
    dsimp only at hlt hne
    simp only [phiF, pOfB, Matrix.of_apply]
    by_cases ha : ε a = true
    · have hb : ε b = false := by cases hb : ε b <;> simp_all
      simp only [dif_pos ha, dif_pos hb, pmat, dif_pos (And.intro hlt hne)]
    · have hb : ε b = true := by cases hb : ε b <;> simp_all
      have h1 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => lt_asymm h.1 hlt
      have h2 : b < a ∧ ε a ≠ ε b := ⟨hlt, hne⟩
      simp only [dif_neg ha, dif_pos hb, pmat, dif_neg h1, dif_pos h2, star_star]

theorem lintegral_pmat_le (ε : Fin n → Bool) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ H : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞,
      ∫⁻ z : PCoord ε → ℂ, H (pmat z) ≤ c * ∫⁻ B : Pt ε → Qt ε → ℂ, H (pOfB ε B) := by
  let e : (Pt ε → Qt ε → ℂ) ≃L[ℝ] (PCoord ε → ℂ) := (phiL ε).toContinuousLinearEquiv
  let eM := e.toHomeomorph.toMeasurableEquiv
  have h1 : ∀ _ : Pt ε, (volume : Measure (Qt ε → ℂ)).IsAddHaarMeasure := fun _ => inferInstance
  have h2 : ∀ _ : Pt ε, SigmaFinite (volume : Measure (Qt ε → ℂ)) := fun _ => inferInstance
  have h3 : ∀ _ : Pt ε, MeasurableAdd (Qt ε → ℂ) := fun _ => inferInstance
  have h0 : (volume : Measure (Pt ε → Qt ε → ℂ)).IsAddHaarMeasure := inferInstance
  have : (Measure.map eM (volume : Measure (Pt ε → Qt ε → ℂ))).IsAddHaarMeasure :=
    ContinuousLinearEquiv.isAddHaarMeasure_map e volume
  have hv := Measure.isAddLeftInvariant_eq_smul (volume : Measure (PCoord ε → ℂ))
    (Measure.map eM (volume : Measure (Pt ε → Qt ε → ℂ)))
  refine ⟨((volume : Measure (PCoord ε → ℂ)).addHaarScalarFactor
    (Measure.map eM (volume : Measure (Pt ε → Qt ε → ℂ))) : ℝ≥0∞), ENNReal.coe_ne_top, fun H => le_of_eq ?_⟩
  conv_lhs => rw [hv]
  rw [lintegral_smul_measure, lintegral_map_equiv]
  congr 2
  funext B
  show H (pmat (phiF ε B)) = _
  rw [pmat_phiF]

theorem haar_polar_le (ε : Fin n → Bool) (hq : 1 ≤ q0 ε) (ν : Measure (UJ ε)) [ν.IsHaarMeasure] :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : UJ ε → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂ν ≤
        C * ∫⁻ B : Pt ε → Qt ε → ℂ,
          (∫⁻ k, f (toUJ ε (toMK k * NormedSpace.exp (pOfB ε B))) ∂(muK ε)) *
            ENNReal.ofReal (Real.exp (n * Real.sqrt (2 * q0 ε) * Real.sqrt (hs (pOfB ε B)))) := by
  have := muPolar_isHaar ε
  have hν : ν = (Measure.haarScalarFactor ν (muPolar ε) : ℝ≥0∞) • muPolar ε :=
    Measure.isMulLeftInvariant_eq_smul ν (muPolar ε)
  obtain ⟨c', hc', hvol⟩ := lintegral_pmat_le ε
  have hK : muK ε Set.univ ≠ 0 := (ENNReal.toReal_pos_iff.1 (muK_univ_pos ε)).1.ne'
  set c : ℝ≥0∞ := (Measure.haarScalarFactor ν (muPolar ε) : ℝ≥0∞) with hcdef
  refine ⟨c * (muK ε Set.univ)⁻¹ * c',
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.inv_ne_top.2 hK)) hc', ?_⟩
  intro f hf
  set F : (Fin n → Fin n → ℂ) → ℝ≥0∞ := fun m => f (toUJ ε m) with hFdef
  have hFm : Measurable F := measurable_comp_toUJ ε hf
  have hFg : ∀ g : UJ ε, F (toM g) = f g := fun g => by simp only [hFdef, toUJ_toM]
  have hJm : Measurable (fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) :=
    ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  have hmeas : AEMeasurable (Function.uncurry fun (k : KG ε) (z : PCoord ε → ℂ) =>
      F (polarM (k, z)) * ENNReal.ofReal (Jac z)) ((dk ε).prod volume) :=
    ((hFm.comp (intMuCD_measurable_pM ε)).mul (hJm.comp measurable_snd)).aemeasurable
  let H : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞ := fun X =>
    (∫⁻ k, F (toMK k * NormedSpace.exp X) ∂(muK ε)) *
      ENNReal.ofReal (Real.exp (n * Real.sqrt (2 * q0 ε) * Real.sqrt (hs X)))
  have hJ : ∀ z : PCoord ε → ℂ, ENNReal.ofReal (Jac z) ≤
      ENNReal.ofReal (Real.exp (n * Real.sqrt (2 * q0 ε) * Real.sqrt (hs (pmat z)))) := by
    intro z
    refine ENNReal.ofReal_le_ofReal ((jac_le_exp z).trans (Real.exp_le_exp.2 ?_))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  calc ∫⁻ g, f g ∂ν = c * ∫⁻ g, F (toM g) ∂(muPolar ε) := by
        conv_lhs => rw [hν]
        rw [lintegral_smul_measure, smul_eq_mul]
        simp only [hFg]
    _ = c * ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
        rw [lintegral_muPolar ε F hFm]
    _ = c * ∫⁻ z, ∫⁻ k, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂(dk ε) ∂volume := by
        rw [lintegral_lintegral_swap hmeas]
    _ = c * ∫⁻ z, (muK ε Set.univ)⁻¹ * ((∫⁻ k, F (toMK k * NormedSpace.exp (pmat z)) ∂(muK ε)) *
          ENNReal.ofReal (Jac z)) ∂volume := by
        congr 1
        refine lintegral_congr fun z => ?_
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, dk, lintegral_smul_measure, smul_eq_mul,
          mul_assoc]
        rfl
    _ ≤ c * ∫⁻ z : PCoord ε → ℂ, (muK ε Set.univ)⁻¹ * H (pmat z) ∂volume := by
        exact mul_le_mul_right (lintegral_mono fun z => mul_le_mul_right (mul_le_mul_right (hJ z) _) _) c
    _ = c * ((muK ε Set.univ)⁻¹ * ∫⁻ z : PCoord ε → ℂ, H (pmat z) ∂volume) := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hK)]
    _ ≤ c * ((muK ε Set.univ)⁻¹ * (c' * ∫⁻ B : Pt ε → Qt ε → ℂ, H (pOfB ε B))) := by
        gcongr
        exact hvol H
    _ = c * (muK ε Set.univ)⁻¹ * c' * ∫⁻ B : Pt ε → Qt ε → ℂ, H (pOfB ε B) := by
        simp only [mul_assoc]

end ReciprocityTheory.ChartRestriction.DS.S7
