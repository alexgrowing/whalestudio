import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.JacobianNearOneOfSmall
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPol
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.MeasurableEmbeddingUpqMat

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

open Topology Filter

variable {n : ℕ}

def muCDtr {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) (ε : Fin n → Bool) : Measure (Formalism.BasicNotions.UpqT P Q) :=
  Measure.comap (β := Fin n → Fin n → ℂ)
    (fun g : Formalism.BasicNotions.UpqT P Q => Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))
    (ENNReal.ofReal (cPQ ε) • muPolarMat ε)

theorem tie_volU_pos (N : ℕ) : 0 < volU N :=
  Finset.prod_pos fun i _ => by positivity

theorem tie_tendsto {f : ℝ → ENNReal} {x : ℝ} (hx : 0 < x)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal ((1 - η) * x) ≤ f r ∧ f r ≤ ENNReal.ofReal ((1 + η) * x)) :
    Tendsto f (𝓝[>] 0) (𝓝 (ENNReal.ofReal x)) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hat : a ≠ ⊤ := ne_top_of_lt ha
    have ht : a.toReal < x := by
      have := (ENNReal.toReal_lt_toReal hat ENNReal.ofReal_ne_top).2 ha
      rwa [ENNReal.toReal_ofReal hx.le] at this
    have ht0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
    have hη : 0 < (x - a.toReal) / (2 * x) := div_pos (by linarith) (by linarith)
    filter_upwards [h _ hη] with r hr
    have e1 : (1 - (x - a.toReal) / (2 * x)) * x = (x + a.toReal) / 2 := by field_simp; ring
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal hat).symm
      _ < ENNReal.ofReal ((1 - (x - a.toReal) / (2 * x)) * x) := by
          rw [e1]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      _ ≤ f r := hr.1
  · by_cases hat : a = ⊤
    · filter_upwards [h 1 one_pos] with r hr
      exact lt_of_le_of_lt hr.2 (hat ▸ ENNReal.ofReal_lt_top)
    · have ht : x < a.toReal := by
        have := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hat).2 ha
        rwa [ENNReal.toReal_ofReal hx.le] at this
      have hη : 0 < (a.toReal - x) / (2 * x) := div_pos (by linarith) (by linarith)
      filter_upwards [h _ hη] with r hr
      have e1 : (1 + (a.toReal - x) / (2 * x)) * x = (x + a.toReal) / 2 := by field_simp; ring
      calc f r ≤ _ := hr.2
        _ < ENNReal.ofReal a.toReal := by
          rw [e1]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
        _ = a := ENNReal.ofReal_toReal hat

theorem tie_cancel {p q : ℝ} {v : ENNReal} (hv0 : v ≠ 0) (hvt : v ≠ ⊤) (hq : 0 ≤ q)
    (h : ENNReal.ofReal p * v ≤ ENNReal.ofReal q * v) : p ≤ q := by
  have := (ENNReal.mul_le_mul_iff_left hv0 hvt).1 h
  have h2 := (ENNReal.ofReal_le_ofReal_iff hq).1 this
  exact h2

theorem tie_d_eq (ε : Fin n → Bool) (d : ℝ) (hd0 : 0 < d)
    (hd : DensOn (fun S => muPolar ε (expSet S)) d) : d = 1 / (volU (pOf ε) * volU (qOf ε)) := by
  haveI := muPolar_isHaar ε
  obtain ⟨hK, hP, hG⟩ := gco_haar ε
  have hpol := haar_pol_density (muPolar ε) d hd
  set x := volU (pOf ε) * volU (qOf ε) with hx
  have hx0 : 0 < x := mul_pos (tie_volU_pos _) (tie_volU_pos _)
  set D := 1 / x with hD
  have hD0 : 0 < D := by positivity
  have key : ∀ η : ℝ, 0 < η → η < 1 → (1 - η) * d ≤ (1 + η) * D ∧ (1 - η) * D ≤ (1 + η) * d := by
    intro η hη hη1
    obtain ⟨δ1, hδ1, h1⟩ := hpol η hη
    obtain ⟨δ2, hδ2, h2⟩ := muPolar_near_one ε η hη
    set δ := min δ1 δ2
    have hδ : 0 < δ := lt_min hδ1 hδ2
    set B := Metric.ball (0 : KCo ε) (δ / 2)
    set C := Metric.ball (0 : PCoord ε → ℂ) (δ / 2)
    have hB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
    have hC0 : volume C ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
    have hBt : volume B ≠ ⊤ := measure_ball_lt_top.ne
    have hCt : volume C ≠ ⊤ := measure_ball_lt_top.ne
    have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
    have hCm : MeasurableSet C := Metric.isOpen_ball.measurableSet
    have hSm : MeasurableSet (B ×ˢ C) := hBm.prod hCm
    have hvS : volume (B ×ˢ C) = volume B * volume C := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
    have hv0 : volume B * volume C ≠ 0 := mul_ne_zero hB0 hC0
    have hvt : volume B * volume C ≠ ⊤ := ENNReal.mul_ne_top hBt hCt
    have hsm : ∀ s ∈ B ×ˢ C, ‖s‖ < δ1 := by
      intro s hs
      have h1' : ‖s.1‖ < δ / 2 := by simpa [B] using hs.1
      have h2' : ‖s.2‖ < δ / 2 := by simpa [C] using hs.2
      have : ‖s‖ ≤ δ / 2 := norm_prod_le_iff.2 ⟨h1'.le, h2'.le⟩
      linarith [min_le_left δ1 δ2]
    have hB : ∀ w ∈ B, ‖w‖ < δ2 := by
      intro w hw
      have : ‖w‖ < δ / 2 := by simpa [B] using hw
      linarith [min_le_right δ1 δ2]
    have hC : ∀ z ∈ C, ‖z‖ < δ2 := by
      intro z hz
      have : ‖z‖ < δ / 2 := by simpa [C] using hz
      linarith [min_le_right δ1 δ2]
    obtain ⟨u1, l1⟩ := h1 (B ×ˢ C) hSm hsm
    obtain ⟨u2, l2⟩ := h2 B C hBm hCm hB hC
    rw [hvS] at u1 l1
    have e1 : (1 + η) / x = (1 + η) * D := by rw [hD]; ring
    have e2 : (1 - η) / x = (1 - η) * D := by rw [hD]; ring
    rw [e1] at u2
    rw [e2] at l2
    constructor
    · exact tie_cancel hv0 hvt (by positivity) (l1.trans u2)
    · exact tie_cancel hv0 hvt (by positivity) (l2.trans u1)
  rcases lt_trichotomy d D with hlt | heq | hgt
  · exfalso
    set η := (D - d) / (2 * (D + d))
    have hη : 0 < η := div_pos (by linarith) (by linarith)
    have hη1 : η < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    have e : η * (2 * (D + d)) = D - d := div_mul_cancel₀ _ (by linarith)
    have := (key η hη hη1).2
    nlinarith
  · exact heq
  · exfalso
    set η := (d - D) / (2 * (D + d))
    have hη : 0 < η := div_pos (by linarith) (by linarith)
    have hη1 : η < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    have e : η * (2 * (D + d)) = d - D := div_mul_cancel₀ _ (by linarith)
    have := (key η hη hη1).1
    nlinarith

section

variable {P Q : ℕ}

theorem tie_sum_reindex (e : Fin P ⊕ Fin Q ≃ Fin n) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖Matrix.reindex e.symm e.symm M i j‖ = ∑ a, ∑ b, ‖M a b‖ := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [← Equiv.sum_comp e (fun a => ∑ b, ‖M a b‖)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp e (fun b => ‖M (e i) b‖)

theorem tie_mem_ball (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (r : ℝ) (s : GCo ε) :
    gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r ↔ ∑ a, ∑ b, ‖gMat s a b‖ < r := by
  show ∑ i, ∑ j, ‖Matrix.reindex e.symm e.symm (gMat s) i j‖ < r ↔ _
  rw [tie_sum_reindex]

theorem tie_gToLie_cont (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Continuous (gToLie e he1 he2 : GCo ε → Formalism.BasicNotions.lieU P Q) := by
  have h1 : Continuous fun s : GCo ε => gToLieMat e s :=
    (LinearMap.continuous_of_finiteDimensional (gMatL ε)).matrix_submatrix _ _
  exact h1.subtype_mk _

theorem tie_ball_open (P Q : ℕ) (r : ℝ) : IsOpen (Formalism.BasicNotions.ballU P Q r) :=
  isOpen_lt (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_norm.comp (continuous_subtype_val.matrix_elem i j)) continuous_const

end

theorem omegaDensity_muCDtr {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.OmegaDensity (muCDtr e ε) (ENNReal.ofReal (cOmega n)) := by
  haveI := muPolar_isHaar ε
  haveI := lieU_borel P Q
  obtain ⟨hK, hP, hG⟩ := gco_haar ε
  obtain ⟨d, hd0, hd⟩ := haar_exp_density (muPolar ε)
  have hdD := tie_d_eq ε d hd0 hd
  refine ⟨_, isOmegaLeb_gToLie e he1 he2, ?_⟩
  set κ : ℝ := 2 ^ (n * (n - 1) / 2) with hκ
  have hκ0 : 0 < κ := by positivity
  have hσc : Continuous fun s : GCo ε => ∑ a, ∑ b, ‖gMat s a b‖ :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_norm.comp ((LinearMap.continuous_of_finiteDimensional (gMatL ε)).matrix_elem a b)
  have hnum : ∀ r, muCDtr e ε {g | ∃ X ∈ Formalism.BasicNotions.ballU P Q r, Formalism.BasicNotions.UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} =
      ENNReal.ofReal (cPQ ε) * muPolar ε (expSet {s : GCo ε | gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r}) := by
    intro r
    have hE := measurableEmbedding_upqMat e he1 he2
    show Measure.comap (β := Fin n → Fin n → ℂ) (fun g => upqMat e g) (ENNReal.ofReal (cPQ ε) • muPolarMat ε) _ =
      _ * Measure.comap (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) (muPolarMat ε) _
    rw [hE.comap_apply, (measurableEmbedding_toM ε).comap_apply, Measure.smul_apply, smul_eq_mul]
    congr 2
    exact image_expBall e he1 he2 r
  have hden : ∀ r, (ENNReal.ofReal κ • Measure.map (gToLie e he1 he2) volume) (Formalism.BasicNotions.ballU P Q r) =
      ENNReal.ofReal κ * volume {s : GCo ε | gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r} := by
    intro r
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (tie_gToLie_cont e he1 he2).measurable (tie_ball_open P Q r).measurableSet]
    rfl
  have hvn := tie_volU_pos n
  have hvp := tie_volU_pos (pOf ε)
  have hvq := tie_volU_pos (qOf ε)
  have hc : cOmega n * κ = cPQ ε * d := by
    rw [hdD, cPQ_eq_volU, cOmega, ← hκ]
    field_simp
  have hc0 : 0 < cOmega n := cOmega_pos n
  have hcP : 0 ≤ cPQ ε := (cPQ_pos ε).le
  refine tie_tendsto hc0 (fun η hη => ?_)
  obtain ⟨δ, hδ, hdδ⟩ := hd η hη
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [hnum r, hden r]
  set S := {s : GCo ε | gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r} with hS
  have hSe : S = {s | ∑ a, ∑ b, ‖gMat s a b‖ < r} := Set.ext fun s => tie_mem_ball e he1 he2 r s
  have hSo : IsOpen S := by rw [hSe]; exact isOpen_lt hσc continuous_const
  have h0S : (0 : GCo ε) ∈ S := by
    rw [hSe, Set.mem_ofPred_eq, show gMat (0 : GCo ε) = 0 from (gMatL ε).map_zero]
    simpa using hr.1
  have hSb : ∀ s ∈ S, ‖s‖ < δ := fun s hs => by
    rw [hSe] at hs
    exact lt_of_le_of_lt (norm_le_sum_gMat s) (lt_trans hs hr.2)
  have hSball : S ⊆ Metric.ball 0 r := fun s hs => by
    rw [hSe] at hs
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt (norm_le_sum_gMat s) hs
  have hV0 : volume S ≠ 0 := (hSo.measure_pos volume ⟨0, h0S⟩).ne'
  have hVt : volume S ≠ ⊤ := ((measure_mono hSball).trans_lt measure_ball_lt_top).ne
  obtain ⟨hu, hl⟩ := hdδ S hSo.measurableSet hSb
  have hden0 : ENNReal.ofReal κ * volume S ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 hκ0).ne' hV0
  have hdent : ENNReal.ofReal κ * volume S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt
  have eq1 : (1 - η) * cOmega n * κ = cPQ ε * ((1 - η) * d) := by linear_combination (1 - η) * hc
  have eq2 : (1 + η) * cOmega n * κ = cPQ ε * ((1 + η) * d) := by linear_combination (1 + η) * hc
  constructor
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)]
    calc ENNReal.ofReal ((1 - η) * cOmega n) * (ENNReal.ofReal κ * volume S)
        = ENNReal.ofReal (cPQ ε) * (ENNReal.ofReal ((1 - η) * d) * volume S) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul' hκ0.le, eq1, ENNReal.ofReal_mul hcP, mul_assoc]
      _ ≤ _ := by gcongr
  · apply ENNReal.div_le_of_le_mul
    calc ENNReal.ofReal (cPQ ε) * muPolar ε (expSet S)
        ≤ ENNReal.ofReal (cPQ ε) * (ENNReal.ofReal ((1 + η) * d) * volume S) := by gcongr
      _ = ENNReal.ofReal ((1 + η) * cOmega n) * (ENNReal.ofReal κ * volume S) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hcP, ← eq2, ENNReal.ofReal_mul' hκ0.le, mul_assoc]

end ReciprocityTheory.ChartRestriction.DS
