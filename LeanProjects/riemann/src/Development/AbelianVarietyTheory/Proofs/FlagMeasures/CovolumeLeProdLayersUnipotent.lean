import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptoticStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingTriangularShearStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoVolumeSublevelDivPowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeProductOverGradingLayersStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLieCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCoordSqSumLeHilbertSchmidtUnitaryGroupStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool} {d : ℕ}

theorem continuous_uMat_sub_one : Continuous fun g : UJ ε => uMat g - 1 :=
  (Units.continuous_val.comp continuous_subtype_val).sub continuous_const

theorem continuous_coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1) :=
  continuous_pi fun i => (ipL (E i)).continuous_of_finiteDimensional.comp continuous_uMat_sub_one

theorem continuous_hs_sub_one : Continuous fun g : UJ ε => hs (uMat g - 1) := by
  unfold hs
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_uMat_sub_one.matrix_elem i j).norm).pow 2

theorem mul_sub_one (g h : UJ ε) :
    uMat (g * h) - 1 = (uMat g - 1) + (uMat h - 1) + (uMat g - 1) * (uMat h - 1) := by
  have : uMat (g * h) = uMat g * uMat h := rfl
  rw [this]; noncomm_ring

theorem measurePreserving_coord {m : ℕ} {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    {E : Fin d → Matrix (Fin n) (Fin n) ℂ} {deg : Fin d → ℕ}
    (hle : ∀ c, A (c + 1) ≤ A c) (hm : A m = ⊥)
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ c X, (X ∈ A c ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (E '' {i | c ≤ deg i}))
    {ν : Measure (UJ ε)} (hν : IsGaugeSub {g | uMat g - 1 ∈ A 0} d ν) :
    MeasurePreserving (fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1)) ν volume := by
  have hE0 : ∀ i, E i ∈ A 0 ∧ inG ε (E i) := fun i =>
    (hsp 0 (E i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)
  have hsp0 : ∀ X, (X ∈ A 0 ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E) := fun X => by
    simpa using hsp 0 X
  have hmul0 : ∀ X ∈ A 0, ∀ Y ∈ A 0, X * Y ∈ A 0 := fun X hX Y hY => hle 0 (hmul 0 X hX Y hY).1
  obtain ⟨σ, hσc, hσ⟩ := GlobalTheory.T.exists_orthonormal_lie_coordinates n d m ε A E hm hmul hle hinv hE hE0
  have hσ2 : ∀ x i, ipL (E i) (uMat (σ x) - 1) = x i := fun x => (hσ x).2
  have hinj : ∀ g h : UJ ε, uMat g - 1 ∈ A 0 → uMat h - 1 ∈ A 0 →
      (∀ i, ipL (E i) (uMat g - 1) = ipL (E i) (uMat h - 1)) → g = h := by
    intro g h hg hh hc
    have := sub_mem_of_coord_eq hmul hinv hE hsp hg hh m fun i _ => hc i
    rw [hm, Submodule.mem_bot, sub_eq_zero] at this
    exact Subtype.ext (Units.ext this)
  have hS : MeasurableSet {g : UJ ε | uMat g - 1 ∈ A 0} :=
    ((A 0).closed_of_finiteDimensional.preimage continuous_uMat_sub_one).measurableSet
  have hμ : IsGaugeSub {g | uMat g - 1 ∈ A 0} d ((volume : Measure (Fin d → ℝ)).map σ) := by
    refine ⟨?_, fun s hs => ?_, ?_⟩
    · rw [Measure.map_apply hσc.measurable hS.compl]
      convert measure_empty (μ := (volume : Measure (Fin d → ℝ)))
      ext x
      simpa using (hσ x).1
    · have hs' : uMat s - 1 ∈ A 0 := hs
      have hT := GlobalTheory.T.measurePreserving_add_of_triangular d deg (fun x i => ipL (E i) (uMat (s * σ x) - 1) - x i)
        (((continuous_coord E).comp (continuous_const.mul hσc)).sub continuous_id).measurable (by
          intro x y i hxy
          have h1 := sub_mem_of_coord_eq hmul hinv hE hsp (hσ x).1 (hσ y).1 (deg i) fun k hk => by
            rw [hσ2, hσ2, hxy k hk]
          have h2 := ipL_eq_zero_of_mem hE (fun i => (hE0 i).2) (hinv (deg i + 1))
            (fun X => (hsp (deg i + 1) X).1) (i := i) (by simp) (hmul _ _ h1 _ hs').2
          have h3 : (uMat s - 1) * (uMat (σ x) - uMat (σ y)) =
              (uMat s - 1) * (uMat (σ x) - 1) - (uMat s - 1) * (uMat (σ y) - 1) := by noncomm_ring
          rw [h3, map_sub] at h2
          simp only [mul_sub_one, map_add, hσ2]
          linarith)
      have he : (fun g => s * g) ∘ σ =
          σ ∘ fun x => x + fun i => ipL (E i) (uMat (s * σ x) - 1) - x i := by
        funext x
        refine hinj _ _ ?_ (hσ _).1 fun i => ?_
        · simp only [Function.comp, mul_sub_one]
          exact (A 0).add_mem ((A 0).add_mem hs' (hσ x).1) (hmul0 _ hs' _ (hσ x).1)
        · simp only [Function.comp, hσ2, Pi.add_apply]
          ring
      rw [Measure.map_map (measurable_const_mul s) hσc.measurable, he,
        ← Measure.map_map hσc.measurable hT.measurable, hT.map_eq]
    · have hest := fun x => GlobalTheory.T.traceCoord_sq_sum_le_hilbertSchmidt_unitaryGroup n d ε E hE (fun i => (hE0 i).2) (σ x)
        ((hsp0 _).1 ⟨(A 0).sub_mem (hσ x).1 (hinv 0 _ (hσ x).1), inG_sub_inv _⟩)
      simp only [(hσ _).2] at hest
      have h0 : σ 0 = 1 := hinj _ _ (hσ 0).1 (by simp [uMat]) fun i => by
        rw [hσ2]; simp [uMat]
      have := GlobalTheory.T.tendsto_volume_sqrt_sublevel_div_pow_eq_volume_ball d (fun x => hs (uMat (σ x) - 1))
        (continuous_hs_sub_one.comp hσc).continuousAt (by simp [h0, uMat, hs])
        (fun x => (hest x).1) (fun x => (hest x).2)
      refine this.congr fun r => ?_
      rw [Measure.map_apply hσc.measurable
        (isClosed_le continuous_hs_sub_one.sqrt continuous_const).measurableSet]
      rfl
  have heq := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε (A 0) d E hmul0 hE hsp0 ν hν).2.2.1 _ hμ
  refine ⟨(continuous_coord E).measurable, ?_⟩
  rw [← heq, Measure.map_map (continuous_coord E).measurable hσc.measurable]
  have : (fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1)) ∘ σ = id := by
    funext x i
    exact hσ2 x i
  rw [this, Measure.map_id]

theorem covol_le_prod_layers : ∀ (ι : Type) [Fintype ι] (n d m : ℕ) (ε : ι → Fin n → Bool) (A : ι → ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : ι → Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), (∀ v c, A v (c + 1) ≤ A v c) → (∀ v, A v m = ⊥) → (∀ v c, ∀ X ∈ A v c, ∀ Y ∈ A v 0, X * Y ∈ A v (c + 1) ∧ Y * X ∈ A v (c + 1)) → (∀ v c, ∀ X ∈ A v c, Formalism.REAL.Jm (ε v) * Xᴴ * Formalism.REAL.Jm (ε v) ∈ A v c) → (∀ v i k, ((E v i * (E v k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ v c X, (X ∈ A v c ∧ Formalism.REAL.inG (ε v) X) ↔ X ∈ Submodule.span ℝ (E v '' {i | c ≤ deg i})) → ∀ (ν : ∀ v, Measure (Formalism.REAL.UJ (ε v))) [∀ v, SigmaFinite (ν v)], (∀ v, IsGaugeSub {g | uMat g - 1 ∈ A v 0} d (ν v)) → ∀ (Γ : Subgroup (∀ v, Formalism.REAL.UJ (ε v))) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (∀ γ ∈ Γ, ∀ v, uMat (γ v) - 1 ∈ A v 0) → (∀ c, MeasurableSet (D c)) → (∀ (c : ℕ) (x : ι → {i : Fin d // deg i = c} → ℝ), ∃ γ ∈ Γ, (∀ v, uMat (γ v) - 1 ∈ A v c) ∧ (fun v (i : {i : Fin d // deg i = c}) => (((uMat (γ v) - 1) * (E v i.1)ᴴ).trace).re + x v i) ∈ D c) → covol (Γ : Set (∀ v, Formalism.REAL.UJ (ε v))) (Measure.pi ν) {g | ∀ v, uMat (g v) - 1 ∈ A v 0} ≤ ∏ c ∈ Finset.range m, volume (D c) := by
  intro ι _ n d m ε A E deg hle hm hmul hinv hE hsp ν _ hν Γ D hΓ hD hcov
  have hE0 : ∀ v i, E v i ∈ A v 0 ∧ inG (ε v) (E v i) := fun v i =>
    (hsp v 0 (E v i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)
  have hanti : ∀ v, Antitone (A v) := fun v => antitone_nat_of_succ_le (hle v)
  have horth : ∀ v c i, deg i < c → ∀ X ∈ A v c, ipL (E v i) X = 0 := fun v c i hi X hX =>
    ipL_eq_zero_of_mem (hE v) (fun i => (hE0 v i).2) (hinv v c) (fun X => (hsp v c X).1)
      (by simpa using hi) hX
  have hdeg : ι → ∀ i, deg i < m := by
    intro v i
    by_contra hi
    have h1 := ((hsp v m (E v i)).2 (Submodule.subset_span ⟨i, not_lt.1 hi, rfl⟩)).1
    rw [hm, Submodule.mem_bot] at h1
    have := hE v i i
    simp [h1] at this
  have hmp := measurePreserving_pi ν (fun _ => (volume : Measure (Fin d → ℝ))) fun v =>
    measurePreserving_coord (hle v) (hm v) (hmul v) (hinv v) (hE v) (hsp v) (hν v)
  have hB : MeasurableSet {x : ι → Fin d → ℝ |
      ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => x v i.1) ∈ D c} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (show Measurable fun (x : ι → Fin d → ℝ) v (i : {i : Fin d // deg i = c}) => x v i.1 by
      fun_prop) (hD c)
  rw [← GlobalTheory.T.volume_product_over_grading_layers ι d m deg D hdeg hD]
  refine le_trans ?_ (hmp.measure_preimage hB.nullMeasurableSet).le
  refine iInf_le_of_le _ (iInf_le_of_le (hmp.measurable hB) (iInf_le_of_le ?_ le_rfl))
  intro x hx
  have key : ∀ k : ℕ, ∃ γ ∈ Γ, (∀ v, uMat ((γ * x) v) - 1 ∈ A v 0) ∧ ∀ c < k,
      (fun v (i : {i : Fin d // deg i = c}) => ipL (E v i.1) (uMat ((γ * x) v) - 1)) ∈ D c := by
    intro k
    induction k with
    | zero => exact ⟨1, Γ.one_mem, by simpa using hx, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
    | succ k ih =>
      obtain ⟨γ, hγ, h0, hc⟩ := ih
      obtain ⟨δ, hδ, hδk, hδD⟩ := hcov k fun v i => ipL (E v i.1) (uMat ((γ * x) v) - 1)
      have hexp : ∀ v, uMat ((δ * γ * x) v) - 1 = (uMat (δ v) - 1) + (uMat ((γ * x) v) - 1) +
          (uMat (δ v) - 1) * (uMat ((γ * x) v) - 1) := fun v => by
        rw [mul_assoc, Pi.mul_apply, mul_sub_one]
      have hprod : ∀ v, (uMat (δ v) - 1) * (uMat ((γ * x) v) - 1) ∈ A v (k + 1) := fun v =>
        (hmul v k _ (hδk v) _ (h0 v)).1
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, fun v => ?_, fun c hck => ?_⟩
      · rw [hexp]
        exact (A v 0).add_mem ((A v 0).add_mem (hΓ δ hδ v) (h0 v)) (hanti v (Nat.zero_le _) (hprod v))
      · rcases (Nat.lt_succ_iff.1 hck).lt_or_eq with h | rfl
        · convert hc c h using 1
          funext v i
          rw [hexp, map_add, map_add, horth v k i.1 (by rw [i.2]; exact h) _ (hδk v),
            horth v (k + 1) i.1 (by rw [i.2]; exact hck) _ (hprod v), zero_add, add_zero]
        · convert hδD using 1
          funext v i
          rw [hexp, map_add, map_add, horth v (c + 1) i.1 (by rw [i.2]; exact hck) _ (hprod v), add_zero]
          rfl
  obtain ⟨γ, hγ, -, hc⟩ := key m
  exact ⟨γ, hγ, hc⟩

end GlobalTheory.NilCov
