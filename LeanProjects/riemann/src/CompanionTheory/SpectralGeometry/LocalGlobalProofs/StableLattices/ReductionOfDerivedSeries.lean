import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuReduce

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_of_smOn_univ {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : E → V} (hf : SmOn Set.univ f) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro a
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a (Set.mem_univ a)
  refine (hF.contDiffAt (hU.mem_nhds haU)).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds haU] with g hg
  exact hfF g hg (Set.mem_univ g)

theorem cut_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U) {φ a : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiff ℝ ∞ (fun t => φ t * a t) ∧ HasCompactSupport (fun t => φ t * a t) ∧
      tsupport (fun t => φ t * a t) ⊆ U := by
  have h1 : tsupport (fun t => φ t * a t) ⊆ U := (tsupport_mul_subset_left (f := φ) (g := a)).trans hs
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hc.mul_right, h1⟩
  by_cases hx : x ∈ tsupport (fun t => φ t * a t)
  · exact hφ.contDiffAt.mul (ha.contDiffAt (hU.mem_nhds (h1 hx)))
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hx)

theorem cut_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (v : E) :
    ContDiff ℝ ∞ (fun t => fderiv ℝ φ t v) ∧ HasCompactSupport (fun t => fderiv ℝ φ t v) ∧
      tsupport (fun t => fderiv ℝ φ t v) ⊆ U :=
  ⟨(hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, hc.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans hs⟩

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem contDiff_orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : RepOn G σ) {w : H}
    (hw : IsSm G σ w) {W : List (Mat n)} (hW : LieW G W) {s : E → Mat n} (hs : ContDiff ℝ ∞ s)
    (hm : ∀ t, s t ∈ G) : ContDiff ℝ ∞ (fun t => dsW σ W (σ (s t) w)) := by
  have h1 := SmOn.comp (smOn_dsW h (u := fun x => σ x w) (hw.smOn_mul h) hW)
    (φ := fun t : E => ((1 : Mat n), s t)) (B := Set.univ) (contDiff_const.prodMk hs)
    fun t _ => ⟨h.one_mem, hm t⟩
  refine contDiff_of_smOn_univ (h1.congr fun x _ => ?_)
  simp [h.map_one]

theorem dsW_sum (h : RepOn G σ) {W : List (Mat n)} (hW : LieW G W) {ι : Type*} (c : ι → ℂ) (v : ι → H)
    (hv : ∀ i, IsSm G σ (v i)) (S : Finset ι) :
    IsSm G σ (∑ i ∈ S, c i • v i) ∧ dsW σ W (∑ i ∈ S, c i • v i) = ∑ i ∈ S, c i • dsW σ W (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using IsSm.zero, ?_⟩
    have := dsW_smul h (IsSm.zero (G := G) (σ := σ)) (0 : ℂ) hW
    simpa using this
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ⟨((hv i).smul _).add ih.1, by rw [dsW_add h ((hv i).smul _) ih.1 hW, dsW_smul h (hv i) _ hW, ih.2]⟩

theorem lieW_of {Hm : Mat n} {W : List (Mat n)} (hW : LieWd Hm W) : LieW (UH Hm) W :=
  fun X hX t => ex_mem_of_lie (hW X hX) t

theorem isSm_ds {Hm : Mat n} (h : RepOn (UH Hm) σ) {X : Mat n} (hX : Lie Hm X) {u : H} (hu : IsSm (UH Hm) σ u) :
    IsSm (UH Hm) σ (ds σ X u) :=
  hu.dsW h (W := [X]) (lieW_of fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX)

theorem dsW_append (W W' : List (Mat n)) (v : H) : dsW σ (W ++ W') v = dsW σ W (dsW σ W' v) :=
  List.foldr_append

theorem last_letter [CompleteSpace H] (hlin : DsLin) (had : DsAd) {Hm : Mat n} (hσ : URep Hm σ)
    {W : List (Mat n)} (hW : LieWd Hm W) {Y y : Mat n} (hY : Lie Hm Y) (hy : y ∈ UH Hm) {d e : ℕ}
    {Z : Fin d → Mat n} {Q : Fin e → Mat n} (hZ : ∀ j, Lie Hm (Z j)) (hQ : ∀ i, Lie Hm (Q i))
    {a : Fin d → ℝ} {b : Fin e → ℝ} (hab : y⁻¹ * Y * y = ∑ j, (a j : ℂ) • Z j + ∑ i, (b i : ℂ) • Q i)
    {u : H} (hu : IsSm (UH Hm) σ u) :
    dsW σ (W ++ [Y]) (σ y u) =
      ∑ j, a j • dsW σ W (σ y (ds σ (Z j) u)) + ∑ i, b i • dsW σ W (σ y (ds σ (Q i) u)) := by
  obtain ⟨h1, h2⟩ := had n Hm H σ hσ y hy [Y] (fun X hX => by rw [List.mem_singleton.1 hX]; exact hY)
  obtain ⟨Λ, hΛ⟩ := hlin n Hm H σ hσ u hu
  have h3 : Lie Hm (y⁻¹ * Y * y) := h1 _ (by simp)
  have h4 : ds σ (y⁻¹ * Y * y) u = ∑ j, (a j : ℂ) • ds σ (Z j) u + ∑ i, (b i : ℂ) • ds σ (Q i) u := by
    rw [hΛ _ h3, hab]
    simp only [Complex.coe_smul, map_add, map_sum, map_smul, hΛ _ (hZ _), hΛ _ (hQ _)]
  have h5 : dsW σ [Y] (σ y u) =
      ∑ j, (a j : ℂ) • σ y (ds σ (Z j) u) + ∑ i, (b i : ℂ) • σ y (ds σ (Q i) u) := by
    rw [h2 u hu]
    change σ y (ds σ (y⁻¹ * Y * y) u) = _
    rw [h4]
    simp only [map_add, map_sum, map_smul]
  have hA := dsW_sum hσ.rep (lieW_of hW) (fun j => (a j : ℂ)) (fun j => σ y (ds σ (Z j) u))
    (fun j => (isSm_ds hσ.rep (hZ j) hu).apply hσ.rep hy) Finset.univ
  have hB := dsW_sum hσ.rep (lieW_of hW) (fun j => (b j : ℂ)) (fun j => σ y (ds σ (Q j) u))
    (fun j => (isSm_ds hσ.rep (hQ j) hu).apply hσ.rep hy) Finset.univ
  rw [dsW_append, h5, dsW_add hσ.rep hA.1 hB.1 (lieW_of hW), hA.2, hB.2]
  simp only [Complex.coe_smul]

theorem fderiv_orbit [CompleteSpace H] (hder : DsDer) {Hm : Mat n} (hσ : URep Hm σ)
    {W : List (Mat n)} (hW : LieWd Hm W) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : E → Mat n}
    (hs : ContDiff ℝ ∞ s) (hm : ∀ t, s t ∈ UH Hm) {t v : E} {Z : Mat n} (hZ : Lie Hm Z)
    (hfl : ∀ τ : ℝ, s (t + τ • v) = s t * ex Z τ) {u : H} (hu : IsSm (UH Hm) σ u) :
    fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t v = dsW σ W (σ (s t) (ds σ Z u)) := by
  have h1 := contDiff_orbit hσ.rep hu (lieW_of hW) hs hm
  have h2 : HasLineDerivAt ℝ (fun t => dsW σ W (σ (s t) u)) (fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t v) t v :=
    (h1.differentiable (by simp) t).hasFDerivAt.hasLineDerivAt v
  have h3 : HasLineDerivAt ℝ (fun t => dsW σ W (σ (s t) u)) (dsW σ W (σ (s t) (ds σ Z u))) t v := by
    unfold HasLineDerivAt
    simp only [hfl]
    exact hder n Hm H σ hσ W hW (s t) (hm t) Z hZ u hu
  exact h2.unique h3

theorem integrable_cut {d : ℕ} {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    {f : (Fin d → ℝ) → H} (hf : Continuous f) : Integrable (fun t => ψ t • f t) :=
  (hψ.smul hf).integrable_of_hasCompactSupport hc.smul_right

theorem parts {d : ℕ} {ψ : (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {f : (Fin d → ℝ) → H} (hf : ContDiff ℝ ∞ f) (v : Fin d → ℝ) :
    ∫ t, ψ t • fderiv ℝ f t v = - ∫ t, fderiv ℝ ψ t v • f t := by
  obtain ⟨h1, h2, -⟩ := cut_fderiv hψ hc (Set.subset_univ _) v
  refine integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (integrable_cut h1.continuous h2 hf.continuous)
    (integrable_cut hψ.continuous hc ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))
    (integrable_cut hψ.continuous hc hf.continuous) (fun x _ => hψ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)

theorem reduce : DsLin → DsAd → DsDer → Reduce := by
  intro hlin had hder n Hm H _ _ _ σ hσ d e Q s U hch W
  simp only [Complex.coe_smul]
  induction W using List.reverseRecOn with
  | nil =>
    intro _ φ hφ hc _
    refine ⟨∫ t, ‖φ t‖, integral_nonneg fun t => norm_nonneg _, fun u _ R hR => ?_⟩
    have hu : ‖u‖ ≤ R := hR [] le_rfl
    refine (norm_integral_le_integral_norm _).trans ?_
    have : ∀ t, ‖φ t • dsW σ [] (σ (s t) u)‖ = ‖φ t‖ * ‖u‖ := fun t => by
      rw [norm_smul]
      exact congrArg _ (hσ.iso _ (hch.mem t) u)
    simp only [this]
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_left hu (integral_nonneg fun t => norm_nonneg _)
  | append_singleton W Y ih =>
    intro hWY φ hφ hc hs
    have hW : LieWd Hm W := fun X hX => hWY X (List.mem_append_left _ hX)
    have hY : Lie Hm Y := hWY Y (by simp)
    obtain ⟨Z, hZ, hfl, hsp⟩ := hch.flow
    obtain ⟨a, b, ha, hb, hab⟩ := hsp Y hY
    have hA := fun j => cut_mul hch.isOpen hφ hc hs (ha j)
    have hB := fun i => cut_mul hch.isOpen hφ hc hs (hb i)
    have hA' := fun j => cut_fderiv (hA j).1 (hA j).2.1 (hA j).2.2 (Pi.single j 1)
    choose C hC0 hC using fun j => ih hW _ (hA' j).1 (hA' j).2.1 (hA' j).2.2
    choose D hD0 hD using fun i => ih hW _ (hB i).1 (hB i).2.1 (hB i).2.2
    refine ⟨∑ j, C j + ∑ i, D i, add_nonneg (Finset.sum_nonneg fun j _ => hC0 j)
      (Finset.sum_nonneg fun j _ => hD0 j), fun u hu R hR => ?_⟩
    have hf := contDiff_orbit hσ.rep hu (lieW_of hW) hch.smooth hch.mem
    have hg := fun i => contDiff_orbit hσ.rep (isSm_ds hσ.rep (hch.lieQ i) hu) (lieW_of hW) hch.smooth hch.mem
    have hpt : ∀ t, φ t • dsW σ (W ++ [Y]) (σ (s t) u) =
        ∑ j, (φ t * a j t) • fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t (Pi.single j 1) +
          ∑ i, (φ t * b i t) • dsW σ W (σ (s t) (ds σ (Q i) u)) := fun t => by
      by_cases ht : t ∈ tsupport φ
      · rw [last_letter hlin had hσ hW hY (hch.mem t) (fun j => hZ j t) hch.lieQ (hab t (hs ht)) hu]
        simp only [fun j => fderiv_orbit hder hσ hW hch.smooth hch.mem (hZ j t) (hfl j t) hu,
          smul_add, Finset.smul_sum, smul_smul]
      · simp [image_eq_zero_of_notMem_tsupport ht]
    have iA : ∀ j, Integrable fun t =>
        (φ t * a j t) • fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t (Pi.single j 1) := fun j =>
      integrable_cut (hA j).1.continuous (hA j).2.1
        ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
    have iB : ∀ i, Integrable fun t => (φ t * b i t) • dsW σ W (σ (s t) (ds σ (Q i) u)) := fun i =>
      integrable_cut (hB i).1.continuous (hB i).2.1 (hg i).continuous
    simp only [hpt]
    rw [integral_add (integrable_finset_sum _ fun j _ => iA j) (integrable_finset_sum _ fun j _ => iB j),
      integral_finset_sum _ fun j _ => iA j, integral_finset_sum _ fun j _ => iB j, add_mul, Finset.sum_mul,
      Finset.sum_mul]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)))
    · rw [parts (hA j).1 (hA j).2.1 hf, norm_neg]
      exact hC j u hu R fun P hP => hR P (by simp; omega)
    · refine hD i _ (isSm_ds hσ.rep (hch.lieQ i) hu) R fun P hP => ?_
      have := hR (P ++ [i]) (by simp; omega)
      rwa [List.map_append, dsW_append] at this

end GlobalTheory.CompanionTheory.BmuReduce

end
