import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplexStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DbarSolveComplexTorusStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodicCechCocycleSmoothCoboundaryStatement
open Complex Matrix
open scoped ContDiff BigOperators Real Topology

namespace GlobalTheory.PeriodicCousin

variable {g : ℕ}

noncomputable def dbar (a : Fin g) (f : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) : ℂ :=
  fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))

theorem dbar_congr {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : f =ᶠ[𝓝 z] f') :
    dbar a f z = dbar a f' z := by
  unfold dbar; rw [h.fderiv_eq]

theorem dbar_sub {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z) :
    dbar a (fun x => f x - f' x) z = dbar a f z - dbar a f' z := by
  unfold dbar
  rw [fderiv_fun_sub h h']
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem contDiffAt_fderiv {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fderiv ℝ f) z :=
  h.fderiv_right (m := ∞) (by norm_cast)

theorem contDiffAt_dbar {a : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (dbar a f) z := by
  have h1 := contDiffAt_fderiv h
  exact (h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))

theorem fderiv_dbar {a : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) (v : Fin g → ℂ) :
    fderiv ℝ (dbar a f) z v = fderiv ℝ (fderiv ℝ f) z v (Pi.single a 1 : Fin g → ℂ) +
      I * fderiv ℝ (fderiv ℝ f) z v (I • (Pi.single a 1 : Fin g → ℂ)) := by
  have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((contDiffAt_fderiv h).differentiableAt (by simp)).hasFDerivAt
  have h2 := fun u : Fin g → ℂ =>
    (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp z h1
  have h3 := (h2 (Pi.single a 1)).add ((h2 (I • (Pi.single a 1 : Fin g → ℂ))).const_mul I)
  have h4 : fderiv ℝ (dbar a f) z = _ := h3.fderiv
  rw [h4]
  simp

theorem dbar_comm {a b : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) : dbar a (dbar b f) z = dbar b (dbar a f) z := by
  have hs : IsSymmSndFDerivAt ℝ f z := h.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have e : ∀ u v, fderiv ℝ (fderiv ℝ f) z u v = fderiv ℝ (fderiv ℝ f) z v u := hs
  show fderiv ℝ (dbar b f) z _ + I * fderiv ℝ (dbar b f) z _ =
    fderiv ℝ (dbar a f) z _ + I * fderiv ℝ (dbar a f) z _
  rw [fderiv_dbar h, fderiv_dbar h, fderiv_dbar h, fderiv_dbar h,
    e (Pi.single b 1) (Pi.single a 1), e (Pi.single b 1) (I • (Pi.single a 1 : Fin g → ℂ)),
    e (I • (Pi.single b 1 : Fin g → ℂ)) (Pi.single a 1),
    e (I • (Pi.single b 1 : Fin g → ℂ)) (I • (Pi.single a 1 : Fin g → ℂ))]
  ring

noncomputable def antilin (t : Fin g → ℂ) : (Fin g → ℂ) →L[ℝ] ℂ :=
  ∑ a, t a • ((conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj a))

theorem antilin_apply (t z : Fin g → ℂ) : antilin t z = t ⬝ᵥ star z := by
  simp [antilin, dotProduct]

theorem dbar_antilin (t z : Fin g → ℂ) (a : Fin g) : dbar a (antilin t) z = 2 * t a := by
  unfold dbar
  rw [ContinuousLinearMap.fderiv, antilin_apply, antilin_apply]
  have h1 : star (Pi.single a 1 : Fin g → ℂ) = Pi.single a 1 := by
    ext j; by_cases h : j = a
    · subst h; simp
    · simp [h]
  rw [star_smul, h1]
  simp only [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, star_def, conj_I]
  linear_combination (-t a) * I_mul_I

end GlobalTheory.PeriodicCousin

namespace GlobalTheory
open PeriodicCousin

theorem holomorphic_periodic_cocycle_coboundary : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i j, DifferentiableOn ℂ (c i j) (U i ∩ U j)) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, c i j (z + l) = c i j z) → (∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z = c i k z) → ∃ (t : (Fin g → ℂ)) (h : ι → (Fin g → ℂ) → ℂ), (∀ i, DifferentiableOn ℂ (h i) (U i) ∧ ∀ (l : Λ), ∀ z ∈ U i, h i (z + l) = h i z + t ⬝ᵥ star (l : (Fin g → ℂ))) ∧ ∀ i j, ∀ z ∈ U i ∩ U j, c i j z = h j z - h i z := by
  intro g Λ hd hs ι U c hU hUΛ hcov hc hcΛ hcoc
  have hcs : ∀ i j, ContDiffOn ℝ ∞ (c i j) (U i ∩ U j) := fun i j =>
    ((GlobalTheory.T.cauchyRiemann_iff_differentiableOn g _ (c i j) ((hU i).inter (hU j))).2 (hc i j)).1
  obtain ⟨b, hb, hcb⟩ := GlobalTheory.T.exists_periodic_smooth_coboundary_of_cech_cocycle g Λ hd hs ι U c hU hUΛ hcov hcs hcΛ hcoc
  choose k hk using hcov
  have hbAt : ∀ i, ∀ z ∈ U i, ContDiffAt ℝ ∞ (b i) z := fun i z hz =>
    (hb i).1.contDiffAt ((hU i).mem_nhds hz)
  have hind : ∀ a i j, ∀ z ∈ U i, z ∈ U j → dbar a (b j) z = dbar a (b i) z := by
    intro a i j z hi hj
    have ho := (hU i).inter (hU j)
    have h0 : dbar a (c i j) z = 0 :=
      ((GlobalTheory.T.cauchyRiemann_iff_differentiableOn g _ (c i j) ho).1 ((hcs i j).differentiableOn (by simp))).2 (hc i j) a z ⟨hi, hj⟩
    have h1 : c i j =ᶠ[𝓝 z] fun x => b j x - b i x := by
      filter_upwards [ho.mem_nhds ⟨hi, hj⟩] with x hx using hcb i j x hx
    rw [dbar_congr h1, dbar_sub ((hbAt j z hj).differentiableAt (by simp))
      ((hbAt i z hi).differentiableAt (by simp))] at h0
    exact sub_eq_zero.1 h0
  let w : Fin g → (Fin g → ℂ) → ℂ := fun a z => dbar a (b (k z)) z
  have hw : ∀ a i, ∀ z ∈ U i, w a z = dbar a (b i) z := fun a i z hz => hind a i (k z) z hz (hk z)
  have hw' : ∀ a i, ∀ z ∈ U i, w a =ᶠ[𝓝 z] dbar a (b i) := by
    intro a i z hz
    filter_upwards [(hU i).mem_nhds hz] with x hx using hw a i x hx
  obtain ⟨t, f, hf, hfΛ, hft⟩ := GlobalTheory.T.exists_periodic_dbar_solution g Λ hd hs w (by
    intro a
    refine ⟨contDiff_iff_contDiffAt.2 fun z =>
      (contDiffAt_dbar (hbAt _ z (hk z))).congr_of_eventuallyEq (hw' a _ z (hk z)), fun l z => ?_⟩
    rw [hw a (k z) _ (hUΛ _ l z (hk z)), hw a (k z) z (hk z)]
    have h1 : (fun x => b (k z) (x + l)) =ᶠ[𝓝 z] b (k z) := by
      filter_upwards [(hU _).mem_nhds (hk z)] with x hx using (hb _).2 l x hx
    rw [← dbar_congr h1]
    unfold dbar
    rw [fderiv_comp_add_right]) (by
    intro a a' z
    show dbar a (w a') z = dbar a' (w a) z
    rw [dbar_congr (hw' a' _ z (hk z)), dbar_congr (hw' a _ z (hk z))]
    exact dbar_comm (hbAt _ z (hk z)))
  have hfd : ∀ z, DifferentiableAt ℝ f z := fun z => (hf.differentiable (by simp)) z
  refine ⟨-((1 / 2 : ℂ) • t), fun i z => b i z - f z - antilin ((1 / 2 : ℂ) • t) z,
    fun i => ⟨?_, ?_⟩, ?_⟩
  · have hbd : ∀ z ∈ U i, DifferentiableAt ℝ (b i) z := fun z hz =>
      (hbAt i z hz).differentiableAt (by simp)
    refine ((GlobalTheory.T.cauchyRiemann_iff_differentiableOn g _ _ (hU i)).1 ?_).1 ?_
    · intro z hz
      exact (((hbd z hz).sub (hfd z)).sub (antilin _).differentiableAt).differentiableWithinAt
    · intro a z hz
      show dbar a (fun z => (b i z - f z) - antilin ((1 / 2 : ℂ) • t) z) z = 0
      have h3 : dbar a f z = w a z - t a := hft a z
      rw [dbar_sub ((hbd z hz).fun_sub (hfd z)) (antilin _).differentiableAt,
        dbar_sub (hbd z hz) (hfd z), dbar_antilin, h3, hw a i z hz]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · intro l z hz
    simp only [(hb i).2 l z hz, hfΛ l z, map_add, antilin_apply _ (l : Fin g → ℂ), neg_dotProduct]
    ring
  · intro i j z hz
    rw [hcb i j z hz]
    ring

end GlobalTheory
