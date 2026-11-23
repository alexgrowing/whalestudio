import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.BesselIsometryScalar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmoothA

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down.ScaleMoveB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Mult1.SmoothA

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_mul {σ : Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (GV k r) σ) {t : Mat k r}
    (ht : t ∈ GV k r) {v : H} (hv : v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ) :
    σ t v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ := by
  have hv' : SmoothOnH (Hpk k r) (fun g => σ g v) := hv
  show SmoothOnH (Hpk k r) (fun g => σ g (σ t v))
  intro g₀ hg₀
  have hg₀t : inUH (Hpk k r) (g₀ * t) := gv_mul hg₀ ht
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv' (g₀ * t) hg₀t
  let R : Mat k r →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ t)
  have hR : ∀ g, R g = g * t := fun g => rfl
  refine ⟨R ⁻¹' U, F ∘ R, hU.preimage R.continuous, by simpa [hR] using hgU,
    hF.comp R.contDiff.contDiffOn (fun g hg => hg), fun g hg hgH => ?_⟩
  have hgH' : g ∈ GV k r := hgH
  simp only [Function.comp, hR]
  rw [← hFe (g * t) hg (gv_mul hgH' ht)]
  show σ g (σ t v) = σ (g * t) v
  rw [hσ.1.2 g hgH' t ht]
  rfl

end sm

theorem lie_conj {t X : Mat k r} (ht : t ∈ GV k r) (hX : Formalism.MainNotions.S.InLieHpk k r X) :
    Formalism.MainNotions.S.InLieHpk k r (t⁻¹ * X * t) := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hh : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hpk_sq, Matrix.one_mul]
  have key : (t⁻¹ * X * t)ᴴ * Hpk k r + Hpk k r * (t⁻¹ * X * t) = tᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * t := by
    rw [gv_inv_eq ht]
    simp only [conjTranspose_mul, hpk_conjT, conjTranspose_conjTranspose, Matrix.mul_assoc, hpk_sq,
      Matrix.mul_one, hh, Matrix.add_mul, Matrix.mul_add]
  show (t⁻¹ * X * t)ᴴ * Hpk k r + Hpk k r * (t⁻¹ * X * t) = 0
  rw [key, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem dsig_conj {σ : Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (GV k r) σ) {t : Mat k r}
    (ht : t ∈ GV k r) {X : Mat k r} (hX : Formalism.MainNotions.S.InLieHpk k r X) (u : H) :
    Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (σ t u) = σ t (Formalism.MainNotions.S.dsig (k := k) (r := r) σ (t⁻¹ * X * t) u) := by
  have hti := gv_inv_mem ht
  have hu : IsUnit t := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (gv_mul_inv ht))
  have hfun : (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (σ t u)) =
      fun s : ℝ => σ t (σ (NormedSpace.exp ((s : ℂ) • (t⁻¹ * X * t))) u) := by
    funext s
    have hE : NormedSpace.exp ((s : ℂ) • X) ∈ GV k r := by rw [cast_smul]; exact exp_mem hX s
    have hconj : (s : ℂ) • (t⁻¹ * X * t) = t⁻¹ * ((s : ℂ) • X) * t := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hconj, Matrix.exp_conj' _ _ hu]
    have h1 : σ (NormedSpace.exp ((s : ℂ) • X)) (σ t u) = σ (NormedSpace.exp ((s : ℂ) • X) * t) u := by
      rw [hσ.1.2 _ hE _ ht]; rfl
    have h2 : σ t (σ (t⁻¹ * NormedSpace.exp ((s : ℂ) • X) * t) u) =
        σ (t * (t⁻¹ * NormedSpace.exp ((s : ℂ) • X) * t)) u := by
      rw [hσ.1.2 _ ht _ (gv_mul (gv_mul hti hE) ht)]; rfl
    rw [h1, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gv_mul_inv ht, Matrix.one_mul]
  unfold Formalism.MainNotions.S.dsig
  rw [hfun]
  set f := fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • (t⁻¹ * X * t))) u with hf
  by_cases hd : DifferentiableAt ℝ f 0
  · exact (((σ t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt).deriv
  · have hnd : ¬ DifferentiableAt ℝ (fun s => σ t (f s)) 0 := by
      intro hd'
      apply hd
      have hinv : ∀ y : H, σ t⁻¹ (σ t y) = y := fun y => by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hti _ ht, gv_inv_mul ht, hσ.1.1]; rfl
      have : f = fun s => σ t⁻¹ (σ t (f s)) := by funext s; rw [hinv]
      rw [this]
      exact ((σ t⁻¹).restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd'
    rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd, map_zero]

theorem dsigW_conj {σ : Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (GV k r) σ) {t : Mat k r}
    (ht : t ∈ GV k r) : ∀ (ws : List (Mat k r)), (∀ X ∈ ws, Formalism.MainNotions.S.InLieHpk k r X) → ∀ u : H,
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ ws (σ t u) =
      σ t (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (ws.map fun X => t⁻¹ * X * t) u)
  | [], _, u => rfl
  | X :: w, hw, u => by
    simp only [Formalism.MainNotions.S.dsigW, List.map_cons]
    rw [dsigW_conj hσ ht w (fun Y hY => hw Y (List.mem_cons_of_mem X hY)) u,
      dsig_conj hσ ht (hw X List.mem_cons_self)]

theorem cw_transport {Wp : Type} [NormedAddCommGroup Wp] {σ : Mat k r → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (GV k r) σ) {t : Mat k r} (ht : t ∈ GV k r) {B : H → Wp}
    (hB : Formalism.MainNotions.S.IsCWCont (k := k) (r := r) σ B) :
    Formalism.MainNotions.S.IsCWCont (k := k) (r := r) σ (fun v => B (σ t v)) := by
  obtain ⟨C, Ws, hWs, hb⟩ := hB
  refine ⟨C, Ws.map (List.map fun X => t⁻¹ * X * t), ?_, fun v hv => ?_⟩
  · intro w hw X hX
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
    obtain ⟨X0, hX0, rfl⟩ := List.mem_map.1 hX
    exact lie_conj ht (hWs w0 hw0 X0 hX0)
  · refine (hb (σ t v) (smooth_mul hσ ht hv)).trans (le_of_eq ?_)
    congr 1
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro w hw
    simp only [Function.comp]
    rw [dsigW_conj hσ ht w (hWs w hw), hσ.2.1 t ht]

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down.ScaleMoveB
