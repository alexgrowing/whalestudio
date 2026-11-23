import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.StepLoc

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem kset_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  have h1 : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hg.1
    simpa [Matrix.star_eq_conjTranspose] using this
  unfold inUJ
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

theorem inG_conj {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) :
    inG ε (g * X * gᴴ) := by
  have h2 : gᴴ * Jm ε = Jm ε * gᴴ := by
    have := congrArg Matrix.conjTranspose hg.2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at this
    exact this.symm
  unfold inG at *
  calc (g * X * gᴴ)ᴴ * Jm ε + Jm ε * (g * X * gᴴ)
      = g * Xᴴ * (gᴴ * Jm ε) + (Jm ε * g) * X * gᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = g * (Xᴴ * Jm ε + Jm ε * X) * gᴴ := by
        rw [h2, ← hg.2]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX]; simp

theorem exp_conj_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    NormedSpace.exp (t • (g * X * gᴴ)) * g = g * NormedSpace.exp (t • X) := by
  have h1 : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hg
    simpa [Matrix.star_eq_conjTranspose] using this
  have hi : g⁻¹ = gᴴ := Matrix.inv_eq_left_inv h1
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse h1)
  have : t • (g * X * gᴴ) = g * (t • X) * g⁻¹ := by
    rw [hi]; simp
  rw [this, Matrix.exp_conj _ _ hu, hi, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem orbit_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) (w : H) :
    orbit σ (g * X * gᴴ) (σ g w) = fun t => σ g (orbit σ X w t) := by
  funext t
  have a1 := hσ.2 _ (exp_indefinite_unitary_holds n ε _ (inG_conj hg hX) t) g (kset_inUJ hg)
  have a2 := hσ.2 g (kset_inUJ hg) _ (exp_indefinite_unitary_holds n ε _ hX t)
  rw [exp_conj_mul hg.1, a2] at a1
  exact (congrArg (fun T : H →L[ℂ] H => T w) a1).symm

theorem dAct_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) {w : H}
    (hw : DifferentiableAt ℝ (orbit σ X w) 0) :
    dAct σ (g * X * gᴴ) (σ g w) = σ g (dAct σ X w) := by
  unfold dAct
  rw [orbit_conj hσ hg hX]
  exact (((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw.hasDerivAt).deriv

theorem dAct_add_smul {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {X : Matrix (Fin n) (Fin n) ℂ}
    {w w' : H} (hw : DifferentiableAt ℝ (orbit σ X w) 0) (hw' : DifferentiableAt ℝ (orbit σ X w') 0)
    (c : ℂ) : dAct σ X (w + c • w') = dAct σ X w + c • dAct σ X w' := by
  have : orbit σ X (w + c • w') = fun t => orbit σ X w t + c • orbit σ X w' t := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  exact (hw.hasDerivAt.fun_add (hw'.hasDerivAt.fun_const_smul c)).deriv

theorem dAct_zero (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) :
    dAct σ X 0 = 0 := by
  have : orbit σ X 0 = fun _ => 0 := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  simp

theorem lowKSub_stable (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv
  have : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) := by
    refine sSup_le fun S hS => ?_
    intro x hx
    exact (le_sSup hS : S ≤ lowKSub ε lam σ) (hS.2.1 g hg x hx)
  exact this hv

theorem dWord_mem {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {P : ℕ} {l : List (Matrix (Fin n) (Fin n) ℂ)} {u : H} (hl : l.length ≤ P) (hX : ∀ X ∈ l, inG ε X)
    (hu : u ∈ lowKSub ε lam σ) : dWord σ l u ∈ stepSpace ε lam σ P :=
  Submodule.subset_span ⟨l, u, hl, hX, hu, rfl⟩

theorem dWord_conj {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) (hd : ∀ P, ∀ w ∈ stepSpace ε lam σ P, IsDiffVec ε σ w)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) {u : H} (hu : u ∈ lowKSub ε lam σ)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hX : ∀ X ∈ l, inG ε X) :
    σ g (dWord σ l u) = dWord σ (l.map fun X => g * X * gᴴ) (σ g u) := by
  induction l with
  | nil => rfl
  | cons Y l ih =>
    have hl : ∀ X ∈ l, inG ε X := fun X h => hX X (List.mem_cons_of_mem _ h)
    have hY : inG ε Y := hX Y List.mem_cons_self
    change σ g (dAct σ Y (dWord σ l u)) =
      dAct σ (g * Y * gᴴ) (dWord σ (l.map fun X => g * X * gᴴ) (σ g u))
    rw [← ih hl, dAct_conj hσ hg hY (hd _ _ (dWord_mem le_rfl hl hu) Y hY)]

theorem stepSpace_props : GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.StepBound → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsHCParam lam → IsDS ε lam σ → ∀ P : ℕ, FiniteDimensional ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ IsKStableOn ε σ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ (∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X w) (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w) 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ (P + 1)) ∧ ∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ w' ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ c : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (w + c • w') = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w + c • GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w' := by
  intro hSB n ε H _ _ _ σ lam hlam hDS P
  have hb : ∀ a, |lam a| ≤ Real.sqrt (∑ a, |lam a|) ^ 2 := by
    intro a
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    exact Finset.single_le_sum (f := fun a => |lam a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hd : ∀ P, ∀ w ∈ stepSpace ε lam σ P, IsDiffVec ε σ w := fun P =>
    (hSB n ε lam H σ _ P hlam hDS hb).2.1
  have hσ : IsCRepOn (UJset ε) σ := hDS.2.2.1.1
  refine ⟨(hSB n ε lam H σ _ P hlam hDS hb).1, ?_, fun X hX w hw => ⟨(hd P w hw X hX).hasDerivAt, ?_⟩,
    fun X hX w hw w' hw' c => dAct_add_smul (hd P w hw X hX) (hd P w' hw' X hX) c⟩
  · intro g hg v hv
    have : stepSpace ε lam σ P ≤ (stepSpace ε lam σ P).comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, u, hl, hX, hu, rfl⟩
      change σ g (dWord σ l u) ∈ stepSpace ε lam σ P
      rw [dWord_conj hσ hd hg hu l hX]
      refine dWord_mem (by simpa using hl) ?_ (lowKSub_stable ε lam σ g hg u hu)
      intro Y hY
      obtain ⟨X, hXl, rfl⟩ := List.mem_map.mp hY
      exact inG_conj hg (hX X hXl)
    exact this hv
  · induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, u, hl, hl', hu, rfl⟩ := hv
      refine dWord_mem (l := X :: l) (by simpa using hl) ?_ hu
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | h
      · exact hX
      · exact hl' Y h
    | zero => rw [dAct_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have := dAct_add_smul (hd P x hx X hX) (hd P y hy X hX) 1
      rw [one_smul, one_smul] at this
      rw [this]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      have := dAct_add_smul (hd P 0 (Submodule.zero_mem _) X hX) (hd P x hx X hX) c
      rw [zero_add, dAct_zero, zero_add] at this
      rw [this]
      exact Submodule.smul_mem _ c ihx

end GlobalTheory.StepLoc
