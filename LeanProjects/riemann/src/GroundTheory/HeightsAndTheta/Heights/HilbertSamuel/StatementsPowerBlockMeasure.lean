import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def PowerBlockMeasure.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (m N D : ℕ) (v : Fin N → Ω) (B : HermLine (addIdx ι N))
    (J : Ideal (MRing (addIdx ι N))) (R : AnRes (mCoordIdeal (addBlock y v)) J D) [MeasurableSpace R.X]
    [BorelSpace R.X] (dV : Measure R.X),
    IsSmoothHerm A → IsSmoothHerm B → B.a = unitDeg (none : Option K) → IsSmoothVolume R.A dV →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    ∃ μ : Measure ((Σ k, ι k) → ℂ), IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧
      IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      ∀ (q : ℕ) (F : MRing (addIdx ι N)), IsMultiHomog F (blockDeg (none : Option K) q) →
        sectionL2Norm μ y A (m * q) (aeval (addBlock y v) F) =
          Real.sqrt ((1 / 2) *
            ((∫ x, (‖eval (R.lift x x) (map (Int.castRingHom ℂ) F)‖ / B.h (R.lift x x) ^ q) ^ 2 ∂dV) +
              ∫ x, (‖eval (conjPt (R.lift x x)) (map (Int.castRingHom ℂ) F)‖ /
                B.h (conjPt (R.lift x x)) ^ q) ^ 2 ∂dV))

namespace PowerBlockDiag

open ProjLine PowerBlockProjectiveLine

def diagIdx : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → Ix (Fin 2)
  | ⟨none, j⟩ => ⟨(), j⟩
  | ⟨some _, i⟩ => ⟨(), i⟩

def oldIdx (p : Ix (Fin 2)) : Σ k, addIdx (GlobalTheory (Fin 2)) 2 k := ⟨some p.1, p.2⟩

def diagPt (w : Ix (Fin 2) → ℂ) : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ := fun p => w (diagIdx p)

theorem addBlock_apply (p : Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) : addBlock y projectiveLineCoordinates p = y (diagIdx p) := by
  rcases p with ⟨_ | _, i⟩ <;> rfl

theorem rename_diag_mem {f : MRing (addIdx (GlobalTheory (Fin 2)) 2)} (hf : f ∈ mCoordIdeal (addBlock y projectiveLineCoordinates)) :
    rename diagIdx f ∈ mCoordIdeal (ι := GlobalTheory (Fin 2)) y := by
  have key : (mConeMap (ι := GlobalTheory (Fin 2)) y).comp (rename diagIdx) =
      ((rename (fun _ : Option Unit => ())).restrictScalars ℤ).comp (mConeMap (addBlock y projectiveLineCoordinates)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, addBlock_apply]
  have h := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at h
  show mConeMap y (rename diagIdx f) = 0
  rw [h]
  have : mConeMap (addBlock y projectiveLineCoordinates) f = 0 := hf
  rw [this, map_zero]

theorem rename_old_mem {f : MRing (GlobalTheory (Fin 2))} (hf : f ∈ mCoordIdeal (ι := GlobalTheory (Fin 2)) y) :
    rename oldIdx f ∈ mCoordIdeal (addBlock y projectiveLineCoordinates) := by
  have key : (mConeMap (addBlock y projectiveLineCoordinates)).comp (rename oldIdx) =
      ((rename (some : Unit → Option Unit)).restrictScalars ℤ).comp (mConeMap (ι := GlobalTheory (Fin 2)) y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, oldIdx, addBlock]
  have h := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at h
  show mConeMap (addBlock y projectiveLineCoordinates) (rename oldIdx f) = 0
  rw [h]
  have : mConeMap (ι := GlobalTheory (Fin 2)) y f = 0 := hf
  rw [this, map_zero]

theorem eval_diagPt (w : Ix (Fin 2) → ℂ) (f : MRing (addIdx (GlobalTheory (Fin 2)) 2)) :
    eval (diagPt w) (map (Int.castRingHom ℂ) f) = eval w (map (Int.castRingHom ℂ) (rename diagIdx f)) := by
  rw [map_rename, eval_rename]
  rfl

theorem eval_oldPart (z : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ) (f : MRing (GlobalTheory (Fin 2))) :
    eval (basePart₂ z) (map (Int.castRingHom ℂ) f) = eval z (map (Int.castRingHom ℂ) (rename oldIdx f)) := by
  rw [map_rename, eval_rename]
  rfl

theorem diagPt_mem {w : Ix (Fin 2) → ℂ} (hw : w ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y)) :
    diagPt w ∈ mcPts (mCoordIdeal (addBlock y projectiveLineCoordinates)) := by
  obtain ⟨hnz, hvan⟩ := hw
  obtain ⟨i, hi⟩ := hnz ()
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · rcases k with _ | _
    · exact ⟨i, hi⟩
    · exact ⟨i, hi⟩
  · rw [eval_diagPt]
    exact hvan _ (rename_diag_mem hf)

theorem oldPart_mem {z : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y projectiveLineCoordinates))) :
    basePart₂ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) := by
  obtain ⟨hnz, hvan⟩ := hz
  refine ⟨fun _ => hnz (some ()), fun f hf => ?_⟩
  rw [eval_oldPart]
  exact hvan _ (rename_old_mem hf)

theorem graph_pt {z : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y projectiveLineCoordinates))) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ j : Fin 2, z ⟨none, j⟩ = lam * z ⟨some (), j⟩ := by
  obtain ⟨hnz, hvan⟩ := hz
  have hF := hvan _ minor_mem
  simp only [map_sub, map_mul, map_X, eval_X] at hF
  have ha : z ⟨some (), (0 : Fin 2)⟩ ≠ 0 ∨ z ⟨some (), (1 : Fin 2)⟩ ≠ 0 := by
    obtain ⟨i, hi⟩ := hnz (some ())
    change Fin 2 at i
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  obtain ⟨lam, h0, h1⟩ : ∃ lam : ℂ, z ⟨none, (0 : Fin 2)⟩ = lam * z ⟨some (), (0 : Fin 2)⟩ ∧
      z ⟨none, (1 : Fin 2)⟩ = lam * z ⟨some (), (1 : Fin 2)⟩ := by
    rcases ha with ha | ha
    · refine ⟨z ⟨none, (0 : Fin 2)⟩ / z ⟨some (), (0 : Fin 2)⟩, by field_simp, ?_⟩
      field_simp
      linear_combination hF
    · refine ⟨z ⟨none, (1 : Fin 2)⟩ / z ⟨some (), (1 : Fin 2)⟩, ?_, by field_simp⟩
      field_simp
      linear_combination -hF
  refine ⟨lam, ?_, fun j => ?_⟩
  · rintro rfl
    obtain ⟨i, hi⟩ := hnz none
    change Fin 2 at i
    fin_cases i
    · exact hi (by simpa using h0)
    · exact hi (by simpa using h1)
  · fin_cases j
    · exact h0
    · exact h1

abbrev JD : Ideal (MRing (addIdx (GlobalTheory (Fin 2)) 2)) := Ideal.span {X ⟨some (), (0 : Fin 2)⟩}

theorem mem_JD_iff (z : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ) :
    z ∈ mcPts JD ↔ (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ z ⟨some (), (0 : Fin 2)⟩ = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := h2 _ (Ideal.subset_span rfl)
    simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun f hf => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    simp [h2]

theorem JD_homog : IsMultiHomogIdeal JD := by
  refine ⟨{(X ⟨some (), (0 : Fin 2)⟩ : MRing (addIdx (GlobalTheory (Fin 2)) 2))}, fun f hf => ?_, rfl⟩
  rw [Set.mem_singleton_iff.mp hf]
  exact ⟨_, isMultiHomog_X _⟩

def liftD (x x' : projectiveLineMultiHomogResolution.X) : (Σ k, addIdx (GlobalTheory (Fin 2)) 2 k) → ℂ := diagPt (projectiveLineMultiHomogResolution.lift x x')

theorem liftD_mem (x x' : projectiveLineMultiHomogResolution.X) (hx' : x' ∈ projectiveLineMultiHomogResolution.U x) :
    liftD x x' ∈ mcPts (mCoordIdeal (addBlock y projectiveLineCoordinates)) :=
  diagPt_mem (projectiveLineMultiHomogResolution.mem x x' hx')

def resDiag : AnRes (mCoordIdeal (addBlock y projectiveLineCoordinates)) JD 1 where
  homog := JD_homog
  nondeg := by
    intro h
    apply projectiveLineMultiHomogResolution.nondeg
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have := rename_diag_mem (h (Ideal.subset_span rfl))
    simpa [diagIdx, Xc] using this
  X := projectiveLineMultiHomogResolution.X
  A := projectiveLineMultiHomogResolution.A
  U := projectiveLineMultiHomogResolution.U
  isOpen_U := projectiveLineMultiHomogResolution.isOpen_U
  mem_U := projectiveLineMultiHomogResolution.mem_U
  lift := liftD
  holo := fun x p => projectiveLineMultiHomogResolution.holo x (diagIdx p)
  mem := liftD_mem
  compat := fun x x' z hz => by
    obtain ⟨c, hc, h⟩ := projectiveLineMultiHomogResolution.compat x x' z hz
    exact ⟨fun _ => c (), fun _ => hc (), funext fun p => congrFun h (diagIdx p)⟩
  surj := fun z hz hzJ => by
    have ho := oldPart_mem hz
    have hoJ : basePart₂ z ∉ mcPts ProjectiveLineResolution.JJ := fun h =>
      hzJ ((mem_JD_iff z).2 ⟨hz.1, ((ProjectiveLineResolution.mem_J_iff _).1 h).2⟩)
    obtain ⟨x, c, hc, hx⟩ := projectiveLineMultiHomogResolution.surj _ ho hoJ
    obtain ⟨lam, hlam, hnew⟩ := graph_pt hz
    refine ⟨x, fun k => Option.elim k (c () / lam) (fun _ => c ()), ?_, ?_⟩
    · rintro (_ | _)
      · exact div_ne_zero (hc ()) hlam
      · exact hc ()
    · funext p
      rcases p with ⟨_ | _, i⟩
      · change projectiveLineMultiHomogResolution.lift x x ⟨(), i⟩ = c () / lam * z ⟨none, i⟩
        rw [hx, hnew i]
        field_simp
        rfl
      · change projectiveLineMultiHomogResolution.lift x x ⟨(), i⟩ = c () * z ⟨some (), i⟩
        rw [hx]
        rfl
  inj := fun x x' hx h => by
    apply projectiveLineMultiHomogResolution.inj x x'
    · intro hJ
      exact hx ((mem_JD_iff _).2 ⟨(liftD_mem x x (projectiveLineMultiHomogResolution.mem_U x)).1, ((ProjectiveLineResolution.mem_J_iff _).1 hJ).2⟩)
    · obtain ⟨c, hc, hcx⟩ := h
      exact ⟨fun _ => c (some ()), fun _ => hc _, funext fun p => congrFun hcx (oldIdx p)⟩
  null := fun j => by
    have hset : {x | liftD x x ∈ mcPts JD} = {x | projectiveLineMultiHomogResolution.lift x x ∈ mcPts ProjectiveLineResolution.JJ} := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_JD_iff, ProjectiveLineResolution.mem_J_iff]
      constructor
      · rintro ⟨-, h⟩
        exact ⟨(projectiveLineMultiHomogResolution.mem x x (projectiveLineMultiHomogResolution.mem_U x)).1, h⟩
      · rintro ⟨-, h⟩
        exact ⟨(liftD_mem x x (projectiveLineMultiHomogResolution.mem_U x)).1, h⟩
    rw [hset]
    exact projectiveLineMultiHomogResolution.null j

end PowerBlockDiag

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
