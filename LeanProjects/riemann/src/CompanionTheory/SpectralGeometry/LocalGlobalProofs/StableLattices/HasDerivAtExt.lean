import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmBracket

open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)

theorem fderiv_comm {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {x : E} (hF : ContDiffAt ℝ ∞ F x) (L M : E →L[ℝ] E) {a b c : E}
    (ha : M x = a) (hb : L x = b) (hc : L a - M b = c) :
    fderiv ℝ (fun g => fderiv ℝ F g (L g)) x a - fderiv ℝ (fun g => fderiv ℝ F g (M g)) x b =
      fderiv ℝ F x c := by
  subst ha hb hc
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).differentiableAt (by simp)
  have hs : IsSymmSndFDerivAt ℝ F x :=
    hF.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  rw [(hD.hasFDerivAt.clm_apply L.hasFDerivAt).fderiv, (hD.hasFDerivAt.clm_apply M.hasFDerivAt).fderiv]
  simp [hs (M x) (L x)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem lie_bracket {J X Y : Mat n} (hX : Xᴴ * J + J * X = 0) (hY : Yᴴ * J + J * Y = 0) :
    (X * Y - Y * X)ᴴ * J + J * (X * Y - Y * X) = 0 := by
  have hLX : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have hLY : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * J = J * (Y * X) := by
    rw [Matrix.mul_assoc, hLX, Matrix.mul_neg, ← Matrix.mul_assoc, hLY, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e2 : Xᴴ * Yᴴ * J = J * (X * Y) := by
    rw [Matrix.mul_assoc, hLY, Matrix.mul_neg, ← Matrix.mul_assoc, hLX, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem hasDerivAt_ext (h : RepOn G σ) {X g : Mat n} (hX : ∀ t, ex X t ∈ G) (hg : g ∈ G) {f F : Mat n → H}
    {U : Set (Mat n)} (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ G → f x = F x) :
    HasDerivAt (fun t => f (g * ex X t)) (fderiv ℝ F g (g * X)) 0 :=
  hasDerivAt_local (A := G) (γ := fun t => g * ex X t) (fun t => h.mul_mem _ hg _ (hX t))
    (by simp [ex_zero]) (hasDerivAt_mul_ex g X) hU hgU hF hfF

theorem ds_ds (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G) {v : H}
    (hv : IsSm G σ v) {F : Mat n → H} {U : Set (Mat n)} (hU : IsOpen U) (h1 : (1 : Mat n) ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ x ∈ U, x ∈ G → σ x v = F x) (L : Mat n →L[ℝ] Mat n)
    (hL : ∀ x, L x = x * Y) :
    ds σ X (ds σ Y v) = fderiv ℝ (fun g => fderiv ℝ F g (L g)) 1 X := by
  have hG : ContDiffOn ℝ ∞ (fun g => fderiv ℝ F g (L g)) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  have hGe : ∀ g ∈ U, g ∈ G → σ g (ds σ Y v) = fderiv ℝ F g (L g) := by
    intro g hg hgG
    rw [apply_ds h hY hgG (hv.differentiableAt h hY), hL]
    exact (hasDerivAt_ext h (f := fun x => σ x v) hY hgG hU hg hF hfF).deriv
  have h2 := hasDerivAt_ext h (f := fun g => σ g (ds σ Y v)) hX h.one_mem hU h1 hG hGe
  simp only [Matrix.one_mul] at h2
  exact h2.deriv

theorem ds_bracket (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G)
    (hXY : ∀ t, ex (X * Y - Y * X) t ∈ G) {v : H} (hv : IsSm G σ v) :
    ds σ X (ds σ Y v) - ds σ Y (ds σ X v) = ds σ (X * Y - Y * X) v := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 h.one_mem
  have h2 := hasDerivAt_ext h (f := fun x => σ x v) hXY h.one_mem hU h1 hF hfF
  simp only [Matrix.one_mul] at h2
  have e : ds σ (X * Y - Y * X) v = fderiv ℝ F 1 (X * Y - Y * X) := h2.deriv
  let L : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ Y).toContinuousLinearMap
  have hL : ∀ x, L x = x * Y := by intro x; simp [L]
  let M : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hM : ∀ x, M x = x * X := by intro x; simp [M]
  rw [ds_ds h hX hY hv hU h1 hF hfF L hL, ds_ds h hY hX hv hU h1 hF hfF M hM, e]
  exact fderiv_comm (hF.contDiffAt (hU.mem_nhds h1)) L M ((hM 1).trans (Matrix.one_mul X))
    ((hL 1).trans (Matrix.one_mul Y)) (congrArg₂ (· - ·) (hL X) (hM Y))

theorem smBracket : CompanionTheory.D.DSIC.SmBracket := by
  intro n ε H _ _ σ hσ X Y hX hY v hv
  have h : RepOn (UJset ε) σ :=
    ⟨by simp [UJset, PI.UpqRep.inUJ], fun a ha b hb => Formalism.REAL.indefinite_unitary_mul_mem ε ha hb, hσ.1.1, hσ.1.2⟩
  have hex : ∀ Z, inG ε Z → ∀ t, ex Z t ∈ UJset ε := fun Z hZ t => Formalism.REAL.exp_indefinite_unitary_holds n ε Z hZ t
  exact ds_bracket h (hex X hX) (hex Y hY) (hex _ (lie_bracket hX hY)) hv

theorem smBracket_of : CompanionTheory.D.DSIC.SmLin → CompanionTheory.D.DSIC.SmBracket := fun _ => smBracket

end GlobalTheory.CompanionTheory.SmBracket
