import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EquivariantSubspace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.AnaHpartUnique
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf Filter Topology
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DiffQuot

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothOnH_continuousOn {H : Matrix (Fin n) (Fin n) ℂ} {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) : ContinuousOn f (UH H) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hcont : ContinuousAt F g := hF.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine (hcont.continuousWithinAt (s := UH H)).congr_of_eventuallyEq ?_ (hfF g hgU hg)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with x hxU hxH
  exact hfF x hxU hxH

theorem left_hasDerivAt {H : Matrix (Fin n) (Fin n) ℂ} (hH : AAInvW.HInvol H)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g X : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hg : g ∈ U) (hgH : inUH H g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, inUH H x → f x = F x) (hX : AAInvW.inLH H X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (fderiv ℝ F g (X * g)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) (X * g) 0 := by
    refine hasDerivAt_iff_tendsto_slope.2 ?_
    have h := (Formalism.REAL.tendsto_slope_exp_smul X).mul_const g
    refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp only [slope_def_module, sub_mul, smul_mul_assoc]
  have hFd : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF.differentiableOn (by simp)) g hg).differentiableAt (hU.mem_nhds hg) |>.hasFDerivAt
  have hcomp := hFd.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have h0 : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) 0 = g := by simp
  have hcU : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by rw [show NormedSpace.exp (((0 : ℝ) : ℂ) • X) * g = g by simp]; exact hU.mem_nhds hg)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hcU] with t ht
  exact hfF _ ht (AAInvW.ana_mul (AAInvW.ana_expt hH hX t) hgH)

theorem left_smooth {H : Matrix (Fin n) (Fin n) ℂ} (hH : AAInvW.HInvol H)
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hX : AAInvW.inLH H X)
    (hf' : ∀ g, inUH H g → ∀ D, HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) D 0 → D = f' g) :
    SmoothOnH H f' ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (f' g) 0 := by
  have hL : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => X * x) := by
    have h := (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)).contDiff (n := ∞)
    convert h using 1
    funext x
    first | simp | rfl
  refine ⟨fun g₀ hg₀ => ?_, fun g hg => ?_⟩
  · obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
    refine ⟨U, fun x => fderiv ℝ F x (X * x), hU, hg₀U, ?_, fun x hxU hxH => ?_⟩
    · exact (((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hF).2).clm_apply hL.contDiffOn
    · exact (hf' x hxH _ (left_hasDerivAt hH hU hxU hxH hF hfF hX)).symm
  · obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
    have hd := left_hasDerivAt hH hU hgU hg hF hfF hX
    have e := hf' g hg _ hd
    rw [e] at hd
    exact hd

end Smooth

section Rep

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hInvol (k r : ℕ) : AAInvW.HInvol (Hpk k r) := by
  exact ⟨Formalism.QuantumDeterminants.GBasic.Hpk_herm k r, Formalism.QuantumDeterminants.GBasic.Hpk_sq k r⟩

theorem exp_mem {X : Mat k r} (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ GG k r := by
  exact AAInvW.ana_expt (hInvol k r) hX t

theorem sm_add {σ : Mat k r → (H →L[ℂ] H)} {v w : H} (hv : IsSmoothVec σ v) (hw : IsSmoothVec σ w) :
    IsSmoothVec σ (v + w) := by
  have h := GlobalTheory.EquivariantSubspace.smoothOnH_add hv hw
  show SmoothOnH _ (fun g => σ g (v + w))
  convert h using 1
  funext g
  simp

theorem sm_smul {σ : Mat k r → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : IsSmoothVec σ v) :
    IsSmoothVec σ (a • v) := by
  have h := GlobalTheory.EquivariantSubspace.smoothOnH_smul a hv
  show SmoothOnH _ (fun g => σ g (a • v))
  convert h using 1
  funext g
  simp

theorem sm_sub {σ : Mat k r → (H →L[ℂ] H)} {v w : H} (hv : IsSmoothVec σ v) (hw : IsSmoothVec σ w) :
    IsSmoothVec σ (v - w) := by
  have h := sm_add hv (sm_smul (-1) hw)
  simpa [sub_eq_add_neg] using h

theorem sm_zero (σ : Mat k r → (H →L[ℂ] H)) : IsSmoothVec σ (0 : H) := by
  have h := GlobalTheory.EquivariantSubspace.smoothOnH_zero (E := H) (Hpk k r)
  show SmoothOnH _ (fun g => σ g 0)
  convert h using 1
  funext g
  simp

theorem hasDerivAt_dsig {σ : Mat k r → (H →L[ℂ] H)} {v : H} {X : Mat k r} (hv : IsSmoothVec σ v)
    (hX : InLieHpk k r X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig σ X v) 0 := by
  have h1 : inUH (Hpk k r) (1 : Mat k r) := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  obtain ⟨U, F, hU, h1U, hF, hfF⟩ := (hv : SmoothOnH (Hpk k r) (fun g => σ g v)) 1 h1
  have hd := left_hasDerivAt (hInvol k r) hU h1U h1 hF hfF hX
  simp only [mul_one] at hd
  exact hd.differentiableAt.hasDerivAt

variable [CompleteSpace H]

theorem sm_translate {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec σ v)
    {g : Mat k r} (hg : g ∈ GG k r) : IsSmoothVec σ (σ g v) := by
  exact ((GlobalTheory.T.smooth_vectors_dense_invariant k r σ v hσ).2.2.2.1 v hv).1 g hg

theorem sm_dsig {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) : IsSmoothVec σ (dsig σ Y v) := by
  exact (((GlobalTheory.T.smooth_vectors_dense_invariant k r σ v hσ).2.2.2.1 v hv).2 Y hY).1

omit [CompleteSpace H] in

theorem inner_map {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {g : Mat k r} (hg : g ∈ GG k r) (v w : H) :
    ⟪σ g v, σ g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g).toLinearMap, norm_map' := hσ.2.1 g hg }
  exact L.inner_map_map v w

omit [CompleteSpace H] in

theorem dsig_skew {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {v w : H} {X : Mat k r}
    (hv : IsSmoothVec σ v) (hw : IsSmoothVec σ w) (hX : InLieHpk k r X) :
    ⟪dsig σ X v, w⟫_ℂ = -⟪v, dsig σ X w⟫_ℂ := by
  have hv' := hasDerivAt_dsig hv hX
  have hw' := hasDerivAt_dsig hw hX
  have key : ∀ t : ℝ, ⟪σ (NormedSpace.exp ((t : ℂ) • X)) v, w⟫_ℂ =
      ⟪v, σ (NormedSpace.exp (((-t : ℝ) : ℂ) • X)) w⟫_ℂ := by
    intro t
    have hcomm : Commute (((-t : ℝ) : ℂ) • X) ((t : ℂ) • X) :=
      ((Commute.refl X).smul_left _).smul_right _
    have hm : NormedSpace.exp (((-t : ℝ) : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul]
      simp
    have h := inner_map hσ (exp_mem hX (-t)) (σ (NormedSpace.exp ((t : ℂ) • X)) v) w
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (exp_mem hX (-t)) _ (exp_mem hX t), hm, hσ.1.1,
      ContinuousLinearMap.one_apply] at h
    exact h.symm
  have hw'' : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) w) (dsig σ X w) (-0) := by
    rw [neg_zero]; exact hw'
  have hn := hw''.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have h1 := HasDerivAt.inner ℂ hv' (hasDerivAt_const (0 : ℝ) w)
  have h2 := HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) v) hn
  have h3 := h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => key t))
  simp at h3
  rw [h3]

theorem dsigW_mem {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (W : List (Mat k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) : ∀ u, IsSmoothVec σ u → IsSmoothVec σ (dsigW σ W u) := by
  induction W with
  | nil => intro u hu; exact hu
  | cons X W ih =>
    intro u hu
    exact sm_dsig hσ (ih (fun Y hY => hW Y (by simp [hY])) u hu) (hW X (by simp))

omit [CompleteSpace H] in
theorem dsigW_append (σ : Mat k r → (H →L[ℂ] H)) (W : List (Mat k r)) (Y : Mat k r) (u : H) :
    dsigW σ (W ++ [Y]) u = dsigW σ W (dsig σ Y u) := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show dsig σ X (dsigW σ (W ++ [Y]) u) = dsig σ X (dsigW σ W (dsig σ Y u))
    rw [ih]

theorem dsigW_adjoint {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (W : List (Mat k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) :
    ∀ w, IsSmoothVec σ w → ∃ w' : H, ∀ u, IsSmoothVec σ u → ⟪w, dsigW σ W u⟫_ℂ = ⟪w', u⟫_ℂ := by
  induction W with
  | nil => intro w _; exact ⟨w, fun u _ => by rfl⟩
  | cons X W ih =>
    intro w hw
    have hX : InLieHpk k r X := hW X (by simp)
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (by simp [hY])
    obtain ⟨w₀, hw₀⟩ := ih hW' (dsig σ X w) (sm_dsig hσ hw hX)
    refine ⟨-w₀, fun u hu => ?_⟩
    have hs := dsig_skew hσ hw (dsigW_mem hσ W hW' u hu) hX
    show ⟪w, dsig σ X (dsigW σ W u)⟫_ℂ = ⟪-w₀, u⟫_ℂ
    rw [inner_neg_left, ← hw₀ u hu, hs, neg_neg]

omit [CompleteSpace H] in
theorem eq_zero_of_closure {σ : Mat k r → (H →L[ℂ] H)} {x : H} (hx : x ∈ closure {v | IsSmoothVec σ v})
    (h : ∀ w, IsSmoothVec σ w → ⟪w, x⟫_ℂ = 0) : x = 0 := by
  have hsub : closure {v | IsSmoothVec σ v} ⊆ {y | ⟪y, x⟫_ℂ = 0} :=
    closure_minimal (fun v hv => h v hv) (isClosed_eq (Continuous.inner continuous_id continuous_const)
      continuous_const)
  exact inner_self_eq_zero.1 (hsub hx)

private theorem dsig_smul_sub_sub {σ : Mat k r → (H →L[ℂ] H)} {X : Mat k r} (hX : InLieHpk k r X) (a : ℂ)
    {x y z : H} (hx : IsSmoothVec σ x) (hy : IsSmoothVec σ y) (hz : IsSmoothVec σ z) :
    dsig σ X (a • (x - y) - z) = a • (dsig σ X x - dsig σ X y) - dsig σ X z := by
  have h := (((hasDerivAt_dsig hx hX).sub (hasDerivAt_dsig hy hX)).const_smul a).sub (hasDerivAt_dsig hz hX)
  have h' : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (a • (x - y) - z))
      (a • (dsig σ X x - dsig σ X y) - dsig σ X z) 0 := by
    convert h using 1
    funext t
    simp [map_sub, map_smul]
  exact h'.deriv

theorem dsigW_comb {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (W : List (Mat k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) (a : ℂ) {x y z : H} (hx : IsSmoothVec σ x) (hy : IsSmoothVec σ y)
    (hz : IsSmoothVec σ z) :
    dsigW σ W (a • (x - y) - z) = a • (dsigW σ W x - dsigW σ W y) - dsigW σ W z := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hX : InLieHpk k r X := hW X (by simp)
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (by simp [hY])
    show dsig σ X (dsigW σ W (a • (x - y) - z)) =
      a • (dsig σ X (dsigW σ W x) - dsig σ X (dsigW σ W y)) - dsig σ X (dsigW σ W z)
    rw [ih hW']
    exact dsig_smul_sub_sub hX a (dsigW_mem hσ W hW' x hx) (dsigW_mem hσ W hW' y hy) (dsigW_mem hσ W hW' z hz)

theorem dsigW_deriv_eq {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (W : List (Mat k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {c : ℝ → H} {c' D : H} (hc : ∀ t, IsSmoothVec σ (c t))
    (hc' : IsSmoothVec σ c') (hd : HasDerivAt c c' 0)
    (hD' : HasDerivAt (fun t => dsigW σ W (c t)) D 0) : D = dsigW σ W c' := by
  have hmem : D - dsigW σ W c' ∈ closure {v | IsSmoothVec σ v} := by
    have hsl := (hasDerivAt_iff_tendsto_slope.1 hD').sub_const (dsigW σ W c')
    refine mem_closure_of_tendsto hsl (Filter.Eventually.of_forall fun t => ?_)
    show IsSmoothVec σ (slope (fun t => dsigW σ W (c t)) 0 t - dsigW σ W c')
    rw [slope_def_module]
    have h := sm_smul (((t - 0)⁻¹ : ℝ) : ℂ)
      (sm_sub (dsigW_mem hσ W hW (c t) (hc t)) (dsigW_mem hσ W hW (c 0) (hc 0)))
    rw [Complex.coe_smul] at h
    exact sm_sub h (dsigW_mem hσ W hW c' hc')
  refine sub_eq_zero.1 (eq_zero_of_closure hmem fun w hw => ?_)
  obtain ⟨w', hw'⟩ := dsigW_adjoint hσ W hW w hw
  have h1 := HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) w) hD'
  have h2 := HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) w') hd
  have h3 := h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hw' (c t) (hc t)))
  simp at h3
  rw [inner_sub_right, h3, hw' c' hc', sub_self]

theorem dsigW_orbit {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec σ v)
    (W : List (Mat k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (hs : SmoothOnH (Hpk k r) (fun g => dsigW σ W (σ g v)))
    (Y : Mat k r) (hY : InLieHpk k r Y) :
    SmoothOnH (Hpk k r) (fun g => dsigW σ W (dsig σ Y (σ g v))) ∧
      ∀ g, inUH (Hpk k r) g → HasDerivAt
        (fun t : ℝ => dsigW σ W (σ (NormedSpace.exp ((t : ℂ) • Y) * g) v))
        (dsigW σ W (dsig σ Y (σ g v))) 0 := by
  refine left_smooth (hInvol k r) hs hY (fun g hg D hD => ?_)
  have hg' : g ∈ GG k r := hg
  have hgv := sm_translate hσ hv hg'
  refine dsigW_deriv_eq hσ W hW (c := fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) (σ g v))
    (fun t => sm_translate hσ hgv (exp_mem hY t)) (sm_dsig hσ hgv hY) (hasDerivAt_dsig hgv hY) ?_
  refine hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [hσ.1.2 _ (exp_mem hY t) _ hg', ContinuousLinearMap.comp_apply]

theorem dsigW_orbit_smooth {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec σ v)
    (W : List (Mat k r)) (hW : ∀ X ∈ W, InLieHpk k r X) :
    SmoothOnH (Hpk k r) (fun g => dsigW σ W (σ g v)) := by
  induction W using List.reverseRecOn with
  | nil => exact hv
  | append_singleton W Y ih =>
    have hW' : ∀ X ∈ W, InLieHpk k r X := fun X hX => hW X (by simp [hX])
    have hY : InLieHpk k r Y := hW Y (by simp)
    have h := (dsigW_orbit hσ hv W hW' (ih hW') Y hY).1
    simp only [dsigW_append]
    exact h

end Rep

end GlobalTheory.DiffQuot

namespace GlobalTheory.DiffQuot

section Main

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem cw_tendsto {σ : Mat k r → (H →L[ℂ] H)} {V : Type} [NormedAddCommGroup V] {Bm : H → V}
    (hB : IsCWCont (k := k) (r := r) σ Bm) {α : Type} {l : Filter α} {u : α → H}
    (hu : ∀ᶠ a in l, IsSmoothVec σ (u a))
    (h : ∀ W : List (Mat k r), (∀ X ∈ W, InLieHpk k r X) → Tendsto (fun a => dsigW σ W (u a)) l (𝓝 0)) :
    Tendsto (fun a => Bm (u a)) l (𝓝 0) := by
  obtain ⟨C, Ws, hWs, hbd⟩ := hB
  have hsum : Tendsto (fun a => (Ws.map fun w => ‖dsigW σ w (u a)‖).sum) l (𝓝 0) := by
    have h := tendsto_list_sum (l := Ws) (f := fun w a => ‖dsigW σ w (u a)‖) (a := fun _ => (0 : ℝ))
      (fun w hw => by simpa using (h w (hWs w hw)).norm)
    simpa using h
  have hg : Tendsto (fun a => C * (Ws.map fun w => ‖dsigW σ w (u a)‖).sum) l (𝓝 0) := by
    simpa using hsum.const_mul C
  exact squeeze_zero_norm' (hu.mono fun a ha => hbd (u a) ha) hg

variable [CompleteSpace H]

theorem dsigW_zero {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (W : List (Mat k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) : dsigW σ W 0 = 0 := by
  have h := dsigW_comb hσ W hW 1 (sm_zero σ) (sm_zero σ) (sm_zero σ)
  simp only [sub_self, smul_zero, zero_sub, one_smul] at h
  have h2 : (2 : ℂ) • dsigW σ W 0 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem word_quot_tendsto {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {x : H} (hx : IsSmoothVec σ x)
    {X : Mat k r} (hX : InLieHpk k r X) (W : List (Mat k r)) (hW : ∀ Y ∈ W, InLieHpk k r Y) :
    Tendsto (fun t : ℝ => dsigW σ W ((t : ℂ)⁻¹ • (σ (NormedSpace.exp ((t : ℂ) • X)) x - x) - dsig σ X x))
      (𝓝[≠] 0) (𝓝 0) := by
  have h1 : inUH (Hpk k r) (1 : Mat k r) := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  have hd := (dsigW_orbit hσ hx W hW (dsigW_orbit_smooth hσ hx W hW) X hX).2 1 h1
  simp only [mul_one, hσ.1.1, ContinuousLinearMap.one_apply] at hd
  have hsl := (hasDerivAt_iff_tendsto_slope.1 hd).sub_const (dsigW σ W (dsig σ X x))
  rw [sub_self] at hsl
  refine hsl.congr' (Filter.Eventually.of_forall fun t => ?_)
  have hxt := sm_translate hσ hx (exp_mem hX t)
  dsimp only
  rw [dsigW_comb hσ W hW _ hxt hx (sm_dsig hσ hx hX), slope_def_module]
  simp only [sub_zero, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
    ContinuousLinearMap.one_apply]
  rw [← Complex.ofReal_inv, Complex.coe_smul t⁻¹]

theorem orbit_hasDerivAt {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {x : H} (hx : IsSmoothVec σ x)
    {X : Mat k r} (hX : InLieHpk k r X) (t : ℝ) :
    HasDerivAt (fun u : ℝ => σ (NormedSpace.exp ((u : ℂ) • X)) x)
      (σ (NormedSpace.exp ((t : ℂ) • X)) (dsig σ X x)) t := by
  have h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (σ (NormedSpace.exp ((s : ℂ) • X)) x))
      (σ (NormedSpace.exp ((t : ℂ) • X)) (dsig σ X x)) (t - t) := by
    rw [sub_self]
    have h := ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_dsig hx hX)
    simpa [Function.comp_def] using h
  have h1 := HasDerivAt.comp_sub_const t t h0
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  have hcomm : Commute ((t : ℂ) • X) (((u - t : ℝ) : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  have hsum : (t : ℂ) • X + ((u - t : ℝ) : ℂ) • X = (u : ℂ) • X := by
    rw [← add_smul]
    congr 1
    push_cast
    ring
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (exp_mem hX t) _ (exp_mem hX (u - t)),
    ← Matrix.exp_add_of_commute _ _ hcomm, hsum]

end Main

end GlobalTheory.DiffQuot

open GlobalTheory.DiffQuot in

theorem GlobalTheory.diffQuot_bessel : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (l : H → Wp) (x : H) (X : Mat k r), IsURepOn (GG k r) σ → IsBesselMapSm z ψ σ π l → IsSmoothVec σ x → InLieHpk k r X → Filter.Tendsto (fun t : ℝ => l ((t : ℂ)⁻¹ • (σ (NormedSpace.exp ((t : ℂ) • X)) x - x))) (nhdsWithin 0 {0}ᶜ) (nhds (l (dsig σ X x))) ∧ ContinuousOn (fun g => l (σ g x)) (GG k r) ∧ ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ GG k r ∧ σ (NormedSpace.exp ((t : ℂ) • X)) x - x = ∫ u in (0 : ℝ)..t, σ (NormedSpace.exp ((u : ℂ) • X)) (dsig σ X x) := by
  intro k r H _ _ _ Wp _ _ _ _ σ z ψ π l x X hσ hl hx hX
  have hd := sm_dsig hσ hx hX
  refine ⟨?_, ?_, ?_⟩
  · have hsm : ∀ t : ℝ, IsSmoothVec σ ((t : ℂ)⁻¹ • (σ (NormedSpace.exp ((t : ℂ) • X)) x - x)) :=
      fun t => sm_smul _ (sm_sub (sm_translate hσ hx (exp_mem hX t)) hx)
    have hT := cw_tendsto hl.2.2.2 (l := nhdsWithin (0 : ℝ) {0}ᶜ)
      (u := fun t : ℝ => (t : ℂ)⁻¹ • (σ (NormedSpace.exp ((t : ℂ) • X)) x - x) - dsig σ X x)
      (Filter.Eventually.of_forall fun t => sm_sub (hsm t) hd) (fun W hW => word_quot_tendsto hσ hx hX W hW)
    have h := hT.add_const (l (dsig σ X x))
    rw [zero_add] at h
    refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
    have e := hl.1 _ (sm_sub (hsm t) hd) _ hd
    rw [sub_add_cancel] at e
    exact e.symm
  · intro g₀ hg₀
    have hsm0 := sm_translate hσ hx hg₀
    have hw : ∀ W : List (Mat k r), (∀ Y ∈ W, InLieHpk k r Y) →
        Tendsto (fun g => dsigW σ W (σ g x - σ g₀ x)) (nhdsWithin g₀ (GG k r)) (nhds 0) := by
      intro W hW
      have hc := smoothOnH_continuousOn (dsigW_orbit_smooth hσ hx W hW) g₀ hg₀
      have h := hc.tendsto.sub_const (dsigW σ W (σ g₀ x))
      rw [sub_self] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with g hg
      have e := dsigW_comb hσ W hW 1 (sm_translate hσ hx hg) hsm0 (sm_zero σ)
      rw [dsigW_zero hσ W hW] at e
      simpa using e.symm
    have hT := cw_tendsto hl.2.2.2 (l := nhdsWithin g₀ (GG k r)) (u := fun g => σ g x - σ g₀ x)
      (by filter_upwards [self_mem_nhdsWithin] with g hg; exact sm_sub (sm_translate hσ hx hg) hsm0) hw
    have h := hT.add_const (l (σ g₀ x))
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with g hg
    have e := hl.1 _ (sm_sub (sm_translate hσ hx hg) hsm0) _ hsm0
    rw [sub_add_cancel] at e
    exact e.symm
  · intro t
    refine ⟨exp_mem hX t, ?_⟩
    have hcont : Continuous (fun u : ℝ => σ (NormedSpace.exp ((u : ℂ) • X)) (dsig σ X x)) :=
      continuous_iff_continuousAt.2 fun u => (orbit_hasDerivAt hσ hd hX u).continuousAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => orbit_hasDerivAt hσ hx hX u)
      (hcont.intervalIntegrable 0 t)]
    simp [hσ.1.1]
