import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cpt_diff (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) := by
  have hn : ∀ (τ : X.Ψ) (a b : Fin r), Differentiable ℂ fun z : V (nd X) => nmat X z τ a b := by
    intro τ a b
    by_cases h : b < a
    · simp only [nmat, dif_pos h]
      first
        | exact (EuclideanSpace.proj (𝕜 := ℂ) _).differentiable
        | fun_prop
    · by_cases h' : a = b
      · simp only [nmat, dif_neg h, if_pos h']
        exact differentiable_const _
      · simp only [nmat, dif_neg h, if_neg h']
        exact differentiable_const _
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  show Differentiable ℂ fun z => ∑ k, mat x0 τ a k * mat (nmat X z) τ k b
  first
    | exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (hn τ k b)
    | (have hk : ∀ k, Differentiable ℂ fun z : V (nd X) => nmat X z τ k b := fun k => hn τ k b
       fun_prop)

theorem comp_cpt_diffOn {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom) (x0 : Frame X.Ψ r) :
    DifferentiableOn ℂ (fun z => P (cpt X x0 z)) (OmF X x0) := hP.comp (cpt_diff X x0).differentiableOn (fun _ hz => hz)

theorem bchar_ne_zero {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (la : Wt X.Ψ r) : bchar la b ≠ 0 := by
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular (by intro a c hca; exact (hb τ).2 a c hca)] at h
  exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ _)

theorem chi_ne {la : Wt X.Ψ r} {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have h1 := h γ hγ
  rw [h0, zero_pow hn.ne'] at h1
  exact zero_ne_one h1

theorem lact_one (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1) * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]
  rfl

theorem cpt_lact (γ : GL (Fin r) E) (x : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ x) z = lact γ (cpt X x z) := by
  funext τ
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat (nmat X z) τ)

def sig (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : V (nd X) :=
  WithLp.toLp 2 fun k => s k x / w0 x

theorem sig_lact {L : Wt X.Ψ r} {w0 : Frame X.Ψ r → ℂ} {s : Fin (nd X) → Frame X.Ψ r → ℂ}
    (hw0 : X.IsSec L w0) (hs : ∀ k, X.IsSec L (s k)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : sig X w0 s (lact γ x) = sig X w0 s x := by
  unfold sig
  congr 1
  funext k
  rw [(hs k).2.2 γ hγ x hx, hw0.2.2 γ hγ x hx, mul_div_mul_left _ _ (chi_ne X (la := L) hγ)]

theorem sig_rmul {L : Wt X.Ψ r} {w0 : Frame X.Ψ r → ℂ} {s : Fin (nd X) → Frame X.Ψ r → ℂ}
    (hw0 : X.IsSec L w0) (hs : ∀ k, X.IsSec L (s k)) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : sig X w0 s (rmul x b) = sig X w0 s x := by
  unfold sig
  congr 1
  funext k
  rw [(hs k).2.1 x hx b hb, hw0.2.1 x hx b hb, mul_div_mul_left _ _ (bchar_ne_zero X hb L)]

theorem frame_entry_diff {f : V (nd X) → Frame X.Ψ r} (hf : Differentiable ℂ f) (τ : X.Ψ) (a b : Fin r) :
    Differentiable ℂ fun z => f z τ a b := differentiable_pi.1 (differentiable_pi.1 (differentiable_pi.1 hf τ) a) b

theorem lact_rmul_diff {f : V (nd X) → Frame X.Ψ r} (hf : Differentiable ℂ f) (γ : GL (Fin r) E)
    (b : Frame X.Ψ r) : Differentiable ℂ fun z => lact γ (rmul (f z) b) := by
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  show Differentiable ℂ fun z => ∑ k, ((γ : Matrix (Fin r) (Fin r) E).map τ.1) i k *
    ∑ l, mat (f z) τ k l * mat b τ l j
  first
    | exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul
        (Differentiable.fun_sum fun l _ => (frame_entry_diff X hf τ k l).mul (differentiable_const _))
    | (have hk : ∀ k l, Differentiable ℂ fun z => f z τ k l := fun k l => frame_entry_diff X hf τ k l
       fun_prop)

private lemma continuous_dmin_Gm (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  unfold dmin lminor gram hermC col mat
  first
    | fun_prop
    | (apply Continuous.matrix_det; apply Continuous.matrix_submatrix; fun_prop)
    | continuity

theorem isOpen_dom : IsOpen X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i :=
    fun τ i => continuous_dmin_Gm X τ i
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := by
    intro τ
    first
      | exact Continuous.matrix_det (continuous_apply τ)
      | (unfold mat; fun_prop)
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => ?_
  refine (isOpen_ne_fun (hdet τ) continuous_const).inter (isOpen_iInter_of_finite fun i => ?_)
  exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hd τ i)))

theorem sig_cpt_diffAt {L : Wt X.Ψ r} {w0 : Frame X.Ψ r → ℂ} {s : Fin (nd X) → Frame X.Ψ r → ℂ}
    (hw0 : X.IsSec L w0) (hs : ∀ k, X.IsSec L (s k)) {x1 : Frame X.Ψ r} {z : V (nd X)}
    (hz : cpt X x1 z ∈ X.dom) (hw : w0 (cpt X x1 z) ≠ 0) :
    DifferentiableAt ℂ (fun w => sig X w0 s (cpt X x1 w)) z := by
  have hO : IsOpen X.dom := isOpen_dom X
  have hd : ∀ P : Frame X.Ψ r → ℂ, X.IsSec L P → DifferentiableAt ℂ (fun w => P (cpt X x1 w)) z := by
    intro P hP
    exact (hP.1.differentiableAt (hO.mem_nhds hz)).comp z ((cpt_diff X x1) z)
  rw [differentiableAt_euclidean]
  intro k
  have hq : DifferentiableAt ℂ (fun w => s k (cpt X x1 w) / w0 (cpt X x1 w)) z := by
    simp only [div_eq_mul_inv]
    exact (hd (s k) (hs k)).mul ((hd w0 hw0).inv hw)
  first
    | exact hq
    | (unfold sig; exact hq)
    | simpa [sig] using hq

theorem etale_transfer (hLU : LUStatement (E := E)) {L : Wt X.Ψ r} {w0 : Frame X.Ψ r → ℂ}
    {s : Fin (nd X) → Frame X.Ψ r → ℂ} (hw0 : X.IsSec L w0) (hs : ∀ k, X.IsSec L (s k))
    {xa : Frame X.Ψ r} (hxa : xa ∈ X.dom)
    (hdet : (fderiv ℂ (fun z => sig X w0 s (cpt X xa z)) 0).det ≠ 0)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {x1 : Frame X.Ψ r} (ho1 : IsOrth X x1) {b1 : Frame X.Ψ r} (hb1 : b1 ∈ Bor X.Ψ r)
    (hy : lact γ (rmul xa b) = rmul x1 b1) (hw1 : w0 x1 ≠ 0) :
    (fderiv ℂ (fun z => sig X w0 s (cpt X x1 z)) 0).det ≠ 0 := by
  obtain ⟨Δ, zOf, bOf, hΔd, -, hzOf, -, hdec, hlast⟩ := hLU r X x1 ho1
  set Y : V (nd X) → Frame X.Ψ r := fun z => lact γ (rmul (cpt X xa z) b) with hYdef
  have hYd : Differentiable ℂ Y := lact_rmul_diff X (cpt_diff X xa) γ b
  have hY0 : Y 0 = rmul (cpt X x1 0) b1 := by
    simp only [hYdef, cpt_zero]
    exact hy
  obtain ⟨hΔ0, hz0, -⟩ := hlast 0 (zero_mem_OmF X x1 ho1) b1 hb1
  rw [← hY0] at hΔ0 hz0
  set G := {x : Frame X.Ψ r | x ∈ X.dom ∧ Δ x ≠ 0} with hGdef
  have hGo : IsOpen G :=
    hΔd.continuous.continuousOn.isOpen_inter_preimage (isOpen_dom X) isOpen_compl_singleton
  have hY0G : Y 0 ∈ G := ⟨by rw [hY0, cpt_zero]; exact OntoS.dom_rmul X (orth_mem_dom X x1 ho1) hb1, hΔ0⟩
  have e1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), Y z ∈ G :=
    hYd.continuous.continuousAt.preimage_mem_nhds (hGo.mem_nhds hY0G)
  have e2 : ∀ᶠ z in 𝓝 (0 : V (nd X)), cpt X xa z ∈ X.dom :=
    (cpt_diff X xa).continuous.continuousAt.preimage_mem_nhds
      ((isOpen_dom X).mem_nhds (by rw [cpt_zero]; exact hxa))
  have hev : ∀ᶠ z in 𝓝 (0 : V (nd X)), Y z ∈ G ∧ cpt X xa z ∈ X.dom := e1.and e2
  set Λ : V (nd X) → V (nd X) := fun z => zOf (Y z) with hΛdef
  have hΛ0 : Λ 0 = 0 := hz0
  have hΛd : DifferentiableAt ℂ Λ 0 :=
    ((hzOf (Y 0) hY0G).differentiableAt (hGo.mem_nhds hY0G)).comp 0 (hYd 0)
  have hrel : (fun z => sig X w0 s (cpt X xa z)) =ᶠ[𝓝 0]
      (fun w => sig X w0 s (cpt X x1 w)) ∘ Λ := by
    filter_upwards [hev] with z hz
    obtain ⟨⟨hYdom, hΔz⟩, hcz⟩ := hz
    obtain ⟨hzO, hbO, hdecz⟩ := hdec (Y z) hYdom hΔz
    calc sig X w0 s (cpt X xa z) = sig X w0 s (rmul (cpt X xa z) b) :=
          (sig_rmul X hw0 hs hb hcz).symm
      _ = sig X w0 s (Y z) := (sig_lact X hw0 hs hγ (OntoS.dom_rmul X hcz hb)).symm
      _ = sig X w0 s (rmul (cpt X x1 (Λ z)) (bOf (Y z))) := by rw [← hdecz]
      _ = sig X w0 s (cpt X x1 (Λ z)) := sig_rmul X hw0 hs hbO hzO
  have hσ1 : DifferentiableAt ℂ (fun w => sig X w0 s (cpt X x1 w)) (Λ 0) := by
    rw [hΛ0]
    refine sig_cpt_diffAt X hw0 hs ?_ ?_
    · rw [cpt_zero]; exact orth_mem_dom X x1 ho1
    · rw [cpt_zero]; exact hw1
  have hfd : fderiv ℂ (fun z => sig X w0 s (cpt X xa z)) 0 =
      (fderiv ℂ (fun w => sig X w0 s (cpt X x1 w)) 0).comp (fderiv ℂ Λ 0) := by
    rw [hrel.fderiv_eq, fderiv_comp 0 hσ1 hΛd, hΛ0]
  rw [hfd] at hdet
  intro h1
  apply hdet
  show LinearMap.det (((fderiv ℂ (fun w => sig X w0 s (cpt X x1 w)) 0 : V (nd X) →L[ℂ] V (nd X)) :
    V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ ((fderiv ℂ Λ 0 : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X))) = 0
  rw [LinearMap.det_comp]
  have h1' : LinearMap.det ((fderiv ℂ (fun w => sig X w0 s (cpt X x1 w)) 0 : V (nd X) →L[ℂ] V (nd X)) :
    V (nd X) →ₗ[ℂ] V (nd X)) = 0 := h1
  rw [h1', zero_mul]

private lemma det_mat_nmat (z : V (nd X)) (τ : X.Ψ) : (mat (nmat X z) τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro a _
    simp [mat, nmat]
  · intro i j h
    have hij : i < j := OrderDual.toDual_lt_toDual.1 h
    simp [mat, nmat, not_lt.2 hij.le, hij.ne]

theorem det_cpt (x0 : Frame X.Ψ r) (z : V (nd X)) (τ : X.Ψ) :
    (mat (cpt X x0 z) τ).det = (mat x0 τ).det := by
  show (mat x0 τ * mat (nmat X z) τ).det = (mat x0 τ).det
  rw [Matrix.det_mul, det_mat_nmat X z τ, mul_one]

theorem nbhd_avoid (x0 : Frame X.Ψ r) (hx0 : ∀ τ, (mat x0 τ).det ≠ 0) {K : Set (V (nd X))}
    (hK : IsCompact K) {x1 : Frame X.Ψ r}
    (hx1 : ∀ z ∈ K, ∀ b ∈ Bor X.Ψ r, x1 ≠ rmul (cpt X x0 z) b) (hx1d : ∀ τ, (mat x1 τ).det ≠ 0) :
    ∃ N ∈ 𝓝 x1, ∀ x ∈ N, ∀ z ∈ K, ∀ b ∈ Bor X.Ψ r, x ≠ rmul (cpt X x0 z) b := by
  have hc := (cpt_diff X x0).continuous
  have hcont : ∀ (τ : X.Ψ) (a c : Fin r), Continuous fun p : Frame X.Ψ r × V (nd X) =>
      ((mat (cpt X x0 p.2) τ).adjugate * mat p.1 τ) a c := by
    intro τ a c
    have h1 : Continuous fun p : Frame X.Ψ r × V (nd X) => mat (cpt X x0 p.2) τ := by
      first
        | exact (continuous_apply τ).comp (hc.comp continuous_snd)
        | (unfold mat; fun_prop)
    have h2 : Continuous fun p : Frame X.Ψ r × V (nd X) => mat p.1 τ := by
      first
        | exact (continuous_apply τ).comp continuous_fst
        | (unfold mat; fun_prop)
    exact (h1.matrix_adjugate.matrix_mul h2).matrix_elem a c
  have hx1P : ∀ z ∈ K, ∃ (τ : X.Ψ) (a c : Fin r), c < a ∧
      ((mat (cpt X x0 z) τ).adjugate * mat x1 τ) a c ≠ 0 := by
    intro z hz
    by_contra hneg
    push_neg at hneg
    have hdc : ∀ τ, (mat (cpt X x0 z) τ).det ≠ 0 := fun τ => by
      rw [det_cpt X x0 z τ]
      exact hx0 τ
    have hu : ∀ τ, IsUnit (mat (cpt X x0 z) τ).det := fun τ => isUnit_iff_ne_zero.2 (hdc τ)
    refine hx1 z hz (fun τ => (mat (cpt X x0 z) τ)⁻¹ * mat x1 τ) ?_ ?_
    · intro τ
      refine ⟨?_, fun a c hca => ?_⟩
      · show ((mat (cpt X x0 z) τ)⁻¹ * mat x1 τ).det ≠ 0
        rw [Matrix.det_mul]
        exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hu τ)).ne_zero (hx1d τ)
      · show ((mat (cpt X x0 z) τ)⁻¹ * mat x1 τ) a c = 0
        rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, hneg τ a c hca, smul_zero]
    · funext τ
      show mat x1 τ = mat (cpt X x0 z) τ * ((mat (cpt X x0 z) τ)⁻¹ * mat x1 τ)
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  have hev : ∀ᶠ x in 𝓝 x1, ∀ z ∈ K, ∃ (τ : X.Ψ) (a c : Fin r), c < a ∧
      ((mat (cpt X x0 z) τ).adjugate * mat x τ) a c ≠ 0 := by
    refine hK.eventually_forall_of_forall_eventually fun z hz => ?_
    obtain ⟨τ, a, c, hca, hne⟩ := hx1P z hz
    have hO : IsOpen {p : Frame X.Ψ r × V (nd X) |
        ((mat (cpt X x0 p.2) τ).adjugate * mat p.1 τ) a c ≠ 0} :=
      isOpen_ne_fun (hcont τ a c) continuous_const
    have hmem : ((x1, z) : Frame X.Ψ r × V (nd X)) ∈ {p : Frame X.Ψ r × V (nd X) |
        ((mat (cpt X x0 p.2) τ).adjugate * mat p.1 τ) a c ≠ 0} := hne
    filter_upwards [hO.mem_nhds hmem] with p hp
    exact ⟨τ, a, c, hca, hp⟩
  obtain ⟨N, hN, hNp⟩ := Filter.eventually_iff_exists_mem.1 hev
  refine ⟨N, hN, fun x hx z hz b hb heq => ?_⟩
  obtain ⟨τ, a, c, hca, hne⟩ := hNp x hx z hz
  apply hne
  rw [heq]
  show ((mat (cpt X x0 z) τ).adjugate * (mat (cpt X x0 z) τ * mat b τ)) a c = 0
  have hz0 : mat b τ a c = 0 := (hb τ).2 a c hca
  rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
    hz0, smul_zero]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
