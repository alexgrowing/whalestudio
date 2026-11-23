import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrbitCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in

theorem rmul_left_cancel {r : ℕ} {Ψ : Finset (E →+* ℂ)} {o a c : Frame Ψ r}
    (ho : ∀ τ, (mat o τ).det ≠ 0) (h : rmul o a = rmul o c) : a = c := by
  funext τ
  have h1 : mat o τ * mat a τ = mat o τ * mat c τ := congrFun h τ
  have hu : IsUnit (mat o τ) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ho τ))
  exact hu.mul_left_cancel h1

theorem exists_swap {r : ℕ} (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    ∃ (U : Set (V (nd X))) (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r),
      IsOpen U ∧ 0 ∈ U ∧ DifferentiableOn ℂ Φ U ∧ Φ 0 = 0 ∧
      ∀ z ∈ U, bf z ∈ Bor X.Ψ r ∧ rmul b (nmat X z) = rmul (nmat X (Φ z)) (bf z) := by
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hod : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X (x0F X) ho
  have hcd := OntoB.cd_cpt X (rmul (x0F X) b)
  have h0 := huniq 0 (IW.zero_mem_OmF X _ ho) b hb
  rw [IW.cpt_zero] at h0
  refine ⟨cpt X (rmul (x0F X) b) ⁻¹' {x | x ∈ X.dom ∧ Δ x ≠ 0},
    fun z => zOf (cpt X (rmul (x0F X) b) z), fun z => bOf (cpt X (rmul (x0F X) b) z), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((FourierCoefficientDomain.isOpen_dom X).inter
      (isOpen_ne_fun hΔ.continuous continuous_const)).preimage hcd.continuous
  · show cpt X _ 0 ∈ X.dom ∧ Δ (cpt X _ 0) ≠ 0
    rw [IW.cpt_zero]
    exact ⟨OntoS.dom_rmul X hod hb, h0.1⟩
  · exact hz.comp (hcd.differentiable (by simp)).differentiableOn fun _ h => h
  · show zOf (cpt X _ 0) = 0
    rw [IW.cpt_zero]
    exact h0.2.1
  · intro z hzU
    obtain ⟨-, h2, h3⟩ := hsplit _ hzU.1 hzU.2
    refine ⟨h2, rmul_left_cancel (fun τ => (hod τ).1) ?_⟩
    rw [← ExtFPf.rmul_assoc, ← ExtFPf.rmul_assoc]
    exact h3

theorem det_fderiv_ne_zero_orbit : (KapGGStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ), X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ∀ x ∈ X.dom, w0 x ≠ 0 → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X))) 0).det ≠ 0 → ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (lact γ (rmul x b)) z) / w0 (cpt X (lact γ (rmul x b)) z) : V (nd X))) 0).det ≠ 0) := by
  intro hK r X L w0 s hw0 hs x hx hwx hdet γ hγ b hb
  obtain ⟨U, Φ, bf, hU, h0U, hΦ, hΦ0, hsw⟩ := exists_swap X hb
  set y := lact γ (rmul x b) with hy
  have hyd : y ∈ X.dom := OntoS.dom_lact X hγ (OntoS.dom_rmul X hx hb)
  have hcpt : ∀ z ∈ U, cpt X y z = lact γ (rmul (cpt X x (Φ z)) (bf z)) := by
    intro z hz
    unfold cpt
    rw [hy, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, (hsw z hz).2, ExtFPf.rmul_assoc]
  have h0y : (0 : V (nd X)) ∈ OmF X y := by
    show cpt X y 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have h0x : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have hJ : (fderiv ℂ Φ 0).det = bchar (kapW X) (bf 0) :=
    hK r X y x γ (U ∩ OmF X y) Φ bf (hU.inter (OntoB.isOpen_OmF X y)) (hΦ.mono Set.inter_subset_left)
      (fun z hz => ⟨hz.2, (hsw z hz.1).1, hcpt z hz.1⟩) 0 ⟨h0U, h0y⟩
  have hJ0 : (fderiv ℂ Φ 0).det ≠ 0 := hJ ▸ OntoE.bchar_ne X _ (hsw 0 h0U).1
  have hΦd : DifferentiableAt ℂ Φ 0 := hΦ.differentiableAt (hU.mem_nhds h0U)
  have hnx : OmF X x ∈ 𝓝 (0 : V (nd X)) := (OntoB.isOpen_OmF X x).mem_nhds h0x
  set F : V (nd X) → V (nd X) := fun z : V (nd X) =>
    (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X)) with hF
  have hFd : DifferentiableAt ℂ F 0 := by
    have hw : DifferentiableAt ℂ (fun z => w0 (cpt X x z)) 0 :=
      (OntoB.hol_comp X x hw0.1).differentiableAt hnx
    have hsk : ∀ k, DifferentiableAt ℂ (fun z => s k (cpt X x z)) 0 := fun k =>
      (OntoB.hol_comp X x (hs k).1).differentiableAt hnx
    rw [hF]
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have hne : w0 (cpt X x 0) ≠ 0 := by rwa [IW.cpt_zero]
    have := (hsk k).mul (hw.inv hne)
    simp only [div_eq_mul_inv]
    exact this
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X y z) / w0 (cpt X y z) : V (nd X))) =ᶠ[𝓝 0] F ∘ Φ := by
    have h1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), Φ z ∈ OmF X x :=
      hΦd.continuousAt.preimage_mem_nhds (by rwa [hΦ0])
    filter_upwards [hU.mem_nhds h0U, h1] with z hz hzx
    have hzx' : cpt X x (Φ z) ∈ X.dom := hzx
    have hbz := (hsw z hz).1
    have hd := OntoS.dom_rmul X hzx' hbz
    have hχ : X.χ L γ ≠ 0 := by
      intro h
      have := OntoE.chi_norm X L hγ
      rw [h, norm_zero] at this
      exact zero_ne_one this
    show _ = F (Φ z)
    rw [hF]
    show (WithLp.toLp 2 _ : V (nd X)) = WithLp.toLp 2 _
    congr 1
    funext k
    rw [hcpt z hz, (hs k).2.2 γ hγ _ hd, hw0.2.2 γ hγ _ hd, mul_div_mul_left _ _ hχ,
      (hs k).2.1 _ hzx' _ hbz, hw0.2.1 _ hzx' _ hbz, mul_div_mul_left _ _ (OntoE.bchar_ne X L hbz)]
  rw [hev.fderiv_eq, fderiv_comp 0 (by rwa [hΦ0]) hΦd, hΦ0]
  have : ((fderiv ℂ F 0).comp (fderiv ℂ Φ 0)).det = (fderiv ℂ F 0).det * (fderiv ℂ Φ 0).det := by
    unfold ContinuousLinearMap.det
    rw [← LinearMap.det_comp]
    rfl
  rw [this]
  exact mul_ne_zero hdet hJ0

end GlobalTheory.OrbitCoord
