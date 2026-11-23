import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma dmin_ortho {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin
  rw [hx τ]
  clear hx
  unfold lminor
  rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  apply Finset.prod_eq_one
  rintro a -
  simp only [Function.comp_apply]
  generalize (↑(Fin.castLE _ a) : ℕ) = b
  clear a
  clear x τ i
  unfold sgn
  split_ifs <;> simp

lemma pnorm_unit {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hu : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1) : X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  simp [norm_div, hu]

theorem supAtUnit (hL1 : Lam1RowSt) : SupAtUnitSt := by
  intro D T h hGam large₂ j hj w hrows hL hrn hlast σ hσ f hf hpos
  set X := (T.U j σ).X with hXdef
  set la := laU (T.U j σ) (wtA w) w.n with hladef
  set P := rdU (T.U j σ) f with hPdef

  have hE : supE X la P ≠ ⊤ := by
    intro h0; rw [supN, h0] at hpos; simp at hpos
  have hE0 : supE X la P ≠ 0 := by
    intro h0; rw [supN, h0] at hpos; simp at hpos
  have hhalf := ENNReal.half_lt_self hE0 hE
  have hhalf' := hhalf
  unfold supE at hhalf'
  obtain ⟨p, hp⟩ := lt_iSup_iff.1 hhalf'
  have hp' : supN X la P / 2 < (X p.1).pnorm (la p.1) (P p.1) p.2 := by
    have := ENNReal.toReal_lt_of_lt_ofReal hp
    rw [ENNReal.toReal_div] at this
    simpa [supN, supE] using this
  have hle : ∀ q : FPt X, (X q.1).pnorm (la q.1) (P q.1) q.2 ≤ supN X la P := by
    intro q
    have h1 : ENNReal.ofReal ((X q.1).pnorm (la q.1) (P q.1) q.2) ≤ supE X la P :=
      le_iSup (fun q : FPt X => ENNReal.ofReal ((X q.1).pnorm (la q.1) (P q.1) q.2)) q
    exact (ENNReal.ofReal_le_iff_le_toReal hE).1 h1
  obtain ⟨k, x, hx⟩ := p

  have hcusp := ((mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n f).1 hf).2 σ hσ
  let S : Submodule ℂ (FDSec X) :=
    { carrier := {Q | ∀ k, ∀ y ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ D.R.r, Q k (rmul y b) = bchar (la k) b * Q k y}
      add_mem' := by
        intro Q R hQ hR k y hy b hb
        simp only [Pi.add_apply, hQ k y hy b hb, hR k y hy b hb]; ring
      zero_mem' := by intro k y _ b _; simp
      smul_mem' := by
        intro c Q hQ k y hy b hb
        simp only [Pi.smul_apply, smul_eq_mul, hQ k y hy b hb]; ring }
  have hS : holSub X la ≤ S := Submodule.span_le.2 (fun Q hQ k y hy b hb => (hQ k).1.1.2.1 y hy b hb)
  have hPS : ∀ y ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ D.R.r, P k (rmul y b) = bchar (la k) b * P k y :=
    hS hcusp k

  have hb := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem (X k) hx
  have hx' := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom (X k) hx hb
  have hort := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf (X k) hx
  have hunit := dmin_ortho (X k) hort
  have hpn := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul (X k) (la k) (P k) hPS x hx _ hb
  have hla := ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel (X k) hx hb
  have h2 : supN X la P ≤ 2 * (X k).pnorm (la k) (P k) x := by linarith [hp']
  have hposx : 0 < (X k).pnorm (la k) (P k) x := by linarith
  obtain ⟨hl1, hl2⟩ := hL1 D T h hGam large₂ j hj w hrows hL hrn hlast σ hσ f hf k x hx
    (fun y hy => le_trans (hle ⟨k, y, hy⟩) h2) hposx
  refine ⟨k, ⟨_, hx'⟩, hunit, hort, ?_, by rw [hla]; exact hl1, by rw [hla]; exact hl2⟩
  have e : (X k).pnorm (la k) (P k) (rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf (X k) x)) =
      ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k ⟨_, hx'⟩))‖ := by
    rw [pnorm_unit (X k) (la k) (P k) hunit, hPdef]
    simp [rdU]
    rw [dif_pos hx']
  rw [← e, hpn]
  exact h2

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit
