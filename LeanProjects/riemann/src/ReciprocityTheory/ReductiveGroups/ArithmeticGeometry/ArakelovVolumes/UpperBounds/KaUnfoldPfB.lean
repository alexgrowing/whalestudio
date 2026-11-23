import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import Lemmata.GeneralBFactVariant.Imports

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def untl (X : Data E r) (M : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
    Matrix (Fin r) (Fin r) ℂ := M.submatrix (eT X).symm (eT X).symm

theorem untl_tl (X : Data E r) (M : Matrix (Fin r) (Fin r) ℂ) : untl X (tl X M) = M := by
  ext a b; simp [untl, tl]

theorem tl_one (X : Data E r) : tl X (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  rw [tl, Matrix.submatrix_one_equiv]

theorem gm_mul (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ γ' : GL (Fin r) E) (τ : X.Ψ) :
    gm X x0 (γ * γ') τ = gm X x0 γ τ * gm X x0 γ' τ := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [gm, gm, gm, ← tl_mul]
  congr 1
  rw [Units.val_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (mat x0 τ) (mat x0 τ)⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem gm_one (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) :
    gm X x0 1 τ = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [gm, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.nonsing_inv_mul _ hu, tl_one]

theorem mat_lact_eq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ : GL (Fin r) E) (τ : X.Ψ) :
    mat (lact γ x0) τ = mat x0 τ * untl X (gm X x0 γ τ) := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [gm, untl_tl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]; rfl

theorem orth_dom (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) : x0 ∈ X.dom := by
  refine ExF.mem_dom_of_gramPos X fun τ => ⟨ExF.det_ne_of_orth X ho τ, ?_⟩
  have e : X.gramPos x0 τ = 1 := by
    ext a b
    simp only [Data.gramPos, ho τ, Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.castLE_inj]
    split_ifs <;> simp [sgn]
  rw [e]; exact Matrix.PosDef.one

def rho (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    GL (Fin r) E →* (Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) where
  toFun γ k := ⟨gm X x0 γ ((Fintype.equivFin X.Ψ).symm k), gm X x0 γ⁻¹ ((Fintype.equivFin X.Ψ).symm k),
    by rw [← gm_mul X ho, mul_inv_cancel, gm_one X ho],
    by rw [← gm_mul X ho, inv_mul_cancel, gm_one X ho]⟩
  map_one' := by funext k; exact Units.ext (gm_one X ho _)
  map_mul' γ γ' := by funext k; exact Units.ext (gm_mul X ho γ γ' _)

theorem rho_apply (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ : GL (Fin r) E)
    (k : Fin (Fintype.card X.Ψ)) :
    ((rho X ho γ k : GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) : Matrix _ _ ℂ) =
      gm X x0 γ ((Fintype.equivFin X.Ψ).symm k) := rfl

theorem lact_eq_of_rho (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ γ' : GL (Fin r) E}
    (h : rho X ho γ = rho X ho γ') : lact γ x0 = lact γ' x0 := by
  funext τ
  have hk := congrArg (fun g : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ =>
    (g (Fintype.equivFin X.Ψ τ)).val) h
  simp only [rho_apply, Equiv.symm_apply_apply] at hk
  have e1 := mat_lact_eq X ho γ τ
  have e2 := mat_lact_eq X ho γ' τ
  rw [hk, ← e2] at e1
  exact e1

theorem rho_inj (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    Function.Injective ((rho X ho).comp X.Γ.subtype) := by
  intro γ γ' h
  have hl : lact γ.1 x0 = lact γ'.1 x0 := lact_eq_of_rho X ho h
  have hδ : (γ'.1)⁻¹ * γ.1 ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem γ'.2) γ.2
  have h1 : lact ((γ'.1)⁻¹ * γ.1) x0 = rmul x0 (ExtFPf.oneF X) := by
    rw [ExtFPf.rmul_oneF, ← lact_lact, hl, lact_lact, inv_mul_cancel, lact_one]
  have := X.Γ_free _ hδ x0 (orth_dom X ho) _ (ExtFPf.oneF_mem X) h1
  exact Subtype.ext (inv_mul_eq_one.mp this).symm

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Phi (X : Data E r) (x0 : Frame X.Ψ r)
    (g : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) : Frame X.Ψ r :=
  fun τ => (mat x0 τ * untl X (g (Fintype.equivFin X.Ψ τ)).val : Matrix (Fin r) (Fin r) ℂ)

theorem Phi_rho (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ : GL (Fin r) E) :
    Phi X x0 (rho X ho γ) = lact γ x0 := by
  funext τ
  have := mat_lact_eq X ho γ τ
  rw [show mat (lact γ x0) τ = lact γ x0 τ from rfl] at this
  rw [this, Phi, rho_apply, Equiv.symm_apply_apply]

theorem Phi_cont (X : Data E r) (x0 : Frame X.Ψ r) : Continuous (Phi X x0) := by
  refine continuous_pi fun τ => ?_
  have hc : Continuous fun g : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ =>
      ((g (Fintype.equivFin X.Ψ τ) : GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
        Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :=
    Units.continuous_val.comp (continuous_apply _)
  exact Continuous.matrix_mul continuous_const (hc.matrix_submatrix _ _)

theorem disc (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (hPD : PropDisc X) :
    DiscreteTopology ((rho X ho).comp X.Γ.subtype).range := by
  apply discreteTopology_of_isOpen_singleton_one
  obtain ⟨U, hU, U', hU', hfin⟩ := hPD x0 (orth_dom X ho) x0 (orth_dom X ho)
  have h1 : Phi X x0 ⁻¹' U' ∈ 𝓝 (1 : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) := by
    refine (Phi_cont X x0).continuousAt.preimage_mem_nhds ?_
    rw [← map_one (rho X ho), Phi_rho, lact_one]; exact hU'
  have hF : IsClosed ((rho X ho '' {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r,
      lact γ u = rmul u' b}) \ {1}) := ((hfin.image _).sdiff).isClosed
  rw [isOpen_induced_iff]
  refine ⟨interior (Phi X x0 ⁻¹' U') \ _, isOpen_interior.sdiff hF, ?_⟩
  ext g
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨hg1, hg2⟩
    obtain ⟨γ, hγ⟩ := g.2
    apply Subtype.ext
    by_contra hne
    apply hg2
    have hU'γ : lact γ.1 x0 ∈ U' := by
      have := interior_subset hg1
      rw [Set.mem_preimage, ← hγ] at this
      rwa [MonoidHom.comp_apply, Subgroup.subtype_apply, Phi_rho] at this
    exact ⟨⟨γ.1, ⟨γ.2, x0, mem_of_mem_nhds hU, lact γ.1 x0, hU'γ, ExtFPf.oneF X, ExtFPf.oneF_mem X,
      (ExtFPf.rmul_oneF X _).symm⟩, hγ⟩, hne⟩
  · rintro rfl
    exact ⟨mem_interior_iff_mem_nhds.2 h1, fun h => h.2 rfl⟩

theorem upq_range (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    ∀ g ∈ ((rho X ho).comp X.Γ.subtype).range, ∀ k,
      IsUpq ((g k : GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) := by
  rintro g ⟨γ, rfl⟩ k
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply, rho_apply]
  exact gm_upq X ho γ.2 _

theorem kap_lact_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (bb : ℝ) (γ : GL (Fin r) E)
    (z : V (nd X)) :
    kap X x0 bb (lact γ (cpt X x0 z)) =
      ∏ k, dpow (mob (gm X x0 γ ((Fintype.equivFin X.Ψ).symm k))
        (ExF.Zt X z ((Fintype.equivFin X.Ψ).symm k))ᵀ) bb := by
  rw [kap, ← Equiv.prod_comp (Fintype.equivFin X.Ψ).symm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Mx_lact X ho, Mx_cpt X ho, Yb_mul _ _ (by rw [tl_nM₂₂, ExF.det_unipotentFrame_eq_one]; exact one_ne_zero), Yb_tl_nM]

def vpt (X : Data E r) (z : V (nd X)) : V (nD (Fintype.card X.Ψ) (r - X.p0) X.p0) :=
  WithLp.toLp 2 fun i =>
    (ExF.Zt X z ((Fintype.equivFin X.Ψ).symm (finProdFinEquiv.symm i).1))ᵀ
      (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2

theorem Zof_vpt (X : Data E r) (z : V (nd X)) (k : Fin (Fintype.card X.Ψ)) :
    Zof (vpt X z) k = (ExF.Zt X z ((Fintype.equivFin X.Ψ).symm k))ᵀ := by
  ext a b; simp [Zof, vpt, -finProdFinEquiv_symm_apply, Equiv.symm_apply_apply]

theorem sum_bound (hSB : SumBoundStatement) (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    (hPD : PropDisc X) (bb : ℝ) (hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ OmF X x0,
      ∑' γ : X.Γ, ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) ≤ C := by
  have hs : 2 * (Fintype.card X.Ψ : ℝ) * (((r - X.p0 + X.p0 : ℕ)) : ℝ) ^ 2 < bb := by
    have e : r - X.p0 + X.p0 = r := by have := X.p0_le; omega
    rw [e, Fintype.card_coe]
    have : 0 ≤ (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
    nlinarith
  have hdisc := disc X ho hPD
  obtain ⟨C, hC, hCb⟩ := hSB (Fintype.card X.Ψ) (r - X.p0) X.p0 bb hs _ hdisc (upq_range X ho)
  refine ⟨C, hC, fun z hz => ?_⟩
  have hv : vpt X z ∈ Dset (Fintype.card X.Ψ) (r - X.p0) X.p0 := fun k => by
    rw [Zof_vpt]; exact posDef_Zt X ho hz _
  refine le_trans (le_of_eq ?_) (hCb _ hv)
  rw [← (MonoidHom.ofInjective (rho_inj X ho)).toEquiv.tsum_eq]
  refine tsum_congr fun γ => ?_
  congr 1
  rw [kap_lact_cpt X ho]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Zof_vpt]
  rfl

end

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cont_cpt (X : Data E r) (x0 : Frame X.Ψ r) : Continuous (cpt X x0) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply, nmat]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  split_ifs <;> fun_prop

theorem lu_unique {n : ℕ} {N N' B B' : Matrix (Fin n) (Fin n) ℂ}
    (hN : N.BlockTriangular OrderDual.toDual) (hN' : N'.BlockTriangular OrderDual.toDual)
    (hd : ∀ i, N i i = 1) (hd' : ∀ i, N' i i = 1)
    (hB : B.BlockTriangular id) (hB' : B'.BlockTriangular id) (hBd : B.det ≠ 0)
    (h : N * B = N' * B') : N = N' := by
  exact Bl.general_b_fact_variant.goal1 hN hN' hd hd' hB hB' hBd h

theorem nM_low (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (ExF.nM X z τ).BlockTriangular OrderDual.toDual := fun _ _ hca => ExF.nM_upper X z τ hca

theorem nmat_inj (X : Data E r) {z z' : V (nd X)} (h : ∀ τ, ExF.nM X z τ = ExF.nM X z' τ) : z = z' := by
  ext i
  obtain ⟨⟨τ, ⟨⟨a, b⟩, hab⟩⟩, rfl⟩ := (Fintype.equivFin (Ent X)).surjective i
  have := congrFun (congrFun (h τ) a) b
  simpa [ExF.nM, mat, nmat, hab] using this

theorem cpt_inj (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z z' : V (nd X)} {b b' : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) (h : rmul (cpt X x0 z) b = rmul (cpt X x0 z') b') :
    z = z' ∧ b = b' := by
  have hN : ∀ τ, ExF.nM X z τ * mat b τ = ExF.nM X z' τ * mat b' τ := by
    intro τ
    have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
    have := congrArg (fun y : Frame X.Ψ r => (mat x0 τ)⁻¹ * mat y τ) h
    rwa [show mat (rmul (cpt X x0 z) b) τ = mat x0 τ * (ExF.nM X z τ * mat b τ) by
        show (mat x0 τ * ExF.nM X z τ) * mat b τ = _; exact Matrix.mul_assoc _ _ _,
      show mat (rmul (cpt X x0 z') b') τ = mat x0 τ * (ExF.nM X z' τ * mat b' τ) by
        show (mat x0 τ * ExF.nM X z' τ) * mat b' τ = _; exact Matrix.mul_assoc _ _ _,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  have hn : ∀ τ, ExF.nM X z τ = ExF.nM X z' τ := fun τ =>
    lu_unique (nM_low X z τ) (nM_low X z' τ) (ExF.nM_diag X z τ) (ExF.nM_diag X z' τ)
      (FrameDegreeData.upper_of_bor X hb τ) (FrameDegreeData.upper_of_bor X hb' τ) (hb τ).1 (hN τ)
  refine ⟨nmat_inj X hn, ?_⟩
  funext τ
  have hu : IsUnit (ExF.nM X z τ).det := by rw [ExF.det_nM]; exact isUnit_one
  have := hN τ
  rw [hn τ] at this
  rw [← hn τ] at this
  have := congrArg (fun M => (ExF.nM X z τ)⁻¹ * M) this
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  exact this

end

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
