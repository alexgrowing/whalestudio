import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransporterMovesFrameReadsInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameActionUpperTriangularBlockExists

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareOn.NearFrames

section Comp

open NumberField AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

theorem comp_eq (hσ : GoodEmb c σ) (hU : IsUnf U) {k k' : U.Comp}
    (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k' x') h
  obtain ⟨γ, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem eventually_comp (hσ : GoodEmb c σ) (hU : IsUnf U) (ρ : Xo.X ⟶ Xo.X) (hρ : ρ ≫ Xo.s = Xo.s)
    {k k' : U.Comp} (z₀ : (U.X k).dom) (x₀ : (U.X k').dom) (h₀ : (U.un k' x₀).x = (U.un k z₀).x ≫ ρ) :
    ∀ᶠ z in nhds z₀, ∃ x : (U.X k').dom, (U.un k' x).x = (U.un k z).x ≫ ρ := by
  classical
  obtain ⟨hr, hty, -, hfib, -, g, e, F, ik, ψ, hef, hun⟩ := hU
  let n := Module.finrank ℂ (Frame (U.X k).Ψ r)
  let L : Frame (U.X k).Ψ r ≃L[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ _).equivFun.toContinuousLinearEquiv
  have hB : IsOpen (L.symm ⁻¹' (U.X k).dom) := (FourierCoefficientDomain.isOpen_dom _).preimage L.symm.continuous
  let x : (Fin n → ℂ) → (U.X k).dom := fun b => if h : L.symm b ∈ (U.X k).dom then ⟨_, h⟩ else z₀
  have hxb : ∀ b ∈ L.symm ⁻¹' (U.X k).dom, (x b).1 = L.symm b := fun b hb => by
    simp only [x]; rw [dif_pos (show L.symm b ∈ (U.X k).dom from hb)]
  have hxL : ∀ z : (U.X k).dom, x (L z.1) = z := fun z =>
    Subtype.ext ((hxb _ (by simp)).trans (L.symm_apply_apply _))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) (L.symm ⁻¹' (U.X k).dom) := fun τ a c =>
    (differentiable_pi.1 (differentiable_pi.1 (differentiable_pi.1 L.symm.differentiable τ) a) c).differentiableOn.congr
      fun b hb => by rw [hxb b hb]; rfl
  choose P hP hP' hx _ using hun k
  have h1 := (F.hol (ik k) n _ (fun b => P (x b)) hB ⟨fun b _ => hP' _, fun a => differentiableOn_pi.2 fun i => by
    simp only [hP]
    exact GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr _ (fun b _ => (x b).2) hd _ _ _⟩).1
  have hb₀ : L z₀.1 ∈ L.symm ⁻¹' (U.X k).dom := by simp
  obtain ⟨B₁, i, Q, hB₁, hb₁, hs₁, hQ, hyQ⟩ := F.lift n _ (fun b => F.u (ik k) (P (x b)) ≫ ρ) hB (fun b _ => by
    rw [Category.assoc, hρ, F.over_σ _ _ (hP' _)]) (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h1 _) _ hb₀
  obtain ⟨P₁, hP₁, hP₁', hx₁, -⟩ := hun k' x₀
  obtain rfl : ik k' = i := F.disj _ _ _ _ hP₁' (hQ.1 _ hb₁)
    (hx₁.symm.trans (h₀.trans ((hyQ _ hb₁).trans (by rw [hxL]; exact congrArg (· ≫ ρ) (hx z₀).symm)).symm))
  obtain ⟨B₂, x', hB₂, hb₂, hs₂, -, hx'⟩ := HolChartLift.exists_frames_of_holPeriods c σ e _ (U.X k') (ψ k') hσ
    (F.sig _).1 (F.sig _).2 hr (hty k').1 (hty k').2 (hef k')
    (FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k') (ψ k') hσ hr (hty k').1 (hty k').2 (hef k')
      x₀.1 x₀.2 P₁ hP₁ hP₁') hB₁ Q hQ hb₁
  filter_upwards [(L.continuous.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (hB₂.mem_nhds hb₂)]
    with z hz
  obtain ⟨y, hy, hper, -⟩ := hx' _ hz
  obtain ⟨P₀, hP₀, -, hux, -⟩ := hun k' ⟨y, hy⟩
  obtain rfl : P₀ = Q (L z.1) := AddMonoidHom.ext fun a => funext fun i => (hP₀ a i).trans (hper a i).symm
  refine ⟨⟨y, hy⟩, hux.trans ((hyQ _ (hs₂ hz)).trans ?_)⟩
  rw [hx]
  exact congrArg (fun w => F.u (ik k) (P w) ≫ ρ) (hxL z)

theorem comp_const (hσ : GoodEmb c σ) (hU : IsUnf U) (ρ : Xo.X ⟶ Xo.X) (hρ : ρ ≫ Xo.s = Xo.s) (k : U.Comp)
    (κ : (U.X k).dom → U.Comp) (hκ : ∀ z, ∃ x : (U.X (κ z)).dom, (U.un (κ z) x).x = (U.un k z).x ≫ ρ)
    (z z' : (U.X k).dom) : κ z = κ z' := by
  haveI : ConnectedSpace (U.X k).dom := isConnected_iff_connectedSpace.1 (GlobalTheory.frames_isConnected E r (U.X k))
  refine IsLocallyConstant.apply_eq_of_preconnectedSpace ((IsLocallyConstant.iff_eventually_eq κ).2 fun z₀ => ?_) z z'
  obtain ⟨x₀, h₀⟩ := hκ z₀
  filter_upwards [eventually_comp hσ hU ρ hρ z₀ x₀ h₀] with w hw
  obtain ⟨x, hx⟩ := hw
  obtain ⟨x', hx'⟩ := hκ w
  exact comp_eq hσ hU x x' (hx.trans hx'.symm)

end Comp

section Closed

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in
theorem map_inv_mul (γ : GL (Fin r) E) (τ : E →+* ℂ) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * (γ : Matrix (Fin r) (Fin r) E).map τ = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero τ) (map_one τ)]

theorem eventually_related (X : Data E r) {V : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    {f g : V → Frame X.Ψ r} (hf : Continuous f) (hg : Continuous g) {D S : Set V} {x : V} (hD : D ∈ nhds x)
    (hfD : ∀ z ∈ D, f z ∈ X.dom) (hgD : ∀ z ∈ D, g z ∈ X.dom) (hS : closure S ∈ nhds x)
    (h : ∀ z ∈ S, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, g z = rmul (lact γ (f z)) b) :
    ∀ᶠ z in nhds x, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, g z = rmul (lact γ (f z)) b := by
  classical
  obtain ⟨K, hKx, hKD, hK⟩ := local_compact_nhds hD
  have hfin := GlobalTheory.BlockTransporter.finite_blockTransporter E r X (f '' K ∪ g '' K)
    ((hK.image hf).union (hK.image hg))
    (by rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩); exacts [hfD z (hKD hz), hgD z (hKD hz)])
  let C : GL (Fin r) E → Set V := fun γ => {z | ∀ (τ : X.Ψ) (p q : Fin r), q < p →
    ((mat (f z) τ).adjugate * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (g z) τ)) p q = 0}
  have hC : ∀ γ, IsClosed (C γ) := fun γ => by
    simp only [C, Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ => ?_
    have h1 : Continuous fun z => mat (f z) τ := (continuous_apply τ).comp hf
    have h2 : Continuous fun z => mat (g z) τ := (continuous_apply τ).comp hg
    exact isClosed_eq ((h1.matrix_adjugate.matrix_mul (continuous_const.matrix_mul h2)).matrix_elem p q)
      continuous_const
  have hcl := hfin.isClosed_biUnion fun γ _ => hC γ
  filter_upwards [interior_mem_nhds.2 hKx, hS] with z hzK hzS
  refine (Set.mem_iUnion₂.1 (closure_minimal (s := interior K ∩ S) ?_ hcl
    (isOpen_interior.inter_closure ⟨hzK, hzS⟩))).elim fun γ hγ' => ?_
  swap
  · obtain ⟨⟨hγ, -⟩, hzC⟩ := hγ'
    have hA : ∀ τ, IsUnit (mat (f z) τ).det := fun τ => ((hfD z (hKD (interior_subset hzK)) τ).1).isUnit
    have hG : ∀ τ, (mat (g z) τ).det ≠ 0 := fun τ => (hgD z (hKD (interior_subset hzK)) τ).1
    refine ⟨γ⁻¹, inv_mem hγ, fun τ => ((mat (f z) τ)⁻¹ * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (g z) τ) :
      Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun p q hpq => ?_⟩, funext fun τ => ?_⟩
    · show ((mat (f z) τ)⁻¹ * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (g z) τ)).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_mul]
      refine mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hA τ)).ne_zero (mul_ne_zero ?_ (hG τ))
      exact (Matrix.isUnit_det_of_left_inverse (map_inv_mul γ τ.1)).ne_zero
    · show ((mat (f z) τ)⁻¹ * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (g z) τ)) p q = 0
      rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, hzC τ p q hpq, smul_zero]
    · show mat (g z) τ = (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (f z) τ) *
        ((mat (f z) τ)⁻¹ * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (g z) τ))
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hA τ), ← Matrix.mul_assoc, map_inv_mul,
        Matrix.one_mul]
  · rintro w ⟨hwK, hwS⟩
    obtain ⟨γ, hγ, b, hb, e⟩ := h w hwS
    have e' : ∀ τ : X.Ψ, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (g w) τ =
        mat (f w) τ * mat b τ := fun τ => by
      have : mat (g w) τ = ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (f w) τ) * mat b τ := congrFun e τ
      rw [this, Matrix.mul_assoc, ← Matrix.mul_assoc, map_inv_mul, Matrix.one_mul]
    refine Set.mem_iUnion₂.2 ⟨γ⁻¹, ⟨inv_mem hγ, g w, Or.inr ⟨w, interior_subset hwK, rfl⟩, f w,
      Or.inl ⟨w, interior_subset hwK, rfl⟩, b, fun τ => (hb τ).1, fun τ p q h1 h2 => (hb τ).2 p q ?_,
      funext e'⟩, fun τ p q hpq => ?_⟩
    · rw [Fin.lt_def]; omega
    · rw [e', ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply]
      exact smul_eq_zero_of_right _ ((hb τ).2 p q hpq)

end Closed

end GlobalTheory.ShareOn.NearFrames

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem ReadsInv.mul_inv_mem (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k)
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k₁ : (uAt r v i).Comp) (a₁ a₂ : GL (Fin D.R.r) D.host.E)
    (hm₁ : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k₁) a₁)
    (hm₂ : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k₁) a₂)
    (hq₁ : ReadsInv p r i v ψ γ k k₁ a₁) (hq₂ : ReadsInv p r i v ψ γ k k₁ a₂) :
    a₁ * a₂⁻¹ ∈ ((uAt r v i).X k₁).Γ := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨Xx, ⟨e1, e2, e3⟩, -⟩ := GlobalTheory.ModelLatticeCheck.holds_by_value D (r.used v).full.toCore
    (h.laws v).p.toLawsCore ((i : ℕ) + 1) hj (r.used v).full.σ₀ (r.used v).full.toCore.good_σ₀ k₁
  have eL : Xx.L' = lattice₂ D ((uAt r v i).X k₁).Λ := by
    rw [GlobalTheory.ModelLatExamples.eq_latP D Xx.Λ Xx.L' e3]
    show lattice₂ D Xx.toData.Λ = _
    rw [e1]
  have hGm : Xx.Gm = ((uAt r v i).X k₁).Gm := congrArg Data.Gm e1
  have hΛ : Xx.Λ = ((uAt r v i).X k₁).Λ := congrArg Data.Λ e1
  have hΓ : Xx.Γ = ((uAt r v i).X k₁).Γ := congrArg Data.Γ e1
  have hεm : ((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
      (a₁ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * ((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) :=
    Matrix.GeneralLinearGroup.coe_mul _ _
  have ha₂ : (a₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * ((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hiso : ∀ u w, herm ((uAt r v i).X k₁).Gm
      (((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ u)
      (((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w) =
      herm ((uAt r v i).X k₁).Gm u w := by
    intro u w
    rw [hεm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hm₁.iso, ← hm₂.iso, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ha₂, Matrix.one_mulVec, Matrix.one_mulVec]
  have hlatΛ : ∀ w, w ∈ ((uAt r v i).X k₁).Λ ↔
      ((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w ∈
        ((uAt r v i).X k₁).Λ := by
    intro w
    rw [hεm, ← Matrix.mulVec_mulVec, ← hm₁.lat]
    have := hm₂.lat (((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w)
    rw [Matrix.mulVec_mulVec, ha₂, Matrix.one_mulVec] at this
    exact this.symm
  have hlatL := mem_localLattice_iff_mulVec D _ hlatΛ
  have hcong : ∀ w ∈ lattice₂ D ((uAt r v i).X k₁).Λ,
      ((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w - w ∈
        p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k₁).Λ := by
    intro w hw
    have ew : (a₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ
        (((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ha₂, Matrix.one_mulVec]
    have hu : ((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w ∈ lattice₂ D ((uAt r v i).X k).Λ :=
      (mem_localLattice_iff_mulVec D _ hm₂.lat _).2 (ew.symm ▸ hw)
    obtain ⟨hw₁, q₁⟩ := hq₁ ⟨_, hu⟩
    obtain ⟨hw₂, q₂⟩ := hq₂ ⟨_, hu⟩
    have hq := q₁.trans q₂.symm
    rw [Submodule.Quotient.eq] at hq
    have hmem := Submodule.mem_map_of_mem (f := (lattice₂ D ((uAt r v i).X k₁).Λ).subtype) hq
    rw [Submodule.map_smul'', Submodule.map_subtype_top] at hmem
    have e : ((a₁ * a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w - w =
        (a₁ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w) -
          (a₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (((a₂⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix _ _ _) *ᵥ w) := by
      rw [ew, hεm, Matrix.mulVec_mulVec]
    rw [e]
    simpa using hmem
  have hM := sub_mem_natSMul_of_unitary Xx.Gm Xx.L' Xx.L'_int Xx.L'_dual p.T.Q.H.bar (fun a => p.T.Q.H.bar_eq a)
    p.T.Q.l.Mb p.T.Q.l.M (by have := p.T.Q.l.three_le; omega) p.T.Q.l.prod p.T.Q.l.coprime (a₁ * a₂⁻¹)
    (by rw [hGm]; exact hiso) (by rw [eL]; exact hlatL) (by rw [eL]; exact hcong)
  have hMΛ := sub_mem_natSMul_span D.host.AA Xx.L' Xx.Λ e3 _ p.T.Q.l.M hM
  have hin := Xx.cong (a₁ * a₂⁻¹) ⟨by rw [hGm]; exact hiso, by rw [hΛ]; exact hlatΛ⟩ (by rw [e2]; exact hMΛ)
  rw [← hΓ]
  exact hin

theorem MovesAt.target_eq (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k : (uAt r v i).Comp) (κ : ((uAt r v i).X k).dom → (uAt r v i).Comp)
    (a : ((uAt r v i).X k).dom → GL (Fin D.R.r) D.host.E)
    (hm : ∀ z, GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X (κ z)) (a z))
    (hM : ∀ z, MovesAt p r i v γ k (κ z) (a z) (hm z) z.1 z.2) (z z' : ((uAt r v i).X k).dom) : κ z = κ z' := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hp := (h.laws v).p
  have hpin := hp.pins
  have hσ := (r.used v).full.toCore.good_σ₀
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpin.2.2.2 _ hj).1, (hpin.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q _ hpq hpin.2.1.2
  have hU := hp.unf _ hj _ hσ
  have hA : (r.used v).full.Q.l.A.Coprime (r.used v).full.Q.l.M := by
    rw [show (r.used v).full.Q.l.A = 1 from hpin.2.1.2]; exact Nat.coprime_one_left _
  obtain ⟨ρ, ν, hi, hν⟩ := GlobalTheory.LevelActionLaws.exists_move hpq hA ((r.used v).full.Q.Xo ((i : ℕ) + 1)) γ
  refine NearFrames.comp_const (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσ hU ρ hν.1 k κ (fun w => ?_) z z'
  obtain ⟨hy, t, ht⟩ := hM w
  have hm' := GlobalTheory.LevelActionLaws.frMove_transfer hpq hA _ _ γ hi hν
    (mvPt_spec hL.total γ ((uAt r v i).un k w))
  exact ⟨⟨_, hy⟩, ht.1.symm.trans hm'.1⟩

theorem exists_movesAt_forall_readsInv (p : PtAt ex Csz) (hp : More p) (r : TwoRuns p.T p.P.Gp)
    (h : RunsOk (fw2 p) r) (hr : OwnPin r) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    ∃ ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k,
      ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
        (k : (uAt r v i).Comp), ∃ (k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E)
        (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a),
        ReadsInv p r i v ψ γ k k' a ∧ ∀ z hz, MovesAt p r i v γ k k' a hm z hz := by
  obtain ⟨ψ, hψ⟩ := exists_movesAt_readsInv p hp r h hr i v
  refine ⟨ψ, fun γ k => ?_⟩
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hU : IsUnf (uAt r v i) := (h.laws v).p.toLawsCore.unf _ hj _ (r.used v).full.toCore.good_σ₀
  obtain ⟨-, htr, -, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)
  choose κ a hm hR hM using fun z : ((uAt r v i).X k).dom => hψ γ k z.1 z.2
  obtain ⟨x₀, hx₀⟩ := (GlobalTheory.frames_isConnected _ _ ((uAt r v i).X k)).nonempty
  refine ⟨κ ⟨x₀, hx₀⟩, a _, hm _, hR _, fun z hz => ?_⟩
  have hk := MovesAt.target_eq p r h i v γ k κ a hm hM ⟨z, hz⟩ ⟨x₀, hx₀⟩
  have hm₀ := hm ⟨x₀, hx₀⟩
  have hR₀ := hR ⟨x₀, hx₀⟩
  have hM₁ := hM ⟨z, hz⟩
  have hR₁ := hR ⟨z, hz⟩
  show MovesAt p r i v γ k _ _ hm₀ z hz
  generalize hm ⟨z, hz⟩ = hm₁ at hM₁
  generalize a ⟨x₀, hx₀⟩ = a₀ at hm₀ hR₀
  generalize a ⟨z, hz⟩ = a₁ at hm₁ hM₁ hR₁
  generalize κ ⟨x₀, hx₀⟩ = k₀ at hm₀ hR₀ hk
  generalize κ ⟨z, hz⟩ = k₁ at hm₁ hM₁ hR₁ hk
  subst hk
  have hΓ := ReadsInv.mul_inv_mem p r h i v ψ γ k k₁ a₁ a₀ hm₁ hm₀ hR₁ hR₀
  obtain ⟨hy₁, t₁, f₁⟩ := hM₁
  have hy₀ : castFrame hm₀.psi (lact a₀ z) ∈ ((uAt r v i).X k₁).dom := hm₀.mem_dom hz
  let one : Frame ((uAt r v i).X k₁).Ψ D.R.r := fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hone : one ∈ Bor ((uAt r v i).X k₁).Ψ D.R.r := fun τ =>
    ⟨by show (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ).det ≠ 0; simp, fun p q hpq => Matrix.one_apply_ne hpq.ne'⟩
  have heq : castFrame hm₁.psi (lact a₁ z) = rmul (lact (a₁ * a₀⁻¹) (castFrame hm₀.psi (lact a₀ z))) one := by
    funext τ
    show (a₁ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat z ⟨τ.1, _⟩ =
      (((a₁ * a₀⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 *
        ((a₀ : Matrix _ _ _).map τ.1 * mat z ⟨τ.1, _⟩)) * (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    rw [Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel_right]
  obtain ⟨t', ht'⟩ := (hU.2.2.2.1 k₁ k₁ ⟨_, hy₀⟩ ⟨_, hy₁⟩).2 ⟨_, hΓ, one, hone, congrArg (Sigma.mk k₁) heq⟩
  exact ⟨hy₀, _, htr _ _ _ _ _ ht' f₁⟩

theorem movesAt_nhds_of_dense : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → (closure {z | ∃ hz : z ∈ ((uAt r v i).X k).dom, MovesAt p r i v γ k k' a hm z hz} ∈ nhds x → ∃ N ∈ nhds x, ∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), z ∈ N → MovesAt p r i v γ k k' a hm z hz) ∧ ∃ (k'' : (uAt r v i).Comp) (c : GL (Fin D.R.r) D.host.E) (hc : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k'') c), ∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k'' c hc z hz := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v γ k k' a hm x hx
  obtain ⟨ψ, hψ⟩ := exists_movesAt_forall_readsInv p hp r h hr i v
  obtain ⟨k'', c, hc, -, hM⟩ := hψ γ k
  refine ⟨fun hS => ?_, k'', c, hc, hM⟩
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hU : IsUnf (uAt r v i) := (h.laws v).p.toLawsCore.unf _ hj _ (r.used v).full.toCore.good_σ₀
  obtain ⟨-, htr, hsy, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)
  have step : ∀ z (hz : z ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k' a hm z hz →
      ∃ γ' ∈ ((uAt r v i).X k').Γ, ∃ b ∈ Bor ((uAt r v i).X k').Ψ D.R.r,
        (⟨k'', castFrame hc.psi (lact c z)⟩ : Σ k, Frame ((uAt r v i).X k).Ψ D.R.r) =
          ⟨k', rmul (lact γ' (castFrame hm.psi (lact a z))) b⟩ := by
    rintro z hz ⟨hy₁, t₁, f₁⟩
    obtain ⟨hy₂, t₂, f₂⟩ := hM z hz
    exact (hU.2.2.2.1 k' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).1 ⟨_, htr _ _ _ _ _ f₁ (hsy _ _ _ f₂)⟩
  obtain ⟨z₀, hz₀, hM₀⟩ := closure_nonempty_iff.1 ⟨x, mem_of_mem_nhds hS⟩
  have hk : k'' = k' := by
    obtain ⟨g₀, -, b₀, -, e₀⟩ := step z₀ hz₀ hM₀
    exact (Sigma.mk.inj_iff.1 e₀).1
  subst hk
  have hcont : ∀ (d : GL (Fin D.R.r) D.host.E) (e : ((uAt r v i).X k).Ψ = ((uAt r v i).X k'').Ψ),
      Continuous fun z : Frame ((uAt r v i).X k).Ψ D.R.r => castFrame e (lact d z) := fun d e =>
    continuous_pi fun τ => by
      have h2 : Continuous fun z : Frame ((uAt r v i).X k).Ψ D.R.r => mat z ⟨τ.1, by rw [e]; exact τ.2⟩ :=
        continuous_apply _
      exact (continuous_const (y := (d : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1)).matrix_mul h2
  have hev := NearFrames.eventually_related ((uAt r v i).X k'') (hcont a hm.psi) (hcont c hc.psi)
    ((FourierCoefficientDomain.isOpen_dom _).mem_nhds hx) (fun z hz => hm.mem_dom hz) (fun z hz => hc.mem_dom hz) hS
    (by
      rintro z ⟨hz, hMz⟩
      obtain ⟨γ', hγ', b, hb, e⟩ := step z hz hMz
      exact ⟨γ', hγ', b, hb, eq_of_heq (Sigma.mk.inj_iff.1 e).2⟩)
  refine ⟨_, hev, fun z hz ⟨γ', hγ', b, hb, e⟩ => ?_⟩
  obtain ⟨hy₂, t₂, f₂⟩ := hM z hz
  have hy₁ : castFrame hm.psi (lact a z) ∈ ((uAt r v i).X k'').dom := hm.mem_dom hz
  obtain ⟨t', ht'⟩ := (hU.2.2.2.1 k'' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).2 ⟨γ', hγ', b, hb, congrArg (Sigma.mk k'') e⟩
  exact ⟨hy₁, _, htr _ _ _ _ _ ht' f₂⟩

end GlobalTheory.ShareOn

end
