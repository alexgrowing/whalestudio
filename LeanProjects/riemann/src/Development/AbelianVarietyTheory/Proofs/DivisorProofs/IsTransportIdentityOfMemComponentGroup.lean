import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransporterMovesFrameReadsInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityTransportsComponentToItself

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareOn.OneFrame

section Geo

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
variable {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_marking_match_at (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) :
    ∃ T : ∀ k, Dw.La →ₗ[𝓞 E] (U.X k).Λ, (∀ k, BijMod l.Mb (T k)) ∧
      ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA →
      ∀ (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' →
      ∃ (a : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') a) (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ),
        (∀ v : (U.X k).Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (gam v : Fin r → E)) ∧
        (∀ u, gam (T k (gM u)) - T k' u ∈ l.Mb • (⊤ : Submodule (𝓞 E) (U.X k').Λ)) ∧
        ∃ b ∈ Bor (U.X k').Ψ r, x'.1 = rmul (lact a (castFr h.psi x.1)) b := by
  obtain ⟨T, hT, hmv⟩ := exists_marking_tri hU
  refine ⟨T, hT, fun ρ ν gM gA hν k k' x x' y' t hm hb => ?_⟩
  obtain ⟨gam, A, htr, hA0, hA, hmk⟩ := hmv ρ ν gM gA hν k k' x x' y' t hm hb
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ :=
    GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry E r (U.X k) (U.X k') (hxi k k') gam htr
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -, -, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hA (e.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  rcases hε with rfl | rfl
  · have h : IsMatch (U.X k) (U.X k') a :=
      ⟨hΨ, hp, by rw [hξ, _root_.one_mul], fun u v => by rw [hiso, _root_.one_mul], hlat⟩
    obtain ⟨b, hbB, hxb, -⟩ := GlobalTheory.PeriodBorel.borel_of_periods E r _ _ a h (fun τ => Dw.mult (e.symm τ)) m1 m2
      x.1 x.2 x'.1 x'.2 (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    exact ⟨a, h, gam, hav, hmk, b, hbB, hxb⟩
  · exact (GlobalTheory.AntiIsom.not_antiIsometry E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2
      x'.1 x'.2 (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

end Geo

section Frames

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem unit_mem_Bor (Ψ : Finset (E →+* ℂ)) :
    ((fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) : Frame Ψ r) ∈ Bor Ψ r := fun τ =>
  ⟨by
    show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp, fun a c hac => by
    show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne hac.ne'⟩

theorem rmul_unit {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    rmul x ((fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) : Frame Ψ r) = x := by
  funext τ
  exact Matrix.mul_one (mat x τ)

theorem eq_of_lact_eq_rmul (X : Data E r) {g a : GL (Fin r) E} (hg : g ∈ X.Γ) (ha : a ∈ X.Γ) {x b : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) (e : lact g x = rmul (lact a x) b) : g = a := by
  have h1 := X.Γ_free (a⁻¹ * g) (X.Γ.mul_mem (X.Γ.inv_mem ha) hg) x hx b hb (by
    funext τ
    have e1 : (g : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
        (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ := congrFun e τ
    show ((a⁻¹ * g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ * mat b τ
    rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul])
  exact (inv_mul_eq_one.1 h1).symm

end Frames

end GlobalTheory.ShareOn.OneFrame

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_Γ_of_cong_half {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
    {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (k : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E)
    (ha : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k) a)
    (hcong : ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ,
      (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ) :
    a ∈ ((uAt r v i).X k).Γ := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨Xx, ⟨e1, e2, e3⟩, -⟩ := GlobalTheory.ModelLatticeCheck.holds_by_value D (r.used v).full.toCore
    (h.laws v).p.toLawsCore ((i : ℕ) + 1) hj (r.used v).full.σ₀ (r.used v).full.toCore.good_σ₀ k
  have eL : Xx.L' = lattice₂ D ((uAt r v i).X k).Λ := by
    rw [GlobalTheory.ModelLatExamples.eq_latP D Xx.Λ Xx.L' e3]
    show lattice₂ D Xx.toData.Λ = _
    rw [e1]
  have hGm : Xx.Gm = ((uAt r v i).X k).Gm := congrArg Data.Gm e1
  have hΛ : Xx.Λ = ((uAt r v i).X k).Λ := congrArg Data.Λ e1
  have hΓ : Xx.Γ = ((uAt r v i).X k).Γ := congrArg Data.Γ e1
  have hlatL := mem_localLattice_iff_mulVec D _ ha.lat
  have hM := sub_mem_natSMul_of_unitary Xx.Gm Xx.L' Xx.L'_int Xx.L'_dual p.T.Q.H.bar (fun a => p.T.Q.H.bar_eq a)
    p.T.Q.l.Mb p.T.Q.l.M (by have := p.T.Q.l.three_le; omega) p.T.Q.l.prod p.T.Q.l.coprime a
    (by rw [hGm]; exact ha.iso) (by rw [eL]; exact hlatL) (by rw [eL]; exact hcong)
  have hMΛ := sub_mem_natSMul_span D.host.AA Xx.L' Xx.Λ e3 _ p.T.Q.l.M hM
  have hin := Xx.cong a ⟨by rw [hGm]; exact ha.iso, by rw [hΛ]; exact ha.lat⟩ (by rw [e2]; exact hMΛ)
  rw [← hΓ]
  exact hin

open GlobalTheory.ShareOn.OneFrame in
set_option maxHeartbeats 1000000 in

theorem isTransp_one_of_mem_Γ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp) (γ₀ : GL (Fin D.R.r) D.host.E), γ₀ ∈ ((uAt r v i).X k).Γ → IsTransp p r i v ψ 1 k k γ₀ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v ψ k γ₀ hγ₀
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hp := (h.laws v).p
  have hpin := hp.pins
  have hσ := (r.used v).full.toCore.good_σ₀
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpin.2.2.2 _ hj).1, (hpin.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q _ hpq hpin.2.1.2
  have hU : IsUnf (uAt r v i) := hp.unf _ hj _ hσ
  have hm₀ := GlobalTheory.LevelCusp.isMatch_of_isUStab _ (((uAt r v i).X k).Γ_stab γ₀ hγ₀)
  obtain ⟨-, -, hsy, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)

  have hfr : ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom),
      ∃ (hy : lact γ₀ x ∈ ((uAt r v i).X k).dom) (t : _),
        FrBor t ((uAt r v i).un k ⟨lact γ₀ x, hy⟩)
          (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩)) := by
    intro x hx
    have hy : lact γ₀ x ∈ ((uAt r v i).X k).dom := hm₀.mem_dom hx
    obtain ⟨t, ht⟩ := (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨lact γ₀ x, hy⟩).2
      ⟨γ₀, hγ₀, _, unit_mem_Bor _, by rw [rmul_unit]⟩
    have hf := hL.func 1 _ ((uAt r v i).un k ⟨x, hx⟩) ((uAt r v i).un k ⟨x, hx⟩)
      (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩))
      (hL.one _ _) (Formalism.L2.Pj.mvPt_spec hL.total 1 _)
    have he : (uAt r v i).un k ⟨x, hx⟩ =
        mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩) :=
      (GlobalTheory.LevelLawsCompare.frMap_id_iff _ _).1 hf
    exact ⟨hy, _, (congrArg (FrBor _ ((uAt r v i).un k ⟨lact γ₀ x, hy⟩)) he).mp (hsy _ _ _ ht)⟩
  refine ⟨hm₀, hfr, ?_⟩

  obtain ⟨T, hTb, hmv⟩ := exists_marking_match_at (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (hp.xiAbs _ hj _ hσ k τ).trans (hp.xiAbs _ hj _ hσ k' τ).symm)
  have hI : p.T.Q.l.Mb ≠ ⊥ := fun e => by
    have h1 := natCast_M_mem p.T.Q.l
    rw [e, Ideal.mem_bot, Nat.cast_eq_zero] at h1
    have := p.T.Q.l.three_le
    omega
  obtain ⟨s, f, hf, hfs⟩ := exists_scale D hI D.R.r
  have hb : BijMod p.T.Q.l.Mb (f ((uAt r v i).X k).Λ ∘ₗ T k) := (hTb k).comp (hf _)
  obtain ⟨x, hx⟩ := (GlobalTheory.frames_isConnected _ _ ((uAt r v i).X k)).nonempty
  obtain ⟨hy, t, ht⟩ := hfr x hx
  obtain ⟨ρ, ν, -, hν, hm⟩ := mvPt_spec hL.total 1 ((uAt r v i).un k ⟨x, hx⟩)
  obtain ⟨a, ha, gam, hav, hmk, b, hbB, hxb⟩ := hmv ρ ν _ _ hν k k ⟨x, hx⟩ ⟨lact γ₀ x, hy⟩ _ t hm ht
  have hrd : ∀ w : lattice₂ D ((uAt r v i).X k).Λ,
      Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k).Λ)))
        (latPMap D _ ha.lat w) = Submodule.Quotient.mk w := fun w => by
    refine (hb.reads hb 1 (liftLa 1) (liftLa_spec 1) (latPMap D _ ha.lat) (fun u => ?_) w).trans
      (hb.equiv.apply_symm_apply _)
    have h1 := map_mem_smul_top _ (f ((uAt r v i).X k).Λ) (hmk u)
    have h2 : latPMap D _ ha.lat (f ((uAt r v i).X k).Λ (T k (liftLa (l := p.T.Q.l) 1 u))) =
        f ((uAt r v i).X k).Λ (gam (T k (liftLa (l := p.T.Q.l) 1 u))) := by
      refine Subtype.ext ?_
      refine (congrArg (Matrix.mulVec _) (hfs _ _)).trans (Eq.trans ?_ (hfs _ _).symm)
      rw [Matrix.mulVec_smul]
      exact congrArg _ (hav _)
    have h3 := (f ((uAt r v i).X k).Λ).map_sub (gam (T k (liftLa (l := p.T.Q.l) 1 u))) (T k u)
    rw [← h2] at h3
    exact h3 ▸ h1
  have haΓ : a ∈ ((uAt r v i).X k).Γ := mem_Γ_of_cong_half p r h i v k a ha fun w hw => by
    have hq := (Submodule.Quotient.eq _).1 (hrd ⟨w, hw⟩)
    have hmem := Submodule.mem_map_of_mem (f := (lattice₂ D ((uAt r v i).X k).Λ).subtype) hq
    rw [Submodule.map_smul'', Submodule.map_subtype_top] at hmem
    exact hmem
  have hga : γ₀ = a := eq_of_lact_eq_rmul _ hγ₀ haΓ hx hbB hxb
  subst hga
  intro w
  exact ⟨(mem_localLattice_iff_mulVec D _ ha.lat _).1 w.2, (hrd w).trans ((ψ k).apply_symm_apply _).symm⟩

end GlobalTheory.ShareOn

end
