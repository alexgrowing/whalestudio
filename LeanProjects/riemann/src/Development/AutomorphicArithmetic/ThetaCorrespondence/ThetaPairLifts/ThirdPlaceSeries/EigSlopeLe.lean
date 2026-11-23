import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeBaseStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCore

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefEig
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem actKeeps_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') : ActKeeps (κ := p.κ) p.O i := fun g f hf => by
  obtain ⟨cc, ph, hO⟩ := (hp.oneMap i).1
  obtain ⟨k, hk, -⟩ := (p.pins i).2.lift.lev g
  exact (hO.1 g k hk f hf).1
theorem exists_chi_algebraMap_eq_FW_chi_mul_psi_inv (p : PtAt ex Csz) (i : Fin D.R.m) (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) :
    ∃ χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ, ∀ u, algebraMap p.T.Q.c.F D.what₂.LL (χ u : p.T.Q.c.F) =
      (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) := by
  have hv := _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt p i hp.1 hp.2
  choose b hb using hv
  have hinj : Function.Injective (algebraMap p.T.Q.c.F D.what₂.LL) := (algebraMap p.T.Q.c.F D.what₂.LL).injective
  have hb0 : ∀ u, b u ≠ 0 := fun u h => by
    have := hb u
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  refine ⟨{ toFun := fun u => Units.mk0 (b u) (hb0 u), map_one' := ?_, map_mul' := ?_ }, fun u => hb u⟩
  · refine Units.ext (hinj ?_)
    simp [hb]
  · intro u v
    refine Units.ext (hinj ?_)
    simp only [Units.val_mk0, Units.val_mul, map_mul, hb, Subgroup.coe_mul, MonoidHom.inv_apply]
    push_cast
    ring
set_option maxHeartbeats 1000000 in
theorem exists_finite_group_lev_char_slope : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∃ (G : Type) (_ : Group G) (_ : Finite G) (lev : G → ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La) × ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La)) (χ : G →* (p.T.Q.c.F)ˣ), ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ slope_sq (normW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)) (eigLat (p.T.U ((i : ℕ) + 1)) lev χ (Gk p i)) ≤ muCore p i := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hp hi hG hW hH hF
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.DefEig.exists_chi_algebraMap_eq_FW_chi_mul_psi_inv p i hp
  have hK := _root_.GlobalTheory.DefEig.actKeeps_alt p i hp.1
  have hρ := (p.rhoGeo i).1 hK
  have hsm : ∀ (u : (p.F.lv2.lvl false).P) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n),
      ((p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f) : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
        (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
          ((p.fw.e i f : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := fun u f => by
    rw [LinearEquiv.map_smul, Submodule.coe_smul, ← hχ u, algebraMap_smul]
  refine ⟨(p.F.lv2.lvl false).P, inferInstance, inferInstance, fun g => (p.O i).lev2 (g : p.P.Gp), χ, actLev_levB p i,
    _root_.GlobalTheory.T.freePt_last_index_of_fnAlgClosed p i PP A M hp hi hG hW hH hF, le_of_eq ?_⟩
  have hAB : ((eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ).comap
        (cuspW (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.T.U ((i : ℕ) + 1)) (Gk p i)).subtype).restrictScalars (𝓞 p.T.Q.c.F) =
      ((Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)).comap (VK p.fw i).subtype).restrictScalars (𝓞 p.T.Q.c.F) := by
    ext x
    change (x : p.T.R ((i : ℕ) + 1)) ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      (x : p.T.R ((i : ℕ) + 1)) ∈ Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)
    have hx : (x : p.T.R ((i : ℕ) + 1)) ∈ p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n := by
      exact (cuspW_wtZ (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c) (U := p.T.U ((i : ℕ) + 1))
        (wtA (p.κ i)) (p.κ i).n).le x.2
    constructor
    · intro h
      rw [mem_eigSub_iff] at h
      apply Submodule.subset_span
      refine ⟨hx, fun u => ?_⟩
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨x, hx⟩
      rw [← h2]
      have h3 : (⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) (x : p.T.R ((i : ℕ) + 1)), hf'⟩ :
          p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨x, hx⟩ :=
        Subtype.ext (h u)
      exact (congrArg (fun y => ((p.fw.e i y : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL)) h3).trans (hsm u ⟨x, hx⟩)
    · intro h
      refine Submodule.span_le.2 ?_ h
      rintro f ⟨hf, hT⟩
      rw [SetLike.mem_coe, mem_eigSub_iff]
      intro u
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨f, hf⟩
      have h4 : (p.R.FW i).ρ (u : p.P.Gp) ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
          (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
            ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := hT u
      have h5 : (p.fw.e i ⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f, hf'⟩) =
          p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨f, hf⟩) := by
        exact Subtype.ext (h2.trans (h4.trans (hsm u ⟨f, hf⟩).symm))
      exact congrArg Subtype.val ((p.fw.e i).injective h5)
  have key : eigLat (p.T.U ((i : ℕ) + 1)) (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ (Gk p i) =
      latTypeK p.fw p.F.lv2 i :=
    congrArg (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ⊓ ·) hAB
  rw [muCore, ← key]
end GlobalTheory.DefEig
end
