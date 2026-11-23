import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FlagChartsCoverFramedFieldPoints
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem exists_countable_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (h : GenFrEx Xo c), ∃ (ι : Type) (_ : Countable ι) (C : ι → FChart h),
      ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
        ∃ (i : ι) (ψ : (C i).R →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ),
          FrMap ψ (C i).y z ∧ FrBor t z y := by
  intro E _ _ _ H Dw l Xo c h
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hBC : FrBC Xo c := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1.bc
  choose A iA dA aA j yA hj hp hjs hsm hyA using
    GlobalTheory.LocalFrame.exists_integral_chart_frame hS E H Dw l Xo c
  haveI : IsNoetherian (Xo.XF c) := CompFin.isNoetherian_XF Xo c
  obtain ⟨T, -, hT⟩ := (isCompact_univ (X := Xo.XF c)).elim_nhds_subcover (fun p => Set.range (j p))
    (fun p _ => by
      haveI := hj p
      exact (IsOpenImmersion.isOpen_range (j p)).mem_nhds (hp p))
  choose C hC using fun (p : Xo.XF c) (σ : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) =>
    GlobalTheory.Reg.exists_fChart_cell E H Dw l Xo c hBC h (A p) (j p) (yA p) (hj p) (hjs p) (hsm p) (hyA p) σ
  refine ⟨T × (∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))), inferInstance, fun i => C i.1 i.2, ?_⟩
  intro L _ _ y
  have hcond : y.x ≫ Xo.s =
      spMap (algebraMap c.F L) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.x_over, spMap_comp_ring]
    rfl
  let q : Sp L ⟶ Xo.XF c := pullback.lift y.x (spMap (algebraMap c.F L)) hcond
  obtain ⟨p, hpT, hq⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ (q (IsLocalRing.closedPoint L))))
  haveI := hj p
  obtain ⟨f, hf⟩ := exists_algHom_of_mem_range (pullback.snd _ _) (j p) (hjs p) q (pullback.lift_snd _ _ _) hq
  obtain ⟨z₀, hz₀⟩ := hBC (A p) L f (yA p)
  have hx : y.x = z₀.x := by
    rw [hz₀.1, hyA, ← Category.assoc, hf]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨g, ⟨hgu, hg⟩, -⟩ := (GlobalTheory.T.isTriangularReframe_exists_and_unique E H Dw l Xo c L z₀).2 y hx
  choose σ u b h0 h1 hb e using fun τ => exists_perm_lower_upper (g τ) (hgu τ)
  let x : FlagVar Dw → L := fun v => u v.1 (σ v.1 v.2.1.2) v.2.1.1
  have hu : ∀ τ, (lowM x τ).submatrix (σ τ).symm id = u τ := by
    intro τ
    ext i k
    obtain ⟨i, rfl⟩ := (σ τ).surjective i
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, id, lowM]
    split_ifs with h₁ h₂
    · rfl
    · rw [h₂, h1]
    · exact (h0 τ i k (lt_of_le_of_ne (not_lt.mp h₁) (Ne.symm h₂))).symm
  refine ⟨(⟨p, hpT⟩, σ), hC p σ L f z₀ y x b hz₀ hb ?_⟩
  have : (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) = g := funext fun τ => by rw [hu τ, ← e τ]
  rw [this]
  exact hg

end GlobalTheory.Reg
