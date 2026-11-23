import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueIsLatticeUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemGenusOfIsUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PartsOfLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGzLmap
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.RowsOrb.exists_row_of_unimod : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) → ∃ Λ ∈ Y.what₂ u, ∃ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ = L := by
  intro D large₂ X Y u hStd L hL hU hprim
  obtain ⟨hlat, hun⟩ := GlobalTheory.RowsOrb.Glue.glue_isLattice_unimodular D large₂ X hStd L hL hU
  have hgen := GlobalTheory.RowsOrb.ExGenus.mem_genus_of_isUnimodular D large₂ hStd X u _ hlat hun
  obtain ⟨hx, hx0, hlm, hsub⟩ := GlobalTheory.RowsOrb.parts_of_lat D X u L
  have hzL : GlobalTheory.RowsOrb.zb X u ∈ L := by
    have h1 := (hprim 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rwa [one_smul] at h1
  have hzΛ : X.zu u ∈ latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY := by
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact ⟨GlobalTheory.RowsOrb.zb X u, hzL, rfl⟩
  have hfix0 := (X.Fu_fixed u).2.2.2.1
  have hlf : (lf D (X.Fu u)) = (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) := by
    show (⟨X.Fu u, (X.Fu u).z⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS _) = _
    rw [X.flagZVector u]
  have hfix : FixedHyp D (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
    refine ⟨hlat, hun, ⟨?_, rfl⟩, ?_, ?_⟩
    · show (X.Fu u).z ∈ _
      rw [X.flagZVector u]; exact hzΛ
    · intro P
      rw [hx]
      rw [← hx0, hlf]
      exact hfix0 P
    · intro c hc
      have hc' : ((c • GlobalTheory.RowsOrb.zb X u : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
        rw [Submodule.coe_smul, GlobalTheory.RowsOrb.zb_coe, ← X.flagZVector u]; exact hc
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((hprim c).1 (hsub _ hc'))
      exact ⟨o, ho⟩
  have hrow : IsRowLat D (X.Fu u) (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := ⟨hgen, hfix, hx⟩
  obtain ⟨Λ', ⟨hΛ', γ, hγ, hmap⟩, -⟩ := (Y.rowsOK u).2 _ hrow
  obtain ⟨g, hg⟩ := GlobalTheory.RowsOrb.exists_gz_lmap D X u γ hγ
  exact ⟨Λ', hΛ', g, by rw [hg, hmap, hlm]⟩
