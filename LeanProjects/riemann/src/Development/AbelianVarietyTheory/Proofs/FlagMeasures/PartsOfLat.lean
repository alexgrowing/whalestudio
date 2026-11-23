import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Parts
open GlobalTheory.RowsOrb.Uniq

variable {D : D7} (X : HidaSetting D)

theorem lsS_le {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (v : Fin r → (VS D).V) {y : (VS D).V} (hy : y ∈ latSpanS aa v) :
    y ∈ Submodule.span D.host.E (Set.range v) := by
  have hle : latSpanS aa v ≤ (Submodule.span D.host.E (Set.range v)).restrictScalars (𝓞 D.host.E) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, x, -, rfl⟩
    exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)
  exact hle hy

theorem Xsp_eq (u : D.what₂.Word) : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
  show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
  rw [X.Fu_e]

theorem XS_eq (u : D.what₂.Word) : XS D (X.Fu u) = latSpanS (fun a => aaD D a) X.eX := by
  simp only [XS, latSpanS, aaD, X.Fu_e]

theorem xlam_split (u : D.what₂.Word) (M : Submodule (𝓞 D.host.E) (VS D).V)
    (hM : ∀ x ∈ M, ∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0) :
    XLam (latSpanS (fun a => aaD D a) X.eX ⊔ M ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) =
      XS D (X.Fu u) := by
  rw [XS_eq]
  show _ ⊓ toO (VS D) (Xsp (lf D (X.Fu u))) = _
  rw [Xsp_eq]
  refine le_antisymm ?_ (le_inf (le_sup_left.trans le_sup_left) fun y hy => lsS_le _ _ hy)
  rintro y ⟨hyΛ, hyX⟩
  have hyX' : y ∈ Submodule.span D.host.E (Set.range X.eX) := hyX
  obtain ⟨y1, hy1, b, hb, rfl⟩ := Submodule.mem_sup.mp hyΛ
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.mp hy1
  have haX := lsS_le _ _ ha
  have hbY := lsS_le _ _ hb

  have hb0 : b = 0 := by
    have hpair : ∀ c, (VS D).hT (X.eX c) b = 0 := by
      intro c
      have h1 := orth_span (fun d => X.ee c d) hyX'
      have h2 := orth_span (fun d => X.ee c d) haX
      rw [map_add, map_add, h2, (hM m hm c).1, zero_add, zero_add] at h1
      exact h1
    rw [coord X.ef hbY]
    simp [hpair]
  subst hb0
  rw [add_zero] at hyX' ⊢

  have hmX : m ∈ Submodule.span D.host.E (Set.range X.eX) := by
    have := Submodule.sub_mem _ hyX' haX
    rwa [add_sub_cancel_left] at this
  have hm0 : m = 0 := by
    rw [coord (dual_symm GlobalTheory.RowsOrb.Uniq.hh X.ef) hmX]
    simp [(hM m hm _).2]
  rw [hm0, add_zero]
  exact ha

theorem map_perp (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    ∀ x ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)), ∀ a,
      (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0 := by
  intro x hx a
  obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hx
  exact (GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 a

theorem lmap_eq (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L := by
  ext w
  rw [lmap_char X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) (fun a => aaD D a) (fun a => (aaD D a)⁻¹) X.ef (map_perp X L)
      rfl w]
  constructor
  · rintro ⟨l, hl, hP⟩
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hl
    have hfix : P (VS D).hT X.eX X.fY (w' : (VS D).V) = w' := by
      rw [P_apply]
      simp [((GlobalTheory.RowsOrb.mem_Wb X (w' : (VS D).V)).mp w'.2 _).2]
    have : w' = w := Subtype.ext (hfix.symm.trans hP)
    exact this ▸ hw'
  · intro hw
    refine ⟨(w : (VS D).V), Submodule.mem_map_of_mem hw, ?_⟩
    rw [P_apply]
    simp [((GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 _).2]

end GlobalTheory.RowsOrb.Parts

open GlobalTheory.RowsOrb.Parts in

theorem GlobalTheory.RowsOrb.parts_of_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), XLam (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) = XS D (X.Fu u) ∧ XLam (VS D).L0 (lf D (X.Fu u)) = XS D (X.Fu u) ∧ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L ∧ ∀ w : GlobalTheory.RowsOrb.Wb X, (w : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) → w ∈ L := by
  intro D X u L
  refine ⟨xlam_split X u _ (map_perp X L), ?_, lmap_eq X u L, ?_⟩
  · rw [X.Lam_split]
    exact xlam_split X u X.Lb X.Lb_perp
  · intro w hw
    rw [Lsub, Submodule.mem_inf] at hw
    have hX : toO (VS D) (Xsp (lf D (X.Fu u))) =
        GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := by
      rw [GlobalTheory.RowsOrb.Uniq.fixedFrameOfWord_isotropicSpan_eq, Xsp_eq]
    have hmem : w ∈ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
        L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
        latSpanS (fun a => (aaD D a)⁻¹) X.fY) :=
      (GlobalTheory.RowsOrb.mem_Lmap X u _ w).mpr ((sup_le_sup inf_le_left hX.le) hw.1)
    rwa [lmap_eq X u L] at hmem
