import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd

noncomputable section

namespace MassDataLevelSSteps.LatW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

abbrev crd (y : (VS D).V) : Fin X.B.I.n → X.B.I.E := crdOf X.B.I X.ιE X.bas y

theorem crd_add (y z : (VS D).V) : crd X (y + z) = crd X y + crd X z := by
  funext i; simp [crd, crdOf, map_add]

theorem crd_zero : crd X 0 = 0 := by
  funext i; simp [crd, crdOf]

theorem crd_smul (c : D.host.E) (y : (VS D).V) : crd X (c • y) = X.ιE.symm c • crd X y := by
  funext i; simp [crd, crdOf, map_mul, smul_eq_mul]

theorem crd_mem_span {S : Set (VS D).V} {y : (VS D).V} (hy : y ∈ Submodule.span D.host.E S) :
    crd X y ∈ Submodule.span X.B.I.E (crd X '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [crd_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [crd_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [crd_smul]; exact Submodule.smul_mem _ _ hx

theorem latSpanS_le {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (v : Fin r → (VS D).V) {y : (VS D).V} (hy : y ∈ latSpanS aa v) :
    y ∈ Submodule.span D.host.E (Set.range v) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, c, -, rfl⟩ := hx
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul D.host.E c x]
    exact Submodule.smul_mem _ _ hx

theorem crd_mem_L {y : (VS D).V} (hy : y ∈ (VS D).L0) : crd X y ∈ X.B.I.L := by
  rw [X.L_eq]
  simp only [crd, crdOf, RingEquiv.apply_symm_apply]
  rw [X.bas.sum_repr y]
  exact hy

theorem L_crd {x : Fin X.B.I.n → X.B.I.E} (hx : x ∈ X.B.I.L) : ∃ y ∈ (VS D).L0, x = crd X y := by
  refine ⟨_, (X.L_eq x).1 hx, ?_⟩
  funext i
  show x i = X.ιE.symm (X.bas.repr (∑ j, X.ιE (x j) • X.bas j) i)
  rw [Module.Basis.repr_sum_self]
  simp

theorem ratV_add (R : Type) [CommRing R] [Algebra X.B.I.F R] (a b : Fin X.B.I.n → X.B.I.E) :
    ratV (F := X.B.I.F) R (a + b) = ratV (F := X.B.I.F) R a + ratV (F := X.B.I.F) R b := by
  funext i
  simp [ratV, map_add]

def LX : Set (Fin X.B.I.n → X.B.I.E) := crd X '' (latSpanS (fun a => aaD D a) X.eX : Set (VS D).V)

def LW : Set (Fin X.B.I.n → X.B.I.E) := crd X '' (X.Lb : Set (VS D).V)

def LY : Set (Fin X.B.I.n → X.B.I.E) := crd X '' (latSpanS (fun a => (aaD D a)⁻¹) X.fY : Set (VS D).V)

theorem adapted (w : D.what₂.Word) :
    Formalism.L2.SG.Volumes.Adapted X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (frameOf X w) (LX X) (LW X) (LY X) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := crd_mem_span X (latSpanS_le _ _ hy)
    rw [← Set.range_comp] at h
    exact h
  · rintro _ ⟨y, hy, rfl⟩
    have h := crd_mem_span X (latSpanS_le _ _ hy)
    rw [← Set.range_comp] at h
    exact h
  · rintro _ ⟨y, hy, rfl⟩ a
    have h := X.Lb_perp y hy a
    constructor
    · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas y) = 0
      rw [FrameW.hE_crdOf, h.1, map_zero]
    · show hE _ _ (crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas y) = 0
      rw [FrameW.hE_crdOf, h.2, map_zero]

theorem latLoc_eq (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    latLoc (E := X.B.I.E) v (LX X ∪ LW X ∪ LY X) = latLoc v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  apply le_antisymm
  · apply Submodule.span_mono
    apply Set.image_mono
    rintro _ ((⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
    · exact crd_mem_L X (by rw [X.Lam_split]; exact Submodule.mem_sup_left (Submodule.mem_sup_left hy))
    · exact crd_mem_L X (by rw [X.Lam_split]; exact Submodule.mem_sup_left (Submodule.mem_sup_right hy))
    · exact crd_mem_L X (by rw [X.Lam_split]; exact Submodule.mem_sup_right hy)
  · apply Submodule.span_le.2
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := L_crd X hx
    rw [X.Lam_split] at hy
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hab
    rw [crd_add, crd_add, ratV_add, ratV_add]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.subset_span ⟨crd X a, Or.inl (Or.inl ⟨a, ha, rfl⟩), rfl⟩
    · exact Submodule.subset_span ⟨crd X b, Or.inl (Or.inr ⟨b, hb, rfl⟩), rfl⟩
    · exact Submodule.subset_span ⟨crd X c, Or.inr ⟨c, hc, rfl⟩, rfl⟩

theorem Kf_eq :
    Kf X.B.I.cm.sig X.B.I.J (LX X ∪ LW X ∪ LY X) = Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have hK : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
      Kloc (E := X.B.I.E) v (LX X ∪ LW X ∪ LY X) = Kloc v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro v
    ext g
    show (∀ x, x ∈ latLoc (E := X.B.I.E) v (LX X ∪ LW X ∪ LY X) ↔ _) ↔
      (∀ x, x ∈ latLoc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔ _)
    rw [latLoc_eq]
  simp only [Kf, hK]

end MassDataLevelSSteps.LatW

namespace MassDataLevelSSteps

theorem latAdapted_holds : LatAdapted := by
  intro D X w
  exact ⟨LatW.LX X, LatW.LW X, LatW.LY X, LatW.adapted X w, LatW.Kf_eq X⟩

end MassDataLevelSSteps
