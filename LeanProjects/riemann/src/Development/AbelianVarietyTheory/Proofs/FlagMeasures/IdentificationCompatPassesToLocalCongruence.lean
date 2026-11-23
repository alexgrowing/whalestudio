import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegersDenseLocalIntegersModGStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerOneModGAtPlaceZeroElsewhereStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalVectorCongruentLocalOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalGlobalCongruenceLatticeTypedPlaceStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaLoc

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}
  (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin (r + 1) → V)

theorem cong_add {v w : V} (hv : Cong H Λ f f' v) (hw : Cong H Λ f f' w) : Cong H Λ f f' (v + w) := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hv
  obtain ⟨a', ha', b', hb', c', hc', hbX', hcX', rfl⟩ := hw
  exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', c + c', add_mem hc hc', add_mem hbX hbX',
    add_mem hcX hcX', by abel⟩

theorem cong_neg {v : V} (hv : Cong H Λ f f' v) : Cong H Λ f f' (-v) := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hv
  exact ⟨-a, neg_mem ha, -b, neg_mem hb, -c, neg_mem hc, neg_mem hbX, neg_mem hcX, by abel⟩

theorem cong_of_mem {v : V} (hv : v ∈ H.smulLat (algebraMap F E (theta M)) Λ) : Cong H Λ f f' v :=
  ⟨v, hv, 0, zero_mem _, 0, zero_mem _, zero_mem _, zero_mem _, by simp⟩

theorem cong_iff_of_sub {v w : V} (h : v - w ∈ H.smulLat (algebraMap F E (theta M)) Λ) :
    Cong H Λ f f' v ↔ Cong H Λ f f' w := by
  constructor
  · intro hv
    have := cong_add H Λ f f' hv (cong_neg H Λ f f' (cong_of_mem H Λ f f' h))
    rwa [show v + -(v - w) = w by abel] at this
  · intro hw
    have := cong_add H Λ f f' hw (cong_of_mem H Λ f f' h)
    rwa [show w + (v - w) = v by abel] at this

end Gen

section Glob

variable {D : D7}

theorem ext_latP (Z : LocDat D) (p : PlF D) {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : Ext p β g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) {v : Vp D p} (hv : v ∈ lattice₂ D Z.M p Λ) : g v ∈ lattice₂ D Z.M p Λ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [hg y]
    refine Submodule.subset_span ⟨β y, ?_, rfl⟩
    rw [← hβΛ]
    exact Submodule.mem_map_of_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : g (o • v) = o • g v := by rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ o hv

theorem ext_smulLat (Z : LocDat D) (p : PlF D) {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : Ext p β g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) (c : (D.s.atP p).Ep) {v : Vp D p}
    (hv : v ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ)) : g v ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    show g (c • w) ∈ _
    rw [map_smul]
    exact Submodule.subset_span ⟨g w, ext_latP Z p hg hβΛ hw, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : g (o • v) = o • g v := by rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ o hv

end Glob

theorem iota_typed : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → ∀ β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (∀ a, frame F₂ a = β (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ β (gS D) → ∀ (p : PlF D) (g), Ext p β g → (Z.M p).split ≠ none → ∀ x' ∈ lattice₂ D Z.M p Λ, ∀ x ∈ lattice₂ D Z.M p Λ, x' ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F₁))) → x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame (lf D F0)))) → (Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x')) := by
  intro D Z u u' F0 Λ hR F₁ F₂ _ _ β _ hβΛ _ hIota p g hg hsp x' hx'Λ x hxΛ hx' hx
  have hΛ : Submodule.IsLattice D.host.E Λ := hR.2.1.1
  have hLD := GlobalTheory.T.integers_dense_localIntegers_mod_g D p
  obtain ⟨l, hl, hxl⟩ := GlobalTheory.T.exists_global_vector_congruent_local_orthogonal D Z p hLD Λ hΛ (lf D F0) x hxΛ hx
  obtain ⟨l', hl', hxl'⟩ := GlobalTheory.T.exists_global_vector_congruent_local_orthogonal D Z p hLD Λ hΛ F₁ x' hx'Λ hx'
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.exists_integer_one_mod_g_at_place_zero_elsewhere D p
  have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
  have hl'Λ : l' ∈ Λ := (Submodule.mem_inf.1 hl').1
  have hβl' : β l' ∈ Λ := by rw [← hβΛ]; exact Submodule.mem_map_of_mem hl'Λ
  have e1 : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (baseChange₂ D p (l - l')) := by
    apply cong_iff_of_sub
    have e : x - x' - baseChange₂ D p (l - l') = (x - baseChange₂ D p l) - (x' - baseChange₂ D p l') := by rw [map_sub]; abel
    rw [e]; exact sub_mem hxl hxl'
  have e2 : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x') ↔
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (baseChange₂ D p (l - β l')) := by
    apply cong_iff_of_sub
    have e : x - g x' - baseChange₂ D p (l - β l') = (x - baseChange₂ D p l) - g (x' - baseChange₂ D p l') := by
      rw [map_sub, map_sub, hg l']; abel
    rw [e]; exact sub_mem hxl (ext_smulLat Z p hg hβΛ _ hxl')
  rw [e1, e2, ← GlobalTheory.T.local_global_congruence_lattice_typed_place D Z p hsp a ha1 ha2 Λ hΛ (lf D F0) F₁ (l - l') (sub_mem hlΛ hl'Λ), ← GlobalTheory.T.local_global_congruence_lattice_typed_place D Z p hsp a ha1 ha2 Λ hΛ (lf D F0) F₂ (l - β l') (sub_mem hlΛ hβl')]
  have hal : a • l ∈ Lrep Λ (lf D F0) := Submodule.smul_mem _ a hl
  have hal' : a • l' ∈ Lrep Λ F₁ := Submodule.smul_mem _ a hl'
  have h := hIota (a • l') hal' (a • l) hal
  have e3 : β (a • l') = a • β l' := by
    rw [← algebraMap_smul D.host.E a l', LinearEquiv.map_smul, algebraMap_smul]
  rw [e3] at h
  rw [smul_sub, smul_sub]
  exact h

end GlobalTheory.IotaLoc
