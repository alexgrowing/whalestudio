import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerCongruentLocalModGOnePlaceStatement

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlobalApprox

theorem bcP_osmul (D : D7) (q : PlF D) (a : 𝓞 D.host.E) (m : (VS D).V) :
    baseChange₂ D q (a • m) = (D.s.atP q).ιE (a : D.host.E) • baseChange₂ D q m := by
  rw [← IsScalarTower.algebraMap_smul D.host.E a m]
  exact baseChange_smul₂ (D := D) q _ m

theorem osmul_mem (D : D7) (Z : LocDat D) (q : PlF D) (M : LV D) (m : (VS D).V) (hm : m ∈ M)
    (o : (D.s.atP q).Ep) (ho : o ∈ (D.s.atP q).O) : o • baseChange₂ D q m ∈ lattice₂ D Z.M q M := by
  have hO : (Z.M q).L.O = (D.s.atP q).O := (Z.agree q).2.2.2.1
  have ho' : o ∈ (Z.M q).L.O := by rw [hO]; exact ho
  have hgen : baseChange₂ D q m ∈ lattice₂ D Z.M q M := Submodule.subset_span ⟨m, hm, rfl⟩
  exact (lattice₂ D Z.M q M).smul_mem (⟨o, ho'⟩ : (Z.M q).L.O) hgen

theorem approx_gen (D : D7) (Z : LocDat D) (p : PlF D) (M : LV D) (m : (VS D).V) (hm : m ∈ M)
    (c : (D.s.atP p).Ep) (hc : c ∈ (D.s.atP p).O) :
    ∃ l ∈ M, (∃ w ∈ lattice₂ D Z.M p M, baseChange₂ D p l - c • baseChange₂ D p m = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • w) ∧
      ∀ p' : PlF D, p' ≠ p → ∃ w ∈ lattice₂ D Z.M p' M, baseChange₂ D p' l = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • w := by
  obtain ⟨a, ⟨o, ho, hao⟩, hfar⟩ := GlobalTheory.T.exists_integer_congruent_local_mod_g_one_place D p c hc
  refine ⟨a • m, M.smul_mem a hm, ⟨o • baseChange₂ D p m, osmul_mem D Z p M m hm o ho, ?_⟩, ?_⟩
  · rw [bcP_osmul, ← sub_smul, hao, mul_smul]
  · intro p' hp'
    obtain ⟨o', ho', hao'⟩ := hfar p' hp'
    exact ⟨o' • baseChange₂ D p' m, osmul_mem D Z p' M m hm o' ho', by rw [bcP_osmul, hao', mul_smul]⟩

theorem smul_step {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (g c : R) (b b' x w w' : V)
    (h : b - x = g • w) (h' : b' - c • b = g • w') : b' - c • x = g • (w' + c • w) := by
  rw [smul_add, ← h', smul_comm g c w, ← h, smul_sub]
  abel

theorem approx : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (M : LV D) (x : Vp D p), x ∈ lattice₂ D Z.M p M → ∃ l ∈ M, (∃ w ∈ lattice₂ D Z.M p M, baseChange₂ D p l - x = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • w) ∧ ∀ p' : PlF D, p' ≠ p → ∃ w ∈ lattice₂ D Z.M p' M, baseChange₂ D p' l = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • w := by
  intro D Z p M x hx
  have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
  have hx' : x ∈ Submodule.span (Z.M p).L.O (baseChange₂ D p '' (M : Set (VS D).V)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hm, rfl⟩ := hy
    obtain ⟨l, hl, ⟨w, hw, hlw⟩, hfar⟩ := approx_gen D Z p M m hm 1 (Subring.one_mem _)
    rw [one_smul] at hlw
    exact ⟨l, hl, ⟨w, hw, hlw⟩, hfar⟩
  | zero =>
    refine ⟨0, M.zero_mem, ⟨0, (lattice₂ D Z.M p M).zero_mem, by simp⟩, fun p' _ => ?_⟩
    exact ⟨0, (lattice₂ D Z.M p' M).zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l₁, hl₁, ⟨w₁, hw₁, e₁⟩, f₁⟩ := hy
    obtain ⟨l₂, hl₂, ⟨w₂, hw₂, e₂⟩, f₂⟩ := hz
    refine ⟨l₁ + l₂, M.add_mem hl₁ hl₂, ⟨w₁ + w₂, (lattice₂ D Z.M p M).add_mem hw₁ hw₂, ?_⟩, ?_⟩
    · rw [map_add, smul_add, ← e₁, ← e₂]
      abel
    · intro p' hp'
      obtain ⟨v₁, hv₁, g₁⟩ := f₁ p' hp'
      obtain ⟨v₂, hv₂, g₂⟩ := f₂ p' hp'
      exact ⟨v₁ + v₂, (lattice₂ D Z.M p' M).add_mem hv₁ hv₂, by rw [map_add, g₁, g₂, smul_add]⟩
  | smul r y _ hy =>
    obtain ⟨l, hl, ⟨w, hw, e⟩, _⟩ := hy
    have hr : (r : (D.s.atP p).Ep) ∈ (D.s.atP p).O := by rw [← hO]; exact r.2
    obtain ⟨l', hl', ⟨w', hw', e'⟩, hfar'⟩ := approx_gen D Z p M l hl (r : (D.s.atP p).Ep) hr
    refine ⟨l', hl', ⟨w' + r • w, (lattice₂ D Z.M p M).add_mem hw' ((lattice₂ D Z.M p M).smul_mem r hw), ?_⟩, hfar'⟩
    exact smul_step _ (r : (D.s.atP p).Ep) (baseChange₂ D p l) (baseChange₂ D p l') y w w' e e'

end GlobalTheory.GlobalApprox
