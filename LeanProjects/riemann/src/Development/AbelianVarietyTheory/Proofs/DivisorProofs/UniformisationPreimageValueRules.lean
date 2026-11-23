import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPer

theorem ex_add_lattice {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left} (u : HolUnif A L g) (l : u.Λ) (z : Fin g → ℂ) :
    u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem pre_val_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ U, IsOpen (pre u.ex U)) ∧ (∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U)) ∧ (∀ U (l : u.Λ) (z : Fin g → ℂ), z + l ∈ pre u.ex U ↔ z ∈ pre u.ex U) ∧ (∀ U b (l : u.Λ) (z : Fin g → ℂ), val u.ex U b (z + l) = val u.ex U b z) ∧ (∀ U V, pre u.ex (U ⊓ V) = pre u.ex U ∩ pre u.ex V) ∧ (∀ U V, V ≤ U → pre u.ex V ⊆ pre u.ex U) ∧ (∀ (K : Type) (W : K → A.left.Opens) z, z ∈ pre u.ex (⨆ i, W i) ↔ ∃ i, z ∈ pre u.ex (W i)) ∧ (∀ U z, z ∈ pre u.ex U → ∃ W : A.left.affineOpens, W.1 ≤ U ∧ z ∈ pre u.ex W.1) ∧ (∀ U V (h : V ≤ U) (b : Sec (str A) U), ∀ z ∈ pre u.ex V, val u.ex V (Sec.res (str A) h b) z = val u.ex U b z) ∧ (∀ U, ∀ z ∈ pre u.ex U, ∃ e : Sec (str A) U →ₐ[ℂ] ℂ, ∀ b, val u.ex U b z = e b) ∧ (∀ U b z, z ∈ pre u.ex (A.left.basicOpen b) ↔ val u.ex U b z ≠ 0) ∧ ∀ z, z ∈ pre u.ex ⊤ := by
  intro A _ g L u
  refine ⟨fun U ↦ (u.hol U 0).1, fun U b ↦ (u.hol U b).2, fun U l z ↦ ?_, fun U b l z ↦ ?_, fun U V ↦ ?_,
    fun U V h z hz ↦ top_le_preimage_mono _ h hz, fun K W z ↦ ?_, fun U z hz ↦ ?_,
    fun U V h b z hz ↦ valAt'_map (u.ex z).left (homOfLE h).op b hz, fun U z hz ↦ ?_,
    fun U b z ↦ top_le_preimage_basicOpen_iff _ U b, fun z ↦ le_top (α := (Sp ℂ).Opens)⟩
  · simp only [pre, Set.mem_setOf_eq, ex_add_lattice]
  · simp only [val, ex_add_lattice]
  · ext z
    exact top_le_preimage_inf _ U V
  · refine (top_le_preimage_iff_mem (u.ex z).left _).trans (TopologicalSpace.Opens.mem_iSup.trans ?_)
    exact exists_congr fun i ↦ (top_le_preimage_iff_mem (u.ex z).left _).symm
  · have h1 := (top_le_preimage_iff_mem (u.ex z).left _).1 hz
    obtain ⟨W, hW, h2, h3⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 A.left.isBasis_affineOpens) h1
    exact ⟨⟨W, hW⟩, h3, (top_le_preimage_iff_mem (u.ex z).left _).2 h2⟩
  · refine ⟨{ toRingHom := valAtHom (u.ex z).left U hz, commutes' := fun a ↦ ?_ }, fun b ↦ valAt'_eq_valAtHom _ hz b⟩
    refine (valAt'_eq_valAtHom (u.ex z).left hz _).symm.trans ?_
    refine valAt'_constFn (u.ex z).left (str A) ?_ U a hz
    exact (congrArg _ (Category.comp_id _)).trans (Over.w (u.ex z))

end GlobalTheory.CechPer
