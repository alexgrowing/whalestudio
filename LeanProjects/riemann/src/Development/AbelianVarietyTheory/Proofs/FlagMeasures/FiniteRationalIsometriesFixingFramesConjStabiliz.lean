import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLatticeClassesFiniteLocalOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.FixFin

section Img

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem img_mul (g g' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    LocNG.img (g * g') Λ = LocNG.img g (LocNG.img g' Λ) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨g' x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

theorem img_one (Λ : Submodule M.L.O V) : LocNG.img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hv; exact ⟨v, hv, rfl⟩

theorem img_inv {g : V ≃ₗ[E] V} {Λ Λ' : Submodule M.L.O V} (h : LocNG.img g Λ = Λ') :
    LocNG.img g⁻¹ Λ' = Λ := by
  rw [← h, ← img_mul, inv_mul_cancel, img_one]

theorem mem_Aut {g : V ≃ₗ[E] V} {Λ : Submodule M.L.O V} : g ∈ LocNG.Aut Λ ↔ LocNG.img g Λ = Λ := by
  constructor
  · intro hg
    unfold LocNG.Aut at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact img_one Λ
    | mul x y _ _ hx hy => rw [img_mul, hy, hx]
    | inv x _ hx => exact img_inv hx
  · intro h; exact Subgroup.subset_closure h

theorem img_fg_span (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  have e : (LocNG.img g L : Set V) = (g : V →ₗ[E] V) '' (L : Set V) := rfl
  rw [e, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

end Img

variable {D : D7}

theorem localLattice_fg_span (Z : LocDat D) (Λ : LV D) (h : Submodule.IsLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) (LatLoc.isLattice_map _ _ h)).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

end GlobalTheory.Unfold.FixFin

set_option maxHeartbeats 1000000 in
open GlobalTheory.Unfold.FixFin in

theorem GlobalTheory.Unfold.FixFin.conj_aut_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ a : ∀ p, ↥(FP p).UW0, {p | ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → {h : ↥(FlagPairStabilizer F F') | ∀ p, (((a p)⁻¹ * φ h p * a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀ a ha
  have hLG := LatLoc.lattices_local_global D Z
  obtain ⟨Λa, hΛa, hΛap⟩ := hLG.2 Λ₀ hΛ₀
    (fun p => LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀))
    (fun p => img_fg_span _ _ (localLattice_fg_span Z Λ₀ hΛ₀ p))
    (ha.subset fun p hp hA => hp (mem_Aut.1 hA))
  have H128 := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  have H133 := (GlobalTheory.T.rationalLatticeClasses_finite_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λa hΛa).1
  refine (H133.preimage Subtype.val_injective.injOn).subset ?_
  intro h hh
  refine ⟨h.2, ?_⟩
  have hgl : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap (h : GV D) Λa) :=
    LatLoc.isLattice_map (h : GV D) Λa hΛa
  apply (hLG.1 _ _ hgl hΛa).2
  intro p
  rw [H128.2.2.1 (h : GV D) p _ Λa (hφ h p), hΛap p]
  have e := mem_Aut.1 (hh p)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, img_mul, img_mul] at e
  have e2 := congrArg (LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) e
  rwa [← img_mul, mul_inv_cancel, img_one] at e2
