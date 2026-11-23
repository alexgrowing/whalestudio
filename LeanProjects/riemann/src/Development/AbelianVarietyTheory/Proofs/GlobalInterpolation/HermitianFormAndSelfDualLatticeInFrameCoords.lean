import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.FrameDict

theorem form_coords {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (W : Formalism.BasicNotions.HSpace E) (x y : Fin W.rank → E) :
    hE cm.sig W.gram x y = W.hT (∑ i, x i • W.frame i) (∑ i, y i • W.frame i) := by
  have hs : ∀ a : E, (cm.sig : E →+* E) a = star a := fun _ => rfl
  simp only [hE, Formalism.UG.hform, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul,
    LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, hs,
    Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_one_iff {E : Type} [Field E] [NumberField E] (z : E) :
    z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

theorem dict : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (W : HSpace E), (∀ a b : W.V, hE cm.sig W.gram (fun i => W.frame.repr a i) (fun i => W.frame.repr b i) = W.hT a b) ∧ ∃ L : Submodule (𝓞 E) (Fin W.rank → E), IsSelfDualLat cm.sig W.gram L ∧ (L : Set (Fin W.rank → E)) = latC W := by
  intro F E _ _ _ _ _ _ cm W
  refine ⟨fun a b => ?_, ?_⟩
  · rw [form_coords, W.frame.sum_repr, W.frame.sum_repr]
  obtain ⟨L, hfg, hsp, hL⟩ := exists_lattice W
  refine ⟨L, ⟨hfg, hsp, fun y => ?_⟩, hL⟩
  have hmem : ∀ x : Fin W.rank → E, x ∈ L ↔ ∑ i, x i • W.frame i ∈ W.L0 := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hu : ∀ v : W.V, (∀ u ∈ W.L0, W.hT u v ∈ (1 : Submodule (𝓞 E) E)) ↔ v ∈ W.L0 := fun v => by
    have h : Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 := W.baseLattice_isUnimodular
    conv_rhs => rw [← h]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
  rw [hmem, ← hu]
  constructor
  · intro h x hx
    rw [form_coords, ← mem_one_iff]
    exact h _ ((hmem x).1 hx)
  · intro h u hu'
    have := h (fun i => W.frame.repr u i) (by rw [hmem, W.frame.sum_repr]; exact hu')
    rw [form_coords, W.frame.sum_repr, ← mem_one_iff] at this
    exact this

end GlobalTheory.FrameDict
