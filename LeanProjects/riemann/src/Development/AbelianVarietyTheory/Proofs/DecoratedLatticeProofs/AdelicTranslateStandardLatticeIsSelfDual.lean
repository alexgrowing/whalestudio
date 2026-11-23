import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdMove
variable {D : D7}

theorem moves_exists (V : HSp D) (g : GA D V) : ∃ N, Moves V rfl g N := by
  obtain ⟨Λ, hΛ, -, -, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (GlobalTheory.SplitMove.intSub D V.rank)
    (finHom V g) (GlobalTheory.SplitMove.intSub_fg _) (GlobalTheory.SplitMove.intSub_span _)
  have inv : ∀ y, (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  have inv' : ∀ y, (finHom V g).1 *ᵥ ((finHom V g⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec]
  have ent : ∀ (x : Fin V.rank → D.host.E) i,
      Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E
        (((finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x) i) =
      (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    intro x i
    simp only [GlobalTheory.AdForm.finM, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.reindex_apply,
      finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
  refine ⟨Λ, fun x => ?_⟩
  rw [← SetLike.mem_coe, hΛ, GlobalTheory.SplitMove.coe_intSub]
  change GlobalTheory.AdLat.fv D.host.F x ∈ (finHom V g).1.mulVec '' _ ↔ _
  constructor
  · rintro ⟨y, hy, hxy⟩ i
    rw [← ent, ← hxy, inv]
    exact (GlobalTheory.SplitMove.hat_intVec_iff D V.rank y).1 hy i
  · intro hx
    refine ⟨(finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x, (GlobalTheory.SplitMove.hat_intVec_iff D V.rank _).2 fun i => ?_, inv' _⟩
    rw [ent]; exact hx i

theorem isSdLat_of (V : HSp D) (hV : V.gram = 1) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : IsSelfDualC V N) : Formalism.L2.Col.IsSdLat N := by
  refine ⟨h.1, ?_⟩
  ext x
  rw [h.2 x]
  simp only [Formalism.HermitianLatticesTheory.IsUnimodular, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  have e : Formalism.L2.Col.hStd D.host.E V.rank y x = ∑ i, ∑ j, star (y i) * V.gram i j * x j := by
    rw [hV]
    simp [Formalism.L2.Col.hStd, Matrix.one_apply]
  rw [e]

theorem std_moved_lattice : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), V.gram = 1 → (∀ g : GA D V, ∃ N, Moves V hn g N) ∧ ∀ (g : GA D V) N, Moves V hn g N → Formalism.L2.Col.IsSdLat N ∧ ∃ Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), (Λ : Set (Fin V.rank → D.host.E)) = latFr V hn N ∧ IsSelfDualC V Λ := by
  intro D V n hn hV
  subst hn
  refine ⟨fun g => moves_exists V g, fun g N hN => ?_⟩
  have hsd := GlobalTheory.SplitMove.selfDual_move V hV g N hN
  refine ⟨isSdLat_of V hV N hsd, N, ?_, hsd⟩
  ext x
  first | exact Iff.rfl | simp [GlobalTheory.AdForm.latFr]

end GlobalTheory.StdMove
