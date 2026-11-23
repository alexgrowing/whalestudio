import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatStabAct

open GlobalTheory.AdelicLatMove

variable {D : D7}

def latCoord (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) where
  carrier := L0c D V
  add_mem' := by
    intro a b ha hb
    show ∑ i, (a i + b i) • V.frame i ∈ V.L0
    simp only [add_smul, Finset.sum_add_distrib]
    exact V.L0.add_mem ha hb
  zero_mem' := by
    show ∑ i, (0 : D.host.E) • V.frame i ∈ V.L0
    simp
  smul_mem' := by
    intro c a ha
    show ∑ i, (c • a i) • V.frame i ∈ V.L0
    simp only [smul_assoc, ← Finset.smul_sum]
    exact V.L0.smul_mem c ha

def swapF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom

theorem swap_mem_hatL {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (y : Fin n → Af D.host.F ⊗[D.host.F] D.host.E)
    (hy : y ∈ latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E))) :
    (fun i => swapF D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact pure_mem_hatL Λ a ha x hx
  | zero => simp only [Pi.zero_apply, map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => simp only [Pi.add_apply, map_add]; exact Submodule.add_mem _ ha hb
  | neg a _ ha => simp only [Pi.neg_apply, map_neg]; exact Submodule.neg_mem _ ha

theorem mulVec_pure_mem (V : HSp D) (g : GA D V) (hg : g ∈ KsphC V ∅) (x : Fin V.rank → D.host.E)
    (hx : x ∈ L0c D V) :
    (mt V g).map (toEAf D) *ᵥ (fun i => x i ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (latCoord V) := by
  have h1 : (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V) :=
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, hx, rfl⟩
  have h2 := swap_mem_hatL (latCoord V) _ ((hg.2.1 _).1 h1)
  convert h2 using 1
  funext i
  rw [RingHom.map_mulVec]
  congr 1

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem fin_smul_gen (β α : Af D.host.F) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) •
      (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] M i j : WO S T) =
      Matrix.of fun i j => (pairA D.host.F 0 (β * α)) ⊗ₜ[D.host.F] M i j := by
  ext i j
  change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  exact Prod.ext (mul_zero _) rfl

theorem fin_smul_mem {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {β : Af D.host.F} (hβ : β ∈ intAf D.host.F)
    (h0 : ∀ v, ¬ P v → evalV D.host.F v β = 0) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) • u ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β * α, fun w => ?_, fun w hw => ?_, a, ha, s, hs, t, ht,
      fin_smul_gen β α (fun i j => a * t i * ∑ k, star (s k) * S.gram k j)⟩
    · rw [map_mul]; exact mul_mem (hβ w) (hα w)
    · rw [map_mul, h0 w hw, zero_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem actO_mem_latO_of_stab : ∀ (D : D7) (S T : HSp D), ∀ g ∈ KsphC S ∅, ∀ h ∈ KsphC T ∅, ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop), ∀ u ∈ latO S T (L0c D S) (L0c D T) P, actO S T g h u ∈ latO S T (L0c D S) (L0c D T) P := by
  intro D S T g hg h hh P u hu
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 1
    have e2 := fin_smul_gen (S := S) (T := T) α (1 * 1) (fun i j => a * t i * ∑ k, star (s k) * S.gram k j)
    rw [← e, mul_one, mul_one] at e2
    have e3 : ∀ (c : AE D) (x : WO S T), actO S T g h (c • x) = c • actO S T g h x := fun c x => by
      simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
    rw [← e2, e3, actO_rankOne]
    exact fin_smul_mem hα h0 (rankOne_mem_latO S T (latCoord S) (latCoord T) a ha _
      (mulVec_pure_mem S g hg s hs) _ (mulVec_pure_mem T h hh t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

end GlobalTheory.LatStabAct

end
