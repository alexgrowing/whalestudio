import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LocalLatStab

open GlobalTheory.AdelicLatMove

variable {D : D7}

def swp (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) →+* EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E : _ →+* _)

theorem map_toEAf (V : HSp D) (g : GA D V) :
    (mt V g).map (toEAf D) = (finMat D.sp.cm.sig V.gram g).map (swp D) := rfl

def swpVec (D : D7) (n : ℕ) (α : Af D.host.F) :
    (Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin n → EAf D) :=
  AddMonoidHom.mk' (fun y i => ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (y i))
    (fun y z => by funext i; simp only [Pi.add_apply, map_add, mul_add])

theorem swpVec_pure {n : ℕ} (α β : Af D.host.F) (x : Fin n → D.host.E) :
    swpVec D n α (fun i => β ⊗ₜ[D.host.F] x i) = fun i => x i ⊗ₜ[D.host.F] (α * β) := by
  funext i
  change ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * (x i ⊗ₜ[D.host.F] β) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mulVec_swpVec (V : HSp D) (g : GA D V) (α : Af D.host.F)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (mt V g).map (toEAf D) *ᵥ swpVec D _ α y = swpVec D _ α (finMat D.sp.cm.sig V.gram g *ᵥ y) := by
  rw [map_toEAf]
  funext i
  change ∑ j, swp D (finMat D.sp.cm.sig V.gram g i j) * (((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (y j)) =
    ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (∑ j, finMat D.sp.cm.sig V.gram g i j * y j)
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_left_comm]

theorem rankOne_mem (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (a : D.host.E) (ha : a ∈ D.host.AA)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    (s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hs : s ∈ latHat D.host.F D.host.E LS)
    (t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E) (ht : t ∈ latHat D.host.F D.host.E LT) :
    rankOne S T a (swpVec D _ 1 s) (swpVec D _ α t) ∈ latO S T LS LT P := by
  change rankOneHom S T a _ _ ∈ _
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨β, hβ, x, hx, rfl⟩ := hs
      obtain ⟨γ, hγ, y, hy, rfl⟩ := ht
      rw [swpVec_pure, swpVec_pure, one_mul]
      apply AddSubgroup.subset_closure
      refine ⟨α * γ * β, (mul_mem (mul_mem hα hγ : α * γ ∈ Formalism.UG.intAd D.host.F) hβ :
        α * γ * β ∈ Formalism.UG.intAd D.host.F), fun v hv => ?_, a, ha, x, hx, y, hy,
        rankOne_pure S T a x y β (α * γ)⟩
      rw [map_mul, map_mul, hP v hv, zero_mul, zero_mul]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add, map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg, map_neg]; exact neg_mem hy
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg, map_neg]; exact neg_mem hy

theorem actO_mem (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : GA D S) (h : GA D T)
    (hg : ∀ y ∈ latHat D.host.F D.host.E LS, finMat D.sp.cm.sig S.gram g *ᵥ y ∈ latHat D.host.F D.host.E LS)
    (hh : ∀ y ∈ latHat D.host.F D.host.E LT, finMat D.sp.cm.sig T.gram h *ᵥ y ∈ latHat D.host.F D.host.E LT)
    (u : WO S T) (hu : u ∈ latO S T LS LT P) : actO S T g h u ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := (one_mem _ : (1 : Af D.host.F) ∈ Formalism.UG.intAd D.host.F)
    have e := rankOne_pure S T a s t (1 * 1) (α * 1)
    rw [← swpVec_pure, ← swpVec_pure, mul_one, mul_one, mul_one] at e
    rw [← e, actO_rankOne, mulVec_swpVec, mulVec_swpVec]
    exact rankOne_mem S T LS LT P a ha α hα hP _
      (hg _ (AddSubgroup.subset_closure ⟨1, h1, s, hs, rfl⟩)) _
      (hh _ (AddSubgroup.subset_closure ⟨1, h1, t, ht, rfl⟩))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem finMat_mul_inv (V : HSp D) (g : GA D V) :
    finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g⁻¹ = 1 := by
  let f := Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
  change (mt V g).map f * (mt V g⁻¹).map f = 1
  rw [← Matrix.map_mul (f := f), ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inv_keeps (V : HSp D) (L : Set (Fin V.rank → D.host.E)) (g : GA D V)
    (hg : ∀ y, y ∈ latHat D.host.F D.host.E L ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E L) :
    ∀ y ∈ latHat D.host.F D.host.E L, finMat D.sp.cm.sig V.gram g⁻¹ *ᵥ y ∈ latHat D.host.F D.host.E L := by
  intro y hy
  rw [hg, Matrix.mulVec_mulVec, finMat_mul_inv, Matrix.one_mulVec]
  exact hy

theorem mem_latO_place_iff_actO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, IsPlaceIdem D v ε → ∀ (g : GA D S) (h : GA D T), (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔ (finMat D.sp.cm.sig S.gram g).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) → (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔ (finMat D.sp.cm.sig T.gram h).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) → ∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v) := by
  intro D S T ΛS ΛT _ _ v _ _ g h hg hh u
  refine ⟨actO_mem S T _ _ _ g h (fun y hy => (hg y).1 hy) (fun y hy => (hh y).1 hy) u, fun hu => ?_⟩
  have h1 := actO_mem S T _ _ _ g⁻¹ h⁻¹ (inv_keeps S _ g hg) (inv_keeps T _ h hh) _ hu
  have h2 := actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at h2
  rwa [h2] at h1

end GlobalTheory.LocalLatStab

end
