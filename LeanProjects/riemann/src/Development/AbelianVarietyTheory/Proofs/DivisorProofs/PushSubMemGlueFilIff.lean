import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedPullConstMorVPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

section Coords

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem fstC_push_sub {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    fstC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e -
      algebraMap k (TrivSqZeroExt k V) r • e) = push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e := by
  rw [map_sub, fstC_push, fstC_smul]

theorem sndC_push_sub {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    sndC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e -
      algebraMap k (TrivSqZeroExt k V) r • e) = sndC A₀ e ∘ₗ primPull (dp0 k) (𝟙 _) g - r • sndC A₀ e := by
  rw [map_sub, sndC_push, sndC_smul]

theorem proj_comp_sub {d : ℕ} {M : Type*} [AddCommGroup M] [Module k M] (a : M →ₗ[k] (Fin d → k))
    (P : M →ₗ[k] M) (r : k) (j : Fin d) :
    LinearMap.proj j ∘ₗ (a ∘ₗ P - r • a) = (LinearMap.proj j ∘ₗ a) ∘ₗ P - r • (LinearMap.proj j ∘ₗ a) := by
  ext; simp

set_option maxHeartbeats 2000000 in

theorem push_sub_mem_glueFil_iff {d : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) g e -
        algebraMap k (TrivSqZeroExt k (Fin d → k)) r • e ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e ∈ Fil A₀ ∧
      ∀ j, push (dp0 k) (𝟙 _) g (LinearMap.proj j ∘ₗ sndC A₀ e) - r • (LinearMap.proj j ∘ₗ sndC A₀ e) -
        f j (push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e) ∈ Fil A₀ := by
  rw [mem_glueFil_iff, fstC_push_sub]
  refine and_congr Iff.rfl (forall_congr' fun j ↦ ?_)
  have h0 := sndC_push_sub (V := Fin d → k) g r e
  rw [h0, proj_comp_sub]
  rfl

set_option maxHeartbeats 2000000 in

theorem sub_sum_mem_glueFil_iff {d a : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔
      fstC A₀ e - ∑ i, fstC A₀ (w i) ∈ Fil A₀ ∧
      ∀ j, (LinearMap.proj j ∘ₗ sndC A₀ e - ∑ i, LinearMap.proj j ∘ₗ sndC A₀ (w i)) -
        f j (fstC A₀ e - ∑ i, fstC A₀ (w i)) ∈ Fil A₀ := by
  rw [mem_glueFil_iff, map_sub, map_sum]
  refine and_congr Iff.rfl (forall_congr' fun j ↦ ?_)
  have hs : ∀ h : Fin a → (primDR A₀ →ₗ[k] (Fin d → k)),
      LinearMap.proj j ∘ₗ ∑ x, h x = ∑ x, LinearMap.proj j ∘ₗ h x := fun h ↦ by
    ext c; simp [LinearMap.sum_apply]
  rw [map_sub, map_sum, LinearMap.comp_sub, hs]

variable (f : HdR A₀ →ₗ[k] HdR A₀)
  (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
  (hE : ∀ e, e ∈ E ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f (fstC A₀ e) ∈ Fil A₀))
include hE

set_option maxHeartbeats 2000000 in
theorem push_sub_mem_iff (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) g e -
        algebraMap k (TrivSqZeroExt k k) r • e ∈ E ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e ∈ Fil A₀ ∧
      push (dp0 k) (𝟙 _) g (sndC A₀ e) - r • (sndC A₀ e : HdR A₀) -
        f (push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e) ∈ Fil A₀ := by
  rw [hE, fstC_push_sub, sndC_push_sub]
  rfl

set_option maxHeartbeats 2000000 in
theorem push_mem_iff (g : A₀ ⟶ A₀) [IsMonHom g]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) g e ∈ E ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) ∈ Fil A₀ ∧
      push (dp0 k) (𝟙 _) g (sndC A₀ e) - f (push (dp0 k) (𝟙 _) g (fstC A₀ e)) ∈ Fil A₀ := by
  rw [hE, fstC_push, sndC_push]
  rfl

set_option maxHeartbeats 2000000 in
theorem sub_sum_mem_iff {a : ℕ}
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    e - ∑ i, w i ∈ E ↔ fstC A₀ e - ∑ i, fstC A₀ (w i) ∈ Fil A₀ ∧
      ((sndC A₀ e : HdR A₀) - ∑ i, (sndC A₀ (w i) : HdR A₀)) - f (fstC A₀ e - ∑ i, fstC A₀ (w i)) ∈ Fil A₀ := by
  rw [hE, map_sub, map_sub, map_sum, map_sum]

omit hE

end Coords

end GlobalTheory.HTGlueLie
