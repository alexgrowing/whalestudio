import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix GlobalTheory.AdelicLatMove
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatStab

variable {D : D7}

theorem finE_val (V : HSp D) (g : GA D V) :
    (finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := by
  ext i j
  rfl

theorem mulVec_mem_of_mem_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (x : Fin n → Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    M.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨y, rfl⟩ := hM
  rw [hβ _]
  have hx' := (hβ x).1 hx
  have e : (β⁻¹).val * (frGL β y).val = (intGL D.host.F D.host.E n y).val * (β⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    change β⁻¹ * (β * intGL D.host.F D.host.E n y * β⁻¹) = _
    group
  intro i
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  change ∑ j, (intGL D.host.F D.host.E n y).val i j * ((β⁻¹).val *ᵥ x) j ∈ _
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (y.val i j).2 (hx' j)

theorem rankOne_smul_mem_latO (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop)
    (γ : Af D.host.F) (hγ : γ ∈ Formalism.UG.intAd D.host.F) (hP : ∀ v, ¬ Pv v → evalV D.host.F v γ = 0)
    (a : D.host.E) (ha : a ∈ D.host.AA)
    (s : Fin S.rank → Lev.EAf D) (hs : s ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (t : Fin T.rank → Lev.EAf D) (ht : t ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT) :
    rankOne S T a s (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • t) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  have hs' := mem_closure_of_mem_hatL ΛS s hs
  have ht' := mem_closure_of_mem_hatL ΛT t ht
  clear hs ht
  change rankOneHom S T a s _ ∈ _
  induction hs' using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht' using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      have e : (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • fun i => (y i ⊗ₜ[D.host.F] β : Lev.EAf D)) =
          fun i => y i ⊗ₜ[D.host.F] (γ * β) := by
        ext i
        simp
      rw [e]
      apply AddSubgroup.subset_closure
      refine ⟨γ * β * α, (mul_mem (mul_mem hγ hβ) hα : γ * β * α ∈ Formalism.UG.intAd D.host.F), fun v hv => ?_,
        a, ha, x, hx, y, hy, rankOne_pure S T a x y α (γ * β)⟩
      rw [map_mul, map_mul, hP v hv, zero_mul, zero_mul]
    | zero => rw [smul_zero, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add, map_add]; exact add_mem hy hz
    | neg y _ hy => rw [smul_neg, map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem actO_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) (g : GA D S) (h : GA D T)
    (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv) :
    actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    have e2 : (fun i => (t i ⊗ₜ[D.host.F] α : Lev.EAf D)) =
        ((1 : D.host.E) ⊗ₜ[D.host.F] α : Lev.EAf D) • fun i => (t i ⊗ₜ[D.host.F] (1 : Af D.host.F) : Lev.EAf D) := by
      ext i
      simp
    rw [← e, actO_rankOne, e2, Matrix.mulVec_smul, ← finE_val, ← finE_val]
    exact rankOne_smul_mem_latO S T ΛS ΛT Pv α hα hP a ha _
      (mulVec_mem_of_mem_St ΛS βS _ hS hg _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_of_mem_St ΛT βT _ hT hh _ (pure_mem_hatL ΛT 1 (one_mem _) t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_actO_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT Pv ↔ actO S T g h u ∈ latO S T ΛS ΛT Pv := by
  intro D S T ΛS ΛT βS βT _ _ hS hT g h hg hh Pv u
  refine ⟨actO_mem S T ΛS ΛT βS βT hS hT g h hg hh Pv u, fun hu => ?_⟩
  have h1 := actO_mem S T ΛS ΛT βS βT hS hT g⁻¹ h⁻¹ (by rw [map_inv]; exact inv_mem hg)
    (by rw [map_inv]; exact inv_mem hh) Pv _ hu
  have h2 := actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at h2
  rwa [h2] at h1

end GlobalTheory.LatStab

end
