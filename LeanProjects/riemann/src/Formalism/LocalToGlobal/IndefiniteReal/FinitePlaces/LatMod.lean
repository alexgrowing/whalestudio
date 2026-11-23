import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemFin

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7}

def jF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem jF_tmul (β : Af D.host.F) (y : D.host.E) : jF D (β ⊗ₜ[D.host.F] y) = pairA D.host.F 0 β ⊗ₜ[D.host.F] y := rfl

theorem mul_pairA (x : AF D.host.F) (α : Af D.host.F) :
    x * pairA D.host.F 0 α = pairA D.host.F 0 (sndA D.host.F x * α) :=
  Prod.ext (by show x.1 * 0 = 0; rw [mul_zero]) rfl

theorem finPart_tmul (x : AF D.host.F) (z : D.host.E) : finPart D (x ⊗ₜ[D.host.F] z) = sndA D.host.F x ⊗ₜ[D.host.F] z :=
  rfl

set_option maxHeartbeats 800000 in

theorem mul_gen (a : AE D) (α : Af D.host.F) (m : D.host.E) :
    a * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      jF D (finPart D a * (α ⊗ₜ[D.host.F] (1 : D.host.E))) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] m) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul, map_zero, zero_mul]
  | tmul x z =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_pairA, finPart_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      jF_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, add_mul, map_add, add_mul]

theorem gen_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    {c : D.host.E} (hc : c ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS) {t : Fin T.rank → D.host.E}
    (ht : t ∈ ΛT) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j) : WO S T) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
  AddSubgroup.subset_closure ⟨α, hα, fun _ h => absurd trivial h, c, hc, s, hs, t, ht, rfl⟩

set_option maxHeartbeats 1600000 in
theorem jF_gen_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D)
    {c : D.host.E} (hc : c ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS) {t : Fin T.rank → D.host.E}
    (ht : t ∈ ΛT) :
    (Matrix.of fun i j => jF D z * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, y, rfl⟩ := hx
    have hyc : (y : D.host.E) * c ∈ D.host.AA := by
      have := Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) y hc
      rwa [Algebra.smul_def] at this
    have hm : (Matrix.of fun i j => jF D (β ⊗ₜ[D.host.F] (y : D.host.E)) *
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) =
        Matrix.of fun i j => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((y : D.host.E) * c * t i * ∑ k, star (s k) * S.gram k j) := by
      ext i j
      rw [Matrix.of_apply, Matrix.of_apply, jF_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc, mul_assoc,
        mul_assoc]
    rw [hm]
    exact gen_mem S T ΛS ΛT hβ hyc hs ht
  | zero =>
    have hm : (Matrix.of fun i j => jF D 0 *
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) = 0 := by
      ext i j; rw [Matrix.of_apply, map_zero, zero_mul]; rfl
    rw [hm]; exact zero_mem _
  | add x y _ _ hx hy =>
    have hm : (Matrix.of fun i j => jF D (x + y) *
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) =
        (Matrix.of fun i j => jF D x * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))) +
        (Matrix.of fun i j => jF D y * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))) := by
      ext i j; rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, map_add, add_mul]
    rw [hm]; exact add_mem hx hy
  | neg x _ hx =>
    have hm : (Matrix.of fun i j => jF D (-x) *
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) =
        -(Matrix.of fun i j => jF D x * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))) := by
      ext i j; rw [Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, map_neg, neg_mul]
    rw [hm]; exact neg_mem hx

set_option maxHeartbeats 1600000 in

theorem latO_smul_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {a : AE D} (ha : finPart D a ∈ intAE D) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    a • u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩ := hx
    have hz : finPart D a * (α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
      intAE_mul ha (AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩)
    have hm : a • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j) :
        WO S T) = Matrix.of fun i j => jF D (finPart D a * (α ⊗ₜ[D.host.F] (1 : D.host.E))) *
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) := by
      ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, smul_eq_mul, mul_gen]
    rw [hm]
    exact jF_gen_mem S T ΛS ΛT hz hc hs ht
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end Formalism.IndefR.Fin

end
