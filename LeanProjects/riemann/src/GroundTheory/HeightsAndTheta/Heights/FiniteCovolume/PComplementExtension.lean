import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementExtension

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic

noncomputable section

namespace ComplementExtension

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W} {v w : W}

theorem toSesq_v_v (hp : IsHyperbolicPair h v w) : h.toSesq v v = 0 := hp.1

theorem toSesq_w_w (hp : IsHyperbolicPair h v w) : h.toSesq w w = 0 := hp.2.1

theorem toSesq_v_w (hp : IsHyperbolicPair h v w) : h.toSesq v w = 1 := hp.2.2

theorem toSesq_w_v (hp : IsHyperbolicPair h v w) : h.toSesq w v = 1 := by
  rw [← h.isSymm.eq v w, hp.2.2, map_one]

theorem toSesq_swap_eq_zero {u z : W} (hz : h.toSesq u z = 0) : h.toSesq z u = 0 := by
  rw [← h.isSymm.eq u z, hz, map_zero]

def proj (hp : IsHyperbolicPair h v w) : W →ₗ[E] hypComplement h v w :=
  LinearMap.codRestrict _
    (LinearMap.id - (h.toSesq w).smulRight v - (h.toSesq v).smulRight w)
    (fun x => by
      rw [mem_hypComplement]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
        smul_eq_mul, toSesq_v_v hp, toSesq_w_w hp, toSesq_v_w hp, toSesq_w_v hp]
      constructor <;> ring)

theorem proj_apply (hp : IsHyperbolicPair h v w) (x : W) :
    (proj hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := rfl

theorem split (hp : IsHyperbolicPair h v w) (x : W) :
    h.toSesq w x • v + (proj hp x : W) + h.toSesq v x • w = x := by
  rw [proj_apply]; abel

theorem toSesq_split (hp : IsHyperbolicPair h v w) (a b a' b' : E) (z z' : hypComplement h v w) :
    h.toSesq (a • v + (z : W) + b • w) (a' • v + (z' : W) + b' • w) =
      conjHom F E a * b' + conjHom F E b * a' + h.toSesq z z' := by
  obtain ⟨hvz, hwz⟩ := mem_hypComplement.1 z.2
  obtain ⟨hvz', hwz'⟩ := mem_hypComplement.1 z'.2
  have hzv := toSesq_swap_eq_zero hvz
  have hzw := toSesq_swap_eq_zero hwz
  simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, toSesq_v_v hp, toSesq_w_w hp, toSesq_v_w hp, toSesq_w_v hp, hvz', hwz', hzv, hzw]
  ring

def extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) : W →ₗ[E] W :=
  (h.toSesq w).smulRight v + (hypComplement h v w).subtype ∘ₗ m ∘ₗ proj hp +
    (h.toSesq v).smulRight w

theorem extMap_apply (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    extMap hp m x = h.toSesq w x • v + (m (proj hp x) : W) + h.toSesq v x • w := rfl

theorem toSesq_w_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq w (extMap hp m x) = h.toSesq w x := by
  have := (mem_hypComplement.1 (m (proj hp x)).2).2
  simp only [extMap_apply, map_add, map_smul, smul_eq_mul, toSesq_w_w hp, toSesq_w_v hp, this]
  ring

theorem toSesq_v_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq v (extMap hp m x) = h.toSesq v x := by
  have := (mem_hypComplement.1 (m (proj hp x)).2).1
  simp only [extMap_apply, map_add, map_smul, smul_eq_mul, toSesq_v_v hp, toSesq_v_w hp, this]
  ring

theorem proj_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    proj hp (extMap hp m x) = m (proj hp x) := by
  apply Subtype.ext
  rw [proj_apply, toSesq_w_extMap, toSesq_v_extMap, extMap_apply]
  abel

theorem extMap_comp (hp : IsHyperbolicPair h v w)
    (m m' : hypComplement h v w →ₗ[E] hypComplement h v w) :
    extMap hp m ∘ₗ extMap hp m' = extMap hp (m ∘ₗ m') := by
  ext x
  rw [LinearMap.comp_apply, extMap_apply hp m, toSesq_w_extMap, toSesq_v_extMap, proj_extMap,
    extMap_apply]
  rfl

theorem extMap_id (hp : IsHyperbolicPair h v w) : extMap hp LinearMap.id = LinearMap.id := by
  ext x
  rw [extMap_apply, LinearMap.id_apply, LinearMap.id_apply]
  exact split hp x

theorem proj_of_mem (hp : IsHyperbolicPair h v w) (x : hypComplement h v w) :
    proj hp (x : W) = x := by
  obtain ⟨hvx, hwx⟩ := mem_hypComplement.1 x.2
  apply Subtype.ext
  rw [proj_apply, hvx, hwx]
  simp

theorem proj_v (hp : IsHyperbolicPair h v w) : proj hp v = 0 := by
  apply Subtype.ext
  rw [proj_apply, toSesq_w_v hp, hp.1]
  simp

theorem proj_w (hp : IsHyperbolicPair h v w) : proj hp w = 0 := by
  apply Subtype.ext
  rw [proj_apply, hp.2.1, hp.2.2]
  simp

theorem proof (h : HermitianForm F E W) : ComplementExtension.Statement h := by
  intro v w hp h' hh' m
  let M : hypComplement h v w ≃ₗ[E] hypComplement h v w := m
  let e : W ≃ₗ[E] W := LinearEquiv.ofLinearMap (extMap hp M.toLinearMap)
    (extMap hp M.symm.toLinearMap)
    (by rw [extMap_comp, LinearEquiv.comp_symm, extMap_id])
    (by rw [extMap_comp, LinearEquiv.symm_comp, extMap_id])
  have he : ∀ x, e x = extMap hp M.toLinearMap x := fun x => rfl
  have hM : ∀ a b, h.toSesq (M a : W) (M b : W) = h.toSesq (a : W) b := by
    intro a b
    rw [← hh', ← hh']
    exact m.2 a b
  have hmem : e ∈ h.unitaryGroup := by
    intro x y
    rw [he, he, extMap_apply, extMap_apply, toSesq_split hp]
    conv_rhs => rw [← split hp x, ← split hp y]
    rw [toSesq_split hp]
    simp only [LinearEquiv.coe_coe, hM]
  refine ⟨⟨e, hmem⟩, ?_, ?_, ?_⟩
  · change e v = v
    rw [he, extMap_apply, proj_v, map_zero, toSesq_w_v hp, hp.1]
    simp
  · change e w = w
    rw [he, extMap_apply, proj_w, map_zero, hp.2.1, hp.2.2]
    simp
  · intro x
    change e x = ((M x : hypComplement h v w) : W)
    obtain ⟨hvx, hwx⟩ := mem_hypComplement.1 x.2
    rw [he, extMap_apply, proj_of_mem, hvx, hwx]
    simp

end ComplementExtension

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
