import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MatCount

open Matrix Module

variable {k : Type} [Field k] {n : ℕ}

section
variable {X : Type} [AddCommGroup X] [Module k X]
  (ρ : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k X)

theorem unit_mul (i j l p : Fin (n+1)) (x : X) :
    ρ (single i j 1) (ρ (single l p 1) x) = if j = l then ρ (single i p 1) x else 0 := by
  rw [← Module.End.mul_apply, ← map_mul]
  split_ifs with h
  · subst h; rw [single_mul_single_same, mul_one]
  · rw [single_mul_single_of_ne (h := h), map_zero, LinearMap.zero_apply]

theorem recon (x : X) : ∑ i, ρ (single i 0 1) (ρ (single 0 i 1) x) = x := by
  simp only [unit_mul, if_true]
  rw [← LinearMap.sum_apply, ← map_sum, sum_single_one, map_one, Module.End.one_apply]

abbrev corner : Submodule k X := LinearMap.range (ρ (single 0 0 1))

theorem unit_mem_corner (i : Fin (n+1)) (x : X) : ρ (single 0 i 1) x ∈ corner ρ :=
  ⟨ρ (single 0 i 1) x, by rw [unit_mul]; simp⟩

theorem unit_corner (v : corner ρ) (i : Fin (n+1)) :
    ρ (single 0 i 1) (v : X) = if i = 0 then (v : X) else 0 := by
  obtain ⟨y, hy⟩ := v.2
  rw [← hy, unit_mul]

def cut (i : Fin (n+1)) : X →ₗ[k] corner ρ :=
  (ρ (single 0 i 1)).codRestrict (corner ρ) (unit_mem_corner ρ i)

@[simp] theorem cut_coe (i : Fin (n+1)) (x : X) : ((cut ρ i x : corner ρ) : X) = ρ (single 0 i 1) x := rfl

theorem cut_unit (i l p : Fin (n+1)) (x : X) :
    cut ρ i (ρ (single l p 1) x) = if i = l then cut ρ p x else 0 := by
  apply Subtype.ext
  rw [cut_coe, unit_mul]
  split_ifs <;> simp

theorem cut_corner (i : Fin (n+1)) (v : corner ρ) : cut ρ i v = if i = 0 then v else 0 := by
  apply Subtype.ext
  rw [cut_coe, unit_corner]
  split_ifs <;> simp

def piEquiv : X ≃ₗ[k] (Fin (n+1) → corner ρ) :=
  LinearEquiv.ofLinear (LinearMap.pi fun i => cut ρ i)
    (∑ i, ρ (single i 0 1) ∘ₗ (corner ρ).subtype ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.ext fun v => funext fun j => ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
        Submodule.subtype_apply, LinearMap.proj_apply, cut_unit, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, cut_corner, LinearMap.id_apply])
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        cut_coe, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.id_apply]
      exact recon ρ x)

theorem finrank_eq [FiniteDimensional k X] : finrank k X = (n+1) * finrank k (corner ρ) := by
  rw [(piEquiv ρ).finrank_eq, Module.finrank_pi_fintype]
  simp
end

section
variable {X Y : Type} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
  (ρX : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k X)
  (ρY : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k Y)

theorem comm {T : X →ₗ[k] Y} (hT : T ∈ GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) (a : Matrix (Fin (n+1)) (Fin (n+1)) k)
    (x : X) : T (ρX a x) = ρY a (T x) :=
  (GlobalTheory.HTRho.mem_homO _ _ T).1 hT a x

theorem maps_corner (T : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) :
    ∀ x ∈ corner ρX, (T : X →ₗ[k] Y) x ∈ corner ρY := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(T : X →ₗ[k] Y) y, (comm ρX ρY T.2 _ y).symm⟩

def restr : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom →ₗ[k] (corner ρX →ₗ[k] corner ρY) where
  toFun T := (T : X →ₗ[k] Y).restrict (maps_corner ρX ρY T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restr_coe (T : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) (v : corner ρX) :
    ((restr ρX ρY T v : corner ρY) : Y) = (T : X →ₗ[k] Y) v := rfl

def ext (S : corner ρX →ₗ[k] corner ρY) : X →ₗ[k] Y :=
  ∑ i, ρY (single i 0 1) ∘ₗ (corner ρY).subtype ∘ₗ S ∘ₗ cut ρX i

theorem ext_apply (S : corner ρX →ₗ[k] corner ρY) (x : X) :
    ext ρX ρY S x = ∑ i, ρY (single i 0 1) (S (cut ρX i x)) := by
  simp [ext, LinearMap.sum_apply]

theorem ext_unit (S : corner ρX →ₗ[k] corner ρY) (l p : Fin (n+1)) (x : X) :
    ext ρX ρY S (ρX (single l p 1) x) = ρY (single l p 1) (ext ρX ρY S x) := by
  rw [ext_apply, ext_apply, map_sum]
  simp only [cut_unit, unit_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single l (fun b _ hb => by rw [if_neg hb, map_zero, Submodule.coe_zero, map_zero])
    (by simp)]
  simp

theorem ext_mem (S : corner ρX →ₗ[k] corner ρY) :
    ext ρX ρY S ∈ GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom := by
  rw [GlobalTheory.HTRho.mem_homO]
  intro a x
  change ext ρX ρY S (ρX a x) = ρY a (ext ρX ρY S x)
  have ha : a = ∑ l, ∑ p, a l p • single l p (1 : k) := by
    conv_lhs => rw [matrix_eq_sum_single a]
    simp only [smul_single, smul_eq_mul, mul_one]
  rw [ha]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, ext_unit]

theorem restr_bij : Function.Bijective (restr ρX ρY) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun T hT => ?_
    apply Subtype.ext
    refine LinearMap.ext fun x => ?_
    have h0 : ∀ i, (T : X →ₗ[k] Y) (ρX (single 0 i 1) x) = 0 := fun i => by
      exact (congrArg Subtype.val (LinearMap.congr_fun hT ⟨_, unit_mem_corner ρX i x⟩) :)
    change (T : X →ₗ[k] Y) x = 0
    rw [← recon ρX x, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [comm ρX ρY T.2, h0, map_zero]
  · intro S
    refine ⟨⟨ext ρX ρY S, ext_mem ρX ρY S⟩, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [restr_coe]
    change ext ρX ρY S v = _
    rw [ext_apply]
    simp only [cut_corner]
    rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg hb, map_zero, Submodule.coe_zero, map_zero])
      (by simp)]
    simp [unit_corner]

theorem finrank_homO [FiniteDimensional k X] [FiniteDimensional k Y] :
    finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = finrank k (corner ρX) * finrank k (corner ρY) := by
  rw [(LinearEquiv.ofBijective _ (restr_bij ρX ρY)).finrank_eq, Module.finrank_linearMap]
end

theorem count : ∀ (k : Type) [Field k] (m : ℕ) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (ρX : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k X) (ρY : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k Y),
    m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = Module.finrank k X * Module.finrank k Y := by
  intro k _ m X Y _ _ _ _ _ _ ρX ρY
  cases m with
  | zero =>
    have hX : Subsingleton X := by
      refine ⟨fun a b => ?_⟩
      have h : (1 : Module.End k X) = 0 := by
        rw [← map_one ρX, ← map_zero ρX]
        congr 1
        ext i
        exact i.elim0
      have ha := congrArg (fun f : Module.End k X => f a) h
      have hb := congrArg (fun f : Module.End k X => f b) h
      simp only [Module.End.one_apply, LinearMap.zero_apply] at ha hb
      rw [ha, hb]
    simp [finrank_zero_of_subsingleton]
  | succ n =>
    rw [finrank_homO, finrank_eq ρX, finrank_eq ρY]
    ring

end GlobalTheory.MatCount
