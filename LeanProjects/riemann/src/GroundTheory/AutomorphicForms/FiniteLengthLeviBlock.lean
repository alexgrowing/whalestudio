import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemma
import GroundTheory.AutomorphicForms.CuspidalSplitting
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology

section Smooth

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem isSmooth_comp_of_continuous {ρ : Representation ℂ H V} (hρ : IsSmooth ρ) (f : G →* H)
    (hf : Continuous f) : IsSmooth (ρ.comp f) := by
  intro v
  have : (stabilizerOf (ρ.comp f) v : Set G) = f ⁻¹' (stabilizerOf ρ v : Set H) := by
    ext g
    rfl
  rw [this]
  exact (hρ v).preimage hf

end Smooth

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Diagonal

theorem mem_center_levi_of_diagonal {γ : Fin n → ℕ} (x : levi F n γ) (d : Fin n → F)
    (hx : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d)
    (hd : ∀ i j, γ i = γ j → d i = d j) : x ∈ Submonoid.center (levi F n γ) := by
  rw [Submonoid.mem_center_iff]
  intro m
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp only [Subgroup.coe_mul, Units.val_mul, hx, mul_diagonal, diagonal_mul]
  by_cases h : γ i = γ j
  · rw [hd i j h, mul_comm]
  · rw [mem_levi.1 m.2 i j h, zero_mul, mul_zero]

end Diagonal

section Block

variable {δ : Fin n → ℕ}

variable (F δ) in

def blockEmb (a : Set.range δ) : GL (Fin (blockSize δ a)) F →* levi F n δ :=
  (leviEquivPi F δ).symm.toMulEquiv.toMonoidHom.comp
    (MonoidHom.mulSingle (fun b : Set.range δ => GL (Fin (blockSize δ b)) F) a)

theorem leviEquivPi_blockEmb (a : Set.range δ) (y : GL (Fin (blockSize δ a)) F) :
    leviEquivPi F δ (blockEmb F δ a y) = Pi.mulSingle a y := by
  show leviEquivPi F δ ((leviEquivPi F δ).symm (Pi.mulSingle a y)) = _
  exact (leviEquivPi F δ).apply_symm_apply _

theorem continuous_blockEmb (a : Set.range δ) : Continuous (blockEmb F δ a) := by
  have h : Continuous fun y : GL (Fin (blockSize δ a)) F =>
      (Pi.mulSingle a y : ∀ b : Set.range δ, GL (Fin (blockSize δ b)) F) :=
    continuous_mulSingle (A := fun b : Set.range δ => GL (Fin (blockSize δ b)) F) a
  exact (leviEquivPi F δ).symm.continuous.comp h

theorem blockEmb_commute (a : Set.range δ) (y : GL (Fin (blockSize δ a)) F) (x : levi F n δ)
    (hx : leviEquivPi F δ x a = 1) : blockEmb F δ a y * x = x * blockEmb F δ a y := by
  apply (leviEquivPi F δ).injective
  rw [map_mul, map_mul, leviEquivPi_blockEmb]
  funext b
  by_cases hb : b = a
  · subst hb
    simp [hx]
  · simp [Pi.mulSingle_eq_of_ne hb]

variable (F δ) in

def blockRest (a : Set.range δ) (x : levi F n δ) : levi F n δ :=
  (leviEquivPi F δ).symm (Function.update (leviEquivPi F δ x) a 1)

theorem leviEquivPi_blockRest_self (a : Set.range δ) (x : levi F n δ) :
    leviEquivPi F δ (blockRest F δ a x) a = 1 := by
  simp [blockRest]

theorem blockEmb_mul_blockRest (a : Set.range δ) (x : levi F n δ) :
    blockEmb F δ a (leviEquivPi F δ x a) * blockRest F δ a x = x := by
  apply (leviEquivPi F δ).injective
  rw [map_mul, leviEquivPi_blockEmb]
  funext b
  by_cases hb : b = a
  · subst hb
    simp [blockRest]
  · simp [blockRest, Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]

theorem blockEmb_mem_center {a : Set.range δ} {z : GL (Fin (blockSize δ a)) F}
    (hz : z ∈ Subgroup.center (GL (Fin (blockSize δ a)) F)) :
    blockEmb F δ a z ∈ Subgroup.center (levi F n δ) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply (leviEquivPi F δ).injective
  rw [map_mul, map_mul, leviEquivPi_blockEmb]
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same]
    exact Subgroup.mem_center_iff.1 hz _
  · simp [Pi.mulSingle_eq_of_ne hb]

theorem coe_levi_apply_of_blockOf_eq (x : levi F n δ) {i j : Fin n}
    (hij : blockOf δ j = blockOf δ i) :
    ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ((leviEquivPi F δ x (blockOf δ i) : GL (Fin (blockSize δ (blockOf δ i))) F) :
        Matrix _ _ F) ((fiberFin δ (blockOf δ i)).symm ⟨i, rfl⟩)
          ((fiberFin δ (blockOf δ i)).symm ⟨j, hij⟩) := by
  rw [leviEquivPi_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem mulSingle_scalar_apply {a : Set.range δ} {z : GL (Fin (blockSize δ a)) F} {s : F}
    (hz : ((z : GL (Fin (blockSize δ a)) F) : Matrix (Fin (blockSize δ a)) (Fin (blockSize δ a)) F) =
      Matrix.scalar (Fin (blockSize δ a)) s) (b : Set.range δ) (k l : Fin (blockSize δ b)) :
    ((Pi.mulSingle (M := fun b : Set.range δ => GL (Fin (blockSize δ b)) F) a z b :
      GL (Fin (blockSize δ b)) F) : Matrix (Fin (blockSize δ b)) (Fin (blockSize δ b)) F) k l =
      if k = l then (if b = a then s else 1) else 0 := by
  by_cases hb : b = a
  · subst hb
    rw [Pi.mulSingle_eq_same, hz, Matrix.scalar_apply, Matrix.diagonal_apply]
    simp
  · rw [Pi.mulSingle_eq_of_ne hb, Units.val_one, Matrix.one_apply]
    simp [hb]

theorem coe_blockEmb_apply_of_scalar {a : Set.range δ} {z : GL (Fin (blockSize δ a)) F} {s : F}
    (hz : ((z : GL (Fin (blockSize δ a)) F) : Matrix (Fin (blockSize δ a)) (Fin (blockSize δ a)) F) =
      Matrix.scalar (Fin (blockSize δ a)) s) :
    (((blockEmb F δ a z : levi F n δ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun i => if blockOf δ i = a then s else 1 := by
  ext i j
  by_cases hij : blockOf δ j = blockOf δ i
  · rw [coe_levi_apply_of_blockOf_eq _ hij, leviEquivPi_blockEmb, mulSingle_scalar_apply hz,
      diagonal_apply]
    have : ((fiberFin δ (blockOf δ i)).symm ⟨i, rfl⟩ =
        (fiberFin δ (blockOf δ i)).symm ⟨j, hij⟩) ↔ i = j := by
      rw [Equiv.apply_eq_iff_eq]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · rintro rfl
        rfl
    simp only [this]
  · have hne : i ≠ j := fun h => hij (h ▸ rfl)
    rw [diagonal_apply_ne _ hne]
    exact mem_levi.1 (blockEmb F δ a z).2 i j fun h => hij (Subtype.ext h.symm)

theorem blockEmb_mem_unipotentRadical {α' : Type*} [LinearOrder α'] (γ : Fin n → α')
    {a : Set.range δ} {y : GL (Fin (blockSize δ a)) F}
    (hy : y ∈ unipotentRadical F (blockSize δ a) (restrictFun δ γ a)) :
    ((blockEmb F δ a y : levi F n δ) : GL (Fin n) F) ∈ unipotentRadical F n γ := by
  rw [mem_unipotentRadical_iff_leviEquivPi, leviEquivPi_blockEmb]
  intro b
  by_cases hb : b = a
  · subst hb
    simpa using hy
  · rw [Pi.mulSingle_eq_of_ne hb]
    exact one_mem _

theorem eq_one_of_mem_unipotentRadical_const {m : ℕ} {c : ℕ} {g : GL (Fin m) F}
    (hg : g ∈ unipotentRadical F m (fun _ : Fin m => c)) : g = 1 := by
  obtain ⟨-, h⟩ := mem_unipotentRadical.1 hg
  exact Units.ext (Matrix.ext fun i j => h i j rfl)

variable (δ) in

def blockExtend (a : Set.range δ) (ε : Fin (blockSize δ a) → ℕ) : Fin n → ℕ := fun i =>
  if h : blockOf δ i = a then ε ((fiberFin δ a).symm ⟨i, h⟩) else 0

theorem restrictFun_blockExtend_self (a : Set.range δ) (ε : Fin (blockSize δ a) → ℕ) :
    restrictFun δ (blockExtend δ a ε) a = ε := by
  funext k
  simp only [restrictFun, blockExtend, dif_pos (fiberFin δ a k).2]
  congr 1
  rw [Equiv.symm_apply_eq]

theorem restrictFun_blockExtend_of_ne {a b : Set.range δ} (hb : b ≠ a)
    (ε : Fin (blockSize δ a) → ℕ) : restrictFun δ (blockExtend δ a ε) b = fun _ => 0 := by
  funext k
  simp only [restrictFun, blockExtend]
  rw [dif_neg]
  intro h
  exact hb ((fiberFin δ b k).2.symm.trans h)

theorem exists_split_blockExtend {a : Set.range δ} {ε : Fin (blockSize δ a) → ℕ}
    (hε : ∃ k l, ε k ≠ ε l) : ∃ i j, δ i = δ j ∧ blockExtend δ a ε i ≠ blockExtend δ a ε j := by
  obtain ⟨k, l, hkl⟩ := hε
  refine ⟨(fiberFin δ a k).1, (fiberFin δ a l).1, ?_, ?_⟩
  · exact congrArg Subtype.val ((fiberFin δ a k).2.trans (fiberFin δ a l).2.symm)
  · have hk := congrFun (restrictFun_blockExtend_self a ε) k
    have hl := congrFun (restrictFun_blockExtend_self a ε) l
    simp only [restrictFun] at hk hl
    rw [hk, hl]
    exact hkl

theorem exists_blockEmb_of_mem_unipotentRadical {a : Set.range δ} {ε : Fin (blockSize δ a) → ℕ}
    (u : levi F n δ) (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n (blockExtend δ a ε)) :
    ∃ y ∈ unipotentRadical F (blockSize δ a) ε, blockEmb F δ a y = u := by
  rw [mem_unipotentRadical_iff_leviEquivPi] at hu
  have ha := hu a
  rw [restrictFun_blockExtend_self] at ha
  refine ⟨leviEquivPi F δ u a, ha, ?_⟩
  apply (leviEquivPi F δ).injective
  rw [leviEquivPi_blockEmb]
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · rw [Pi.mulSingle_eq_of_ne hb]
    have := hu b
    rw [restrictFun_blockExtend_of_ne hb] at this
    exact (eq_one_of_mem_unipotentRadical_const this).symm

end Block

end Parabolic

end GroundTheory.Automorphic
