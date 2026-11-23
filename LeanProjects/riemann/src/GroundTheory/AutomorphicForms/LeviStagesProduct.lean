import Mathlib
import GroundTheory.AutomorphicForms.LeviCartan
import GroundTheory.AutomorphicForms.LeviStagesInduction
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology

section Transport

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] (e : G ≃ₜ* H)
  {V : Type*} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H V)

theorem stabilizerOf_comp (v : V) :
    (stabilizerOf (σ.comp e.toMulEquiv.toMonoidHom) v : Set G) = e ⁻¹' (stabilizerOf σ v : Set H) :=
  rfl

theorem fixedVectors_comp (K : Subgroup G) :
    fixedVectors (σ.comp e.toMulEquiv.toMonoidHom) K =
      fixedVectors σ (K.map e.toMulEquiv.toMonoidHom) := by
  ext v
  simp only [mem_fixedVectors, Subgroup.mem_map]
  constructor
  · rintro hv _ ⟨k, hk, rfl⟩
    exact hv k hk
  · intro hv k hk
    exact hv _ ⟨k, hk, rfl⟩

theorem isSmooth_comp_iff : IsSmooth (σ.comp e.toMulEquiv.toMonoidHom) ↔ IsSmooth σ := by
  refine forall_congr' fun v => ?_
  rw [stabilizerOf_comp]
  exact e.toHomeomorph.isOpen_preimage

theorem coe_map_eq_image (K : Subgroup G) :
    ((K.map e.toMulEquiv.toMonoidHom : Subgroup H) : Set H) = e '' (K : Set G) :=
  Subgroup.coe_map _ _

theorem map_comap_eq (K : Subgroup H) :
    (K.comap e.toMulEquiv.toMonoidHom).map e.toMulEquiv.toMonoidHom = K :=
  Subgroup.map_comap_eq_self_of_surjective e.toMulEquiv.surjective K

theorem isAdmissible_comp_iff :
    IsAdmissible (σ.comp e.toMulEquiv.toMonoidHom) ↔ IsAdmissible σ := by
  refine and_congr (isSmooth_comp_iff e σ) ⟨fun h K hKc hKo => ?_, fun h K hKc hKo => ?_⟩
  · have hc : IsCompact ((K.comap e.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
      rw [Subgroup.coe_comap]
      exact e.toHomeomorph.isCompact_preimage.2 hKc
    have ho : IsOpen ((K.comap e.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
      rw [Subgroup.coe_comap]
      exact hKo.preimage e.continuous
    have := h _ hc ho
    rw [fixedVectors_comp, map_comap_eq] at this
    exact this
  · rw [fixedVectors_comp]
    refine h _ ?_ ?_
    · rw [coe_map_eq_image]
      exact hKc.image e.continuous
    · rw [coe_map_eq_image]
      exact e.toHomeomorph.isOpenMap _ hKo

def subrepresentationCompOrderIso {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (σ : Representation ℂ H V) :
    Subrepresentation (σ.comp f) ≃o Subrepresentation σ where
  toFun S := ⟨S.toSubmodule, fun h v hv => by
    obtain ⟨g, rfl⟩ := hf h
    exact S.apply_mem_toSubmodule g hv⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp_iff :
    Representation.IsIrreducible (σ.comp e.toMulEquiv.toMonoidHom) ↔ σ.IsIrreducible :=
  OrderIso.isSimpleOrder_iff (subrepresentationCompOrderIso _ e.toMulEquiv.surjective σ)

end Transport

section Blocks

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem blocks_one (a : Set.range β) : blocks β F (1 : Matrix (Fin n) (Fin n) F) a = 1 := by
  ext i j
  simp only [blocks, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg (fun e => h (Subtype.ext e)), if_neg h]

theorem blocks_mul_apply {X Y : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0)
    (hY : ∀ i j, β i ≠ β j → Y i j = 0) (a : Set.range β) :
    blocks β F (X * Y) a = blocks β F X a * blocks β F Y a := by
  rw [blocks_mul hX hY]
  rfl

theorem levi_blockDiag {m : GL (Fin n) F} (hm : m ∈ levi F n β) :
    ∀ i j, β i ≠ β j → (m : Matrix (Fin n) (Fin n) F) i j = 0 :=
  mem_levi.1 hm

variable (F) in

def leviBlock (m : levi F n β) (a : Set.range β) : GL (Fiber β a) F where
  val := blocks β F ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a
  inv := blocks β F (((m⁻¹ : levi F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a
  val_inv := by
    rw [← blocks_mul_apply (levi_blockDiag m.2) (levi_blockDiag (m⁻¹).2), ← Units.val_mul,
      ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one, blocks_one]
  inv_val := by
    rw [← blocks_mul_apply (levi_blockDiag (m⁻¹).2) (levi_blockDiag m.2), ← Units.val_mul,
      ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one, blocks_one]

theorem coe_leviBlock (m : levi F n β) (a : Set.range β) :
    ((leviBlock F m a : GL (Fiber β a) F) : Matrix (Fiber β a) (Fiber β a) F) =
      blocks β F ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a := rfl

variable (F) in

def leviAssemble (x : ∀ a : Set.range β, GL (Fiber β a) F) : levi F n β :=
  ⟨⟨blockAssemble β F fun a => (x a : Matrix (Fiber β a) (Fiber β a) F),
      blockAssemble β F fun a => (((x a)⁻¹ : GL (Fiber β a) F) : Matrix (Fiber β a) (Fiber β a) F),
      by
        rw [← map_mul, ← map_one (blockAssemble β F)]
        congr 1
        funext a
        exact Units.mul_inv (x a),
      by
        rw [← map_mul, ← map_one (blockAssemble β F)]
        congr 1
        funext a
        exact Units.inv_mul (x a)⟩,
    mem_levi.2 fun _ _ h => blockAssemble_apply_of_ne _ h⟩

theorem coe_leviAssemble (x : ∀ a : Set.range β, GL (Fiber β a) F) :
    (((leviAssemble F x : levi F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      blockAssemble β F fun a => (x a : Matrix (Fiber β a) (Fiber β a) F) := rfl

theorem continuous_blockAssemble_apply {X : Type*} [TopologicalSpace X]
    {f : X → ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) F}
    (hf : ∀ a i j, Continuous fun x => f x a i j) :
    Continuous fun x => blockAssemble β F (f x) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : β i = β j
  · have hj : blockOf β j = blockOf β i := Subtype.ext h.symm
    have e : (fun x => blockAssemble β F (f x) i j) =
        fun x => f x (blockOf β i) ⟨i, rfl⟩ ⟨j, hj⟩ :=
      funext fun x => blockAssemble_apply_of_eq _ rfl hj
    rw [e]
    exact hf _ _ _
  · have e : (fun x => blockAssemble β F (f x) i j) = fun _ => 0 :=
      funext fun x => blockAssemble_apply_of_ne _ h
    rw [e]
    exact continuous_const

variable (F β) in

def leviEquivBlocks : levi F n β ≃ₜ* (∀ a : Set.range β, GL (Fiber β a) F) where
  toFun m a := leviBlock F m a
  invFun := leviAssemble F
  left_inv m := Subtype.ext (Units.ext (blockAssemble_blocks (levi_blockDiag m.2)))
  right_inv x := funext fun a => Units.ext (congrFun (blocks_blockAssemble _) a)
  map_mul' m m' := funext fun a => Units.ext (by
    show blocks β F (((m * m' : levi F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a = _
    rw [Subgroup.coe_mul, Units.val_mul, blocks_mul_apply (levi_blockDiag m.2)
      (levi_blockDiag m'.2)]
    rfl)
  continuous_toFun := continuous_pi fun a => Units.continuous_iff.2
    ⟨continuous_matrix fun i j =>
        (continuous_entry F n i.1 j.1).comp continuous_subtype_val,
      continuous_matrix fun i j =>
        (continuous_entry F n i.1 j.1).comp (continuous_subtype_val.comp continuous_inv)⟩
  continuous_invFun := Continuous.subtype_mk (Units.continuous_iff.2
    ⟨continuous_blockAssemble_apply fun a i j =>
        (Units.continuous_val.matrix_elem i j).comp (continuous_apply a),
      continuous_blockAssemble_apply fun a i j =>
        (Units.continuous_coe_inv.matrix_elem i j).comp (continuous_apply a)⟩) _

theorem leviEquivBlocks_apply (m : levi F n β) (a : Set.range β) :
    ((leviEquivBlocks F β m a : GL (Fiber β a) F) : Matrix (Fiber β a) (Fiber β a) F) =
      fun i j => (m : GL (Fin n) F) i.1 j.1 := rfl

end Blocks

section Numbering

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def glReindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : GL ι F ≃ₜ* GL κ F where
  toMulEquiv := Units.mapEquiv (reindexAlgEquiv F F e).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨continuous_matrix fun i j => Units.continuous_val.matrix_elem (e.symm i) (e.symm j),
      continuous_matrix fun i j => Units.continuous_coe_inv.matrix_elem (e.symm i) (e.symm j)⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨continuous_matrix fun i j => Units.continuous_val.matrix_elem (e i) (e j),
      continuous_matrix fun i j => Units.continuous_coe_inv.matrix_elem (e i) (e j)⟩

variable {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)

def blockSize (a : Set.range β) : ℕ := Fintype.card (Fiber β a)

theorem sum_blockSize : ∑ a : Set.range β, blockSize β a = n := by
  rw [show ∑ a : Set.range β, blockSize β a = Fintype.card (Σ a : Set.range β, Fiber β a) from
    (Fintype.card_sigma).symm]
  rw [Fintype.card_congr (Equiv.sigmaFiberEquiv (blockOf β)), Fintype.card_fin]

theorem blockSize_pos (a : Set.range β) : 0 < blockSize β a := by
  obtain ⟨i, hi⟩ := a.2
  exact Fintype.card_pos_iff.2 ⟨⟨i, Subtype.ext hi⟩⟩

theorem blockSize_lt (hβ : ∃ i j, β i ≠ β j) (a : Set.range β) : blockSize β a < n := by
  obtain ⟨i, j, hij⟩ := hβ
  have hout : ∃ k, blockOf β k ≠ a := by
    by_contra hall
    push Not at hall
    exact hij ((congrArg Subtype.val (hall i)).trans (congrArg Subtype.val (hall j)).symm)
  obtain ⟨k, hk⟩ := hout
  have := Fintype.card_subtype_lt (p := fun i => blockOf β i = a) hk
  rwa [Fintype.card_fin] at this

variable (F) in

def leviEquivPi : levi F n β ≃ₜ* (∀ a : Set.range β, GL (Fin (blockSize β a)) F) :=
  (leviEquivBlocks F β).trans
    { toMulEquiv := MulEquiv.piCongrRight fun a =>
        (glReindex (F := F) (Fintype.equivFinOfCardEq rfl : Fiber β a ≃ Fin (blockSize β a))).toMulEquiv
      continuous_toFun := continuous_pi fun a =>
        (glReindex (F := F) (Fintype.equivFinOfCardEq rfl : Fiber β a ≃ Fin (blockSize β a))).continuous.comp
          (continuous_apply a)
      continuous_invFun := continuous_pi fun a =>
        (glReindex (F := F) (Fintype.equivFinOfCardEq rfl : Fiber β a ≃ Fin (blockSize β a))).symm.continuous.comp
          (continuous_apply a) }

end Numbering

section Restrict

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)

def fiberFin (a : Set.range β) : Fin (blockSize β a) ≃ Fiber β a :=
  (Fintype.equivFinOfCardEq rfl : Fiber β a ≃ Fin (blockSize β a)).symm

def restrictFun {α' : Type*} (γ : Fin n → α') (a : Set.range β) : Fin (blockSize β a) → α' :=
  fun k => γ (fiberFin β a k).1

variable {β}

theorem leviEquivPi_apply (m : levi F n β) (a : Set.range β) (k l : Fin (blockSize β a)) :
    ((leviEquivPi F β m a : GL (Fin (blockSize β a)) F) : Matrix _ _ F) k l =
      (m : GL (Fin n) F) (fiberFin β a k).1 (fiberFin β a l).1 := rfl

theorem fiberFin_symm_apply_blockOf (i : Fin n) :
    (fiberFin β (blockOf β i) ((fiberFin β (blockOf β i)).symm ⟨i, rfl⟩)).1 = i := by
  rw [Equiv.apply_symm_apply]

theorem mem_blockUpper_iff_leviEquivPi {α' : Type*} [LinearOrder α'] (γ : Fin n → α')
    (m : levi F n β) :
    (m : GL (Fin n) F) ∈ blockUpper F n γ ↔
      ∀ a, leviEquivPi F β m a ∈ blockUpper F (blockSize β a) (restrictFun β γ a) := by
  constructor
  · intro hm a k l hkl
    rw [leviEquivPi_apply]
    exact hm hkl
  · intro h i j hij
    by_cases hb : β i = β j
    · have hj : blockOf β j = blockOf β i := Subtype.ext hb.symm
      set a := blockOf β i
      set k := (fiberFin β a).symm ⟨i, rfl⟩
      set l := (fiberFin β a).symm ⟨j, hj⟩
      have hk : (fiberFin β a k).1 = i := by simp [k]
      have hl : (fiberFin β a l).1 = j := by simp [l]
      have hkl : restrictFun β γ a l < restrictFun β γ a k := by
        simp only [restrictFun, hk, hl]
        exact hij
      have := h a hkl
      rw [leviEquivPi_apply, hk, hl] at this
      exact this
    · exact mem_levi.1 m.2 i j hb

theorem mem_levi_iff_leviEquivPi {α' : Type*} [LinearOrder α'] (γ : Fin n → α')
    (m : levi F n β) :
    (m : GL (Fin n) F) ∈ levi F n γ ↔
      ∀ a, leviEquivPi F β m a ∈ levi F (blockSize β a) (restrictFun β γ a) := by
  show (m : GL (Fin n) F) ∈ blockUpper F n γ ⊓ blockUpper F n (OrderDual.toDual ∘ γ) ↔ _
  rw [Subgroup.mem_inf, mem_blockUpper_iff_leviEquivPi, mem_blockUpper_iff_leviEquivPi]
  exact ⟨fun h a => ⟨h.1 a, h.2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩

theorem mem_unipotentRadical_iff_leviEquivPi {α' : Type*} [LinearOrder α'] (γ : Fin n → α')
    (m : levi F n β) :
    (m : GL (Fin n) F) ∈ unipotentRadical F n γ ↔
      ∀ a, leviEquivPi F β m a ∈ unipotentRadical F (blockSize β a) (restrictFun β γ a) := by
  rw [mem_unipotentRadical, mem_blockUpper_iff_leviEquivPi]
  simp only [mem_unipotentRadical]
  constructor
  · rintro ⟨hP, h1⟩
    refine fun a => ⟨hP a, fun k l hkl => ?_⟩
    rw [leviEquivPi_apply, h1 _ _ hkl]
    by_cases hkl' : k = l
    · subst hkl'
      simp
    · have hne : (fiberFin β a k).1 ≠ (fiberFin β a l).1 := fun e =>
        hkl' ((fiberFin β a).injective (Subtype.ext e))
      rw [one_apply_ne hne, one_apply_ne hkl']
  · intro h
    refine ⟨fun a => (h a).1, fun i j hij => ?_⟩
    by_cases hb : β i = β j
    · have hj : blockOf β j = blockOf β i := Subtype.ext hb.symm
      set a := blockOf β i
      set k := (fiberFin β a).symm ⟨i, rfl⟩
      set l := (fiberFin β a).symm ⟨j, hj⟩
      have hk : (fiberFin β a k).1 = i := by simp [k]
      have hl : (fiberFin β a l).1 = j := by simp [l]
      have hkl : restrictFun β γ a k = restrictFun β γ a l := by
        simp only [restrictFun, hk, hl]
        exact hij
      have := (h a).2 k l hkl
      rw [leviEquivPi_apply, hk, hl] at this
      rw [this]
      by_cases hij' : i = j
      · subst hij'
        have hkl' : k = l := by simp [k, l]
        rw [hkl', one_apply_eq, one_apply_eq]
      · have hkl' : k ≠ l := fun e => hij' (by rw [← hk, ← hl, e])
        rw [one_apply_ne hkl', one_apply_ne hij']
    · have hne : i ≠ j := fun e => hb (by rw [e])
      rw [mem_levi.1 m.2 i j hb, one_apply_ne hne]

end Restrict

end Parabolic

end GroundTheory.Automorphic
