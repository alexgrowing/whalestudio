import Mathlib
import Formalism.UnipotentAdelicQuotients.CuspEllipticValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps

noncomputable section
open CategoryTheory CuspElliptic
namespace GlobalTheory.CuspCharCheck

section Group
variable {G : Type} [Group G]

theorem isChar_iff (χ : G → ℂ) : IsChar χ ↔ ∃ V : FDRep ℂ G, V.character = χ := by
  constructor
  · rintro ⟨n, ρ, h⟩
    let r : Representation ℂ G (Fin n → ℂ) :=
      (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toMonoidHom.comp ((Units.coeHom _).comp ρ)
    refine ⟨FDRep.of r, funext fun x => ?_⟩
    rw [h]
    exact Matrix.trace_toLin'_eq _
  · rintro ⟨V, rfl⟩
    let b := Module.finBasis ℂ V
    let m : G →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
      (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp V.ρ
    exact ⟨_, m.toHomUnits, fun x => LinearMap.trace_eq_matrix_trace ℂ b _⟩

theorem norm_iff [Fintype G] (V : FDRep ℂ G) :
    (∑ x, V.character x * star (V.character x)) = (Fintype.card G : ℂ) ↔ Simple V := by
  rw [FDRep.simple_iff_char_is_norm_one, Nat.card_eq_fintype_card]
  simp only [GlobalTheory.BadShare.ZCalc.character_inv, starRingEnd_apply]

theorem isIrrChar_iff [Fintype G] (χ : G → ℂ) : IsIrrChar χ ↔ ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ := by
  unfold IsIrrChar
  rw [isChar_iff]
  constructor
  · rintro ⟨⟨V, rfl⟩, h⟩
    exact ⟨V, (norm_iff V).1 h, rfl⟩
  · rintro ⟨V, h, rfl⟩
    exact ⟨⟨V, rfl⟩, (norm_iff V).2 h⟩

theorem sum_subgroup_eq_zero_iff [Fintype G] (V : FDRep ℂ G) (U : Subgroup G) [DecidablePred (· ∈ U)] :
    (∑ u : G, if u ∈ U then V.character u else 0) = 0 ↔ ∀ v : V, (∀ u ∈ U, V.ρ u v = v) → v = 0 := by
  have hc : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  haveI := invertibleOfNonzero hc
  have h := Representation.card_inv_mul_sum_char_eq_finrank (V.ρ.comp U.subtype : Representation ℂ U V)
  have hs : (∑ u : G, if u ∈ U then V.character u else 0) =
      ∑ g : U, Representation.character (V.ρ.comp U.subtype : Representation ℂ U V) g := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) (fun g => V.character g)
  rw [hs]
  have h2 : (∑ g : U, Representation.character (V.ρ.comp U.subtype : Representation ℂ U V) g) = 0 ↔
      Representation.invariants (V.ρ.comp U.subtype : Representation ℂ U V) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← Nat.cast_eq_zero (R := ℂ), ← h, mul_eq_zero, or_iff_right (inv_ne_zero hc)]
  rw [h2, Submodule.eq_bot_iff]
  refine forall_congr' fun v => imp_congr ?_ Iff.rfl
  rw [Representation.mem_invariants]
  exact ⟨fun h u hu => h ⟨u, hu⟩, fun h u => h u.1 u.2⟩

theorem zero_isChar : IsChar (fun _ : G => (0 : ℂ)) := ⟨0, 1, fun _ => by simp⟩

theorem zero_not_isIrrChar [Fintype G] : ¬ IsIrrChar (fun _ : G => (0 : ℂ)) := by
  rintro ⟨-, h⟩
  simp only [zero_mul, Finset.sum_const_zero] at h
  exact (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h.symm

end Group

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem mem_unipBlock_iff (d a : ℕ) (u : GL (Fin d) F) :
    u ∈ (unipBlock d a : Set (GL (Fin d) F)) ↔
      ∀ i j : Fin d, ¬ (i.val < a ∧ a ≤ j.val) → ((u : Matrix (Fin d) (Fin d) F) - 1) i j = 0 := by
  unfold unipBlock
  refine forall₂_congr fun i j => ?_
  rw [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply]
  tauto

omit [Fintype F] [DecidableEq F] in
theorem block_mul_eq_zero {d a : ℕ} {X Y : Matrix (Fin d) (Fin d) F}
    (hX : ∀ i j : Fin d, ¬ (i.val < a ∧ a ≤ j.val) → X i j = 0)
    (hY : ∀ i j : Fin d, ¬ (i.val < a ∧ a ≤ j.val) → Y i j = 0) : X * Y = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k.val < a
  · rw [hX i k (by omega), zero_mul]
  · rw [hY k j (by omega), mul_zero]

def unipSubgroup (d a : ℕ) : Subgroup (GL (Fin d) F) where
  carrier := unipBlock d a
  one_mem' := (mem_unipBlock_iff d a 1).2 fun i j _ => by simp
  mul_mem' := by
    intro u v hu hv
    rw [mem_unipBlock_iff] at hu hv ⊢
    intro i j hij
    have h0 := block_mul_eq_zero hu hv
    have : ((u * v : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) - 1 =
        ((u : Matrix (Fin d) (Fin d) F) - 1) + ((v : Matrix (Fin d) (Fin d) F) - 1) := by
      rw [Units.val_mul, ← sub_eq_zero, ← h0]; noncomm_ring
    rw [this, Matrix.add_apply, hu i j hij, hv i j hij, add_zero]
  inv_mem' := by
    intro u hu
    rw [mem_unipBlock_iff] at hu ⊢
    intro i j hij
    have h0 := block_mul_eq_zero hu hu
    have h1 : (u : Matrix (Fin d) (Fin d) F) * (1 - ((u : Matrix (Fin d) (Fin d) F) - 1)) = 1 := by
      rw [← sub_eq_zero, ← neg_eq_zero, ← h0]; noncomm_ring
    have h2 : ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 - ((u : Matrix (Fin d) (Fin d) F) - 1) :=
      Units.inv_eq_of_mul_eq_one_right h1
    rw [h2, sub_sub_cancel_left, Matrix.neg_apply, hu i j hij, neg_zero]

theorem exists_mem_unipBlock (d a : ℕ) (X : Matrix (Fin d) (Fin d) F)
    (hX : ∀ i j : Fin d, ¬ (i.val < a ∧ a ≤ j.val) → X i j = 0) :
    ∃ u ∈ (unipBlock d a : Set (GL (Fin d) F)), (u : Matrix (Fin d) (Fin d) F) = 1 + X := by
  have h0 := block_mul_eq_zero hX hX
  refine ⟨⟨1 + X, 1 - X, ?_, ?_⟩, (mem_unipBlock_iff d a _).2 (by simpa using hX), rfl⟩
  · rw [← sub_eq_zero, ← neg_eq_zero, ← h0]; noncomm_ring
  · rw [← sub_eq_zero, ← neg_eq_zero, ← h0]; noncomm_ring

theorem isCuspChar_iff {d : ℕ} (χ : GL (Fin d) F → ℂ) :
    IsCuspChar χ ↔ ∃ V : FDRep ℂ (GL (Fin d) F), Simple V ∧ V.character = χ ∧
      ∀ a, 0 < a → a < d → ∀ v : V, (∀ u ∈ (unipSubgroup d a : Subgroup (GL (Fin d) F)), V.ρ u v = v) → v = 0 := by
  classical
  unfold IsCuspChar
  rw [isIrrChar_iff]
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, h⟩
    refine ⟨V, hV, rfl, fun a h0 h1 => (sum_subgroup_eq_zero_iff V _).1 ?_⟩
    convert h a h0 h1 using 3
    rfl
  · rintro ⟨V, hV, rfl, h⟩
    refine ⟨⟨V, hV, rfl⟩, fun a h0 h1 => ?_⟩
    convert (sum_subgroup_eq_zero_iff V _).2 (h a h0 h1) using 3
    rfl

theorem isCuspChar_iff_of_le_one {d : ℕ} (hd : d ≤ 1) (χ : GL (Fin d) F → ℂ) : IsCuspChar χ ↔ IsIrrChar χ :=
  ⟨fun h => h.1, fun h => ⟨h, fun a h0 h1 => by omega⟩⟩

theorem isIrrChar_of_hom {G : Type} [Group G] [Fintype G] (c : G →* ℂˣ) : IsIrrChar (fun x => (c x : ℂ)) := by
  have hc : IsChar (fun x => (c x : ℂ)) :=
    ⟨1, (Units.map (Matrix.scalar (Fin 1) : ℂ →+* _).toMonoidHom).comp c, fun x => by simp⟩
  refine ⟨hc, ?_⟩
  obtain ⟨V, hV⟩ := (isChar_iff _).1 hc
  have : ∀ x, (c x : ℂ) * star (c x : ℂ) = 1 := fun x => by
    have h := GlobalTheory.BadShare.ZCalc.character_inv V x
    rw [hV, starRingEnd_apply] at h
    rw [← h, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [Finset.sum_congr rfl fun x _ => this x]
  simp

theorem isCuspChar_rank_one (c : GL (Fin 1) F →* ℂˣ) : IsCuspChar (fun x => (c x : ℂ)) :=
  (isCuspChar_iff_of_le_one le_rfl _).2 (isIrrChar_of_hom c)

theorem not_isCuspChar_one {d : ℕ} (hd : 2 ≤ d) : ¬ IsCuspChar (fun _ : GL (Fin d) F => (1 : ℂ)) := by
  classical
  rintro ⟨-, h⟩
  have h1 := h 1 one_pos (by omega)
  rw [Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
  exact h1 (Finset.mem_univ 1) (unipSubgroup d 1 : Subgroup (GL (Fin d) F)).one_mem

theorem isCuspChar_of_hom {d : ℕ} (c : GL (Fin d) F →* ℂˣ)
    (hc : ∀ a, 0 < a → a < d → ∃ t ∈ (unipBlock d a : Set (GL (Fin d) F)), (c t : ℂ) ≠ 1) :
    IsCuspChar (fun x => (c x : ℂ)) := by
  classical
  refine ⟨isIrrChar_of_hom _, fun a h0 h1 => ?_⟩
  obtain ⟨t, ht, hs⟩ := hc a h0 h1
  let U : Subgroup (GL (Fin d) F) := unipSubgroup d a
  let f : U →* ℂ := ((Units.coeHom ℂ).comp c).comp U.subtype
  have h := sum_hom_units_eq_zero f (fun h => hs (by
    have h2 := DFunLike.congr_fun h (⟨t, ht⟩ : U)
    exact h2))
  rw [← Finset.sum_filter]
  refine Eq.trans ?_ h
  exact Finset.sum_subtype (p := (· ∈ U)) _ (fun x => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _))
    (fun g => ((c g : ℂˣ) : ℂ))

def permOfGL (d : ℕ) : GL (Fin d) F →* Equiv.Perm (Fin d → F) :=
  MonoidHom.toHomPerm
    { toFun := fun (g : GL (Fin d) F) => (fun v => (g : Matrix (Fin d) (Fin d) F).mulVec v : Function.End (Fin d → F))
      map_one' := funext fun v => Matrix.one_mulVec v
      map_mul' := fun g h => funext fun v => (Matrix.mulVec_mulVec v _ _).symm }

def signChar : GL (Fin 2) (ZMod 2) →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp (Equiv.Perm.sign.comp (permOfGL 2))

def transv : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩

theorem transv_mem : transv ∈ (unipBlock 2 1 : Set (GL (Fin 2) (ZMod 2))) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [transv]

theorem signChar_transv : signChar transv = -1 := by
  have hp : permOfGL 2 transv = Equiv.swap ![0, 1] ![1, 1] := by
    ext v i
    revert v i
    decide
  show Units.map _ (Equiv.Perm.sign (permOfGL 2 transv)) = -1
  rw [hp, Equiv.Perm.sign_swap (by decide)]
  ext; simp

theorem isCuspChar_signChar : IsCuspChar (fun x => (signChar x : ℂ)) := by
  refine isCuspChar_of_hom _ fun a h0 h1 => ?_
  obtain rfl : a = 1 := by omega
  refine ⟨transv, transv_mem, ?_⟩
  rw [signChar_transv]
  norm_num

end GlobalTheory.CuspCharCheck
