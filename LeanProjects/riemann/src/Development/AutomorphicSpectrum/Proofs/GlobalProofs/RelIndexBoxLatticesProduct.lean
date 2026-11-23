import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemConjSub
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.IsArtinianRingKummerAdjoinRootQuotientRoot
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex

open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV

section Line

variable {F : Type} [Field F]

def line (O : Subring F) (c : F) : AddSubgroup F :=
  O.toAddSubgroup.map (AddMonoidHom.mulLeft c)

theorem mem_line {O : Subring F} {c x : F} : x ∈ line O c ↔ ∃ o ∈ O, x = c * o := by
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩

theorem map_line (O : Subring F) (e c : F) :
    (line O c).map (AddMonoidHom.mulLeft e) = line O (e * c) := by
  ext x
  simp only [AddSubgroup.mem_map, mem_line, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
    exact ⟨o, ho, by ring⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨c * o, ⟨o, ho, rfl⟩, by ring⟩

end Line

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem line_le_of_val_le (h : LF O ϖ nrm q) {x y : F} (hy : y ≠ 0)
    (hxy : ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y) : line O x ≤ line O y := by
  have hvy : 0 < ValuativeRel.valuation F y := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy)
  have h1 : x / y ∈ O := by
    rw [mem_iff_val_le h, map_div₀]
    exact div_le_one_of_le₀ hxy zero_le'
  intro z hz
  obtain ⟨o, ho, rfl⟩ := mem_line.1 hz
  exact mem_line.2 ⟨x / y * o, O.mul_mem h1 ho, by field_simp⟩

theorem line_eq_of_val_eq (h : LF O ϖ nrm q) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ValuativeRel.valuation F x = ValuativeRel.valuation F y) : line O x = line O y :=
  le_antisymm (line_le_of_val_le h hy hxy.le) (line_le_of_val_le h hx hxy.ge)

theorem ball_eq_line (h : LF O ϖ nrm q) {d : F} (hd : d ≠ 0) : ball d = line O d⁻¹ := by
  ext x
  rw [mem_ball, mem_line, ← h.O_eq]
  constructor
  · intro hx
    exact ⟨_, hx, by field_simp⟩
  · rintro ⟨o, ho, rfl⟩
    rwa [mul_comm d⁻¹, mul_assoc, inv_mul_cancel₀ hd, mul_one]

theorem relIndex_line_pow (h : LF O ϖ nrm q) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (line O (c * ϖ ^ k)).relIndex (line O c) = q ^ k := by
  have hϖ0 : ϖ ^ k ≠ 0 := pow_ne_zero _ h.ne
  have hp : ∃ p : 𝒪[F], Irreducible p ∧ (p : F) = (Units.mk0 ϖ h.ne : Fˣ) :=
    ⟨_, irreducible_pi h, rfl⟩
  have h1 := relIndex_ball (Units.mk0 ϖ h.ne) hp (k : ℤ)
  have hu : (((Units.mk0 ϖ h.ne : Fˣ) ^ (k : ℤ) : Fˣ) : F) = ϖ ^ k := by simp
  rw [hu, ball_eq_line h one_ne_zero, ball_eq_line h hϖ0, Int.toNat_natCast, inv_one] at h1
  have hinj : Function.Injective (AddMonoidHom.mulLeft (c * ϖ ^ k)) :=
    mul_right_injective₀ (mul_ne_zero hc hϖ0)
  have h2 := AddSubgroup.relIndex_map_map_of_injective (line O 1) (line O (ϖ ^ k)⁻¹) hinj
  rw [map_line, map_line, mul_one, mul_assoc, mul_inv_cancel₀ hϖ0, mul_one] at h2
  rw [h2, h1, h.card]
  rfl

theorem relIndex_line (h : LF O ϖ nrm q) {c o : F} (hc : c ≠ 0) (ho : o ∈ O) (ho0 : o ≠ 0) :
    (((line O (c * o)).relIndex (line O c) : ℕ) : ℝ) = nrm c / nrm (c * o) := by
  obtain ⟨k, hk⟩ := val_eq_pow_of_int h ho0 ((mem_iff_val_le h o).1 ho)
  have hline : line O (c * o) = line O (c * ϖ ^ k) :=
    line_eq_of_val_eq h (mul_ne_zero hc ho0) (mul_ne_zero hc (pow_ne_zero _ h.ne))
      (by rw [map_mul, map_mul, hk, map_pow])
  have hq : (q : ℝ) ≠ 0 := by
    have := one_lt_q h
    exact_mod_cast (by omega : q ≠ 0)
  have hn : nrm o = ((q : ℝ) ^ k)⁻¹ := by
    have := nrm_eq_zpow h (x := o) (e := (k : ℤ)) (by simpa using hk)
    simpa [_root_.zpow_neg] using this
  have hnc : nrm c ≠ 0 := (nrm.pos hc).ne'
  rw [hline, relIndex_line_pow h hc k, map_mul, hn]
  push_cast
  field_simp

end Local

section Box

variable {F : Type} [Field F]

abbrev Idx {n : ℕ} (β : Fin n → ℕ) : Type := {p : Fin n × Fin n // β p.1 ≤ β p.2}

noncomputable def ext0 {n : ℕ} (β : Fin n → ℕ) : (Idx β → F) →+ Matrix (Fin n) (Fin n) F where
  toFun x := Matrix.of fun a b => if hab : β a ≤ β b then x ⟨(a, b), hab⟩ else 0
  map_zero' := by
    ext a b
    simp
  map_add' x y := by
    ext a b
    by_cases hab : β a ≤ β b <;> simp [hab]

theorem matrixExtendByZero_apply {n : ℕ} (β : Fin n → ℕ) (x : Idx β → F) (p : Idx β) :
    ext0 β x p.1.1 p.1.2 = x p := by
  have : β p.1.1 ≤ β p.1.2 := p.2
  simp [ext0, this]

theorem extendByZero_injective {n : ℕ} (β : Fin n → ℕ) : Function.Injective (ext0 (F := F) β) := by
  intro x y hxy
  funext p
  rw [← matrixExtendByZero_apply β x p, ← matrixExtendByZero_apply β y p, hxy]

theorem boxAdd_eq_map (O : Subring F) {n : ℕ} (β : Fin n → ℕ) (c : Fin n → Fin n → F) :
    boxAdd O β c =
      (AddSubgroup.pi Set.univ fun p : Idx β => line O (c p.1.1 p.1.2)).map (ext0 β) := by
  ext X
  constructor
  · rintro ⟨hX, hX'⟩
    refine AddSubgroup.mem_map.2 ⟨fun p => X p.1.1 p.1.2, ?_, ?_⟩
    · rw [AddSubgroup.mem_pi]
      intro p _
      exact mem_line.2 (hX' _ _)
    · ext a b
      by_cases hab : β a ≤ β b
      · simp [ext0, hab]
      · simp [ext0, hab, hX (not_le.1 hab)]
  · rintro h
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 h
    rw [AddSubgroup.mem_pi] at hx
    refine ⟨fun a b hab => ?_, fun a b => ?_⟩
    · simp [ext0, not_le.2 hab]
    · by_cases hab : β a ≤ β b
      · obtain ⟨o, ho, e⟩ := mem_line.1 (hx ⟨(a, b), hab⟩ (Set.mem_univ _))
        exact ⟨o, ho, by simpa [ext0, hab] using e⟩
      · exact ⟨0, O.zero_mem, by simp [ext0, hab]⟩

end Box

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (c c' : Fin n → Fin n → F), (∀ a b, c a b ≠ 0) → (∀ a b, c' a b ≠ 0) → (∀ a b, ∃ o ∈ O, c' a b = c a b * o) → (((boxAdd O β c').relIndex (boxAdd O β c) : ℕ) : ℝ) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => β p.1 ≤ β p.2), nrm (c p.1 p.2) / nrm (c' p.1 p.2) := by
  intro F _ _ _ _ O ϖ nrm q h n β c c' hc hc' hcc
  rw [boxAdd_eq_map, boxAdd_eq_map, AddSubgroup.relIndex_map_map_of_injective _ _ (extendByZero_injective β),
    relIndex_pi', Nat.cast_prod,
    Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => β p.1 ≤ β p.2)
      (p := fun p : Fin n × Fin n => β p.1 ≤ β p.2) (fun p => by simp)]
  refine Finset.prod_congr rfl fun p _ => ?_
  obtain ⟨o, ho, e⟩ := hcc p.1.1 p.1.2
  have ho0 : o ≠ 0 := by
    rintro rfl
    exact hc' p.1.1 p.1.2 (by simpa using e)
  rw [e]
  exact relIndex_line h (hc _ _) ho ho0

end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
