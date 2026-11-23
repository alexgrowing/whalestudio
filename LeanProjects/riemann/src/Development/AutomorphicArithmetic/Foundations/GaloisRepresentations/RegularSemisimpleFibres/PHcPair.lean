import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAddStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIrrCharAddStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingAddNatPosSymmStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIsCharEqAddOfPairNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInvStatement

noncomputable section

open GlobalTheory.BI GlobalTheory.Shin

namespace UpperTheory.Gal.InertialTypesAlt

section Group

variable {G : Type} [Group G] [Finite G]

private theorem sum_eq_pair {χ : G → ℂ} (ψ : G → ℂ) (hχ : IsChar ℂ ℂ χ) :
    (∑ᶠ g, star (χ g) * ψ g) = (Nat.card G : ℂ) * pair ψ χ := by
  have h := GlobalTheory.T.star_virtualCharacter_eq_apply_inv G χ (AddSubgroup.subset_closure hχ)
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  unfold pair
  rw [← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  exact finsum_congr fun g => by rw [h, mul_comm]

private theorem pairs_iff {χ : G → ℂ} (ψ : G → ℂ) (hχ : IsChar ℂ ℂ χ) : Pairs χ ψ ↔ pair ψ χ ≠ 0 := by
  have hc : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold Pairs
  rw [sum_eq_pair ψ hχ, mul_ne_zero_iff]
  tauto

private theorem pair_add_ne {a u b v : G → ℂ} (ha : IsChar ℂ ℂ a) (hu : IsChar ℂ ℂ u) (hb : IsChar ℂ ℂ b)
    (hv : IsChar ℂ ℂ v) (h : pair a b ≠ 0) : pair (a + u) (b + v) ≠ 0 := by
  obtain ⟨hadd, hnat, -, hsymm⟩ := GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm ℂ ℂ G
  obtain ⟨n1, h1⟩ := hnat b a hb ha
  obtain ⟨n2, h2⟩ := hnat v a hv ha
  obtain ⟨n3, h3⟩ := hnat b u hb hu
  obtain ⟨n4, h4⟩ := hnat v u hv hu
  have e : pair (a + u) (b + v) = pair b a + pair v a + (pair b u + pair v u) := by
    rw [hadd, hsymm a (b + v), hsymm u (b + v), hadd b v a, hadd b v u]
  have hn1 : n1 ≠ 0 := by
    rintro rfl
    exact h (by rw [hsymm, h1]; simp)
  rw [e, h1, h2, h3, h4]
  exact_mod_cast (by omega : n1 + n2 + (n3 + n4) ≠ 0)

private theorem isChar_of_irr {φ : G → ℂ} (h : IsIrrChar ℂ ℂ φ) : IsChar ℂ ℂ φ := by
  obtain ⟨n, ρ, -, e⟩ := h
  exact ⟨n, ρ, e⟩

private theorem common {A : G → ℂ} (hA : IsChar ℂ ℂ A) {α : G → ℂ} (hα : IsChar ℂ ℂ α) (h : pair A α ≠ 0) :
    ∃ φ R R' : G → ℂ, IsIrrChar ℂ ℂ φ ∧ IsChar ℂ ℂ R ∧ IsChar ℂ ℂ R' ∧ A = φ + R ∧ α = φ + R' := by
  obtain ⟨hadd, -, -, hsymm⟩ := GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm ℂ ℂ G
  obtain ⟨-, hcadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ G
  have hzero : ∀ c : G → ℂ, pair 0 c = 0 := by
    intro c
    have := hadd 0 0 c
    rw [add_zero] at this
    linear_combination -this
  revert h
  refine GlobalTheory.T.isCharacterOverSubfield_induction_irreducible ℂ ℂ G (fun α => pair A α ≠ 0 → ∃ φ R R' : G → ℂ, IsIrrChar ℂ ℂ φ ∧ IsChar ℂ ℂ R ∧
    IsChar ℂ ℂ R' ∧ A = φ + R ∧ α = φ + R') ?_ ?_ α hα
  · intro h0
    exact absurd (by rw [hsymm, hzero] : pair A 0 = 0) h0
  · intro φ c hφ hc ih hne
    have hsplit : pair A (φ + c) = pair A φ + pair A c := by
      rw [hsymm A (φ + c), hadd, hsymm φ A, hsymm c A]
    by_cases h1 : pair A φ = 0
    · rw [hsplit, h1, zero_add] at hne
      obtain ⟨ψ, R, R', hψ, hR, hR', hA', hc'⟩ := ih hne
      refine ⟨ψ, R, φ + R', hψ, hR, hcadd _ _ (isChar_of_irr hφ) hR', hA', ?_⟩
      rw [hc']
      abel
    · obtain ⟨R, hR, hAR⟩ := GlobalTheory.T.exists_isChar_eq_add_of_pair_ne_zero' ℂ ℂ G φ A hφ hA h1
      exact ⟨φ, R, c, hφ, hR, hc, hAR, rfl⟩

private theorem irr_one_ne {φ : G → ℂ} (h : IsIrrChar ℂ ℂ φ) : φ 1 ≠ 0 := by
  obtain ⟨n, ρ, hirr, hφ⟩ := h
  rw [hφ, Representation.char_one]
  simp only [Module.finrank_fin_fun, Algebra.algebraMap_self, RingHom.id_apply, ne_eq, Nat.cast_eq_zero]
  rintro rfl
  apply hirr.bot_ne_top
  ext v
  rw [Subsingleton.elim v 0]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

private theorem pair_self_ne {x : G → ℂ} (hx : IsChar ℂ ℂ x) (h : x 1 ≠ 0) : pair x x ≠ 0 := by
  obtain ⟨-, -, hirr, -⟩ := GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm ℂ ℂ G
  have hx0 : x ≠ 0 := fun e => h (by simp [e])
  obtain ⟨φ, c, hφ, hc, rfl⟩ := GlobalTheory.T.exists_isIrrChar_add_isChar_of_ne_zero ℂ ℂ G x hx hx0
  obtain ⟨n, hn, hpn⟩ := hirr φ hφ
  refine pair_add_ne (isChar_of_irr hφ) hc (isChar_of_irr hφ) hc ?_
  rw [hpn]
  exact_mod_cast hn.ne'

end Group

section Hc

variable {F : Type} [Field F] [Finite F]

private theorem hc_add_left (a b n : ℕ) (α α' : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) :
    hc a b (α + α') β n = hc a b α β n + hc a b α' β n := by
  funext x
  simp only [hc, hcTw, Pi.add_apply]
  rw [← mul_add, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1
  refine finsum_congr fun y => ?_
  split_ifs <;> simp [add_mul]

private theorem hc_add_right (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β β' : GL (Fin b) F → ℂ) :
    hc a b α (β + β') n = hc a b α β n + hc a b α β' n := by
  funext x
  simp only [hc, hcTw, Pi.add_apply]
  rw [← mul_add, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1
  refine finsum_congr fun y => ?_
  split_ifs <;> simp [mul_add]

end Hc

theorem hcPair : HcChar → HcOne → HcPair := by
  intro hC hO F _ _ a b n hn α A β B hα hA hβ hB hAα hBβ
  have hcC : ∀ (x : GL (Fin a) F → ℂ) (y : GL (Fin b) F → ℂ), IsChar ℂ ℂ x → IsChar ℂ ℂ y →
      IsChar ℂ ℂ (hc a b x y n) :=
    fun x y hx hy => hC F a b n hn x y hx hy
  obtain ⟨-, hcadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ (GL (Fin n) F)
  rw [pairs_iff _ (hcC A B hA hB)]
  rw [pairs_iff _ hA] at hAα
  rw [pairs_iff _ hB] at hBβ
  obtain ⟨φ, R, R', hφ, hR, hR', rfl, rfl⟩ := common hα hA hAα
  obtain ⟨ψ, S, S', hψ, hS, hS', rfl, rfl⟩ := common hβ hB hBβ
  have hφ' := isChar_of_irr hφ
  have hψ' := isChar_of_irr hψ
  have e1 : hc a b (φ + R) (ψ + S) n =
      hc a b φ ψ n + (hc a b φ S n + (hc a b R ψ n + hc a b R S n)) := by
    rw [hc_add_left, hc_add_right, hc_add_right]
    abel
  have e2 : hc a b (φ + R') (ψ + S') n =
      hc a b φ ψ n + (hc a b φ S' n + (hc a b R' ψ n + hc a b R' S' n)) := by
    rw [hc_add_left, hc_add_right, hc_add_right]
    abel
  rw [e1, e2]
  refine pair_add_ne (hcC _ _ hφ' hψ')
    (hcadd _ _ (hcC _ _ hφ' hS) (hcadd _ _ (hcC _ _ hR hψ') (hcC _ _ hR hS)))
    (hcC _ _ hφ' hψ')
    (hcadd _ _ (hcC _ _ hφ' hS') (hcadd _ _ (hcC _ _ hR' hψ') (hcC _ _ hR' hS'))) ?_
  exact pair_self_ne (hcC _ _ hφ' hψ') (hO F a b n hn φ ψ (irr_one_ne hφ) (irr_one_ne hψ))

end UpperTheory.Gal.InertialTypesAlt
