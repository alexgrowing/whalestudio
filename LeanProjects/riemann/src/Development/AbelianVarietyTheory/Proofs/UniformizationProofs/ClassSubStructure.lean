import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PerfectPairingOrthogonalOfCard
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeisenbergWeightSpaceFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeisenbergWeightSpaceIrreducible

noncomputable section

namespace GlobalTheory.ClassWeight

abbrev TorChar (X : Type) [AddCommGroup X] (F : Type) [Field F] (N : ℕ) : Subgroup (Multiplicative X →* Fˣ) :=
  (powMonoidHom N : (Multiplicative X →* Fˣ) →* (Multiplicative X →* Fˣ)).ker

variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}

def evalChar (F : Type) [Field F] (N : ℕ) (α : X) : TorChar X F N →* Fˣ :=
  MonoidHom.mk' (fun τ => τ.1 (Multiplicative.ofAdd α)) fun _ _ => rfl

theorem evalChar_add (α β : X) (τ : TorChar X F N) :
    evalChar F N (α + β) τ = evalChar F N α τ * evalChar F N β τ := map_mul τ.1 _ _

theorem evalChar_add_nsmul (α mu : X) (τ : TorChar X F N) : evalChar F N (α + N • mu) τ = evalChar F N α τ := by
  have h : evalChar F N (N • mu) τ = 1 :=
    (map_pow τ.1 (Multiplicative.ofAdd mu) N).trans (DFunLike.congr_fun (show τ.1 ^ N = 1 from τ.2) _)
  rw [evalChar_add, h, mul_one]

theorem exists_evalChar_ne [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) {α β : X}
    (h : ¬ ∃ mu, β = α + N • mu) : ∃ τ : TorChar X F N, evalChar F N β τ ≠ evalChar F N α τ := by
  have : NeZero (N : F) := ⟨hN⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have : NeZero N := ⟨hN0⟩
  let K : AddSubgroup X := (nsmulAddMonoidHom N : X →+ X).range
  have hK : ∀ q : X ⧸ K, N • q = 0 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨x, rfl⟩
  have : Module.Finite ℤ (X ⧸ K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap (QuotientAddGroup.mk'_surjective K)
  have : Finite (X ⧸ K) := Module.finite_of_fg_torsion _ fun q =>
    ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0)⟩, (natCast_zsmul q N).trans (hK q)⟩
  have h0 : HasEnoughRootsOfUnity F N := inferInstance
  have : HasEnoughRootsOfUnity F (Monoid.exponent (Multiplicative (X ⧸ K))) :=
    h0.of_dvd F (Monoid.exponent_dvd_of_forall_pow_eq_one fun q => hK q.toAdd)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative (X ⧸ K)) F
    (a := Multiplicative.ofAdd ((β - α : X) : X ⧸ K)) fun e => by
      obtain ⟨mu, hmu⟩ := (QuotientAddGroup.eq_zero_iff _).1 (show ((β - α : X) : X ⧸ K) = 0 from e)
      exact h ⟨mu, (sub_eq_iff_eq_add'.1 hmu.symm)⟩
  let τ : TorChar X F N := ⟨φ.comp (QuotientAddGroup.mk' K).toMultiplicative, MonoidHom.ext fun x =>
    (map_pow φ _ N).symm.trans ((congrArg φ (show (Multiplicative.ofAdd (x.toAdd : X ⧸ K)) ^ N = 1 from hK (x.toAdd : X ⧸ K))).trans (map_one φ))⟩
  refine ⟨τ, fun e => hφ ?_⟩
  have e₂ := evalChar_add (β - α) α τ
  rw [sub_add_cancel, e] at e₂
  exact right_eq_mul.1 e₂

variable {E : Type} [AddCommGroup E] [Module F E] {W : X → Type} [∀ α, AddCommGroup (W α)] [∀ α, Module F (W α)]

def classSub (S : ∀ α, E →ₗ[F] W α) (N : ℕ) (α : X) : Submodule F E where
  carrier := {v | ∀ β, (¬ ∃ mu, β = α + N • mu) → S β v = 0}
  add_mem' := fun {v v'} h h' β hβ => by rw [map_add, h β hβ, h' β hβ, add_zero]
  zero_mem' := fun β _ => map_zero _
  smul_mem' := fun c v h β hβ => by rw [map_smul, h β hβ, smul_zero]

theorem mem_classSub {S : ∀ α, E →ₗ[F] W α} {α : X} {v : E} :
    v ∈ classSub S N α ↔ ∀ β, (¬ ∃ mu, β = α + N • mu) → S β v = 0 := Iff.rfl

theorem exists_proj [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) (S : ∀ α, E →ₗ[F] W α)
    (hc : (Nat.card (TorChar X F N) : F) ≠ 0) (l : TorChar X F N → E → E)
    (hl : ∀ τ v β, S β (l τ v) = (evalChar F N β τ : F) • S β v) (α : X) (v : E) :
    ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v := by
  have : Finite (TorChar X F N) := Nat.finite_of_card_ne_zero fun e => hc (by rw [e, Nat.cast_zero])
  have := Fintype.ofFinite (TorChar X F N)
  have key : ∀ β, S β ((Nat.card (TorChar X F N) : F)⁻¹ • ∑ τ, (((evalChar F N α τ)⁻¹ : Fˣ) : F) • l τ v) =
      ((Nat.card (TorChar X F N) : F)⁻¹ * ∑ τ, ((Units.coeHom F).comp (evalChar F N β / evalChar F N α)) τ) • S β v :=
    fun β => by
      rw [map_smul, map_sum, mul_smul, Finset.sum_smul]
      refine congrArg _ (Finset.sum_congr rfl fun τ _ => ?_)
      rw [map_smul, hl, smul_smul, ← Units.val_mul, mul_comm, ← div_eq_mul_inv]
      rfl
  refine ⟨_, fun β hβ => (key β).trans ?_, fun mu => (key _).trans ?_⟩
  · obtain ⟨τ, hτ⟩ := exists_evalChar_ne hN hβ
    rw [sum_hom_units_eq_zero _ fun e => hτ (div_eq_one.1 (Units.ext (DFunLike.congr_fun e τ))), mul_zero, zero_smul]
  · have e : ∀ τ, ((Units.coeHom F).comp (evalChar F N (α + N • mu) / evalChar F N α)) τ = 1 := fun τ =>
      congrArg Units.val (div_eq_one.2 (evalChar_add_nsmul α mu τ))
    rw [Finset.sum_congr rfl fun τ _ => e τ, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_one, inv_mul_cancel₀ hc, one_smul]

theorem classSub_structure [Module.Finite ℤ X] [IsAlgClosed F] [FiniteDimensional F E] (hN : (N : F) ≠ 0)
    {A : Type} [CommGroup A] [Finite A] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)) (hA : (Nat.card A : F) ≠ 0)
    (hd : Module.finrank F E ^ 2 = Nat.card A) (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hn : ∀ a, (∀ b, e a b = 1) → a = 1)
    (S : ∀ α, E →ₗ[F] W α) (hS : ∀ v, (∀ α, S α v = 0) → v = 0)
    (a : TorChar X F N →* A) (ha : Function.Injective a)
    (hT : ∀ τ, ∃ c : Fˣ, ∀ v α, S α (Φ (a τ) v) = ((c * evalChar F N α τ : Fˣ) : F) • S α v)
    (H : Subgroup A) (hH : ∀ h ∈ H, ∀ α v v' (c : F), S α v = c • S α v' → S α (Φ h v) = c • S α (Φ h v'))
    (hcard : Nat.card (TorChar X F N) * Nat.card H = Nat.card A) (α : X) :
    (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
    Module.finrank F (classSub S N α) * Nat.card (TorChar X F N) = Module.finrank F E ∧
    ∀ U : Submodule F E, U ≤ classSub S N α → (∀ h ∈ H, ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = classSub S N α := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hd
      omega
    · exact h
  have ext : ∀ v v', (∀ α, S α v = S α v') → v = v' := fun v v' h =>
    sub_eq_zero.1 (hS _ fun α => by rw [map_sub, h, sub_self])
  choose c hcT using hT
  let l₀ : TorChar X F N → (E ≃ₗ[F] E) := fun τ => (Φ (a τ)).trans (LinearEquiv.smulOfUnit (c τ)⁻¹)
  have l₀e : ∀ τ v, l₀ τ v = (((c τ)⁻¹ : Fˣ) : F) • Φ (a τ) v := fun _ _ => rfl
  have hl : ∀ τ v β, S β (l₀ τ v) = (evalChar F N β τ : F) • S β v := fun τ v β => by
    rw [l₀e, map_smul, hcT, smul_smul, ← Units.val_mul, inv_mul_cancel_left]
  let l : TorChar X F N →* (E ≃ₗ[F] E) := MonoidHom.mk' l₀ fun τ τ' => LinearEquiv.ext fun v => ext _ _ fun β => by
    rw [LinearEquiv.mul_apply, hl, hl, hl, smul_smul, map_mul, Units.val_mul]
  let i : TorChar X F N ≃* a.range := MonoidHom.ofInjective ha
  let lam : a.range →* (E ≃ₗ[F] E) := l.comp i.symm.toMonoidHom
  have hlam : ∀ t : a.range, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v := fun t => by
    obtain ⟨τ, rfl⟩ := i.surjective t
    refine ⟨(c τ)⁻¹, fun v => ?_⟩
    show l₀ (i.symm (i τ)) v = _
    rw [i.symm_apply_apply]; rfl
  let Wt : (a.range →* Fˣ) → Submodule F E := fun χ =>
    { carrier := {v | ∀ t, lam t v = (χ t : F) • v}
      add_mem' := fun {v v'} h h' t => by rw [map_add, h t, h' t, smul_add]
      zero_mem' := fun t => by rw [map_zero, smul_zero]
      smul_mem' := fun r v h t => by rw [map_smul, h t, smul_comm] }
  have hWt : ∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v := fun _ _ => Iff.rfl
  let χ : a.range →* Fˣ := (evalChar F N α).comp i.symm.toMonoidHom
  have hW : Wt χ = classSub S N α := Submodule.ext fun v => ⟨fun h β hβ => by
      obtain ⟨τ, hτ⟩ := exists_evalChar_ne (F := F) hN hβ
      have h₁ : l₀ (i.symm (i τ)) v = (evalChar F N α (i.symm (i τ)) : F) • v := h (i τ)
      have h₂ := congrArg (S β) h₁
      rw [i.symm_apply_apply, hl, map_smul] at h₂
      by_contra h₃
      exact hτ (Units.ext (smul_left_injective F h₃ h₂)), fun h t => ext _ _ fun β => by
      refine (hl (i.symm t) v β).trans ?_
      rw [map_smul]
      by_cases hβ : ∃ mu, β = α + N • mu
      · obtain ⟨mu, rfl⟩ := hβ
        rw [evalChar_add_nsmul]; rfl
      · rw [h β hβ, smul_zero, smul_zero]⟩
  have hci : Nat.card a.range = Nat.card (TorChar X F N) := (Nat.card_congr i.toEquiv).symm
  have hTH : ∀ t ∈ a.range, ∀ h ∈ H, e t h = 1 := by
    rintro _ ⟨τ, rfl⟩ h hh
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have h₁ : Φ (a τ) (Φ h v) = Φ h (Φ (a τ) v) := ext _ _ fun β =>
      (hcT τ _ β).trans (hH h hh β _ _ _ (hcT τ v β)).symm
    have h₂ : Φ h (Φ (a τ) v) ≠ 0 := by simpa using hv
    apply HeisenbergWeightDim.units_eq_of_smul_eq h₂
    rw [← hc, h₁, Units.val_one, one_smul]
  have hperp := (perfectPairing_orthogonal_of_card F A e (HeisenbergWeightDim.comm_mul_left hm hc)
    (HeisenbergWeightDim.comm_mul_right hm hc) hn a.range H hTH (by rw [hci, hcard])).2.1
  refine ⟨exists_proj hN S (fun h => hA (by rw [← hcard, Nat.cast_mul, h, zero_mul])) (fun τ v => l₀ τ v) hl α, ?_,
    fun U hU hst => ?_⟩
  · rw [← hW, ← hci]
    exact (heisenberg_weightSpace_finrank F A E e Φ hA hd hm hc hn a.range lam hlam Wt hWt).2 χ
  · rw [← hW] at hU ⊢
    exact heisenberg_weightSpace_irreducible F A E e Φ hA hd hm hc hn a.range lam hlam Wt hWt χ U hU
      fun h hh => hst h ((hperp h).1 fun t ht => hh ⟨t, ht⟩)

end GlobalTheory.ClassWeight
