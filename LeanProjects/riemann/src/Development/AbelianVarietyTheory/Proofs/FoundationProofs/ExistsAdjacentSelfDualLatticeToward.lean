import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PerfectPairingQuotients
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem index_comap_toSpanSingleton_ne_zero {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) {y : X} (hy : y ∈ B) :
    (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index ≠ 0 := by
  have h1 : (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup =
      A.toAddSubgroup.comap (LinearMap.toSpanSingleton R X y).toAddMonoidHom := rfl
  rw [h1, AddSubgroup.index_comap]
  intro h0
  refine hAB (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rintro _ ⟨r, rfl⟩
  exact B.smul_mem r hy

theorem exists_mem_maximal_annihilator {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) (hBA : ¬ B ≤ A) :
    ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ ∀ r : R, r • x ∈ A ↔ r ∈ P := by
  have hex : ∃ n, ∃ y ∈ B, y ∉ A ∧
      (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index = n := by
    obtain ⟨y, hyB, hyA⟩ := SetLike.not_le_iff_exists.1 hBA
    exact ⟨_, y, hyB, hyA, rfl⟩
  obtain ⟨x, hxB, hxA, hx⟩ := Nat.find_spec hex
  have hne := index_comap_toSpanSingleton_ne_zero A B hAB hxB
  let P : Ideal R := A.comap (LinearMap.toSpanSingleton R X x)
  have hP : ∀ r : R, r • x ∈ A ↔ r ∈ P := fun r => Iff.rfl
  have hfin : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero hne
  have hprime : P.IsPrime := by
    refine ⟨fun htop => hxA ?_, fun {r s} hrs => ?_⟩
    · have : (1 : R) ∈ P := htop ▸ Submodule.mem_top
      simpa using (hP 1).2 this
    · by_contra hcon
      rw [not_or] at hcon
      have hs : s • x ∉ A := fun h => hcon.2 ((hP s).1 h)
      have hmin := Nat.find_min' hex ⟨s • x, B.smul_mem s hxB, hs, rfl⟩
      have hne' := index_comap_toSpanSingleton_ne_zero A B hAB (B.smul_mem s hxB)
      have hle : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup ≤
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        intro a ha
        have ha' : a • x ∈ A := ha
        show a • s • x ∈ A
        rw [smul_comm]
        exact A.smul_mem s ha'
      have hmul := AddSubgroup.relIndex_mul_index hle
      rw [← hx, ← hmul] at hmin
      have h1 : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup.relIndex
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup = 1 := by
        rw [← hmul] at hne
        have h2 := Nat.pos_of_ne_zero (left_ne_zero_of_mul hne)
        have h3 := Nat.pos_of_ne_zero hne'
        nlinarith
      rw [AddSubgroup.relIndex_eq_one] at h1
      have hr : r ∈ (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        show r • s • x ∈ A
        rw [smul_smul]
        exact (hP _).2 hrs
      exact hcon.1 (h1 hr)
  haveI := hprime
  exact ⟨x, hxB, P, Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain _), hfin, hP⟩

theorem exists_adj_selfDual_step : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → ¬ B ≤ A → ∃ A' : Submodule R X, SelfDual γ A' ∧ Adj A A' ∧ A' ≤ (A' ⊓ A) ⊔ (A' ⊓ B) := by
  intro R X M _ _ _ _ _ σ w γ W h A B hA hB hAB hBA
  obtain ⟨x, hxB, P, hPm, hPf, hP⟩ := exists_mem_maximal_annihilator A B hAB hBA
  let T : Submodule R X := Submodule.span R {x}
  have hTB : T ≤ B := (Submodule.span_singleton_le_iff_mem x B).2 hxB
  have hxT : x ∈ T := Submodule.mem_span_singleton_self x
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, one_mul]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]
        exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hS : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSA : S ≤ A := fun a ha => ha.1
  have hidx : A.toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := fun h0 =>
    hAB (AddSubgroup.relIndex_eq_zero_of_le_right (fun t ht => hTB ht) h0)
  obtain ⟨-, hdual, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup (fun a ha => ⟨fun h1 => h1.2, fun h1 => ⟨ha, h1⟩⟩)
    (fun t _ => ⟨fun h1 a ha => h.iso hA ha h1,
      fun h1 => (hA t).2 fun a ha => h.swap_eq_one (h1 a ha)⟩) hidx
  refine ⟨S ⊔ T, fun y => ⟨fun hy z hz => ?_, fun hy => ?_⟩,
    ⟨x, Submodule.mem_sup_right hxT, P, hPm, hPf, hP, ?_⟩, ?_⟩
  · obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨b, hb, u, hu, rfl⟩ := Submodule.mem_sup.1 hz
    rw [h.add_left, h.add_right, h.add_right, h.iso hA ha.1 hb.1, ha.2 u hu,
      h.swap_eq_one (hb.2 t ht), h.iso hB (hTB ht) (hTB hu)]
    simp
  · obtain ⟨t, ht, hyt⟩ := hdual y fun a _ ha =>
      h.swap_eq_one (hy a (Submodule.mem_sup_left ha))
    have ht' : t ∈ T := ht
    have h1 : y + -t ∈ S := by
      refine ⟨(hA _).2 fun a ha => h.swap_eq_one ?_, fun u hu => ?_⟩
      · rw [h.add_right, h.neg_right, hyt a ha, mul_inv_cancel₀ (h.ne_zero _ _)]
      · rw [h.add_left, hy u (Submodule.mem_sup_right hu),
          h.iso hB (B.neg_mem (hTB ht')) (hTB hu), one_mul]
    exact Submodule.mem_sup.2 ⟨_, h1, t, ht', by abel⟩
  · exact sup_le_sup_right (le_inf hSA le_sup_left) _
  · exact sup_le_sup (le_inf le_sup_left hSA) (le_inf le_sup_right hTB)

end GlobalTheory.FinWeil
