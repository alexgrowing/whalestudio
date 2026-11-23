import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetFinerParabolicOfCharacterSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfBlocksLeOne

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_nontrivial_of_character_support :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL k)), HasSupport π s → (∀ y ∈ s, y.1 = 1) → Nontrivial (Jacquet π (unipB k (Fin N))) := by
  intro hG hZ k _ _ _ _ N V _ _ π s hs h1
  have hV : Nontrivial V := by
    obtain ⟨h, x, hx, hirr, hcu, e0, hsub⟩ := hs
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    obtain ⟨a, b, hab⟩ := (hirr.toNontrivial).exists_pair_ne
    apply hab
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    have : a1 = b1 := Subsingleton.elim _ _
    subst this
    rfl
  let S : ∀ {r : ℕ} {d : Fin r → ℕ}, ((a : Fin r) × Fin (d a) ≃ Fin N) → Finset (Fin N × Fin N) :=
    fun e => Finset.univ.filter (fun pq : Fin N × Fin N => ¬ blk e pq.1 < blk e pq.2)
  have key : ∀ m : ℕ, ∀ (r : ℕ) (d : Fin r → ℕ) (e : (a : Fin r) × Fin (d a) ≃ Fin N),
      (S e).card ≤ m → Nontrivial (Jacquet π (unipRad k e)) →
      Nontrivial (Jacquet π (unipB k (Fin N))) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro r d e hm hJ
      by_cases hd : ∀ a, d a ≤ 1
      · exact UpperTheory.jacquet_borel_nontrivial_of_blocks_le_one k N V π r d e hd hJ
      push_neg at hd
      obtain ⟨j, hj⟩ := hd
      obtain ⟨t, c, f, hf, hmono, p, q, hpq, hnpq⟩ :=
        UpperTheory.jacquet_finer_parabolic_of_character_support hG hZ k N V π s hs h1 r d e j (by omega) hJ
      have hlt : (S f).card < (S e).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨(p, q), ?_, ?_⟩
          · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hnpq
          · simp [S, hpq]
        · intro x hx
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact fun h => hx (hmono _ _ h)
      exact ih _ (lt_of_lt_of_le hlt hm) t c f le_rfl hf
  let e1 : (a : Fin 1) × Fin ((fun _ : Fin 1 => N) a) ≃ Fin N :=
    { toFun := fun p => p.2
      invFun := fun i => ⟨0, i⟩
      left_inv := by
        rintro ⟨a, i⟩
        fin_cases a
        rfl
      right_inv := fun i => rfl }
  have hU : ∀ g ∈ unipRad k e1, g = 1 := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
    have h0 := congrFun (MonoidHom.mem_ker.mp hp) 0
    ext i j
    have h2 := congrArg (fun u : GL (Fin N) k => (u : Matrix (Fin N) (Fin N) k) i j) h0
    simpa [leviProj, diagBlock, MonoidHom.pi, e1] using h2
  have hker : twKer π (unipRad k e1) 1 = ⊥ := by
    rw [twKer, Submodule.span_eq_bot]
    rintro w ⟨n, v, rfl⟩
    rw [hU n.1 n.2]
    simp
  apply key _ 1 (fun _ => N) e1 le_rfl
  show Nontrivial (V ⧸ twKer π (unipRad k e1) 1)
  rw [hker, Submodule.Quotient.nontrivial_iff]
  exact bot_ne_top
