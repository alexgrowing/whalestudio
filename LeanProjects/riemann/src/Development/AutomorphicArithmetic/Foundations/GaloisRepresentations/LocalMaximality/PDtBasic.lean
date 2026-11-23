import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private theorem dt_eq (b : Module.Basis (Fin d) K Ω[K⁄ℂ]) (hb : ∀ j, b j = D ℂ K (tt K x j)) (S : Finset (Fin d)) :
    dtS K x S = b.ExteriorAlgebra S := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (rfl : S.card = S.card)]
  simp only [dtS, ExteriorAlgebra.ιMulti_family]
  congr 1
  ext a
  simp [hb, Set.powersetCard.ofFinEmbEquiv_symm_apply]

private theorem dt_univ : dtS K x Finset.univ = ExteriorAlgebra.ιMulti K d fun j => D ℂ K (tt K x j) := by
  have h : (Finset.univ : Finset (Fin d)).card = d := by simp
  have key : ∀ (n : ℕ) (hn : (Finset.univ : Finset (Fin d)).card = n) , n = d →
      (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (tt K x ((Finset.univ : Finset (Fin d)).orderEmbOfFin hn a))) =
      ExteriorAlgebra.ιMulti K d fun j => D ℂ K (tt K x j) := by
    intro n hn e
    subst e
    congr 1
    ext a
    have : (Finset.univ : Finset (Fin n)).orderEmbOfFin hn a = a := by
      have := Finset.orderEmbOfFin_unique' (s := (Finset.univ : Finset (Fin n))) hn (f := (OrderIso.refl (Fin n)).toOrderEmbedding) (by simp)
      rw [← this]; rfl
    rw [this]
  exact key _ rfl h

end

theorem UpperTheory.Gal.productCup_of_system.dtBasic_of :
    DtBasic := by
  intro F K _ _ _ _ _ _ d x hc τ hτ
  obtain ⟨b0, hb0⟩ := hc.exists_basis
  have hb : ∀ j, b0 j = D ℂ K (tt K x j) := hb0
  have hfun : dtS K x = b0.ExteriorAlgebra := funext (dt_eq x b0 hb)
  have hprod : algebraMap F K (omG x 0) = ∏ l, tt K x l := by
    unfold omG
    rw [Fin.prod_univ_succ, div_self (x 0).ne_zero, one_mul, map_prod]
    rfl
  refine ⟨?_, ?_, ?_, hprod, ?_⟩
  · rw [hfun]
    exact b0.ExteriorAlgebra.linearIndependent
  · intro S
    refine Submodule.subset_span ⟨1, one_mem _, fun a => tt K x (S.orderEmbOfFin rfl a),
      fun j => tco_mem ℂ K (xv x) _, ?_⟩
    rw [one_smul]
    rfl
  · have hne : ∀ j, tt K x j ≠ 0 := fun j =>
      (map_ne_zero _).2 (div_ne_zero (x j.succ).ne_zero (x 0).ne_zero)
    have hv : vol0 ℂ K (xv x) = (∏ j, (tt K x j)⁻¹) • ExteriorAlgebra.ιMulti K d fun j => D ℂ K (tt K x j) := by
      rw [← AlternatingMap.map_smul_univ]
      rfl
    rw [dt_univ, hprod, hv, smul_smul, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun j _ => mul_inv_cancel₀ (hne j), Finset.prod_const_one, one_smul]
  · have hd : ∀ S : Finset (Fin d), Disjoint (Sᶜ) S := fun S => disjoint_compl_left
    refine ⟨fun S => (Set.powersetCard.permOfDisjoint
      (s := (⟨Sᶜ, rfl⟩ : Set.powersetCard (Fin d) Sᶜ.card))
      (t := (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card)) (hd S)).sign, fun U S hUS => ?_⟩
    rw [hfun]
    split_ifs with h
    · subst h
      have e := ExteriorAlgebra.basis_mul_of_disjoint b0
        (⟨Sᶜ, rfl⟩ : Set.powersetCard (Fin d) Sᶜ.card) (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card) (hd S)
      have hu : ((Set.powersetCard.disjUnion (s := (⟨Sᶜ, rfl⟩ : Set.powersetCard (Fin d) Sᶜ.card))
          (t := (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card)) (hd S) : Set.powersetCard (Fin d) (Sᶜ.card + S.card)) : Finset (Fin d)) = Finset.univ := by
        ext i
        simp [Set.powersetCard.disjUnion]
        tauto
      rw [hu] at e
      exact e
    · have hnd : ¬ Disjoint U S := by
        intro hUd
        apply h
        have hc2 : (U ∪ S).card = Fintype.card (Fin d) := by
          rw [Finset.card_union_of_disjoint hUd, hUS, Fintype.card_fin]
        have huniv : U ∪ S = Finset.univ := (Finset.card_eq_iff_eq_univ _).1 hc2
        ext i
        have := Finset.ext_iff.1 huniv i
        have h2 : i ∈ U → i ∉ S := fun a => Finset.disjoint_left.1 hUd a
        simp at this ⊢
        tauto
      exact ExteriorAlgebra.basis_mul_of_not_disjoint b0
        (⟨U, rfl⟩ : Set.powersetCard (Fin d) U.card) (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card) hnd
