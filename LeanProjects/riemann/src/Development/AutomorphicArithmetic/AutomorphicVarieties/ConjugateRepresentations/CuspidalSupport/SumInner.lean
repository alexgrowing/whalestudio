import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_three {A B C P R : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq P]
    (f : A → P) (f' : B → P) (f'' : C → P) (h : Function.Bijective (Sum.elim (Sum.elim f f') f''))
    (g : (A → R) → (B → R) → ℂ) :
    ∑ c : P → R, g (c ∘ f) (c ∘ f') = (Fintype.card R : ℂ) ^ Fintype.card C * ∑ c₁, ∑ c₂, g c₁ c₂ := by
  let e : (P → R) ≃ ((A → R) × (B → R)) × (C → R) :=
    ((Equiv.ofBijective _ h).symm.arrowCongr (Equiv.refl R)).trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        ((Equiv.sumArrowEquivProdArrow _ _ _).prodCongr (Equiv.refl _)))
  have h1 : ∑ c : P → R, g (c ∘ f) (c ∘ f') = ∑ x : ((A → R) × (B → R)) × (C → R), g x.1.1 x.1.2 :=
    Fintype.sum_equiv e _ _ (fun c => rfl)
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  push_cast
  rfl

private def pair3 {r s : ℕ} (S : Finset (Fin (r + s))) (p : sub1 S × ((sub2 S)ᶜ : Finset (Fin s))) : satakePairs S :=
  ⟨(Fin.castAdd s p.1.1, Fin.natAdd r p.2.1), (Finset.mem_filter.1 p.1.2).2, by simpa [sub2] using p.2.2, by
    have := p.1.1.2
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega⟩

private theorem bij3 {r s : ℕ} (S : Finset (Fin (r + s))) :
    Function.Bijective (Sum.elim (Sum.elim (pair1 S) (pair2 S)) (pair3 S)) := by
  constructor
  · rintro ((⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩) | ⟨⟨a, h⟩, ⟨b, h'⟩⟩) ((⟨⟨c, d⟩, k⟩ | ⟨⟨c, d⟩, k⟩) | ⟨⟨c, k⟩, ⟨d, k'⟩⟩) H <;>
      simp only [Sum.elim_inl, Sum.elim_inr, pair1, pair2, pair3, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castAdd, Fin.val_natAdd, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at H ⊢ <;>
      omega
  · rintro ⟨⟨a, b⟩, h1, h2, h3⟩
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        exact ⟨.inl (.inl ⟨(a, b), by simpa [sub1] using h1, by simpa [sub1] using h2, h3⟩), rfl⟩
      | right b =>
        exact ⟨.inr (⟨a, by simpa [sub1] using h1⟩, ⟨b, by simpa [sub2] using h2⟩), rfl⟩
    | right a =>
      induction b using Fin.addCases with
      | left b =>
        exfalso
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at h3
        omega
      | right b =>
        refine ⟨.inl (.inr ⟨(a, b), by simpa [sub2] using h1, by simpa [sub2] using h2, ?_⟩), rfl⟩
        simp only [Fin.lt_def, Fin.val_natAdd] at h3 ⊢
        omega

theorem UpperTheory.V.Cj.S.sumInner :
    UpperTheory.V.Cj.S.SumInner := by
  intro r s R _ S g
  rw [sum_three (pair1 S) (pair2 S) (pair3 S) (bij3 S) g]
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
