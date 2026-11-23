import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveProdQuotientOfMemAnnihilatorKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian

open IsLocalRing TensorProduct

namespace GlobalTheory.StrictHenselSplit

theorem isFiniteSplit_of_finrank_eq (A : Type) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] : ∀ (r : ℕ) (B : Type) [CommRing B] [Algebra A B]
    [Algebra.Etale A B] [Module.Finite A B], Module.finrank A B = r → Algebra.IsFiniteSplit A B := by
  intro r
  induction r with
  | zero =>
    intro B _ _ _ _ hr
    haveI : Module.Free A B := Module.free_of_flat_of_isLocalRing
    haveI : Subsingleton B := (Module.finrank_eq_zero_iff_of_free A B).1 hr
    exact .of_subsingleton_top
  | succ r ih =>
    intro B _ _ _ _ hr
    haveI : Module.Free A B := Module.free_of_flat_of_isLocalRing
    obtain ⟨m, ⟨f⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun (ResidueField A)
      (ResidueField A ⊗[A] B)
    have hm : m = r + 1 := by
      have h1 := Module.finrank_baseChange (R := ResidueField A) (S := A) (M' := B)
      rw [f.toLinearEquiv.finrank_eq, Module.finrank_fin_fun] at h1
      omega
    let φ₀ : B →ₐ[A] ResidueField A :=
      (((Pi.evalAlgHom (ResidueField A) (fun _ : Fin m => ResidueField A) ⟨0, by omega⟩).comp
        f.toAlgHom).restrictScalars A).comp Algebra.TensorProduct.includeRight
    obtain ⟨ε, -⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp A B A).2 φ₀
    obtain ⟨e, ⟨he, he1⟩, -⟩ := GlobalTheory.existsUnique_mem_annihilator_ker ε
    let g : B ≃ₐ[A] A × (B ⧸ Ideal.span {e}) :=
      AlgEquiv.ofBijective _ (GlobalTheory.bijective_prod_quotient_of_mem_annihilator_ker he he1)
    haveI : Algebra.Etale A (A × (B ⧸ Ideal.span {e})) := .of_equiv g
    haveI : Algebra.Etale A (B ⧸ Ideal.span {e}) := by
      algebraize [RingHom.snd A (B ⧸ Ideal.span {e})]
      have : IsScalarTower A (A × (B ⧸ Ideal.span {e})) (B ⧸ Ideal.span {e}) :=
        IsScalarTower.of_algebraMap_eq' rfl
      exact .comp A (A × (B ⧸ Ideal.span {e})) (B ⧸ Ideal.span {e})
    haveI : Module.Finite A (B ⧸ Ideal.span {e}) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (Ideal.span {e})).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI : Module.Free A (B ⧸ Ideal.span {e}) := Module.free_of_flat_of_isLocalRing
    have hC : Module.finrank A (B ⧸ Ideal.span {e}) = r := by
      have := g.toLinearEquiv.finrank_eq
      rw [Module.finrank_prod, Module.finrank_self] at this
      omega
    obtain ⟨k, ⟨h⟩⟩ := (ih (B ⧸ Ideal.span {e}) hC).nonempty_algEquiv_fun
    have : Algebra.IsFiniteSplit A (Fin 1 ⊕ Fin k → A) := inferInstance
    exact .of_algEquiv ((AlgEquiv.sumArrowEquivProdArrow (Fin 1) (Fin k) A A).trans
      ((AlgEquiv.prodCongr (AlgEquiv.funUnique (ι := Fin 1) A A) h.symm).trans g.symm))

end GlobalTheory.StrictHenselSplit

theorem GlobalTheory.etale_finite_strictHenselian_split : ∀ (A B : Type) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [Module.Finite A B], ∃ n : ℕ, Nonempty (B ≃ₐ[A] (Fin n → A)) := by
  intro A B _ _ _ _ _ _ _
  exact (GlobalTheory.StrictHenselSplit.isFiniteSplit_of_finrank_eq A _ B rfl).nonempty_algEquiv_fun

example : ∀ (A B : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B], ∃ n : ℕ, Nonempty (B ≃ₐ[A] (Fin n → A)) := GlobalTheory.etale_finite_strictHenselian_split
