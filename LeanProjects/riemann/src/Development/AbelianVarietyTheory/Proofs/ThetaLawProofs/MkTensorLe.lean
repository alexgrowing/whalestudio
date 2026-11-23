import Mathlib

namespace GlobalTheory.EmbC

open Cardinal TensorProduct

theorem mk_tensor_le (R A B : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (hA : #A ≤ 𝔠) (hB : #B ≤ 𝔠) : #(A ⊗[R] B) ≤ 𝔠 := by
  have h1 : Function.Surjective (fun l : List (A × B) => (l.map (fun p => p.1 ⊗ₜ[R] p.2)).sum) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨[], by simp⟩
    | tmul a b => exact ⟨[(a, b)], by simp⟩
    | add x y hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨m, rfl⟩ := hy
      exact ⟨l ++ m, by simp⟩
  refine (Cardinal.mk_le_of_surjective h1).trans ((Cardinal.mk_list_le_max _).trans ?_)
  refine max_le Cardinal.aleph0_le_continuum ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc #A * #B ≤ 𝔠 * 𝔠 := mul_le_mul' hA hB
    _ = 𝔠 := Cardinal.continuum_mul_self

theorem exists_emb (R A B : Type) [CommRing R] [IsDomain R] [Field A] [Field B] [CharZero A]
    [Algebra R A] [Algebra R B] (hA : #A = 𝔠) (hB : #B = 𝔠)
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B)) :
    ∃ (σ : A →+* ℂ) (σ' : B →+* ℂ), σ.comp (algebraMap R A) = σ'.comp (algebraMap R B) := by
  haveI : Nontrivial (A ⊗[R] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R A B ha hb
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⊗[R] B)
  letI : Field ((A ⊗[R] B) ⧸ m) := Ideal.Quotient.field m
  let L := (A ⊗[R] B) ⧸ m
  let Ω := AlgebraicClosure L
  let p : (A ⊗[R] B) →+* Ω := (algebraMap L Ω).comp (Ideal.Quotient.mk m)
  let i : A →+* Ω := p.comp (Algebra.TensorProduct.includeLeftRingHom)
  let j : B →+* Ω := p.comp (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
  haveI : CharZero Ω := charZero_of_injective_ringHom i.injective
  have hL : #L ≤ 𝔠 :=
    (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (mk_tensor_le R A B hA.le hB.le)
  have hΩ : #Ω = 𝔠 := by
    apply le_antisymm
    · exact (Algebra.IsAlgebraic.cardinalMk_le_max L Ω).trans (max_le hL Cardinal.aleph0_le_continuum)
    · rw [← hA]; exact Cardinal.mk_le_of_injective i.injective
  obtain ⟨e⟩ : Nonempty (Ω ≃+* ℂ) :=
    IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [hΩ]; exact Cardinal.aleph0_lt_continuum)
      (Cardinal.eq.mp (by rw [hΩ, Cardinal.mk_complex]))
  refine ⟨e.toRingHom.comp i, e.toRingHom.comp j, ?_⟩
  ext r
  have : (algebraMap R A r) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B r) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show e (p ((algebraMap R A r) ⊗ₜ[R] (1 : B))) = e (p ((1 : A) ⊗ₜ[R] (algebraMap R B r)))
  rw [this]

theorem exists_comp_eq (R : Type) [CommRing R] [IsDomain R] (f f' : R →+* ℂ)
    (hf : Function.Injective f) (hf' : Function.Injective f') :
    ∃ σ σ' : ℂ →+* ℂ, σ.comp f = σ'.comp f' :=
  @exists_emb R ℂ ℂ _ _ _ _ _ f.toAlgebra f'.toAlgebra Cardinal.mk_complex Cardinal.mk_complex hf hf'

end GlobalTheory.EmbC
