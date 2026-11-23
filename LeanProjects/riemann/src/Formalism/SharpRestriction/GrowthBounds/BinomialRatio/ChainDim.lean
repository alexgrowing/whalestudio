import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem card_tuples (r g : ℕ) (hr : 0 < r) : Nat.card {P : Fin r → ℕ // ∑ i, P i = g} = sdXi r g := by
  classical
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin r) g), Nat.card_eq_fintype_card, Sym.card_sym_eq_choose,
    Fintype.card_fin]
  unfold sdXi
  rw [show r + g - 1 = g + r - 1 by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

def monoEquiv (N r : ℕ) (d : Fin N → ℕ) :
    ↥({m | ∀ i, multideg m i = d i} : Set (Fin N × Fin r →₀ ℕ)) ≃ (∀ i, {P : Fin r → ℕ // ∑ c, P c = d i}) where
  toFun m := fun i => ⟨fun c => m.1 (i, c), m.2 i⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun x => (f x.1).1 x.2), fun i => by
    show ∑ c, (Finsupp.equivFunOnFinite.symm (fun x : Fin N × Fin r => (f x.1).1 x.2)) (i, c) = d i
    simpa using (f i).2⟩
  left_inv m := by
    apply Subtype.ext
    ext x
    simp
  right_inv f := by
    funext i
    apply Subtype.ext
    funext c
    simp

theorem finrank_Pol (K : Type*) [Field K] (N r : ℕ) (hr : 0 < r) (d : Fin N → ℕ) :
    Module.finrank K (Pol K r d) = ∏ i, sdXi r (d i) := by
  classical
  unfold Pol
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _), Nat.card_congr (monoEquiv N r d),
    Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => card_tuples r (d i) hr

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def dvr5 : UniformizedDVR 5 ℤ_[5] where
  w := (5 : ℕ)
  w_irr := PadicInt.irreducible_p
  p_mem := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  p_ne := by exact_mod_cast (by norm_num : (5 : ℕ) ≠ 0)
  complete := inferInstance

theorem chainDim_of (hY : DimYAt) : ChainDimAt := by
  intro N r _ LL
  have h := hY 5 ℤ_[5] dvr5 N r LL 0 Fin.elim0 Fin.elim0 (fun k => k.elim0)
  rw [← h]
  unfold Yjt chPol
  rw [iInf_of_empty, inf_top_eq, finrank_Pol _ N r (NeZero.pos r) LL.deg, Nat.cast_prod]

end Formalism.MainNotions.ColumnSystems.Pf
