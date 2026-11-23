import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys

open Classical in

theorem aeval_gen_sub_one_surjective (O : Type) [CommRing O] (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] :
    Function.Surjective (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) := by
  set φ := (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) with hφ
  have hg : ∀ g : Multiplicative (ι → ZMod n), MonoidAlgebra.of O _ g ∈ φ.range := by
    intro g
    refine ⟨∏ q, (MvPolynomial.X q + 1) ^ (Multiplicative.toAdd g q).val, ?_⟩
    have h1 : g = ∏ q, (Multiplicative.ofAdd (Pi.single q (1 : ZMod n) : ι → ZMod n)) ^ (Multiplicative.toAdd g q).val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      funext j
      simp only [toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_one, ZMod.natCast_zmod_val]
    conv_rhs => rw [h1]
    simp only [hφ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow, map_add, map_one,
      MvPolynomial.aeval_X, sub_add_cancel]
  intro x
  change x ∈ φ.range
  induction x using MonoidAlgebra.induction_on with
  | of g => exact hg g
  | add f g hf hg => exact add_mem hf hg
  | smul r f hf => exact Subalgebra.smul_mem _ hf r

theorem toLam_surjective {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : Function.Surjective (toLam X i M ι) := by
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  exact aeval_gen_sub_one_surjective (X.O0 i) (X.l i ^ M) ι

theorem SlopeTestRemainingChoices.empty {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    {i : X.Tw} {M : ℕ} {A : Finset (PlE D.host)} {ι : Type} {P : ι → PlE D.host} {d}
    (h : SlopeTestRemainingChoices X i M A P d) : SlopeTestRemainingChoices X i M ∅ P d := by
  refine ⟨fun q v hv => ?_, h.2⟩
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h.1 q v hv
  exact ⟨h1, h2, h3, h4, Finset.notMem_empty _, h6⟩

theorem galois_twisted_selmer_auxprimes_of_matrix_and_bounds : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂)
    (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X),
    ThmS bkP → SelmerLengthsByDeterminant bkP → ResidualBoundOddPrimes bkP → ThmC bkP → GaloisSideTwistedSelmerAuxiliaryPrimes bkP := by
  intro D N X bkP hS hS4 h103 hC i T hT
  have hO : OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)) := by
    rcases Nat.eq_zero_or_pos (nu X i) with h | h
    · rw [h, pow_zero, IsDiscreteValuationRing.addVal_one]
      exact h103 i h
    · exact hC i h
  obtain ⟨R, Dd, M₀, hM₀⟩ := hO T hT
  refine ⟨R, Dd, max M₀ 1, le_max_right _ _, fun M hM H S d hF z hz H' ho hn A => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨P, hA, hSt, hP⟩ := hM₀ M (le_trans (le_max_left _ _) hM) H S d hF z hz H' ho hn A
  refine ⟨P, hA, hSt, fun s hs Q hQ => ?_⟩
  obtain ⟨a, Φ, hΦ, -⟩ := hS i s (hT s hs) M _ P _ Q hM1 hA.empty hQ
  obtain ⟨F, hFΦ⟩ := toLam_surjective X i M (Fin R ⊕ Fin R) Φ.det
  exact ⟨F, hS4 i s M _ P _ Q hM1 hA.empty hQ a Φ hΦ F hFΦ, hP s hs Q hQ a Φ hΦ F hFΦ⟩

end GlobalTheory.TwSys
