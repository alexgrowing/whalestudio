import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem addChar_pow_natCard_eq_one {A L : Type} [AddGroup A] [CommMonoid L] (ψ : AddChar A L) (c : A) :
    ψ c ^ Nat.card A = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]

theorem mem_Ks_of_pow_g (B : Base) (k : Fin 2) {x : B.LL} (hx : x ^ B.host.g k = 1) : x ∈ B.Ks := by
  have hp := B.host.g_prime k
  obtain ⟨z, hzK, hz⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
  have hne : B.host.g k * (B.host.g k - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (B.host.g k * (B.host.g k - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g k * (B.host.g k - 1)) := ⟨hne⟩
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one (ξ := x) (by rw [pow_mul, hx, one_pow])
  rw [← hj]
  exact pow_mem hzK j

theorem chr0_mem_Ks : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (p : lev0 I),
    ((chr0 I p : B.LLˣ) : B.LL) ∈ B.Ks := by
  classical
  intro B px I p
  have hPr := (GlobalTheory.Mem.Col2.base_fields_primes_ok B px).2.1
  unfold chr0 P0 LevelP.ofLocal
  erw [MonoidHom.finset_prod_apply, Units.coe_prod]
  refine B.Ks.prod_mem fun PP _ => ?_
  have hk : ∃ k, PP.1 ∈ (B.primes px).vG k := by
    have h : PP.1 ∈ (B.primes px).vG 0 ∪ (B.primes px).vG 1 := by
      have h0 := PP.2
      unfold Formalism.L2.Col.Primes.vGs at h0
      convert h0
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hw⟩ := hk
  refine mem_Ks_of_pow_g B k ?_
  have hc : Nat.card (kP PP.1) = B.host.g k := by
    have h := hPr.vG_norm k PP.1 hw
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
    exact h
  rw [← hc]
  exact addChar_pow_natCard_eq_one _ _

end GlobalTheory.Mem.R3
