import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormGamma1PrimePowInvariant

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.NormDelta

def conjM (γ : SL(2, ℤ)) (l : ℕ) (j k B : ℤ) (hB : (l : ℤ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) : SL(2, ℤ) :=
  ⟨!![γ 0 0 + j * γ 1 0, B; l * γ 1 0, γ 1 1 - k * γ 1 0], by
    have hd := γ.2
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 at hd
    linear_combination hd - γ 1 0 * hB⟩

open scoped MatrixGroups in
private lemma toGQ_mul_ofSL_eq_ofSL_mul_toGQ (γ γ' : SL(2, ℤ)) (l : ℕ) (hl : 0 < l) (j k B : ℤ)
    (hB : (l : ℤ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0))
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 0 0 + j * γ 1 0, B; l * γ 1 0, γ 1 1 - k * γ 1 0]) :
    _root_.GlobalTheory.KZ.toGQ !![1, j; 0, (l : ℤ)] * _root_.GlobalTheory.KZ.ofSL γ =
      _root_.GlobalTheory.KZ.ofSL γ' * _root_.GlobalTheory.KZ.toGQ !![1, k; 0, (l : ℤ)] := by
  have hdet : ∀ m : ℤ, 0 < (!![1, m; 0, (l : ℤ)]).det := by
    intro m
    simp only [Matrix.det_fin_two_of, one_mul, mul_zero, sub_zero]
    exact_mod_cast hl
  unfold _root_.GlobalTheory.KZ.toGQ _root_.GlobalTheory.KZ.ofSL
  rw [dif_pos (hdet j), dif_pos (hdet k)]
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i i'
  have h00 := congrFun (congrFun hγ' 0) 0
  have h01 := congrFun (congrFun hγ' 0) 1
  have h10 := congrFun (congrFun hγ' 1) 0
  have h11 := congrFun (congrFun hγ' 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at h00 h01 h10 h11
  have hBq : ((l : ℚ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) := by exact_mod_cast hB
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.toGLPos,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, h00, h01, h10, h11] <;>
    first | ring1 | linear_combination -hBq

open scoped MatrixGroups in

theorem _root_.GlobalTheory.NormDelta.norm_delta (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : _root_.GlobalTheory.KZ.Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ)
    (hn : 0 < n) (hlN : ¬ l ∣ N) (f : X.K) (hf : _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f)
    (hδ : ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (_root_.GlobalTheory.KZ.ofSL δ) f = g ^ (l ^ n)) :
    ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧
        (∏ j ∈ Finset.range l, X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) *
          X.sl (_root_.GlobalTheory.KZ.ofSL δ) (∏ j ∈ Finset.range l, X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) = g ^ (l ^ n) := by
  intro δ hδN hδl
  obtain ⟨g, hg, hfg⟩ := hδ δ hδN hδl
  have hlp : l.Prime := Fact.out
  have hl0 : 0 < l := hlp.pos
  refine ⟨∏ j ∈ Finset.range l,
      X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g,
    _root_.GlobalTheory.normInv_gamma1 Ω ε X N l n hn g hg, ?_⟩
  rw [CongruenceSubgroup.Gamma1_mem] at hδN
  obtain ⟨-, -, hcN⟩ := hδN
  rw [CongruenceSubgroup.Gamma_mem] at hδl
  obtain ⟨ha', hb', hc', hd'⟩ := hδl
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at ha' hb' hc' hd'
  have hlpow : ∀ x : ℤ, ((x : ZMod (l ^ n)) = 0) → (l : ℤ) ∣ x := fun x hx =>
    (dvd_pow_self (l : ℤ) hn.ne').trans (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd x (l ^ n)).1 hx)
  obtain ⟨xa, hxa⟩ := hlpow (δ 0 0 + 1) (by push_cast; linear_combination -ha')
  obtain ⟨xd, hxd⟩ := hlpow (δ 1 1 + 1) (by push_cast; linear_combination -hd')
  obtain ⟨xb, hxb⟩ := hlpow (δ 0 1) (by linear_combination -hb')
  obtain ⟨xc, hxc⟩ := hlpow (δ 1 0) (by linear_combination -hc')
  have hcop : IsCoprime (N : ℤ) ((l : ℤ) ^ n) := by
    have := Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hlp).2 hlN).symm
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  have hcM : ((δ 1 0 : ℤ) : ZMod (N * l ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    refine hcop.mul_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hcN) ?_
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 1 0) (l ^ n)).1 (by linear_combination -hc')
    exact_mod_cast this
  have hdetM : ((δ 0 0 : ℤ) : ZMod (N * l ^ n)) * (δ 1 1 : ℤ) = 1 := by
    have hdet := δ.2
    rw [Matrix.det_fin_two] at hdet
    have := congrArg (Int.cast : ℤ → ZMod (N * l ^ n)) hdet
    push_cast at this
    rw [hcM] at this
    simpa using this
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hB : (l : ℤ) * (xb + j * xd - j * xa - j * j * xc) =
      δ 0 1 + j * δ 1 1 - j * (δ 0 0 + j * δ 1 0) := by
    linear_combination -hxb - j * hxd + j * hxa + j * j * hxc
  have hη : _root_.GlobalTheory.NormDelta.conjM δ l j j _ hB * δ⁻¹ ∈ CongruenceSubgroup.Gamma1 (N * l ^ n) := by
    rw [CongruenceSubgroup.Gamma1_mem, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [_root_.GlobalTheory.NormDelta.conjM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons]
    push_cast
    rw [hcM]
    refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | linear_combination hdetM
  have hsplit : _root_.GlobalTheory.KZ.ofSL (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB) =
      _root_.GlobalTheory.KZ.ofSL (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB * δ⁻¹) *
        _root_.GlobalTheory.KZ.ofSL δ := by
    rw [← map_mul, inv_mul_cancel_right]
  have hact : X.sl (_root_.GlobalTheory.KZ.ofSL δ)
      (X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) =
      X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)])
        (X.sl (_root_.GlobalTheory.KZ.ofSL δ) f) := by
    rw [← _root_.GlobalTheory.KZ.Tower.sl_mul,
      toGQ_mul_ofSL_eq_ofSL_mul_toGQ δ (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB) l hl0 j j _ hB rfl,
      _root_.GlobalTheory.KZ.Tower.sl_mul, hsplit,
      _root_.GlobalTheory.KZ.Tower.sl_mul, hf _ hη]
  rw [hact, ← map_mul, hfg, map_pow]

end GlobalTheory.NormDelta
