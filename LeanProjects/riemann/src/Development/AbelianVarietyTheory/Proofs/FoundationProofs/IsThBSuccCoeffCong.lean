import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatio
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongr
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThBCompat

private theorem cast_eq_of_dvd {N M : ℕ} (h : N ∣ M) (x y : ℤ) (hxy : (x : ZMod M) = (y : ZMod M)) :
    (x : ZMod N) = (y : ZMod N) := by
  have := congrArg (ZMod.castHom h (ZMod N)) hxy
  simpa only [map_intCast] using this

private theorem gamma_le {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h1)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h2)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h3)
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h4)

private theorem gamma1_le {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma1 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h1)
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h2)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h3)

theorem isThB_succ_coeff_cong : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n : ℕ) (b : X.Fn l) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l (n + 1) b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l hl l2 hN hN1 hlA n b φ φ' h1 h2
  obtain ⟨f, hfI, hfc, hfδ, hfD⟩ := h1
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h2
  have hfc' : AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f := by
    have h := AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) (b ![1, 0])
    change (b ![1, 0]).val n = _
    rw [← h]
    change AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n)
      (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) (b ![1, 0])) = _
    rw [hfc]
    rfl
  obtain ⟨u, hu⟩ := GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc'.symm.trans hf'c)
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hu0 : (u : X.K) ≠ 0 := u.ne_zero
  have hle : CongruenceSubgroup.Gamma1 (N * l ^ (n + 1)) ≤ CongruenceSubgroup.Gamma1 (N * l ^ n) :=
    gamma1_le (Nat.mul_dvd_mul_left N (pow_dvd_pow l (Nat.le_succ n)))
  have hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f' := by rw [hu]; field_simp
  have hT := GlobalTheory.TInv.sl_T_eq X N l (n + 1) hl.out l2 hN hN1 (u : X.K) hu0 (by
      intro γ hγ
      rw [pow_succ, pow_mul, hL, map_pow, map_mul, map_inv₀, hfI γ hγ, hf'I γ (hle hγ)]) (by
      intro δ hδ hδ'
      obtain ⟨g, hgI, hg⟩ := hfδ δ hδ hδ'
      obtain ⟨g', hg'I, hg'⟩ := hf'δ δ hδ (gamma_le (pow_dvd_pow l (Nat.le_succ n)) hδ')
      have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := by
        intro h0; exact hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hg; exact mul_ne_zero hf0 hsf hg
      refine ⟨g' / g ^ l, ?_, ?_⟩
      · intro γ hγ; rw [map_div₀, map_pow, hgI γ hγ, hg'I γ (hle hγ)]
      · have key : ((u : X.K) * X.sl (ofSL δ) u) ^ (l ^ n) = (g' / g ^ l) ^ (l ^ n) := by
          rw [div_pow, ← pow_mul, ← pow_succ', ← hg', ← hg, hu, map_mul, map_pow]; field_simp; ring
        rw [pow_succ, pow_mul, pow_mul, key])
  have hfD' : IsDl X A l n 1 (f : X.K) φ := by
    obtain ⟨hA, a, c, κ, hκ, hac, ha, hc, hcg⟩ := hfD
    refine ⟨hA, a, c, κ, hκ, hac, ha, hc, fun r => ?_⟩
    obtain ⟨z, hz, e⟩ := hcg r
    exact ⟨l * z, A.mul_mem _ _ (natCast_mem A l) hz, by rw [e, pow_succ, mul_assoc]⟩
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, GlobalTheory.Glue.DlPow.isAlgebraic_of_tower X⟩
  exact GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD' (by rw [← hu]; exact hf'D)

end GlobalTheory.ThBCompat
