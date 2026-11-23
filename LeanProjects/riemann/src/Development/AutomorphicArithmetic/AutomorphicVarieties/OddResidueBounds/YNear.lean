import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Expand
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primden
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.TwistedBernoulliValueCongrPowMulFirst
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.GroupRingIntAtDivSmulOfPadicValNatLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.yNear :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a r : ℕ) (ha : a.Coprime N), Odd a → l ^ (r + ck l (e + 1) + 1) ∣ N → IntAt l r (yEl (e + 1) a ha φ - coefMap ℚ Γ (ytEl e a φ)) := by
  intro l _ Γ _ _ N _ φ e a r ha hodd hdvd
  have hy := (Stk.twistedStickelbergerElements_agree N a ha Γ φ (e + 1)).1
  have hyt := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.1
  have hcf := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.2.2
  choose z hz using Stk.twistedBernoulliValue_congr_pow_mul_first N a e ha hodd
  rw [hy, hyt, hcf]
  have key : Stk.yForm (e + 1) a φ - Stk.cf ℚ Γ (Stk.ytEl e a φ)
      = ((N : ℚ) / (Stk.dk (e + 1) : ℚ)) • Stk.cf ℚ Γ (Stk.sumEl φ (fun b => -z b)) := by
    rw [Stk.cf_sumEl]
    unfold Stk.yForm Stk.ytEl
    rw [map_neg, Stk.cf_sumEl]
    unfold Stk.sumEl
    rw [neg_sub_neg, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hz _, MonoidAlgebra.smul_single]
    first
      | rw [← MonoidAlgebra.single_sub]
      | erw [← Finsupp.single_sub]
    congr 1
    simp only [smul_eq_mul]
    push_cast
    ring
  rw [key]
  have hN0 : N ≠ 0 := NeZero.ne N
  have hv := (padicValNat_dvd_iff_le hN0).mp hdvd
  apply Stk.groupRing_intAt_div_smul_of_padicValNat_le l N (Stk.dk (e + 1)) r (Nat.pos_of_ne_zero hN0) (Stk.dk_pos (Nat.succ_pos e))
  have hck : ck l (e + 1) = padicValNat l (Stk.dk (e + 1)) := rfl
  omega
