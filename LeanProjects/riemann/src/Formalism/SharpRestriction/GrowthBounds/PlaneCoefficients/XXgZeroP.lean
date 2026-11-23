import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TouchCOfMem

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]
  [NeZero r] (Dt : SignedChainData p O r J)

theorem twoPow_pos (j : ZMod J) (m : Fin r) : 0 < Dt.P j m := pow_pos (Nat.Prime.pos Fact.out) _

theorem XXg_zeroP (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) :
    XXg Dt d th thL 0 := by
  refine ⟨Submodule.zero_mem _, fun rho j i => ?_, fun j mm _ => ?_⟩
  · rw [Fdig_zero, valS_zero_eq_top]; exact geZ_top _
  · rw [valS_zero_eq_top]; exact geZ_top _

private theorem touchC_of_liftVar_mem_chainML (x0 : TL J Dt.nL r) (a : Fin r) (j : ZMod J) (i : Fin (Dt.nch j))
    (h : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i) : touchC Dt x0 j i := by
  obtain ⟨j', y⟩ := x0
  obtain ⟨z, hz, hzz⟩ := h
  rcases y with l | m <;> rcases z with l' | m'
  · simp only [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
    injection hzz with h1 h2
    subst h1
    cases h2
    exact Or.inl ⟨l', rfl, hz⟩
  · simp [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
  · simp [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
  · simp only [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
    injection hzz with h1 h2
    subst h1 h2
    exact Or.inr ⟨m', rfl⟩

theorem plDer' (x0 : TL J Dt.nL r) (a : Fin r) (d d' : TL J Dt.nL r → ℕ) (h0 : d' x0 = d x0 + 1)
    (h1 : ∀ i, i ≠ x0 → d' i = d i) (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ)
    (t1 : ∀ j i, th j i ≤ th' j i)
    (t2 : ∀ j i, touchC Dt x0 j i → Dt.trueLet.vec x0 = true → th j i + 1 ≤ th' j i)
    (t3 : ∀ j m, thL j m ≤ thL' j m)
    (t4 : ∀ j m, x0 ∈ Dt.TSet j m → Dt.trueLet.vec x0 = true → thL j m + 1 ≤ thL' j m)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (hH : XXg Dt d' th' thL' H) :
    XXg Dt d th thL (pderiv (x0, a) H) := by
  obtain ⟨hP, hC, hT⟩ := hH
  refine ⟨Pol_pderiv x0 a h0 h1 hP, fun rho j i => ?_, fun j m hm => ?_⟩
  · obtain ⟨c1, c2, c3, rho1, rho2, hc2, hF⟩ := Fdig_der_ex Dt (twoPow_pos Dt) (x0, a) rho
    rw [hF]
    have e1 : geZ (valS Dt.modelLet (Dt.chainML j i) (c1 • Dt.Fdig rho1 H)) (th j i) :=
      geZ_anti (t1 j i) (geZ_mono (valS_smul_ge _ _ _ _) (hC rho1 j i))
    have e2 : geZ (valS Dt.modelLet (Dt.chainML j i)
        (c2 • (X (Dt.liftVar (x0, a)) * pderiv (Dt.liftVar (x0, a)) (Dt.Fdig rho1 H)))) (th j i) := by
      by_cases hc : c2 = 0
      · rw [hc, zero_smul, valS_zero_eq_top]
        exact geZ_top _
      have hv : Dt.trueLet.vec x0 = true := hc2 hc
      refine geZ_mono (valS_smul_ge _ _ _ _) (geZ_mono (valS_X_mul_of _ _ _ _ ?_) ?_)
      · intro _
        rw [modelLet_vec]
        exact hv
      by_cases hs : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i
      · exact valuation_ge_of_le_add_one (valS_pderiv _ _ _ _) (hC rho1 j i) (t2 j i (touchC_of_liftVar_mem_chainML Dt x0 a j i hs) hv)
      · exact geZ_anti (t1 j i)
          (geZ_mono (valS_pderiv_of _ _ _ _ (fun h => absurd h hs)) (hC rho1 j i))
    have e3 : geZ (valS Dt.modelLet (Dt.chainML j i)
        (c3 • pderiv (Dt.liftVar (x0, a)) (Dt.Fdig rho2 H))) (th j i) := by
      refine geZ_mono (valS_smul_ge _ _ _ _) ?_
      by_cases hb : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i ∧ Dt.trueLet.vec x0 = true
      · exact valuation_ge_of_le_add_one (valS_pderiv _ _ _ _) (hC rho2 j i) (t2 j i (touchC_of_liftVar_mem_chainML Dt x0 a j i hb.1) hb.2)
      · refine geZ_anti (t1 j i) (geZ_mono (valS_pderiv_of _ _ _ _ ?_) (hC rho2 j i))
        intro hs
        rw [modelLet_vec]
        by_contra hc
        exact hb ⟨hs, by simpa using hc⟩
    exact geZ_mono (flt_valS_add _ _ _ _) (geZ_min (geZ_mono (flt_valS_add _ _ _ _) (geZ_min e1 e2)) e3)
  · by_cases hb : x0 ∈ Dt.TSet j m ∧ Dt.trueLet.vec x0 = true
    · exact valuation_ge_of_le_add_one (valS_pderiv _ _ H (x0, a)) (hT j m hm) (t4 j m hb.1 hb.2)
    · refine geZ_anti (t3 j m) (geZ_mono (valS_pderiv_of _ _ H (x0, a) ?_) (hT j m hm))
      intro hs
      by_contra hc
      exact hb ⟨hs, by simpa using hc⟩

theorem plMul' (x0 : TL J Dt.nL r) (a : Fin r) (d d' : TL J Dt.nL r → ℕ) (h0 : d x0 = d' x0 + 1)
    (h1 : ∀ i, i ≠ x0 → d' i = d i) (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ)
    (t1 : ∀ j i, th j i ≤ th' j i)
    (t2 : ∀ j i, touchC Dt x0 j i → Dt.trueLet.vec x0 = false → th j i + 1 ≤ th' j i)
    (t3 : ∀ j m, thL j m ≤ thL' j m)
    (t4 : ∀ j m, x0 ∈ Dt.TSet j m → Dt.trueLet.vec x0 = false → thL j m + 1 ≤ thL' j m)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (hH : XXg Dt d' th' thL' H) :
    XXg Dt d th thL (X (x0, a) * H) := by
  obtain ⟨hP, hC, hT⟩ := hH
  refine ⟨Pol_X_mul x0 a h0 h1 hP, fun rho j i => ?_, fun j m hm => ?_⟩
  · obtain ⟨c1, c2, rho1, rho2, hF⟩ := Fdig_mul_ex Dt (twoPow_pos Dt) (x0, a) rho
    rw [hF]
    have e1 : geZ (valS Dt.modelLet (Dt.chainML j i) (c1 • Dt.Fdig rho1 H)) (th j i) :=
      geZ_anti (t1 j i) (geZ_mono (valS_smul_ge _ _ _ _) (hC rho1 j i))
    have e2 : geZ (valS Dt.modelLet (Dt.chainML j i)
        (c2 • (X (Dt.liftVar (x0, a)) * Dt.Fdig rho2 H))) (th j i) := by
      refine geZ_mono (valS_smul_ge _ _ _ _) ?_
      by_cases hb : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i ∧ Dt.trueLet.vec x0 = false
      · exact valuation_ge_of_le_add_one (valS_X_mul _ _ _ _) (hC rho2 j i) (t2 j i (touchC_of_liftVar_mem_chainML Dt x0 a j i hb.1) hb.2)
      · refine geZ_anti (t1 j i) (geZ_mono (valS_X_mul_of _ _ _ _ ?_) (hC rho2 j i))
        intro hs
        rw [modelLet_vec]
        by_contra hc
        exact hb ⟨hs, by simpa using hc⟩
    exact geZ_mono (flt_valS_add _ _ _ _) (geZ_min e1 e2)
  · by_cases hb : x0 ∈ Dt.TSet j m ∧ Dt.trueLet.vec x0 = false
    · exact valuation_ge_of_le_add_one (valS_X_mul _ _ H (x0, a)) (hT j m hm) (t4 j m hb.1 hb.2)
    · refine geZ_anti (t3 j m) (geZ_mono (valS_X_mul_of _ _ H (x0, a) ?_) (hT j m hm))
      intro hs
      by_contra hc
      exact hb ⟨hs, by simpa using hc⟩

end Formalism.MainNotions.PairMembershipBlocks

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem plDer : PlDer := by
  intro p _ O _ _ _ r J _ _ Dt x0 a d th th' thL thL' hD H hH
  exact plDer' Dt x0 a d (Function.update d x0 (d x0 + 1)) (by simp)
    (fun i hi => by simp [Function.update_of_ne hi]) th th' thL thL' hD.1
    (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) H hH

theorem plMul : PlMul := by
  intro p _ O _ _ _ r J _ _ Dt x0 a d th th' thL thL' hD hd H hH
  exact plMul' Dt x0 a d (Function.update d x0 (d x0 - 1)) (by simp; omega)
    (fun i hi => by simp [Function.update_of_ne hi]) th th' thL thL' hD.1
    (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) H hH

theorem plEul : PlEul := by
  intro p _ O _ _ _ r J _ _ Dt x0 a d th th' thL thL' hD H hH
  rcases Nat.eq_zero_or_pos (d x0) with hz | hpos
  · have hvars : (x0, a) ∉ H.vars := by
      intro hv
      obtain ⟨m, hm, hma⟩ := (MvPolynomial.mem_vars _).1 hv
      have hdeg := (mem_Pol'.1 hH.1) m hm x0
      rw [hz] at hdeg
      have hle : m (x0, a) ≤ multideg m x0 :=
        Finset.single_le_sum (f := fun c => m (x0, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      rw [hdeg] at hle
      exact (Finsupp.mem_support_iff.1 hma) (by omega)
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hvars, mul_zero]
    exact XXg_zeroP Dt d th thL
  · have e0 : d x0 = Function.update d x0 (d x0 - 1) x0 + 1 := by simp; omega
    have e1 : ∀ i, i ≠ x0 → Function.update d x0 (d x0 - 1) i = d i :=
      fun i hi => by simp [Function.update_of_ne hi]
    have e1' : ∀ i, i ≠ x0 → d i = Function.update d x0 (d x0 - 1) i :=
      fun i hi => (e1 i hi).symm
    cases hv : Dt.trueLet.vec x0
    · have hD1 := plDer' Dt x0 a (Function.update d x0 (d x0 - 1)) d e0 e1' th' th' thL' thL'
        (fun _ _ => le_rfl) (fun _ _ _ hf => by simp [hv] at hf) (fun _ _ => le_rfl)
        (fun _ _ _ hf => by simp [hv] at hf) H hH
      exact plMul' Dt x0 a d (Function.update d x0 (d x0 - 1)) e0 e1 th th' thL thL' hD.1
        (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) _ hD1
    · have hD1 := plDer' Dt x0 a (Function.update d x0 (d x0 - 1)) d e0 e1' th th' thL thL' hD.1
        (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) H hH
      exact plMul' Dt x0 a d (Function.update d x0 (d x0 - 1)) e0 e1 th th thL thL
        (fun _ _ => le_rfl) (fun _ _ _ hf => by simp [hv] at hf) (fun _ _ => le_rfl)
        (fun _ _ _ hf => by simp [hv] at hf) _ hD1

end Formalism.MainNotions.PairMembershipBlocks
