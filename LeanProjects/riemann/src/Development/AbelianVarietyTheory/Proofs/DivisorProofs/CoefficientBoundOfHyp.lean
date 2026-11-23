import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open GlobalTheory.RowClaim GlobalTheory.ArchTens ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.ArchTens.VolSize

theorem abs_zpow_le {q : ℕ} (hq : q ≠ 0) {z : ℤ} {A : ℝ} (h : |(z : ℝ)| ≤ A) :
    |(((q : ℚ) ^ z : ℚ) : ℝ)| ≤ Real.exp (A * Real.log q) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have e : (((q : ℚ) ^ z : ℚ) : ℝ) = Real.exp ((z : ℝ) * Real.log q) := by
    rw [← Real.log_zpow, Real.exp_log (zpow_pos h0 z)]
    push_cast
    rfl
  rw [e, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ((le_abs_self _).trans h) (Real.log_natCast_nonneg _))

theorem prod_zpow_sum {q : ℚ} (hq : q ≠ 0) {ι : Type} (s : Finset ι) (z : ι → ℤ) : ∏ i ∈ s, q ^ z i = q ^ ∑ i ∈ s, z i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem coef_le_of_chosen {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    |((S.term t Φ β ⟨P, hl⟩).coef : ℝ)| ≤
      Real.exp ((D.R.m : ℝ) ^ 3 * bigN D * cosExp G P * Real.log (resCard (Kw P) : ℕ)) := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT (fun j hj _ => givenLevel_KO G t P hj)
  have hb := hβ ⟨P, hl⟩
  have hb' : β ⟨P, hl⟩ ∈ unfSupport (psiAt W P) (unitVol P) false
      (Reps.through hs (givenLevel G t P) (stair (locGrid G t P) (unifAt P) (cosExp G P))) (Tflip W S.B t Φ P) := by
    have : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
    rw [this] at hb
    exact hb
  have hβ' := funext (hO _ hb')
  have hz : ∀ i : Fin ((locGrid G t P).m - 2), ∃ z : ℤ,
      invVol (conjLevel hs (givenLevel G t P) ((repsAt G t P).elt (β ⟨P, hl⟩)) (j := i + 1) (by omega)) =
        (resCard (Kw P) : ℚ) ^ z ∧ |z| ≤ (bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ))) := fun i =>
    factor_stair G t P hs (cosExp G P) _ (Nat.succ_pos _) _ (by
      rw [hβ']
      exact through_elt _ (by omega))
  choose z hz hzb using hz
  have hq : resCard (Kw P) ≠ 0 := resCard_ne P
  have e : (S.term t Φ β ⟨P, hl⟩).coef = (resCard (Kw P) : ℚ) ^ (∑ i, z i) := by
    rw [← prod_zpow_sum (by exact_mod_cast hq)]
    refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => hz i)
    rfl
  rw [e]
  refine abs_zpow_le hq ?_
  have hm2 : (((locGrid G t P).m - 2 : ℕ) : ℤ) ≤ D.R.m := by
    have : (locGrid G t P).m - 2 ≤ D.R.m := by show D.R.m - 2 ≤ D.R.m; omega
    exact_mod_cast this
  have key : |∑ i, z i| ≤ (D.R.m : ℤ) ^ 3 * bigN D * cosExp G P :=
    calc |∑ i, z i| ≤ ∑ i, |z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin ((locGrid G t P).m - 2), (bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ))) :=
        Finset.sum_le_sum fun i _ => hzb i
      _ = (((locGrid G t P).m - 2 : ℕ) : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ)))) := by simp
      _ ≤ (D.R.m : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ)))) :=
        mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = _ := by ring
  exact_mod_cast key

theorem exponent_le (P : Pl D.host.E) {C : ℝ} (hC : 2 ≤ C) :
    (D.R.m : ℝ) ^ 3 * bigN D * cosExp G P * Real.log (resCard (Kw P) : ℕ) ≤
      C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz G P := by
  have h1 := log_absNorm_le P
  have hS := placeSz_nonneg G P
  have hmN : (D.R.m : ℝ) ≤ bigN D := by exact_mod_cast m_le_bigN
  rw [ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have h2 : (cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ) ≤ C * placeSz G P :=
    calc (cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ)
        ≤ (cosExp G P : ℝ) * (2 * Real.log (Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = 2 * placeSz G P := by rw [placeSz]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC hS
  have h3 : (D.R.m : ℝ) ^ 3 * bigN D ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 :=
    calc (D.R.m : ℝ) ^ 3 * bigN D = (D.R.m : ℝ) ^ 2 * bigN D * D.R.m := by ring
      _ ≤ (D.R.m : ℝ) ^ 2 * bigN D * bigN D := mul_le_mul_of_nonneg_left hmN (by positivity)
      _ = _ := by ring
  calc _ = ((D.R.m : ℝ) ^ 3 * bigN D) * ((cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ)) := by ring
    _ ≤ ((D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2) * (C * placeSz G P) :=
      mul_le_mul h3 h2 (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) (by positivity)
    _ = _ := by ring

theorem coefK : GlobalTheory.FunPr.Hypotheses₂ → BigC fun _ ch C _ => CoefAt ch C := by
  intro _
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => ?_⟩⟩⟩
  have hL := s.core.lev
  have hde := Test.pde_ne_q s
  rintro Φ β hβ ⟨P, hl⟩
  have hP : P ∈ ch.G.pl.W0 := by
    classical
    rcases Finset.mem_union.1 hl with h | h
    · exact h
    · exact absurd h (fun hP => (hL.Q_ram A.μ0 P).2 (Or.inl hP) (by rw [hL.xi_base]; exact fun _ _ => rfl))
  exact (coef_le_of_chosen hL ch.S.toGridChoice A.μ0 Φ hde (GlobalTheory.RowTest.guard_of_qGuard s.guard A.μ0) hP hl hβ).trans
    (Real.exp_le_exp.2 (exponent_le P hC))

end GlobalTheory.ArchTens.VolSize

end
