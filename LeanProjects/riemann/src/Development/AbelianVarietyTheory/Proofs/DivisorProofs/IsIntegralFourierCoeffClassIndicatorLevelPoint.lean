import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovInt

open IsDedekindDomain

def intZ (D : D7) {H : Host D.host.E} (Dw : Datum H) (l : Level H) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) : ℕ :=
  Nat.card (Fin n → LevQ Dw l) * (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w *
    l.M ^ Formalism.L2.Pj.DF Dw w

theorem intZ_eq (D : D7) {H : Host D.host.E} (Dw : Datum H) (l : Level H) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) :
    intZ D Dw l n w = l.M ^ (Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) * n) *
      (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w * l.M ^ Formalism.L2.Pj.DF Dw w := by
  rw [intZ, GlobalTheory.PlaceInt.card_fun_levQ]

theorem sum_padicValNat_mul_le (v : ℕ → ℤ) (hv : ∀ a b, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b) (h0 : ∀ a, 0 ≤ v a)
    {N : ℕ} (hN : N ≠ 0) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, (padicValNat p N : ℤ) * v p ≤ v N := by
  classical
  have h1 : v 1 = 0 := by have := hv 1 1 one_ne_zero one_ne_zero; rw [Nat.mul_one] at this; omega
  have key : ∀ N : ℕ, N ≠ 0 → ∑ p ∈ s, (padicValNat p N : ℤ) * v p ≤ v N := by
    intro N
    induction N using Nat.recOnMul with
    | zero => exact fun h => absurd rfl h
    | one => intro _; simp [h1]
    | prime l hl =>
      intro _
      have : ∀ p ∈ s, (padicValNat p l : ℤ) * v p = if p = l then v l else 0 := by
        intro p hp
        haveI := Fact.mk (hs p hp)
        haveI := Fact.mk hl
        split_ifs with h
        · subst h; simp
        · rw [padicValNat_primes h]; simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs
      exacts [le_rfl, h0 _]
    | mul a b iha ihb =>
      intro hab
      have ha := left_ne_zero_of_mul hab
      have hb := right_ne_zero_of_mul hab
      have : ∀ p ∈ s, (padicValNat p (a * b) : ℤ) * v p = (padicValNat p a : ℤ) * v p + (padicValNat p b : ℤ) * v p := by
        intro p hp
        haveI := Fact.mk (hs p hp)
        rw [padicValNat.mul ha hb]; push_cast; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hv a b ha hb]
      exact add_le_add (iha ha) (ihb hb)
  exact key N hN

theorem ram_sum_le_vV_discr (E : Type) [Field E] [NumberField E] (T : CDVR) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (e X : ℕ) :
    ∑ p ∈ s, (vV T.V (p : T.Fr) : ℝ) / e *
        ((padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ)) * (X : ℝ) / 2 ≤
      (vV T.V (((NumberField.discr E).natAbs ^ X : ℕ) : T.Fr) : ℝ) / e := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  have hN : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
  have h0 : ∀ a : ℕ, 0 ≤ vV T.V (a : T.Fr) := fun a => GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T a
  have h1 := sum_padicValNat_mul_le (fun a => vV T.V (a : T.Fr))
    (fun a b ha hb => by
      simp only [Nat.cast_mul]
      exact vV_mul (Nat.cast_ne_zero.2 ha) (Nat.cast_ne_zero.2 hb)) h0 hN s hs
  have h2 : ∑ p ∈ s, (padicValNat p (NumberField.discr E).natAbs : ℝ) * (vV T.V (p : T.Fr) : ℝ) ≤
      (vV T.V (((NumberField.discr E).natAbs : ℕ) : T.Fr) : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).2 h1
    rw [Int.cast_sum] at h
    simpa only [Int.cast_mul, Int.cast_natCast] using h
  have hk : (1 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))
  rw [Nat.cast_pow, GlobalTheory.ShortBound.vV_pow (Nat.cast_ne_zero.2 hN), Int.cast_mul, Int.cast_natCast]
  have hX : (0 : ℝ) ≤ (X : ℝ) / e := by positivity
  refine le_trans ?_ ((mul_le_mul_of_nonneg_left h2 hX).trans (le_of_eq (by ring)))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h3 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast h0 p
  have h4 : (padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) ≤
      (padicValNat p (NumberField.discr E).natAbs : ℝ) := div_le_self (Nat.cast_nonneg _) hk
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hX h3)
  have h6 : (0 : ℝ) ≤ (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) * (padicValNat p (NumberField.discr E).natAbs : ℝ) :=
    mul_nonneg (mul_nonneg hX h3) (Nat.cast_nonneg _)
  calc _ = (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) *
        ((padicValNat p (NumberField.discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ)) / 2 := by ring
    _ ≤ (X : ℝ) / e * (vV T.V (p : T.Fr) : ℝ) * (padicValNat p (NumberField.discr E).natAbs : ℝ) := by linarith
    _ = _ := by ring

theorem log_discr_natAbs_le (E : Type) [Field E] [NumberField E] :
    Real.log ((NumberField.discr E).natAbs : ℝ) ≤ (Module.finrank ℚ E : ℝ) * fieldSz E := by
  have hk : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E))
  have h := (div_le_iff₀ hk).1 (log_rd_le_fieldSz E)
  rw [Nat.cast_natAbs, Int.cast_abs]
  linarith

theorem isIntegral_fourierCoeff_classIndicator_levelPoint {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) (hM : l.M ≠ 0) {n : ℕ} (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw l) : IsIntegral ℤ (x0Dat c x0 q) := by
  unfold x0Dat
  refine ⟨Polynomial.X ^ l.M - 1, Polynomial.monic_X_pow_sub_C 1 hM, ?_⟩
  have h1 : zetaM c ^ l.M = 1 := GlobalTheory.Survey.BaseClassMove.zetaM_pow c
  have h2 : (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b))) ^ l.M = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
  simp [h2]

end GlobalTheory.CovInt
