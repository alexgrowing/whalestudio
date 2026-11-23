import Mathlib
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.SharpRestriction.Divisibility.JumpSets
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.DataForced
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

namespace Formalism.MainNotions.WeightDegreeSizes

section PartG

open Formalism.BasicNotions Formalism.BasicNotions.DV

def IsTopAt (D : D7) (τ : D.what₂.Tau) (t : D.host.TT) : Prop :=
  (D.eTau τ : D.R.GG) = D.R.tau1 t

def NotTop (D : D7) (τ : D.what₂.Tau) : Prop := (D.eTau τ : D.R.GG) ∉ D.host.topPlaces

def TrueWeightDegreeBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u τ, (∀ t, IsTopAt D τ t →
      |((D.fm u).deg τ : ℝ) - (L.aT t : ℝ)| ≤ C * (L.sc.b' + L.Sc + (D.R.m : ℝ) * L.etaSz + (D.R.N D.R.m : ℝ))) ∧
    (NotTop D τ → |((D.fm u).deg τ : ℝ)| ≤ C * (L.Sc + (D.R.m : ℝ) * L.etaSz + (D.R.N D.R.m : ℝ)))

open Classical in

def D1 (D : D7) (L : SizeData₂ D) (τ : D.what₂.Tau) : ℝ :=
  L.Sc + (D.R.m : ℝ) * L.etaSz + if NotTop D τ then 0 else L.sc.b'

def OrthonormalFrameNormBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u τ, (D.fm u).beOn τ ^ 2 ≤
    Real.exp (C * ((D.R.N D.R.m : ℝ) * D1 D L τ + (D.R.N D.R.m : ℝ) ^ 2) * L.La)

def LogLevelPrimeBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ C * (D.R.m : ℝ) * L.sc.L

def OrthoNormProductBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ptB D u ≤ Real.exp (SZbP D L C u)

theorem OrthoNormProductBound.log {D : D7} {L : SizeData₂ D} {C : ℝ} (h : OrthoNormProductBound D L C) (u : D.what₂.Word)
    (h0 : 0 < Formalism.MainNotions.product_first_zeroth_parts.ptB D u) : Real.log (Formalism.MainNotions.product_first_zeroth_parts.ptB D u) ≤ SZbP D L C u :=
  (Real.log_le_iff_le_exp h0).2 (h u)

def OrthoNormBoundUniform : Prop :=
  ∀ C1 C2 C3 : ℝ, ∃ C : ℝ, ∀ (D : D7) (L : SizeData₂ D), L.sc.L ≤ L.La →
    TrueWeightDegreeBound D L C1 → OrthonormalFrameNormBound D L C2 → LogLevelPrimeBound D L C3 → OrthoNormProductBound D L C

section Proof

open Formalism.FrobeniusOrbits

theorem tau1_mem_Psi (φ : Formalism.HC.Frame) (t : φ.A) : φ.tau1 t ∈ φ.Psi := φ.tau1_mem_Psi t

theorem tau1_injective_alt (φ : Formalism.HC.Frame) : Function.Injective φ.tau1 := φ.tau1_injective

def tauOfTop (D : D7) (t : D.host.TT) : D.what₂.Tau := D.eTau.symm ⟨D.R.tau1 t, tau1_mem_Psi _ _⟩

theorem isTopAt_tauOfTop (D : D7) (t : D.host.TT) : IsTopAt D (tauOfTop D t) t := by
  unfold IsTopAt tauOfTop
  rw [Equiv.apply_symm_apply]

theorem not_notTop {D : D7} {τ : D.what₂.Tau} {t : D.host.TT} (h : IsTopAt D τ t) : ¬ NotTop D τ := by
  intro hn
  exact hn (by rw [h]; exact Finset.mem_image.mpr ⟨t, t.2, rfl⟩)

open Classical in

theorem sum_top (D : D7) (g : D.what₂.Tau → ℝ) :
    ∑ τ ∈ Finset.univ.filter (fun τ => ¬ NotTop D τ), g τ = ∑ t : D.host.TT, g (tauOfTop D t) := by
  symm
  refine Finset.sum_bij (fun (t : D.host.TT) _ => tauOfTop D t) ?_ ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_notTop (isTopAt_tauOfTop D t)
  · intro s _ t _ hst
    have := congrArg Subtype.val (D.eTau.symm.injective hst)
    exact Subtype.ext (tau1_injective_alt _ this)
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, NotTop, not_not] at hτ
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hτ
    refine ⟨⟨t, ht⟩, Finset.mem_univ _, ?_⟩
    apply D.eTau.injective
    unfold tauOfTop
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext he
  · intro t _
    rfl

theorem core_nontop {C1 C2 C3 N S lT La dg : ℝ} (h : |dg| ≤ C1 * (S + N)) (hS : 0 ≤ S) (hN : 0 ≤ N) (hLa : 0 ≤ La)
    (hl0 : 0 ≤ lT) (hl : lT ≤ |C3| * (N * La)) :
    -dg * lT + C2 * (N * S + N ^ 2) * La ≤ (|C1| * |C3| + |C2|) * (S * N + N ^ 2) * La := by
  have hSN : 0 ≤ S + N := add_nonneg hS hN
  have a1 : -dg ≤ |C1| * (S + N) := by
    have := neg_abs_le dg
    have := mul_le_mul_of_nonneg_right (le_abs_self C1) hSN
    linarith
  have a2 : -dg * lT ≤ |C1| * (S + N) * lT := mul_le_mul_of_nonneg_right a1 hl0
  have a3 : |C1| * (S + N) * lT ≤ |C1| * (S + N) * (|C3| * (N * La)) :=
    mul_le_mul_of_nonneg_left hl (mul_nonneg (abs_nonneg _) hSN)
  have a4 : C2 * ((N * S + N ^ 2) * La) ≤ |C2| * ((N * S + N ^ 2) * La) :=
    mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)
  have a5 : 0 ≤ |C1| * |C3| * (N ^ 2 * La) := by positivity
  linarith

theorem core_top {C1 C2 C3 N S b' a lT La dg : ℝ} (h : |dg - a| ≤ C1 * (b' + S + N)) (hS : 0 ≤ S) (hb : 0 ≤ b')
    (hN : 0 ≤ N) (hLa : 0 ≤ La) (hl0 : 0 ≤ lT) (hl : lT ≤ |C3| * (N * La)) :
    -dg * lT + C2 * (N * (S + b') + N ^ 2) * La ≤ (|C1| * |C3| + |C2|) * (S * N + N ^ 2) * La +
      (-(a * lT) + (|C1| * |C3| + |C2|) * (b' * N) * La) := by
  have hbS : 0 ≤ b' + S + N := add_nonneg (add_nonneg hb hS) hN
  have a1 : -dg ≤ -a + |C1| * (b' + S + N) := by
    have := neg_abs_le (dg - a)
    have := mul_le_mul_of_nonneg_right (le_abs_self C1) hbS
    linarith
  have a2 : -dg * lT ≤ (-a + |C1| * (b' + S + N)) * lT := mul_le_mul_of_nonneg_right a1 hl0
  have a3 : |C1| * (b' + S + N) * lT ≤ |C1| * (b' + S + N) * (|C3| * (N * La)) :=
    mul_le_mul_of_nonneg_left hl (mul_nonneg (abs_nonneg _) hbS)
  have a4 : C2 * ((N * (S + b') + N ^ 2) * La) ≤ |C2| * ((N * (S + b') + N ^ 2) * La) :=
    mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)
  have a5 : 0 ≤ |C1| * |C3| * (N ^ 2 * La) := by positivity
  linarith

theorem stmtSZP : OrthoNormBoundUniform := by
  classical
  intro C1 C2 C3
  refine ⟨|C1| * |C3| + |C2|, fun D L hL h1 h2 h3 u => ?_⟩
  have hx : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  have hTpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hlT0 : 0 ≤ Real.log ((D.mem u).A.T : ℝ) := Real.log_natCast_nonneg _
  have hLpos : 0 ≤ L.sc.L := by unfold Scale.L; exact (Real.rpow_pos_of_pos hx _).le
  have hLa : 0 ≤ L.La := le_trans hLpos hL
  have hb' : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'; positivity
  have hmN : (D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.m ≤ D.R.N D.R.m := by
      unfold Ranks.N
      nlinarith [Nat.zero_le D.R.k, Nat.zero_le (D.R.m * D.R.t)]
    exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  have hS0 : 0 ≤ L.Sc + (D.R.m : ℝ) * L.etaSz :=
    add_nonneg L.Sc_pos.le (mul_nonneg hm0 L.etaSz_pos.le)
  have hlT : Real.log ((D.mem u).A.T : ℝ) ≤ |C3| * ((D.R.N D.R.m : ℝ) * L.La) := by
    have e1 := h3 u
    have e2 : C3 * ((D.R.m : ℝ) * L.sc.L) ≤ |C3| * ((D.R.m : ℝ) * L.sc.L) :=
      mul_le_mul_of_nonneg_right (le_abs_self C3) (mul_nonneg hm0 hLpos)
    have e3 : (D.R.m : ℝ) * L.sc.L ≤ (D.R.N D.R.m : ℝ) * L.La := mul_le_mul hmN hL hLpos hN0
    have e4 := mul_le_mul_of_nonneg_left e3 (abs_nonneg C3)
    linarith
  let g : D.what₂.Tau → ℝ := fun τ => -((D.fm u).deg τ : ℝ) * Real.log ((D.mem u).A.T : ℝ) +
    C2 * ((D.R.N D.R.m : ℝ) * D1 D L τ + (D.R.N D.R.m : ℝ) ^ 2) * L.La
  have hfac : ∀ τ, ((D.mem u).A.T : ℝ) ^ (-((D.fm u).deg τ)) * (D.fm u).beOn τ ^ 2 ≤ Real.exp (g τ) := by
    intro τ
    have e : ((D.mem u).A.T : ℝ) ^ (-((D.fm u).deg τ)) =
        Real.exp (-((D.fm u).deg τ : ℝ) * Real.log ((D.mem u).A.T : ℝ)) := by
      rw [← Real.rpow_intCast, Real.rpow_def_of_pos hTpos]
      congr 1
      push_cast
      ring
    show _ ≤ Real.exp (_ + _)
    rw [Real.exp_add, e]
    exact mul_le_mul_of_nonneg_left (h2 u τ) (Real.exp_pos _).le
  let P : ℝ := (|C1| * |C3| + |C2|) * ((L.Sc + (D.R.m : ℝ) * L.etaSz) * (D.R.N D.R.m : ℝ) + (D.R.N D.R.m : ℝ) ^ 2) * L.La
  have hnt : ∀ τ, NotTop D τ → g τ - P ≤ 0 := by
    intro τ hn
    have := core_nontop (C2 := C2) (C3 := C3) ((h1 u τ).2 hn) hS0 hN0 hLa hlT0 hlT
    show -((D.fm u).deg τ : ℝ) * _ + C2 * (_ * D1 D L τ + _) * _ - P ≤ 0
    unfold D1
    rw [if_pos hn, add_zero]
    linarith
  have htp : ∀ t : D.host.TT, g (tauOfTop D t) - P ≤
      -((L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
        (|C1| * |C3| + |C2|) * (L.sc.b' * (D.R.N D.R.m : ℝ)) * L.La := by
    intro t
    have ht := isTopAt_tauOfTop D t
    have h0 := (h1 u (tauOfTop D t)).1 t ht
    have h0' : |((D.fm u).deg (tauOfTop D t) : ℝ) - (L.aT t : ℝ)| ≤
        C1 * (L.sc.b' + (L.Sc + (D.R.m : ℝ) * L.etaSz) + (D.R.N D.R.m : ℝ)) := by
      rw [← add_assoc]; exact h0
    have := core_top (C2 := C2) (C3 := C3) h0' hS0 hb' hN0 hLa hlT0 hlT
    show -((D.fm u).deg (tauOfTop D t) : ℝ) * _ + C2 * (_ * D1 D L (tauOfTop D t) + _) * _ - P ≤ _
    unfold D1
    rw [if_neg (not_notTop ht)]
    linarith
  have hsum : ∑ τ, g τ ≤ SZbP D L (|C1| * |C3| + |C2|) u := by
    have s1 : ∑ τ, g τ = ∑ τ, (g τ - P) + (D.R.f : ℝ) * P := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]
      ring
    have s2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => ¬ NotTop D τ) (fun τ => g τ - P)
    have s3 : ∑ τ ∈ Finset.univ.filter (fun τ => ¬ ¬ NotTop D τ), (g τ - P) ≤ 0 :=
      Finset.sum_nonpos fun τ hτ => hnt τ (not_not.mp (Finset.mem_filter.mp hτ).2)
    have s4 := sum_top D (fun τ => g τ - P)
    have s5 := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset D.host.TT)) => htp t)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      Finset.sum_neg_distrib] at s5
    unfold SZbP
    have : (D.R.f : ℝ) * P + (D.host.TT.card : ℝ) * ((|C1| * |C3| + |C2|) * (L.sc.b' * (D.R.N D.R.m : ℝ)) * L.La) =
        (|C1| * |C3| + |C2|) * ((D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) +
          (D.R.f : ℝ) * ((D.R.m : ℝ) * L.etaSz + L.Sc) * (D.R.N D.R.m : ℝ) +
          (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) * L.La := by
      show (D.R.f : ℝ) * ((|C1| * |C3| + |C2|) * ((L.Sc + (D.R.m : ℝ) * L.etaSz) * (D.R.N D.R.m : ℝ) + (D.R.N D.R.m : ℝ) ^ 2) * L.La) + _ = _
      ring
    linarith
  unfold Formalism.MainNotions.product_first_zeroth_parts.ptB
  calc ∏ τ, ((D.mem u).A.T : ℝ) ^ (-((D.fm u).deg τ)) * (D.fm u).beOn τ ^ 2
      ≤ ∏ τ, Real.exp (g τ) :=
        Finset.prod_le_prod (fun τ _ => mul_nonneg (zpow_nonneg hTpos.le _) (sq_nonneg _)) (fun τ _ => hfac τ)
    _ = Real.exp (∑ τ, g τ) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.2 hsum

end Proof

def familyOrthoNormBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, OrthoNormProductBound (Fm.D x i) (Fm.L x i) C

theorem L_le_La {D : D7} (L : SizeData₂ D) (h : Formalism.MainNotions.SizesAt L) : L.sc.L ≤ L.La := by
  obtain ⟨_, _, _, _, _, _, hQ, _⟩ := h
  obtain ⟨_, _, _, _, _, _, hr, _⟩ := hQ
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  unfold SizeData₂.La Scale.a Scale.b
  have hb : 0 < Real.exp L.sc.L := Real.exp_pos _
  have : Real.exp L.sc.L ≤ L.sc.x * Real.exp L.sc.L * D.host.rdE := by
    have h1 : Real.exp L.sc.L ≤ L.sc.x * Real.exp L.sc.L := by nlinarith
    have h2 : 0 ≤ L.sc.x * Real.exp L.sc.L := by positivity
    nlinarith
  calc L.sc.L = Real.log (Real.exp L.sc.L) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log hb this

theorem OrthoNormProductBound.mono {D : D7} {L : SizeData₂ D} {C C' : ℝ} (hLa : 0 ≤ L.La) (hC : C ≤ C') (h : OrthoNormProductBound D L C) :
    OrthoNormProductBound D L C' := by
  intro u
  refine (h u).trans (Real.exp_le_exp.2 ?_)
  unfold SZbP
  have hb' : 0 ≤ L.sc.b' := by
    have hx : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
    unfold Scale.b' Scale.a Scale.b Scale.X'; positivity
  have hS := L.Sc_pos.le
  have hE := L.etaSz_pos.le
  have : 0 ≤ ((D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * L.etaSz + L.Sc) * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC this) hLa
  linarith

def AdmSZPF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  (∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, TrueWeightDegreeBound (Fm.D x i) (Fm.L x i) C) ∧
  (∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, OrthonormalFrameNormBound (Fm.D x i) (Fm.L x i) C) ∧
  (∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LogLevelPrimeBound (Fm.D x i) (Fm.L x i) C)

def FamilyOrthoNormBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmSZPF Fm → familyOrthoNormBound Fm

theorem stmtSZPF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilyOrthoNormBound Fm := by
  rintro ⟨⟨C1, x1, h1⟩, ⟨C2, x2, h2⟩, ⟨C3, x3, h3⟩⟩
  obtain ⟨C, hC⟩ := stmtSZP C1 C2 C3
  refine ⟨C, max x1 (max x2 x3), fun x hx hx1 i => ?_⟩
  have a1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have a2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have a3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  exact hC _ _ (L_le_La _ (Fm.sizes x hx1 i)) (h1 x a1 hx1 i) (h2 x a2 hx1 i) (h3 x a3 hx1 i)

theorem logLevelPrime_of_size {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : Formalism.MainNotions.TuSize Fm) :
    ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LogLevelPrimeBound (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨x0, h⟩ := h
  exact ⟨Fm.CTu, x0, fun x hx _ i u => (h x hx i).2 u⟩

end PartG

section PartA

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G NumberField IsDedekindDomain
open scoped BigOperators

variable {D : D7}

theorem gain_above {L : SizeData₂ D} (X : Inst D L) (K : Consts) (hF : ∀ w, ParametersFill X K w)
    (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (w : D.what₂.places.Pl)
    (hX : L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)) : L.gain j w = 0 := by
  by_cases hs : w ∈ L.supp
  · by_cases hin : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)
    · rw [(hF w).2.2.2.1 hs hin j hj]
      unfold gainP
      rw [if_pos (Or.inr hX)]
    · exact (L.not_inert w (fun h => hin (Or.inr h)) (fun h => hin (Or.inl h))).1 j
  · exact L.gain_supp j w hs

def ConclusionZ (D : D7) (L : SizeData₂ D) : Prop := L.ZeroAbove

def Ovr (D : D7) (p : ℕ) (S : Finset D.what₂.places.Pl) : Prop := ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p

theorem resChar_iff (D : D7) (l : ℕ) (hl : l.Prime) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = l ↔ (l : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  constructor
  · intro h; rw [← h]; exact resChar_mem D w
  · intro hmem
    by_contra hne
    have h1 := resChar_mem D w
    have hcop : Nat.Coprime (D.what₂.places.resChar w) l :=
      (Nat.coprime_primes (D.what₂.places.resChar_prime w) hl).mpr hne
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (D.what₂.places.resChar w : ℤ) + b * (l : ℤ) = 1 := by
      refine ⟨Nat.gcdA (D.what₂.places.resChar w) l, Nat.gcdB (D.what₂.places.resChar w) l, ?_⟩
      have := Nat.gcd_eq_gcd_ab (D.what₂.places.resChar w) l
      rw [hcop] at this
      push_cast at this
      linarith
    have h1' : (1 : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
      have : ((a * (D.what₂.places.resChar w : ℤ) + b * (l : ℤ) : ℤ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
        push_cast
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hmem)
      rwa [hab, Int.cast_one] at this
    exact (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1')

theorem exists_ovr (D : D7) (p : ℕ) (hp : p.Prime) : ∃ S, Ovr D p S := by
  classical
  obtain ⟨S, hS⟩ := finite_places_over (K := D.what₂.LL) p hp
  refine ⟨S.map D.plEq.symm.toEmbedding, fun w => ?_⟩
  rw [Finset.mem_map_equiv, Equiv.symm_symm, hS, resChar_iff D p hp]

theorem loss_bound_nonneg (L : SizeData₂ D) : 0 ≤ L.B0 := by
  have hx0 : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  simp only [SizeData₂.B0, sizeBudget, bSize]
  have := Real.rpow_nonneg hx0.le L.sc.eps
  have := Real.exp_pos (L.sc.x ^ L.sc.eps)
  positivity

def sumA (L : SizeData₂ D) : ℝ := ∑ t : D.host.TT, (L.aT t : ℝ)

open Classical in

def C2atG (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ (i : Fin 2) u, ∀ j ∈ SizeData₂.lifts D,
    |(∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g i), SizeData₂.sz w (L.E u j w)) -
      sumA L * Real.log (D.host.g i : ℝ)| ≤ C * L.B0

def C2off (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D,
    ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes), |SizeData₂.sz w (L.E u j w)| ≤ C * L.B0

def IsotypicRank (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop := LocalQuadraticParts.adm11 D L C

theorem secondComplement_of_split (L : SizeData₂ D) (C1 C2 : ℝ) (h0 : 0 ≤ C1) (h1 : C2atG D L C1) (h2 : C2off D L C2) :
    IsotypicRank D L (2 * C1 + C2) := by
  classical
  intro u j hj
  have hB := loss_bound_nonneg L
  refine ⟨?_, (h2 u j hj).trans (by nlinarith)⟩
  have hg0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
  have hlog : Real.log (∏ g ∈ L.gTypes, (g : ℝ)) = Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) := by
    unfold SizeData₂.gTypes
    rw [Finset.prod_pair D.host.g_ne, Real.log_mul hg0.ne' hg1.ne']
  set f : D.what₂.places.Pl → ℝ := fun w => SizeData₂.sz w (L.E u j w) with hf
  have hsplit : ∑ w ∈ L.supp, f w =
      (∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g 0), f w) +
      (∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g 1), f w) +
      ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes), f w := by
    rw [← Finset.sum_filter_add_sum_filter_not L.supp (fun w => D.what₂.places.resChar w = D.host.g 0) f,
      ← Finset.sum_filter_add_sum_filter_not
        (L.supp.filter (fun w => ¬ D.what₂.places.resChar w = D.host.g 0))
        (fun w => D.what₂.places.resChar w = D.host.g 1) f, Finset.filter_filter, Finset.filter_filter, add_assoc]
    congr 2
    · refine Finset.sum_congr (Finset.filter_congr fun w _ => ?_) fun _ _ => rfl
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨fun h' => D.host.g_ne (h'.symm.trans h), h⟩
    · refine Finset.sum_congr (Finset.filter_congr fun w _ => ?_) fun _ _ => rfl
      simp [SizeData₂.gTypes]
  have a0 := h1 0 u j hj
  have a1 := h1 1 u j hj
  have a2 : |∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes), f w| ≤ C2 * L.B0 :=
    (Finset.abs_sum_le_sum_abs _ _).trans (h2 u j hj)
  rw [hlog, hsplit]
  rw [abs_le] at a0 a1 a2 ⊢
  unfold sumA at a0 a1
  constructor <;> nlinarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2]

theorem stmtZ {L : SizeData₂ D} (Gi : Inst D L) (K : Consts) (X : ErrX D) (c : ErrC)
    (hF : ∀ w, ParametersFill Gi K w) (hE : L.EDef X K c) : ConclusionZ D L :=
  fun u j hj w hX hT hg hd hG => ⟨gain_above Gi K hF j hj w hX, hE.zeroAbove u j hj w hX hT hg hd hG⟩

theorem zero_gain_above_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ConclusionZ (Fm.D x i) (Fm.L x i) :=
  fun x hx i => stmtZ (Fm.Gx x i) Fm.GK (Fm.ex x hx i).errX Fm.cX.err (Fm.fills x hx i) (Fm.ex x hx i).err.edef

def NormDecompositionCond (D : D7) (X : ErrX D) : Prop :=
  ∀ (i : Fin 2) u, ∀ j ∈ SizeData₂.lifts D, ∀ S : Finset D.what₂.places.Pl, Ovr D (D.host.g i) S →
    ∑ w ∈ S, SizeData₂.sz w (vNN X i u j w) = (∑ τ : D.what₂.Tau, nuAbs D u j τ) * Real.log (D.host.g i : ℝ)

def LevelPrimeNotTypePrime (D : D7) : Prop := ∀ u (i : Fin 2), D.host.g i ≠ (D.mem u).A.T

def errG (L : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ :=
  2 * (∑ τ : D.what₂.Tau, wj D j τ) +
    C * ((D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Nm D) +
      (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x)

def DegreeCountBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D,
    |(∑ τ : D.what₂.Tau, nuAbs D u j τ) - (fockDeg D j : ℝ) - sumA L| ≤ errG L C j

def TypePrimeSizeBound (D : D7) (L : SizeData₂ D) (c : ErrC) (Cd C : ℝ) : Prop :=
  ∀ (i : Fin 2) u, ∀ j ∈ SizeData₂.lifts D,
    (errG L Cd j + 2 * (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) +
      2 * (c.g * (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz))) *
        Real.log (D.host.g i : ℝ) ≤ C * L.B0

theorem Eval_atG (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (hT : LevelPrimeNotTypePrime D) (i : Fin 2) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = D.host.g i) :
    Eval L X K c u j w = (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) + EatG L X c i u j w := by
  unfold Eval
  simp only [hw, if_neg (hT u i)]
  fin_cases i
  · simp
  · have : D.host.g 1 ≠ D.host.g 0 := D.host.g_ne.symm
    simp [this]

theorem C2atG_of (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (Cd C : ℝ) (hc : c.Large)
    (hE : L.EDef X K c) (hT : LevelPrimeNotTypePrime D) (hN : NormDecompositionCond D X) (hD : DegreeCountBound D L Cd) (hS : TypePrimeSizeBound D L c Cd C) :
    C2atG D L C := by
  classical
  intro i u j hj
  obtain ⟨S, hSo⟩ := exists_ovr D (D.host.g i) (D.host.g_prime i)
  obtain ⟨er, her⟩ : ∃ er : ℝ, er = c.g * (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) := ⟨_, rfl⟩
  obtain ⟨vd, hvd⟩ : ∃ vd : ℝ, vd = (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) := ⟨_, rfl⟩
  have her0 : 0 ≤ er := by
    rw [her]
    have h1 : 0 ≤ c.g := le_trans (by norm_num) hc.2.2
    have h2 := L.etaSz_pos.le
    have h3 : 0 ≤ Nm D := by unfold Nm; positivity
    positivity
  have hvd0 : 0 ≤ vd := by rw [hvd]; positivity
  have h1 : ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g i), SizeData₂.sz w (L.E u j w) =
      ∑ w ∈ S, SizeData₂.sz w (L.E u j w) := by
    refine Finset.sum_subset (fun w hw => (hSo w).2 (Finset.mem_filter.1 hw).2) fun w hw hn => ?_
    have : w ∉ L.supp := fun h => hn (Finset.mem_filter.2 ⟨h, (hSo w).1 hw⟩)
    rw [L.E_supp u j w this]
    simp [SizeData₂.sz]
  have h2 : ∀ w ∈ S, SizeData₂.sz w (L.E u j w) =
      2 * (vd + FTypeG D j + er) * (lw D.what₂.LL (D.plEq w) * (D.what₂.places.ramIdx w : ℝ)) +
        SizeData₂.sz w (vNN X i u j w) := by
    intro w hw
    rw [hE u j hj w, Eval_atG L X K c hT i u j w ((hSo w).1 hw)]
    unfold EatG SizeData₂.sz SizeData₂.lwP
    rw [← her, ← hvd]
    ring
  have hlg : 0 ≤ Real.log (D.host.g i : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (D.host.g_prime i).one_lt.le)
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.mul_sum,
    factEtaMean D (D.host.g i) (D.host.g_prime i) S hSo, hN i u j hj S hSo]
  have hd := hD u j hj
  have hs := hS i u j hj
  rw [← her, ← hvd] at hs
  have e1 : 2 * (vd + FTypeG D j + er) * Real.log (D.host.g i : ℝ) +
      (∑ τ : D.what₂.Tau, nuAbs D u j τ) * Real.log (D.host.g i : ℝ) - sumA L * Real.log (D.host.g i : ℝ) =
      (((∑ τ : D.what₂.Tau, nuAbs D u j τ) - (fockDeg D j : ℝ) - sumA L) + (2 * vd + 2 * er)) *
        Real.log (D.host.g i : ℝ) := by
    unfold FTypeG; ring
  rw [e1, abs_mul, abs_of_nonneg hlg]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hlg) hs
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * vd + 2 * er)]
  linarith

theorem logWeight_nonneg (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := by
  unfold SizeData₂.lwP lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem sum_by_prime (S : Finset D.what₂.places.Pl) (h : ℕ → ℝ) (h0 : ∀ p, 0 ≤ h p) :
    ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * h (D.what₂.places.resChar w) ≤
      ∑ p ∈ S.image D.what₂.places.resChar, Real.log (p : ℝ) * h p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := D.what₂.places.resChar) (t := S.image D.what₂.places.resChar)
    (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨w0, _, hw0⟩ := Finset.mem_image.1 hp
  have hpp : p.Prime := hw0 ▸ D.what₂.places.resChar_prime w0
  obtain ⟨Sp, hSp⟩ := exists_ovr D p hpp
  have e1 : ∑ w ∈ S.filter (fun w => D.what₂.places.resChar w = p),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * h (D.what₂.places.resChar w) =
      (∑ w ∈ S.filter (fun w => D.what₂.places.resChar w = p), SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * h p := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [(Finset.mem_filter.1 hw).2]
  rw [e1]
  refine mul_le_mul_of_nonneg_right ?_ (h0 p)
  rw [← factEtaMean D p hpp Sp hSp]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (hSp w).2 (Finset.mem_filter.1 hw).2)
    fun w _ _ => mul_nonneg (logWeight_nonneg w) (Nat.cast_nonneg _)

theorem sum_val_log_le (n : ℕ) (hn : 0 < n) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, Real.log (p : ℝ) * (padicValNat p n : ℝ) ≤ Real.log (n : ℝ) := by
  classical
  have h1 : (∏ p ∈ P, p ^ padicValNat p n) ∣ n := by
    induction P using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ pow_padicValNat_dvd
        (ih fun p hp => hP p (Finset.mem_insert_of_mem hp))
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP a (Finset.mem_insert_self _ _))
        (hP q (Finset.mem_insert_of_mem hq))).2 (fun h => ha (h ▸ hq)))
  have h2 : (∏ p ∈ P, p ^ padicValNat p n) ≤ n := Nat.le_of_dvd hn h1
  have h3 : (0 : ℝ) < ((∏ p ∈ P, p ^ padicValNat p n : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _
  calc ∑ p ∈ P, Real.log (p : ℝ) * (padicValNat p n : ℝ)
      = Real.log ((∏ p ∈ P, p ^ padicValNat p n : ℕ) : ℝ) := by
        push_cast
        rw [Real.log_prod (fun p hp => by
          have := (hP p hp).pos
          positivity)]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Real.log_pow]; ring
    _ ≤ Real.log (n : ℝ) := Real.log_le_log h3 (by exact_mod_cast h2)

open Classical in

def EatCI (L : SizeData₂ D) (K : Consts) (c : ErrC) (j p : ℕ) : ℝ :=
  if IsResidueClassZero D p ∧ hP D p = 0 then EatC L c j p else EatI L K c j p

def LevelPrimeBudget (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop := ∀ u, Formalism.MainNotions.product_first_zeroth_parts.WeightBudgetBound D u L C

def StabiliserLogBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop := ∀ u, 2 * Real.log ((D.mem u).C.DGam : ℝ) ≤ C * L.B0

def DiscriminantOffsetBound (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, 2 * Real.log (D.host.d : ℝ) * |EatD D j| ≤ C * L.B0

def InertPrimeLossBound (D : D7) (L : SizeData₂ D) (K : Consts) (c : ErrC) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ P : Finset ℕ,
    (∀ p ∈ P, p.Prime ∧ (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) →
    ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatCI L K c j p| ≤ C * L.B0

open Classical in

def hOff (L : SizeData₂ D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j p : ℕ) : ℝ :=
  (padicValNat p (D.mem u).C.DGam : ℝ) + (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0) +
    (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0)

theorem hOff_nonneg (L : SizeData₂ D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j p : ℕ) : 0 ≤ hOff L K c u j p := by
  unfold hOff
  have h1 : (0 : ℝ) ≤ (padicValNat p (D.mem u).C.DGam : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0) := by split_ifs <;> simp
  have h3 : 0 ≤ (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0) := by
    split_ifs <;> simp
  linarith

theorem Eval_off (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ) (w : D.what₂.places.Pl)
    (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T) (hg : D.what₂.places.resChar w ∉ L.gTypes) :
    |Eval L X K c u j w| ≤ hOff L K c u j (D.what₂.places.resChar w) := by
  have h0 : D.what₂.places.resChar w ≠ D.host.g 0 := fun h => hg (by simp [SizeData₂.gTypes, h])
  have h1 : D.what₂.places.resChar w ≠ D.host.g 1 := fun h => hg (by simp [SizeData₂.gTypes, h])
  have hv : (0 : ℝ) ≤ (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ) := Nat.cast_nonneg _
  unfold Eval hOff EatCI
  simp only [if_neg h0, if_neg h1, if_neg hT]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hv]
  by_cases hr : D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD
  · simp only [if_pos hr]
    have : 0 ≤ (if (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
        (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        |if IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) = 0 then
          EatC L c j (D.what₂.places.resChar w) else EatI L K c j (D.what₂.places.resChar w)| else 0) := by
      split_ifs <;> simp
    linarith
  · simp only [if_neg hr]
    by_cases hi : (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
        (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hi]; linarith
    · simp only [if_neg hi]; simp

theorem EatT_nonneg (u : D.what₂.Word) (w : D.what₂.places.Pl) : 0 ≤ EatT D u w := by
  unfold EatT
  have h3 : 0 ≤ Nm D := by unfold Nm; positivity
  split_ifs
  · positivity
  · exact le_rfl

theorem abs_sz (w : D.what₂.places.Pl) (y : ℝ) :
    |SizeData₂.sz w y| = 2 * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * |y|) := by
  unfold SizeData₂.sz
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (logWeight_nonneg w), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ))]
  ring

theorem C2off_of (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (CT CG Cd CI : ℝ)
    (hE : L.EDef X K c) (hT : LevelPrimeBudget D L CT) (hG : StabiliserLogBound D L CG) (hD : DiscriminantOffsetBound D L Cd)
    (hI : InertPrimeLossBound D L K c CI) : C2off D L (CT + CG + Cd + CI) := by
  classical
  intro u j hj
  set S := L.supp.filter (fun w => D.what₂.places.resChar w ∉ L.gTypes) with hS
  rw [← Finset.sum_filter_add_sum_filter_not S (fun w => D.what₂.places.resChar w = (D.mem u).A.T)]
  have p1 : ∑ w ∈ S.filter (fun w => D.what₂.places.resChar w = (D.mem u).A.T), |SizeData₂.sz w (L.E u j w)| ≤ CT * L.B0 := by
    have e : ∀ w ∈ S.filter (fun w => D.what₂.places.resChar w = (D.mem u).A.T),
        |SizeData₂.sz w (L.E u j w)| = SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) := by
      intro w hw
      have hw' := (Finset.mem_filter.1 hw).2
      have : L.E u j w = EatT D u w := by
        rw [hE u j hj w]; unfold Eval; simp only [if_pos hw']
      rw [this, abs_of_nonneg]
      unfold SizeData₂.sz
      have := logWeight_nonneg w
      have := EatT_nonneg u w
      positivity
    rw [Finset.sum_congr rfl e]
    exact (((hT u).1 (S.filter (fun w => D.what₂.places.resChar w = (D.mem u).A.T))
      (fun w hw => (Finset.mem_filter.1 hw).2)).2).trans (hT u).2
  set S2 := S.filter (fun w => ¬ D.what₂.places.resChar w = (D.mem u).A.T) with hS2
  set P := S2.image D.what₂.places.resChar with hP
  have hPp : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨w0, _, hw0⟩ := Finset.mem_image.1 hp
    exact hw0 ▸ D.what₂.places.resChar_prime w0
  have p2 : ∑ w ∈ S2, |SizeData₂.sz w (L.E u j w)| ≤ 2 * ∑ p ∈ P, Real.log (p : ℝ) * hOff L K c u j p := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_by_prime S2 (hOff L K c u j) (hOff_nonneg L K c u j)) (by norm_num))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    have hw2 := Finset.mem_filter.1 hw
    have hw1 := Finset.mem_filter.1 hw2.1
    rw [abs_sz, hE u j hj w]
    have := Eval_off L X K c u j w hw2.2 hw1.2
    have h5 : 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := mul_nonneg (logWeight_nonneg w) (Nat.cast_nonneg _)
    nlinarith
  have q1 : ∑ p ∈ P, Real.log (p : ℝ) * (padicValNat p (D.mem u).C.DGam : ℝ) ≤ Real.log ((D.mem u).C.DGam : ℝ) :=
    sum_val_log_le _ (D.mem u).C.DGam_pos P hPp
  have q2 : ∑ p ∈ P, Real.log (p : ℝ) * (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0) ≤
      Real.log (D.host.d : ℝ) * |EatD D j| := by
    have : ∀ p ∈ P, Real.log (p : ℝ) * (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0) =
        if D.host.cls p = PrimeClass.ramD then Real.log (p : ℝ) * |EatD D j| else 0 := by
      intro p _; split_ifs <;> simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := {D.host.d})
      (fun p hp => Finset.mem_singleton.2 (cls_ramD (Finset.mem_filter.1 hp).2))
      fun p _ _ => mul_nonneg (Real.log_natCast_nonneg _) (abs_nonneg _)).trans ?_
    simp
  have q3 : ∑ p ∈ P, 2 * (Real.log (p : ℝ) *
      (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0)) ≤ CI * L.B0 := by
    have : ∀ p ∈ P, 2 * (Real.log (p : ℝ) *
        (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0)) =
        if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then 2 * Real.log (p : ℝ) * |EatCI L K c j p| else 0 := by
      intro p _; split_ifs <;> ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
    exact hI j hj _ fun p hp => ⟨hPp p (Finset.mem_filter.1 hp).1, (Finset.mem_filter.1 hp).2⟩
  have q4 : ∑ p ∈ P, Real.log (p : ℝ) * hOff L K c u j p =
      (∑ p ∈ P, Real.log (p : ℝ) * (padicValNat p (D.mem u).C.DGam : ℝ)) +
      (∑ p ∈ P, Real.log (p : ℝ) * (if D.host.cls p = PrimeClass.ramD then |EatD D j| else 0)) +
      ∑ p ∈ P, Real.log (p : ℝ) *
        (if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then |EatCI L K c j p| else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold hOff; ring
  rw [← Finset.mul_sum] at q3
  have g1 := hG u
  have g2 := hD j hj
  rw [q4] at p2
  nlinarith

def SecondComplementInputs (D : D7) (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (Cdeg Cg CT CG Cd CI : ℝ) : Prop :=
  LevelPrimeNotTypePrime D ∧ NormDecompositionCond D X ∧ DegreeCountBound D L Cdeg ∧ TypePrimeSizeBound D L c Cdeg Cg ∧ LevelPrimeBudget D L CT ∧ StabiliserLogBound D L CG ∧
    DiscriminantOffsetBound D L Cd ∧ InertPrimeLossBound D L K c CI

theorem secondComplement_of_inputs (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (Cdeg Cg CT CG Cd CI : ℝ) (hc : c.Large) (hCg : 0 ≤ Cg)
    (hE : L.EDef X K c) (h : SecondComplementInputs D L X K c Cdeg Cg CT CG Cd CI) :
    IsotypicRank D L (2 * Cg + (CT + CG + Cd + CI)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact secondComplement_of_split L Cg _ hCg (C2atG_of L X K c Cdeg Cg hc hE a1 a2 a3 a4) (C2off_of L X K c CT CG Cd CI hE a5 a6 a7 a8)

def FamilySecondComplementInputs {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ Cdeg Cg CT CG Cd CI x0 : ℝ, 0 ≤ Cg ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x,
    SecondComplementInputs (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX Fm.GK Fm.cX.err Cdeg Cg CT CG Cd CI

def familySecondComplement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, IsotypicRank (Fm.D x i) (Fm.L x i) C

theorem secondComplement_family_of_inputs {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : FamilySecondComplementInputs Fm) : familySecondComplement Fm := by
  obtain ⟨Cdeg, Cg, CT, CG, Cd, CI, x0, h0, h⟩ := h
  exact ⟨_, x0, fun x hx0 hx i => secondComplement_of_inputs (Fm.L x i) (Fm.ex x hx i).errX Fm.GK Fm.cX.err Cdeg Cg CT CG Cd CI
    (Fm.ex x hx i).err.large h0 (Fm.ex x hx i).err.edef (h x hx0 hx i)⟩

theorem secondComplement_family_of_large {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (_hc : Fm.cX.err.Large) (h : FamilySecondComplementInputs Fm) : familySecondComplement Fm := secondComplement_family_of_inputs Fm h

end PartA

section PartB

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

def PairAtT (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  DGamDef D → (∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ z ∈ locW D.what₂.places w ((D.fm u).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.Ptil ((D.fm u).emb D.R.m z) ((D.eMt u).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ))) ∧
  ∀ u μ, μ ≠ D.what₂.mu0 → ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ z ∈ locW D.what₂.places w ((T.fm u μ).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).Ptil ((T.fm u μ).emb D.R.m z) ((D.eMtTw u μ).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ))

def PairingAtEveryPlace (D : D7) (Dx : DivX D) (T : TwForms D) : Prop := PairInt D Dx T ∧ PairAtT D Dx T

def MemberChainIntegral (D : D7) : Prop := ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u

def TwistedChainIntegral (D : D7) (T : TwForms D) : Prop :=
  ∀ u μ, μ ≠ D.what₂.mu0 → ∃ h : (T.fm u μ).PRat, (T.fm u μ).PtilIntegral h

def PeriodClassSumWeyl (D : D7) : Prop :=
  DGamDef D → ∀ u, ∀ x ∈ (D.fm u).ptLat.L, ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm F) ∧
      ∀ w : D.what₂.places.Pl, y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def TwistedPeriodIntegral (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  DGamDef D → ∀ u μ, μ ≠ D.what₂.mu0 → ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ →
        y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def PairingFromIntegrality (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  MemberChainIntegral D → TwistedChainIntegral D T → PeriodClassSumWeyl D → TwistedPeriodIntegral D Dx T → PairingAtEveryPlace D Dx T

theorem pair_add_ge (D : D7) (w : D.what₂.places.Pl) {a b : D.what₂.LL} {B : ℝ}
    (ha : a = 0 ∨ B ≤ (vAdd (D.plEq w) a : ℝ)) (hb : b = 0 ∨ B ≤ (vAdd (D.plEq w) b : ℝ)) :
    a + b = 0 ∨ B ≤ (vAdd (D.plEq w) (a + b) : ℝ) := by
  rcases ha with rfl | ha
  · simpa using hb
  rcases hb with rfl | hb
  · simpa using Or.inr ha
  by_cases ha0 : a = 0
  · subst ha0; simpa using Or.inr hb
  by_cases hb0 : b = 0
  · subst hb0; simpa using Or.inr ha
  by_cases hab : a + b = 0
  · exact Or.inl hab
  right
  have h := (D.what₂.places.val w).map_add a b
  rw [D.val_eq w _ ha0, D.val_eq w _ hb0, D.val_eq w _ hab] at h
  have h' : min (vAdd (D.plEq w) a) (vAdd (D.plEq w) b) ≤ vAdd (D.plEq w) (a + b) := by
    rcases le_total (vAdd (D.plEq w) a) (vAdd (D.plEq w) b) with h1 | h1
    · rw [min_eq_left h1]
      rw [min_eq_left (by exact_mod_cast h1)] at h
      exact_mod_cast h
    · rw [min_eq_right h1]
      rw [min_eq_right (by exact_mod_cast h1)] at h
      exact_mod_cast h
  have h2 : (min (vAdd (D.plEq w) a) (vAdd (D.plEq w) b) : ℝ) ≤ (vAdd (D.plEq w) (a + b) : ℝ) := by
    exact_mod_cast h'
  exact le_trans (le_min ha hb) h2

theorem pair_smul_ge (D : D7) (w : D.what₂.places.Pl) {r b : D.what₂.LL} {B : ℝ}
    (hr : r ∈ intW D.what₂.places w) (hb : b = 0 ∨ B ≤ (vAdd (D.plEq w) b : ℝ)) :
    r * b = 0 ∨ B ≤ (vAdd (D.plEq w) (r * b) : ℝ) := by
  rcases hb with rfl | hb
  · left; simp
  by_cases hr0 : r = 0
  · left; simp [hr0]
  by_cases hb0 : b = 0
  · left; simp [hb0]
  right
  rw [vAdd_mul' _ hr0 hb0]
  have h0 : (0 : WithTop ℤ) ≤ D.what₂.places.val w r := hr
  rw [D.val_eq w _ hr0] at h0
  have h1 : (0 : ℤ) ≤ vAdd (D.plEq w) r := by exact_mod_cast h0
  have h2 : (0 : ℝ) ≤ (vAdd (D.plEq w) r : ℝ) := by exact_mod_cast h1
  push_cast
  linarith

theorem pair_core (D : D7) (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V]
    (Λ : Submodule (𝓞 D.what₂.LL) V) (g : V →ₛₗ[D.what₂.embLL] ℂ) (B : ℝ)
    (h : ∀ x ∈ Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = g x ∧ (y = 0 ∨ B ≤ (vAdd (D.plEq w) y : ℝ))) :
    ∀ z ∈ locW D.what₂.places w Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = g z ∧ (y = 0 ∨ B ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro z hz
  unfold locW at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, by simp, Or.inl rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb], pair_add_ge D w ha' hb'⟩
  | smul r x _ hx =>
    obtain ⟨a, ha, ha'⟩ := hx
    refine ⟨(r : D.what₂.LL) * a, ?_, pair_smul_ge D w r.2 ha'⟩
    rw [map_mul, ha, Subring.smul_def, LinearMap.map_smulₛₗ]
    rfl

theorem stmtPair (D : D7) (Dx : DivX D) (T : TwForms D) : PairingFromIntegrality D Dx T := by
  intro h0 hT hp0 hpT
  have A : ∀ (hD : DGamDef D) u (w : D.what₂.places.Pl), ∀ z ∈ locW D.what₂.places w ((D.fm u).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.Ptil ((D.fm u).emb D.R.m z) ((D.eMt u).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
    intro hD u w z hz F hF hF0
    obtain ⟨_, _, _, ⟨hR, hI, _⟩, _⟩ := h0 u
    let g : ((D.fm u).lat D.R.m).V →ₛₗ[D.what₂.embLL] ℂ :=
      ((((D.mem u).P.period.flip ((D.eMt u).symm F)).comp ((D.mem u).P.lowerMap.comp (D.mem u).P.evz))).comp ((D.fm u).emb D.R.m)
    refine pair_core D w _ g _ ?_ z hz
    intro x hx
    obtain ⟨y, hy, hv⟩ := hp0 hD u _ (hI x hx) F hF hF0
    refine ⟨y, ?_, hv w⟩
    rw [hy, (D.fm u).PtL_spec hR x]
    rfl
  have B : ∀ (hD : DGamDef D) u μ, μ ≠ D.what₂.mu0 → ∀ w : D.what₂.places.Pl,
    D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ z ∈ locW D.what₂.places w ((T.fm u μ).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).Ptil ((T.fm u μ).emb D.R.m z) ((D.eMtTw u μ).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
    intro hD u μ hμ w hQ z hz F hF hF0
    obtain ⟨hR, hI⟩ := hT u μ hμ
    let g : ((T.fm u μ).lat D.R.m).V →ₛₗ[D.what₂.embLL] ℂ :=
      ((((D.PTw u μ).period.flip ((D.eMtTw u μ).symm F)).comp ((D.PTw u μ).lowerMap.comp (D.PTw u μ).evz))).comp ((T.fm u μ).emb D.R.m)
    refine pair_core D w _ g _ ?_ z hz
    intro x hx
    obtain ⟨y, hy, hv⟩ := hpT hD u μ hμ _ (hI x hx) F hF hF0
    refine ⟨y, ?_, hv w hQ⟩
    rw [hy, (T.fm u μ).PtL_spec hR x]
    rfl
  exact ⟨fun hD => ⟨fun u w _ => A hD u w, fun u μ _ hμ w _ => B hD u μ hμ w⟩,
    fun hD => ⟨fun u w _ => A hD u w, fun u μ hμ w _ => B hD u μ hμ w⟩⟩

def ValuationAtLevelPrime (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ μ, D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam D u w,
      ColGe T u μ w x (-((D.R.m : ℝ) * EatT D u w))

def LevelPrimeCoprimeStabiliser (D : D7) : Prop := ∀ u, ¬ (D.mem u).A.T ∣ (D.mem u).C.DGam

def LevelPrimeSizes (D : D7) (L : SizeData₂ D) : Prop := ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ETDef D u L

def ServedHasModel {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ → GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)

def GainLe {D : D7} {L : SizeData₂ D} (X : Inst D L) (K : Consts) : Prop :=
  ∀ (w : D.what₂.places.Pl), ∀ j ∈ SizeData₂.lifts D, L.gainD j w ≤ gainS X K (D.what₂.places.resChar w) j

def NuInM (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T → LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)

def ValuationAtDiscriminant (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D)
    (ce : ErrC) (sp : ℝ) : Prop := WeilJacquetShalikaLaw.LossAtDiscriminant D L K Dx T lev Xe ce sp

def UniformRadiusLetters (D : D7) (L : SizeData₂ D) (K : Consts) (Dx : DivX D) (T : TwForms D) (lev : LevelData D) (Xe : ErrX D)
    (ce : ErrC) (sp : ℝ) : Prop := WeilJacquetShalikaLaw.MediumInertPrimeLengthBound D L K Dx T lev Xe ce sp

def L2BoundAlt (D : D7) (L : SizeData₂ D) : Prop := Formalism.MainNotions.LocalQuadraticParts.adm2 D L

def FourthComplement (D : D7) (L : SizeData₂ D) : Prop := Formalism.MainNotions.LocalQuadraticParts.adm12 D L

variable {D : D7} {L : SizeData₂ D}

theorem period_geT {Dx : DivX D} {T : TwForms D} (hP : PairAtT D Dx T) (hD : DGamDef D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = (D.mem u).A.T) (φ : (D.div.Nu u).V) (s : ℝ) :
    ∀ μ, D.what₂.places.resChar w ∉ Dx.Qp μ → ColGe T u μ w (D.nuIn u φ) s →
    ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
        (y = 0 ∨ ur D w (s - vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro μ hQ hc F hF hF0
  by_cases hμ : μ = D.what₂.mu0
  · subst hμ
    obtain ⟨y, hy, a, z, hz, rfl, ha⟩ := hc.1 rfl
    obtain ⟨y0, hy0, hv0⟩ := (hP hD).1 u w hw z hz F hF hF0
    refine ⟨a * y0, ?_, val_step D w ha hv0⟩
    rw [D.perCol_base_eq_PtilCol, D.nuIn_jN, PeriodMap.PtilCol, ← hy, map_mul, hy0, LinearMap.map_smulₛₗ]
    simp [PeriodMap.Ptil]
  · obtain ⟨y, hy, a, z, hz, rfl, ha⟩ := hc.2 hμ
    obtain ⟨y0, hy0, hv0⟩ := (hP hD).2 u μ hμ w hw hQ z hz F hF hF0
    refine ⟨a * y0, ?_, val_step D w ha hv0⟩
    rw [D.perCol_tie u μ hμ, D.nuIn_jN, PeriodMap.PtilCol, ← hy, map_mul, hy0, LinearMap.map_smulₛₗ]
    simp [PeriodMap.Ptil]

theorem sg_atT (hE : LevelPrimeSizes D L) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) : L.sg u w = -((D.R.m : ℝ) * EatT D u w) := by
  unfold SizeData₂.sg
  have h : ∀ j ∈ SizeData₂.lifts D, L.gainD j w + L.F j w - L.E u j w = -EatT D u w := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := (hE u w hw).2 j hj
    have h4 : L.gainD j w = 0 := by
      unfold SizeData₂.gainD
      split_ifs
      · rfl
      · exact h1
    rw [h4, h2, h3]
    simp
  rw [Finset.sum_congr rfl h, Finset.sum_const]
  simp [SizeData₂.lifts]

theorem period_integral_at_levelPrime {Dx : DivX D} {T : TwForms D} (hP : PairAtT D Dx T) (hD : DGamDef D) (hE : LevelPrimeSizes D L)
    (hN : NuAtTDef D L) (hG : LevelPrimeCoprimeStabiliser D) (h : ValuationAtLevelPrime D Dx T) :
    ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ φ : (D.div.Nu u).V, φ ∈ L.NuLat u →
      ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
        ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
          (y = 0 ∨ ur D w (L.sg u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro u w hw φ hφ F hF1 hF0
  have hin : D.nuIn u φ ∈ LT.Nlam D u w := by
    refine (hN u w hw φ).1 ⟨1, ?_, by simpa using hφ⟩
    exact fun h1 => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hc := h u w hw (D.what₂.muAt w) (Dx.Qp_muAt w) _ hin
  have h1 := period_geT hP hD u w hw φ _ _ (Dx.Qp_muAt w) hc F hF1 hF0
  have h0 : vDG D u w = 0 := by
    unfold vDG
    rw [hw, padicValNat.eq_zero_of_not_dvd (hG u)]
    simp
  rw [h0, sub_zero, ← sg_atT hE u w hw] at h1
  exact h1

theorem gainP_nonneg {X : Inst D L} {K : Consts} (a b : HH D → ℤ) (p j : ℕ) : 0 ≤ gainP X K a b p j := by
  unfold gainP
  split_ifs
  · exact le_rfl
  · exact add_nonneg (Finset.sum_nonneg fun _ _ => le_max_of_le_right (le_max_right _ _))
      (Finset.sum_nonneg fun _ _ => le_max_right _ _)

theorem gainS_nonneg {X : Inst D L} {K : Consts} (p j : ℕ) : 0 ≤ gainS X K p j := WeilJacquetShalikaLaw.served_gain_nonneg p j

theorem gainLe_of_fills {X : Inst D L} {K : Consts} (hF : ∀ w, ParametersFill X K w)
    (hcs : ∀ p : ℕ, p.Prime → IsCs D p → p ∈ L.drop) : GainLe X K :=
  fun w j hj => WeilJacquetShalikaLaw.gainD_le_gainS hF hcs w j hj

theorem inv_mem_intW (D : D7) (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal) :
    ((s : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact Submodule.zero_mem _
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w ((s : D.what₂.LL))⁻¹
  rw [D.val_eq w _ (inv_ne_zero hs0)]
  have h1 : (D.plEq w).valuation D.what₂.LL (s : D.what₂.LL) = 1 := by
    have := (D.plEq w).valuation_of_algebraMap (K := D.what₂.LL) s
    rw [show (s : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL s from rfl, this]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
  have h2 : vAdd (D.plEq w) ((s : D.what₂.LL))⁻¹ = 0 := by
    unfold vAdd
    rw [map_inv₀, h1]
    simp
  rw [h2]
  rfl

theorem nuIn_mem_Sram_loc (u : D.what₂.Word) (w : D.what₂.places.Pl) (φ : (D.div.Nu u).V)
    (h : LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) (hφ : φ ∈ L.NuLat u) : D.nuIn u φ ∈ LT.Sram D u w := by
  obtain ⟨s, hs, hm⟩ := h φ hφ
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hm
  have h1 := nuIn_mem_Sram D u w (s • φ) hm
  have h2 := (LT.Sram D u w).smul_mem ⟨_, inv_mem_intW D w s hs⟩ h1
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact Submodule.zero_mem _
  have h3 : (⟨_, inv_mem_intW D w s hs⟩ : intW D.what₂.places w) • D.nuIn u (s • φ) = D.nuIn u φ := by
    rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL s φ, map_smul, smul_smul]
    show (((s : D.what₂.LL))⁻¹ * (s : D.what₂.LL)) • D.nuIn u φ = D.nuIn u φ
    rw [inv_mul_cancel₀ hs0, one_smul]
  rw [h3] at h2
  exact h2

theorem period_integral_off_levelPrime {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : PairInt D Dx T) (hE : ErrDefs D L Xe lev K ce) (ht : Ties9 D L X Y c) (hS : c.NuServedDef X Y K)
    (hN : NuInM D L) (hGI : ServedHasModel X K) (hgain : GainLe X K) (h : WeilJacquetShalikaLaw.Conclusion1 D L X Y K c Dx T lev Xe ce 1) :
    ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
      D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) → ∀ φ : (D.div.Nu u).V, φ ∈ L.NuLat u →
      ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
        ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
          (y = 0 ∨ ur D w (L.sg u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro u w hw hgw φ hφ F hF1 hF0
  have hin : InNP X Y K c u w (D.nuIn u φ) := by
    by_cases hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅
    · exact Or.inr ⟨hVV, nuIn_mem_Sram_loc u w φ (hN u w hw) hφ⟩
    · refine Or.inl ⟨hGI u w hw hVV, (hS u w (hGI u w hw hVV) hVV φ).1 ⟨1, ?_, by simpa using hφ⟩⟩
      exact fun h1 => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hc := h ht hE u w hw hgw (D.what₂.muAt w) (WeilJacquetShalikaLaw.used_muAt D w) (Dx.Qp_muAt w) _ hin
  have hle : L.sg u w + vDG D u w ≤ totS X K Xe ce 1 u w := by
    unfold SizeData₂.sg totS ES
    rw [one_mul]
    refine add_le_add_left (Finset.sum_le_sum fun j hj => ?_) _
    rw [← hE.edef u j hj w]
    linarith [hgain w j hj]
  have h1 := period_ge hP hE.dgam u w hw φ _ _ (WeilJacquetShalikaLaw.used_muAt D w) (Dx.Qp_muAt w) (ColGe_mono hle hc) F hF1 hF0
  rw [add_sub_cancel_right] at h1
  exact h1

def PerColSmul (D : D7) : Prop :=
  ∀ u (μ : D.what₂.Tup) (c : ℂ) (φ : D.what₂.Mu u) (F : D.what₂.Amb μ), D.what₂.perCol u μ (c • φ) F = c * D.what₂.perCol u μ φ F

def SgAtG (D : D7) (L : SizeData₂ D) (Xe : ErrX D) (C1 : ℝ) : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i → ∀ u : D.what₂.Word,
    D.what₂.places.resChar w ≠ (D.mem u).A.T →
      (∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w)) ≤ -(∑ j ∈ Formalism.MainNotions.LiftErrorLocal.lifts D, vNN Xe i u j w) - C1 * Formalism.MainNotions.LiftErrorLocal.errC D L

theorem sg_atG (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)) :
    L.sg u w = ∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w) := by
  unfold SizeData₂.sg
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : L.gainD j w = 0 := by
    unfold SizeData₂.gainD
    split_ifs
    · rfl
    · exact L.gain_g j w hg
  rw [h0, zero_add]

theorem mem_gTypes_of (w : D.what₂.places.Pl) (i : Fin 2) (hi : D.what₂.places.resChar w = D.host.g i) :
    D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
  rw [hi]; fin_cases i <;> simp

theorem atG_core {Xe : ErrX D} {C1 C2 : ℝ} (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) (hS : SgAtG D L Xe C1) :
    ∀ u (w : D.what₂.places.Pl) (i : Fin 2), D.what₂.places.resChar w = D.host.g i → D.what₂.places.resChar w ≠ (D.mem u).A.T →
      ∀ φ : (D.div.Nu u).V, φ ∈ MramL D u → ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier,
        ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
          (y = 0 ∨ ur D w (∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w)) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro u w i hi hw φ hφ F hF
  obtain ⟨y, hy, hv⟩ := hCL.1 i w hi u hw (D.what₂.muAt w) φ hφ F hF
  refine ⟨y, hy, hv.imp_right fun hv => ?_⟩
  have he : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have hsg := hS i w hi u hw
  unfold Formalism.MainNotions.LiftErrorLocal.vG at hv
  unfold ur
  have h5 := le_trans hsg hv
  rw [le_div_iff₀ he] at h5
  linarith

theorem period_integral_at_typePrime {Xe : ErrX D} {C1 C2 : ℝ} (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) (hS : SgAtG D L Xe C1) (hN : NuInM D L)
    (hlin : PerColSmul D) :
    ∀ u (w : D.what₂.places.Pl) (i : Fin 2), D.what₂.places.resChar w = D.host.g i → D.what₂.places.resChar w ≠ (D.mem u).A.T →
      ∀ φ : (D.div.Nu u).V, φ ∈ L.NuLat u → ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier,
        ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
          (y = 0 ∨ ur D w (L.sg u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro u w i hi hw φ hφ F hF
  obtain ⟨s, hs, hm⟩ := hN u w hw φ hφ
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hm
  obtain ⟨y, hy, hv⟩ := atG_core hCL hS u w i hi hw (s • φ) hm F hF
  rw [sg_atG u w (mem_gTypes_of w i hi)]
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact Submodule.zero_mem _
  have hj : D.jN u (s • φ) = D.what₂.embLL (s : D.what₂.LL) • D.jN u φ := by
    rw [← algebraMap_smul D.what₂.LL s φ, LinearMap.map_smulₛₗ]
  rw [hj, hlin] at hy
  refine ⟨((s : D.what₂.LL))⁻¹ * y, ?_, ?_⟩
  · rw [map_mul, hy, map_inv₀, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 hs0), one_mul]
  · by_cases hy0 : y = 0
    · left; rw [hy0, mul_zero]
    right
    rcases hv with h0 | hv
    · exact absurd h0 hy0
    have hu : vAdd (D.plEq w) ((s : D.what₂.LL))⁻¹ = 0 := by
      have h1 : (D.plEq w).valuation D.what₂.LL (s : D.what₂.LL) = 1 := by
        have := (D.plEq w).valuation_of_algebraMap (K := D.what₂.LL) s
        rw [show (s : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL s from rfl, this]
        exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
      unfold vAdd
      rw [map_inv₀, h1]
      simp
    rw [Formalism.BasicNotions.SkeletonIndexLemmas.vAdd_mul (D.plEq w) (inv_ne_zero hs0) hy0, hu, zero_add]
    exact hv

theorem l2_bound_of_inputs {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hET : LevelPrimeSizes D L) (ht : Ties9 D L X Y c)
    (hS : c.NuServedDef X Y K) (hNT : NuAtTDef D L) (hN : NuInM D L) (hGI : ServedHasModel X K) (hgain : GainLe X K)
    (hG : LevelPrimeCoprimeStabiliser D) (h1 : WeilJacquetShalikaLaw.Conclusion1 D L X Y K c Dx T lev Xe ce 1) (h5 : ValuationAtLevelPrime D Dx T) {C1 C2 : ℝ}
    (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) (hSg : SgAtG D L Xe C1) (hlin : PerColSmul D) : L2BoundAlt D L := by
  refine Formalism.MainNotions.LocalQuadraticParts.valuation_bound_of_unrounded D L ?_
  intro u w φ hφ F hF1 hF0
  by_cases hw : D.what₂.places.resChar w = (D.mem u).A.T
  · exact period_integral_at_levelPrime hP.2 hE.dgam hET hNT hG h5 u w hw φ hφ F hF1 hF0
  · by_cases hg : D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)
    · have hi : ∃ i : Fin 2, D.what₂.places.resChar w = D.host.g i := by
        rcases Finset.mem_insert.1 hg with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, Finset.mem_singleton.1 h⟩
      obtain ⟨i, hi⟩ := hi
      exact period_integral_at_typePrime hCL hSg hN hlin u w i hi hw φ hφ F hF1
    · exact period_integral_off_levelPrime hP.1 hE ht hS hN hGI hgain h1 u w hw hg φ hφ F hF1 hF0

theorem fourth_complement_of_pairing {K : Consts} {Dx : DivX D} {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hF : L.FDef)
    (h : WeilJacquetShalikaLaw.ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce 1) {C1 C2 : ℝ} (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) (hSg : SgAtG D L Xe C1) :
    FourthComplement D L := by
  intro u w hw φ hφ F hF1 hF0
  by_cases hg : D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)
  · have hi : ∃ i : Fin 2, D.what₂.places.resChar w = D.host.g i := by
      rcases Finset.mem_insert.1 hg with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, Finset.mem_singleton.1 h⟩
    obtain ⟨i, hi⟩ := hi
    exact atG_core hCL hSg u w i hi hw φ hφ F hF1
  · exact stable_lattice_of_no_served_orbit hP.1 hE hF h u w hw hg φ hφ F hF1 hF0

theorem l2_bound_served {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C : ℝ}
    (hP : PairingAtEveryPlace D Dx T) (hS : Serv D L X Y K c Dx T lev Xe ce C) (hE : ErrDefs D L Xe lev K ce) (hET : LevelPrimeSizes D L)
    (ht : Ties9 D L X Y c) (hSd : c.NuServedDef X Y K) (hNT : NuAtTDef D L) (hN : NuInM D L)
    (hGI : ServedHasModel X K) (hF : ∀ w, ParametersFill X K w) (hcs : ∀ p : ℕ, p.Prime → IsCs D p → p ∈ L.drop)
    (hG : LevelPrimeCoprimeStabiliser D) (h5 : ValuationAtLevelPrime D Dx T) {C1 C2 : ℝ}
    (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) (hSg : SgAtG D L Xe C1) (hlin : PerColSmul D) :
    L2BoundAlt D L ∧ FourthComplement D L :=
  ⟨l2_bound_of_inputs hP hE hET ht hSd hNT hN hGI (gainLe_of_fills hF hcs) hG hS.2.1 h5 hCL hSg hlin, fourth_complement_of_pairing hP hE ht.fdef hS.2.2 hCL hSg⟩

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def familyL2Bound : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, L2BoundAlt (Fm.D x i) (Fm.L x i)

def familyFourthComplement : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, FourthComplement (Fm.D x i) (Fm.L x i)

def familyPairing : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), PairingAtEveryPlace (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

def familyPairingInputs : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    MemberChainIntegral (Fm.D x i) ∧ TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw ∧ PeriodClassSumWeyl (Fm.D x i) ∧
      TwistedPeriodIntegral (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

theorem stmtPairF (h : familyPairingInputs Fm) : familyPairing Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h1 i => stmtPair _ _ _ (h x hx h1 i).1 (h x hx h1 i).2.1 (h x hx h1 i).2.2.1 (h x hx h1 i).2.2.2⟩

def FamilyLevelPrimeInputs : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ValuationAtLevelPrime (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw ∧ LevelPrimeSizes (Fm.D x i) (Fm.L x i) ∧ LevelPrimeCoprimeStabiliser (Fm.D x i) ∧
      ServedHasModel (Fm.Gx x i) Fm.GK

def FamilyPeriodFormCond (C1 C2 : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2

def familySizeBoundAtTypePrime (C1 : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, SgAtG (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1

theorem l2_and_fourth_complement_family {C1 C2 : ℝ} (hP : familyPairing Fm) (hS : ServF Fm) (hT : FamilyLevelPrimeInputs Fm) (hCL : FamilyPeriodFormCond Fm C1 C2) (hSg : familySizeBoundAtTypePrime Fm C1)
    (hlin : ∀ x (i : Fm.Ix x), PerColSmul (Fm.D x i)) :
    familyL2Bound Fm ∧ familyFourthComplement Fm := by
  obtain ⟨a, hP⟩ := hP
  obtain ⟨C, _, b, hS⟩ := hS
  obtain ⟨c, hT⟩ := hT
  obtain ⟨d, hCL⟩ := hCL
  obtain ⟨e, hSg⟩ := hSg
  have key : ∀ x, max (max (max a b) c) (max d e) ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
      L2BoundAlt (Fm.D x i) (Fm.L x i) ∧ FourthComplement (Fm.D x i) (Fm.L x i) := by
    intro x hx h1 i
    simp only [max_le_iff] at hx
    obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd, he⟩ := hx
    obtain ⟨t5, tE, tG, tM⟩ := hT x hc h1 i
    exact l2_bound_served (hP x ha h1 i) (hS x hb h1 i) (Fm.ex x h1 i).err tE (local_compatibility_family Fm x h1 i)
      (Fm.ex x h1 i).lat.served (Fm.ex x h1 i).lat.atT (Fm.nuDef x h1 i).1 tM (Fm.fills x h1 i) (WeilJacquetShalikaLaw.isCs_drop Fm x h1 i) tG t5
      (hCL x h1 hd i) (hSg x h1 he i) (hlin x i)
  exact ⟨⟨_, fun x hx h1 i => (key x hx h1 i).1⟩, ⟨_, fun x hx h1 i => (key x hx h1 i).2⟩⟩

end Fam

end PartB

section PartC

open Formalism.BasicNotions NumberField

section Arch

variable {D : D7} {T : ThetaX D}

structure LocC (X : ZetaProductPairs.Loc D T) where

  Vc : D.what₂.Word → Type
  [acVc : ∀ u, AddCommGroup (Vc u)]
  [moVc : ∀ u, Module ℂ (Vc u)]

  VD : D.what₂.Word → Type
  [acVD : ∀ u, AddCommGroup (VD u)]
  [moVD : ∀ u, Module ℂ (VD u)]

  ell : ∀ u, Vc u →ₗ[ℂ] VD u →ₗ[ℂ] ℂ

  vOf : ∀ u, X.ArchDat u → Vc u

  TOf : ∀ u, X.ArchDat u → VD u

  ellT_eq : ∀ u da, X.ellT u da = ell u (vOf u da) (TOf u da)

  v_free : ∀ u (v : Vc u) (da : X.ArchDat u), ∃ da', vOf u da' = v ∧ TOf u da' = TOf u da

attribute [instance] LocC.acVc LocC.moVc LocC.acVD LocC.moVD

def Chain (T : ThetaX D) (P : TH.TPar D) (μ : ℕ → T.Chr) (π : Submodule ℂ (T.AF (T.Xs P.t 0)))
    (φ : T.AF (T.Xs P.t 0)) (F : ∀ j : ℕ, T.cusp (T.Ys P.t j))
    (Φ : ∀ j : ℕ, T.Sch (T.Ys P.t (j + 1)) (T.Ys P.t j)) : Prop :=
  CayleySignature.IsMu T P μ ∧ CayleySignature.IsAutRep T _ π ∧ π ≤ T.typeX P 0 ∧ φ ∈ π ∧
  CayleySignature.IsDv T P D.R.m (F D.R.m : T.AF (T.Ys P.t D.R.m)) ∧
  (∀ j : ℕ, j < D.R.m → Φ j ∈ T.fact _ _ ∧ Φ j ∈ T.kfin _ _ ∧
    ((F j : T.cusp (T.Ys P.t j)) : T.AF (T.Ys P.t j)) = CayleySignature.vth T P.t μ j (Φ j) (F (j + 1)) ∧
    CayleySignature.IsDv T P j (F j : T.AF (T.Ys P.t j)))

def ParametersPolynomiallyBounded (T : ThetaX D) : Prop := ∀ u, CayleySignature.Hyp3 T (T.parOf u)

def NonzeroBesselPeriodChain (D : D7) (T : ThetaX D) : Prop := CayleySignature.PointsLemma D T

def UnfoldingAnyLevel (X : ZetaProductPairs.Loc D T) : Prop :=
  ∀ u μ π φ F Φ (pos : T.Pos (T.Xs (T.parOf u).t 0) (T.Ys (T.parOf u).t 0) (T.iXYs (T.parOf u).t 0)),
    Chain T (T.parOf u) μ π φ F Φ → CayleySignature.bB T (T.parOf u).t 0 pos 0 φ (F 0) ≠ 0 →
    ∃ Xp Yp : ℂ, Xp ≠ 0 ∧ ∀ da, X.ellT u da * Xp = X.Au u da * Yp

def LinearFormNonzero {X : ZetaProductPairs.Loc D T} (Y : LocC X) : Prop := ∀ u, Y.ell u ≠ 0

def ThetaOntoKFinite {X : ZetaProductPairs.Loc D T} (Y : LocC X) : Prop := ∀ u, Submodule.span ℂ (Set.range (Y.TOf u)) = ⊤

def ArchimedeanNonvanishing (X : ZetaProductPairs.Loc D T) : Prop := Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing D T X

theorem ellT_ne {X : ZetaProductPairs.Loc D T} (Y : LocC X) (hE : LinearFormNonzero Y) (hT : ThetaOntoKFinite Y) (u : D.what₂.Word) :
    ∃ da, X.ellT u da ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hE u (LinearMap.ext fun v => ?_)
  refine LinearMap.ext_on (hT u) ?_
  rintro _ ⟨da, rfl⟩
  obtain ⟨da', h1, h2⟩ := Y.v_free u v da
  have := hcon da'
  rw [Y.ellT_eq, h1, h2] at this
  simpa using this

def AdmArch {X : ZetaProductPairs.Loc D T} (Y : LocC X) : Prop :=
  NonzeroBesselPeriodChain D T ∧ ParametersPolynomiallyBounded T ∧ UnfoldingAnyLevel X ∧ LinearFormNonzero Y ∧ ThetaOntoKFinite Y

theorem stmtArch {X : ZetaProductPairs.Loc D T} (Y : LocC X) (h : AdmArch Y) : ArchimedeanNonvanishing X := by
  obtain ⟨hS8, hPar, hUnf, hE, hT⟩ := h
  intro u
  obtain ⟨μ, π, φ, F, Φ, pos, h1, h2, h3, h4, h5, h6, hB⟩ := hS8 (T.parOf u) (hPar u)
  obtain ⟨Xp, Yp, hX, hU⟩ := hUnf u μ π φ F Φ pos ⟨h1, h2, h3, h4, h5, h6⟩ hB
  obtain ⟨da0, hda0⟩ := ellT_ne Y hE hT u
  have hY : Yp ≠ 0 := by
    intro h0
    have := hU da0
    rw [h0, mul_zero] at this
    exact mul_ne_zero hda0 hX this
  refine ⟨Xp / Yp, div_ne_zero hX hY, fun da => ?_, da0, hda0⟩
  rw [div_mul_eq_mul_div, eq_div_iff hY, ← hU da, mul_comm]

def ArchimedeanFromInputs {X : ZetaProductPairs.Loc D T} (Y : LocC X) : Prop := AdmArch Y → ArchimedeanNonvanishing X

end Arch

section Rat

variable (D : D7)

def RationalMapValues : Prop :=
  ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V), ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.Bu u (D.jN u φ) (D.jEE x)

def BkDef : Prop :=
  ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V) (y : D.what₂.LL),
    D.what₂.embLL y = D.what₂.Bu u (D.jN u φ) (D.jEE x) → D.div.Bk u φ x = y

def RationalFormOfMap : Prop := D.BuRational

theorem buR_iff : RationalFormOfMap D ↔ RationalMapValues D ∧ BkDef D := by
  constructor
  · intro h
    refine ⟨fun u φ x => ⟨_, (h u φ x).symm⟩, fun u φ x y hy => ?_⟩
    exact D.what₂.embLL.injective (by rw [hy, h u φ x])
  · rintro ⟨h1, h2⟩ u φ x
    obtain ⟨y, hy⟩ := h1 u φ x
    rw [h2 u φ x y hy, hy]

def PeriodRationalReference : Prop :=
  ∀ (u : D.what₂.Word), ∀ y ∈ (D.fm u).ramL, ∀ φ : D.what₂.Mu u,
    ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) = (D.fm u).emb 0 y →
    ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, ∃ x : D.what₂.LL, D.what₂.embLL x = D.what₂.perCol u D.what₂.mu0 φ F

def ExistsIntegralPlace (Z : DivX D) : Prop := ∀ u, ∃ w, ZetaProductPairs.IntPlace Z u D.what₂.mu0 w

theorem exists_integral_place (Z : DivX D) : ExistsIntegralPlace D Z := by
  intro u
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes ((D.mem u).A.T + D.host.g 0 + D.host.g 1 + D.host.d + 1)
  have : Fact p.Prime := ⟨hpp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hP, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.what₂.LL) (Ideal.span {(p : ℤ)})
  have hmem : (p : 𝓞 D.what₂.LL) ∈ P := by
    have : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 D.what₂.LL)) P := by
      show (p : ℤ) ∈ Ideal.under ℤ P
      rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  have hne : P ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hmem
    exact hpp.ne_zero (by exact_mod_cast hmem)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) := ⟨P, hP.isPrime, hne⟩
  have hr : D.what₂.places.resChar (D.plEq.symm v) = p := by
    rw [resChar_iff D p hpp, Equiv.apply_symm_apply]; exact hmem
  refine ⟨D.plEq.symm v, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; omega
  · rw [hr]; omega
  · rw [hr]; omega
  · rw [hr]; omega
  · rw [Z.degreeZero_partial_set_empty]; simp

variable {D} in
theorem referencePeriodRational_of_integral (Z : DivX D) (h : ZetaProductPairs.PeriodIntegrality Z) : PeriodRationalReference D := by
  intro u y hy φ hφ F hF
  obtain ⟨w, hw⟩ := exists_integral_place D Z u
  obtain ⟨x, hx, _⟩ := h u D.what₂.mu0 w (Or.inl rfl) hw y hy φ hφ F hF
  have hG : (((D.mem u).C.DGam : ℕ) : D.what₂.LL) ^ (D.R.m + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (D.mem u).C.DGam_pos.ne')
  have hG' : (((D.mem u).C.DGam : ℕ) : ℂ) ^ (D.R.m + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (D.mem u).C.DGam_pos.ne')
  refine ⟨x / (((D.mem u).C.DGam : ℕ) : D.what₂.LL) ^ (D.R.m + 1), ?_⟩
  rw [map_div₀, map_pow, map_natCast, hx, mul_div_cancel_left₀ _ hG']

def EEFormDef : Prop := Set.range D.jEE ⊆ AbsolutelyIrreducibleSpan.llSpan D.what₂.embLL (D.what₂.RRset D.what₂.mu0)

theorem iota_proj {R : Ranks} (E : Rows.Data R) (μ : E.Tup) (F : E.Amb μ) (hF : F ∈ E.V0 μ) :
    E.iota μ ((E.Qsp μ).starProjection F) = E.iota μ F := by
  set n : E.Amb μ := (E.Usp μ).starProjection F with hn
  have hnU : n ∈ E.Usp μ := Submodule.starProjection_apply_mem _ _
  have hq : F - n ∈ E.Qsp μ :=
    ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have hp : (E.Qsp μ).starProjection F = F - n := by
    apply Submodule.eq_starProjection_of_mem_orthogonal hq
    rw [sub_sub_cancel, Submodule.mem_orthogonal]
    intro q hq'
    exact inner_eq_zero_symm.mp (Submodule.inner_right_of_mem_orthogonal hnU hq'.2)
  rw [hp, map_sub, show E.iota μ n = 0 from hnU.2, sub_zero]

theorem Bu_add_left (u : D.what₂.Word) (G : D.what₂.EE) (a b : D.what₂.Mu u) :
    D.what₂.Bu u (a + b) G = D.what₂.Bu u a G + D.what₂.Bu u b G := (D.Bu_linL u G).map_add a b

theorem Bu_smul_left (u : D.what₂.Word) (G : D.what₂.EE) (c : ℂ) (a : D.what₂.Mu u) :
    D.what₂.Bu u (c • a) G = c * D.what₂.Bu u a G := (D.Bu_linL u G).map_smul c a

theorem Bu_zero_left (u : D.what₂.Word) (G : D.what₂.EE) : D.what₂.Bu u 0 G = 0 := (D.Bu_linL u G).map_zero

def AdmBuRat : Prop := PeriodRationalReference D ∧ EEFormDef D ∧ Rows.BuDef D.what₂

def RationalMapFromInputs : Prop := AdmBuRat D → RationalMapValues D

def RationalMapDefined : Prop := AdmBuRat D → BkDef D → RationalFormOfMap D

end Rat

section C5

theorem scalarUnitary_split {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V) (κ : ℂ) (hκ : κ ≠ 0)
    (h : ∀ x y : V, inner ℂ (A x) (A y) = ((‖κ‖ ^ 2 : ℝ) : ℂ) * inner ℂ x y) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ U : V ≃ₗᵢ[ℂ] V, ∀ x, A x = c • U x := by
  have hn : (‖κ‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hκ
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((‖κ‖ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by rw [hc]; exact Complex.ofReal_ne_zero.mpr hn
  have hcc : (starRingEnd ℂ) c⁻¹ = c⁻¹ := by
    rw [hc, ← Complex.ofReal_inv, Complex.conj_ofReal]
  have hsq : ((‖κ‖ ^ 2 : ℝ) : ℂ) = c * c := by rw [hc]; push_cast; ring
  have hB : ∀ x y, inner ℂ ((c⁻¹ • A) x) ((c⁻¹ • A) y) = inner ℂ x y := by
    intro x y
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, h, hcc, hsq]
    field_simp
  refine ⟨c, hc0, ((c⁻¹ • A).isometryOfInner hB).toLinearIsometryEquiv rfl, fun x => ?_⟩
  have hx : (((c⁻¹ • A).isometryOfInner hB).toLinearIsometryEquiv rfl) x = (c⁻¹ • A) x := rfl
  rw [hx, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hc0, one_smul]

theorem suShape_ne_zero {D : D7} (u : D.what₂.Word) (s : ℂ) (h : ZetaProductPairs.SuShape D u s) : s ≠ 0 :=
  ZetaProductPairs.suShape_ne_zero u s h

variable {D : D7} {T : ThetaX D}

def ScalarUnitaryRows (D : D7) : Prop := LocalQuadraticParts.adm13 D

theorem iota_ref_map_V0_eq_top (Z : DivX D) (h : InnerProductFormulaField.PointsLemma D Z) :
    (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨q, hq⟩ := (h D.what₂.mu0).1.2 x
  exact ⟨q.1, q.2.1, hq⟩

theorem fifth_complement_of_inputs (X : ZetaProductPairs.Loc D T)
    (h : ZetaProductPairs.MultiplicityOneWithZeta X) (hR : ZetaProductPairs.ExchangeOfPositions X) (hB : Rows.BuDefQ D.what₂) (hZ : ZetaProductPairs.ZeDef X)
    (hS : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤)
    (hA : ArchimedeanNonvanishing X) : ScalarUnitaryRows D := by
  have H := h hB hZ hS
  obtain ⟨_, U0, hU0⟩ := hR
  refine ⟨U0.symm, fun u => ?_⟩
  obtain ⟨hst, ⟨κ, κ0, hin⟩, _, s, hs, hc⟩ := H u
  obtain ⟨c, c0, hAu, hne⟩ := hA u
  obtain ⟨c', c'0, U, hU⟩ := scalarUnitary_split (ZetaProductPairs.FFm u hst) κ κ0 hin
  obtain ⟨Uu, κ', κ'0, hbes⟩ := hU0 u
  have ha : c * s⁻¹ ≠ 0 := mul_ne_zero c0 (inv_ne_zero (suShape_ne_zero u s hs))
  refine ⟨(c * s⁻¹)⁻¹ * c' * κ'⁻¹, mul_ne_zero (mul_ne_zero (inv_ne_zero ha) c'0) (inv_ne_zero κ'0),
    U.trans Uu.symm, fun φ F => ?_⟩
  rw [hbes, (hc c c0 hAu hne).1 φ F, hU, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  field_simp

theorem buDef_of (X : ZetaProductPairs.Loc D T)
    (h : ZetaProductPairs.MultiplicityOneWithZeta X) (hB : Rows.BuDefQ D.what₂) (hZ : ZetaProductPairs.ZeDef X)
    (hS : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤)
    (hA : ArchimedeanNonvanishing X) : Rows.BuDef D.what₂ := by
  intro u φ F hF
  obtain ⟨_, _, _, s, _, hc⟩ := h hB hZ hS u
  obtain ⟨c, c0, hAu, hne⟩ := hA u
  rw [(hc c c0 hAu hne).2 D.what₂.mu0 φ F hF, Rows.Data.zeC, D.what₂.rowsRest_wordColumnUnit_baseTuple, Units.val_one, map_one, one_mul]

def FifthComplementInputs (Z : DivX D) (X : ZetaProductPairs.Loc D T) : Prop :=
  ZetaProductPairs.MultiplicityOneWithZeta X ∧ ZetaProductPairs.ExchangeOfPositions X ∧ InnerProductFormulaField.PointsLemma D Z ∧ Rows.BuDefQ D.what₂ ∧ ZetaProductPairs.ZeDef X ∧ ArchimedeanNonvanishing X

theorem stmtC5' (Z : DivX D) (X : ZetaProductPairs.Loc D T) (h : FifthComplementInputs Z X) : ScalarUnitaryRows D :=
  fifth_complement_of_inputs X h.1 h.2.1 h.2.2.2.1 h.2.2.2.2.1 (iota_ref_map_V0_eq_top Z h.2.2.1) h.2.2.2.2.2

def FifthComplementFromInputs (Z : DivX D) (X : ZetaProductPairs.Loc D T) : Prop := FifthComplementInputs Z X → ScalarUnitaryRows D

end C5

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ZetaProductPairs.Loc (Fm.D x i) (Fm.ex x hx i).th)

def familyArchimedeanNonvanishing : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ArchimedeanNonvanishing (XF x hx i)

def AdmArchF (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocC (XF x hx i)) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AdmArch (YF x hx i)

theorem stmtArchF (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocC (XF x hx i)) (h : AdmArchF Fm XF YF) :
    familyArchimedeanNonvanishing Fm XF := fun x hx i => stmtArch (YF x hx i) (h x hx i)

def familyFifthComplement : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LocalQuadraticParts.adm13 (Fm.D x i)

def familyRationalMap : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, (Fm.D x i).BuRational

theorem fifth_complement_family_of_inputs (h : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FifthComplementInputs (Fm.X x i) (XF x hx i)) : familyFifthComplement Fm :=
  ⟨0, fun x _ hx i => stmtC5' (Fm.X x i) (XF x hx i) (h x hx i)⟩

end Family

end PartC

section PartE

open Formalism.BasicNotions NumberField IsDedekindDomain

structure LocE (D : D7) where

  mY : D.what₂.FT → ℕ

  mW : ℕ → D.what₂.FT → ℕ

  smallLevelDimension : D.what₂.FT → ℕ

section Lat

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end Lat

def Lmu (D : D7) (μ : D.what₂.Tup) : Submodule (𝓞 D.what₂.LL) D.div.RR.V :=
  Submodule.span (𝓞 D.what₂.LL) {y | D.jEE y ∈ D.what₂.RRset μ}

def IsFullL (D : D7) (A : Submodule (𝓞 D.what₂.LL) D.div.RR.V) : Prop :=
  A.FG ∧ Submodule.span D.what₂.LL (A : Set D.div.RR.V) = ⊤

def InRR (D : D7) (μ : D.what₂.Tup) : Prop := LocalQuadraticParts.UsedT D μ

def TwFin (D : D7) : Prop := {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite

def TuplesInRowRangeAll (D : D7) : Prop := ∀ μ, InRR D μ → D.what₂.RRset μ ⊆ Set.range D.jEE

def IotaSurjective (D : D7) : Prop :=
  ∀ μ, InRR D μ → Function.Surjective ((D.what₂.iota μ).domRestrict (D.what₂.Qsp μ))

def FullRowLattices (D : D7) : Prop := ∀ μ, InRR D μ → IsFullL D (Lmu D μ)

def FullLatticesFromInputs (D : D7) : Prop := TuplesInRowRangeAll D → IotaSurjective D → Rows.AIntegral D.what₂ → FullRowLattices D

def RowLatticeFull (D : D7) : Prop := D.RRFull

def RowRankFromLattices (D : D7) : Prop := DV.RRDef D → TwFin D → FullRowLattices D → RowLatticeFull D

section Form

variable {K : Type} [Field K] {σ : K →+* ℂ} {V : Type} [AddCommGroup V] [Module K V]
  {E : Type} [AddCommGroup E] [Module ℂ E] {ι : Type} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K V) (j : V →ₛₗ[σ] E)

theorem form_expand (v : V) : j v = ∑ i, σ (b.repr v i) • j (b i) := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, LinearMap.map_smulₛₗ]

theorem form_inj (hli : LinearIndependent ℂ (fun i => j (b i))) : Function.Injective j := by
  intro x y hxy
  have h0 : j (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [form_expand b j] at h0
  have h3 := Fintype.linearIndependent_iff.1 hli (fun i => σ (b.repr (x - y) i)) h0
  have h4 : b.repr (x - y) = 0 := Finsupp.ext fun i => (map_eq_zero σ).1 (h3 i)
  exact sub_eq_zero.1 (b.repr.map_eq_zero_iff.1 h4)

theorem form_span_top (hli : LinearIndependent ℂ (fun i => j (b i)))
    (hsp : Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) (U : Submodule K V)
    (hU : Submodule.span ℂ (j '' (U : Set V)) = ⊤) : U = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfU⟩ := Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.2 hne)
  let B : Module.Basis ι ℂ E := Module.Basis.mk hli hsp.ge
  let F : E →ₗ[ℂ] ℂ := B.constr ℂ (fun i => σ (f (b i)))
  have hFb : ∀ i, F (j (b i)) = σ (f (b i)) := by
    intro i
    have := B.constr_basis ℂ (fun i => σ (f (b i))) i
    rwa [Module.Basis.mk_apply] at this
  have hF : ∀ v, F (j v) = σ (f v) := by
    intro v
    rw [form_expand b j v]
    conv_rhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, smul_eq_mul, map_mul, hFb]
  have hF0 : F = 0 := LinearMap.ext_on hU (by
    rintro _ ⟨v, hv, rfl⟩
    have : f v = 0 := hfU hv
    rw [hF, this]; simp)
  apply hf0
  refine b.ext fun i => ?_
  have := hFb i
  rw [hF0] at this
  simpa using this.symm

end Form

theorem gen_mem {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V)
    (g : V) (hg : g ∈ L.gen) : g ∈ L.carrier := by
  classical
  refine ⟨fun v => if v = g then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single g]
  · simp
  · intro v _ hv; simp [hv]
  · intro h; exact absurd hg h

section Side

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

def LmuS (μ : D.what₂.Tup) : Submodule (𝓞 D.what₂.LL) S.RR.V :=
  Submodule.span (𝓞 D.what₂.LL) {y | S.jEE y ∈ S.RRset μ}

def TuplesInRowRange : Prop := ∀ μ, InRR D μ → S.RRset μ ⊆ Set.range S.jEE

def LevelIotaSurjective : Prop := ∀ μ, InRR D μ → Function.Surjective (S.iotaQ μ)

def FullRowLatticeSide : Prop :=
  ∀ μ, InRR D μ → (LmuS S μ).FG ∧ Submodule.span D.what₂.LL (LmuS S μ : Set S.RR.V) = ⊤

def FullLatticesFromInputsSide : Prop := TuplesInRowRange S → LevelIotaSurjective S → S.AIntegral → FullRowLatticeSide S

theorem stmtRRlatS : FullLatticesFromInputsSide S := by
  intro ha hc hA μ hμ
  classical
  have hG : (D.what₂.restRowsFiniteGroupCard : ℂ) ≠ 0 := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos.ne'
  let Tl : S.Amb μ →ₗ[ℂ] EE := S.iota μ ∘ₗ ((S.Qsp μ).starProjection : S.Amb μ →L[ℂ] S.Amb μ).toLinearMap
  have hRR : ∀ x, x ∈ (S.Mtilde μ).carrier → x ∈ S.V0 μ → Tl x ∈ S.RRset μ :=
    fun x h1 h2 => ⟨_, ⟨x, ⟨h1, h2⟩, rfl⟩, rfl⟩
  have h1 : ∀ g ∈ (S.Mtilde μ).gen, Tl ((D.what₂.restRowsFiniteGroupCard : ℂ) • S.eOp μ g) ∈ S.RRset μ := fun g hg =>
    hRR _ (hA μ g (gen_mem _ g hg)) ((S.V0 μ).smul_mem _ (LinearMap.mem_range_self _ g))
  have h2 : ∀ g ∈ (S.Mtilde μ).gen, ∃ y : S.RR.V, S.jEE y = Tl ((D.what₂.restRowsFiniteGroupCard : ℂ) • S.eOp μ g) :=
    fun g hg => ha μ hμ (h1 g hg)
  choose! y hy using h2
  have hyL : ∀ g ∈ (S.Mtilde μ).gen, y g ∈ LmuS S μ := fun g hg =>
    Submodule.subset_span (by show S.jEE (y g) ∈ S.RRset μ; rw [hy g hg]; exact h1 g hg)
  have hinj := form_inj S.RR.b S.jEE S.jEE_basis.1
  have hTe : ∀ g ∈ (S.Mtilde μ).gen, Tl (S.eOp μ g) = S.jEE (((D.what₂.restRowsFiniteGroupCard : D.what₂.LL))⁻¹ • y g) := by
    intro g hg
    rw [LinearMap.map_smulₛₗ, hy g hg, map_smul, map_inv₀, map_natCast, smul_smul, inv_mul_cancel₀ hG, one_smul]
  refine ⟨?_, ?_⟩
  · let W : Submodule (𝓞 D.what₂.LL) S.RR.V :=
      Submodule.span (𝓞 D.what₂.LL) ((fun g => ((D.what₂.restRowsFiniteGroupCard : D.what₂.LL))⁻¹ • y g) '' ((S.Mtilde μ).gen : Set (S.Amb μ)))
    have hW : W.FG := Submodule.fg_span (Set.Finite.image _ (S.Mtilde μ).gen.finite_toSet)
    have hle : LmuS S μ ≤ W := by
      refine Submodule.span_le.2 ?_
      rintro z ⟨_, ⟨x, ⟨⟨c, hx⟩, ⟨x', hx'⟩⟩, rfl⟩, hz⟩
      have hex : S.eOp μ x = x := by
        rw [← hx']; exact LinearMap.congr_fun (S.eOp_idem μ) x'
      have hz' : S.jEE z = Tl (S.eOp μ x) := by rw [hex]; exact hz.symm
      have hsum : Tl (S.eOp μ x) = S.jEE (∑ g ∈ (S.Mtilde μ).gen,
          D.what₂.OtoLL (c g) • (((D.what₂.restRowsFiniteGroupCard : D.what₂.LL))⁻¹ • y g)) := by
        rw [hx, map_sum, map_sum, map_sum]
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [map_smul, map_smul, hTe g hg]
        simp only [LinearMap.map_smulₛₗ]
        rfl
      have hzz := hinj (hz'.trans hsum)
      show z ∈ W
      rw [hzz]
      refine W.sum_mem fun g hg => ?_
      have := IsIntegralClosure.algebraMap_mk' (𝓞 D.what₂.LL) (D.what₂.OtoLL (c g)) (D.O_int (c g))
      rw [← this, IsScalarTower.algebraMap_smul]
      exact W.smul_mem _ (Submodule.subset_span ⟨g, hg, rfl⟩)
    have : IsNoetherian (𝓞 D.what₂.LL) W := isNoetherian_of_fg_of_noetherian W hW
    exact isNoetherian_submodule.mp this _ hle
  · refine form_span_top S.RR.b S.jEE S.jEE_basis.1 S.jEE_basis.2 _ ?_
    rw [eq_top_iff]
    intro v _
    obtain ⟨⟨q, hq⟩, hqv⟩ := hc μ hμ v
    have hqv' : S.iota μ q = v := hqv
    have hq0 : q ∈ S.V0 μ := hq.1
    obtain ⟨q', hq'⟩ := hq0
    have heq : S.eOp μ q = q := by rw [← hq']; exact LinearMap.congr_fun (S.eOp_idem μ) q'
    have hpq : (S.Qsp μ).starProjection q = q := (Submodule.starProjection_eq_self_iff).2 hq
    have hv : v = (Tl ∘ₗ S.eOp μ) q := by
      show v = S.iota μ ((S.Qsp μ).starProjection (S.eOp μ q))
      rw [heq, hpq, hqv']
    have hqs : q ∈ Submodule.span ℂ ((S.Mtilde μ).gen : Set (S.Amb μ)) := by rw [(S.Mtilde μ).span_top]; trivial
    have : (Tl ∘ₗ S.eOp μ) q ∈ Submodule.map (Tl ∘ₗ S.eOp μ) (Submodule.span ℂ ((S.Mtilde μ).gen : Set (S.Amb μ))) :=
      Submodule.mem_map_of_mem hqs
    rw [Submodule.map_span] at this
    rw [hv]
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨g, hg, rfl⟩
    show Tl (S.eOp μ g) ∈ _
    rw [hTe g hg]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hyL g hg))

end Side

def SmallLevelRowLatticeFull {D : D7} (P : BaseLevelRowSide D) : Prop := P.BaseRowLatticeFull

theorem stmtRRlat (D : D7) : FullLatticesFromInputs D := by
  intro ha hc hA μ hμ
  have h := stmtRRlatS (RowSide.sharp D) (fun μ hμ => by rw [AbsolutelyIrreducibleSpan.sharp_RRset]; exact ha μ hμ) (fun μ hμ v => by
      obtain ⟨⟨q, hq⟩, hqv⟩ := hc μ hμ v
      have hqv' : D.what₂.iota μ q = v := hqv
      refine ⟨⟨q, by rw [AbsolutelyIrreducibleSpan.sharp_Qsp]; exact hq⟩, ?_⟩
      show (RowSide.sharp D).iota μ q = v
      rw [AbsolutelyIrreducibleSpan.sharp_iota]; exact hqv') hA μ hμ
  unfold LmuS at h
  simp only [AbsolutelyIrreducibleSpan.sharp_RRset] at h
  exact h

def RowLatticeRankPos (D : D7) : Prop := 0 < D.div.RR.rank

theorem Drows_pos_of (D : D7) (h1 : D.what₂.delp < 1) (h2 : 0 < D.what₂.Dall) : 0 < D.what₂.Drows := by
  have h := D.what₂.D_eq
  have h3 : (0 : ℝ) < (D.what₂.Dall : ℝ) := by exact_mod_cast h2
  have h4 : (0 : ℝ) < (D.what₂.Drows : ℝ) := by rw [h]; exact mul_pos (by linarith) h3
  exact_mod_cast h4

theorem rowLatticeRank_pos_of (D : D7) (hF : D.RRFull) (h1 : D.what₂.delp < 1) (h2 : 0 < D.what₂.Dall) : RowLatticeRankPos D := by
  have h := hF.rank
  unfold DivData.Drows at h
  unfold RowLatticeRankPos
  rw [h]
  exact Drows_pos_of D h1 h2

theorem sideNe_of {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (hF : S.RRFull) (hE : ∃ v : EE, v ≠ 0) : S.RR.L ≠ ⊥ := by
  intro h0
  obtain ⟨v, hv⟩ := hE
  have htop : (⊤ : Submodule D.what₂.LL S.RR.V) = ⊥ := by
    rw [← hF.2, h0]; simp
  have hz : ∀ x : S.RR.V, x = 0 := fun x => by
    have hx : x ∈ (⊤ : Submodule D.what₂.LL S.RR.V) := Submodule.mem_top
    rw [htop] at hx
    exact (Submodule.mem_bot _).1 hx
  have hsub : (Set.range fun i => S.jEE (S.RR.b i)) ⊆ {0} := by
    rintro _ ⟨i, rfl⟩
    simp [hz (S.RR.b i)]
  have hv' : v ∈ Submodule.span ℂ (Set.range fun i => S.jEE (S.RR.b i)) := by
    rw [S.jEE_basis.2]; exact Submodule.mem_top
  have h1 := Submodule.span_mono hsub hv'
  rw [Submodule.span_zero_singleton] at h1
  exact hv ((Submodule.mem_bot ℂ).1 h1)

theorem rrNe_of (D : D7) (hF : D.RRFull) (h : 0 < D.what₂.Drows) : D.div.RR.L ≠ ⊥ :=
  sideNe_of (RowSide.sharp D) hF ⟨D.what₂.onb ⟨0, h⟩, D.what₂.onb.orthonormal.ne_zero _⟩

theorem smallRowLattice_ne_bot {D : D7} (P : BaseLevelRowSide D) (hF : P.BaseRowLatticeFull) (h : 0 < D.what₂.D0) : P.principalHermitianLattice.L ≠ ⊥ :=
  sideNe_of P.s hF ⟨D.what₂.onb0 ⟨0, h⟩, D.what₂.onb0.orthonormal.ne_zero _⟩

def SmallLevelExtremalVectors (D : D7) (X : LocE D) : Prop := ∀ π, D.what₂.nRows0 π = X.mY π * X.smallLevelDimension π

def HolomorphicLowestVectors (D : D7) (X : LocE D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π, Module.finrank ℂ (D.what₂.isot j π) = X.mW j π * X.smallLevelDimension π

def MultiplicityTransfer (D : D7) (X : LocE D) : Prop := ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π, X.mW j π = X.mY π

def IsotypicRankTransfer (D : D7) : Prop := Rows.IsotRank D.what₂

theorem isotypicRank_of_transfer (D : D7) (X : LocE D) (h1 : SmallLevelExtremalVectors D X) (h2 : HolomorphicLowestVectors D X) (h : MultiplicityTransfer D X) : IsotypicRankTransfer D := by
  intro j hj1 hj2 π
  rw [h2 j hj1 hj2 π, h j hj1 hj2 π, h1 π]

def IsotypicInternalDecomp (D : D7) : Prop := Rows.IsotInternal D.what₂

def MjRankSmallLevel (D : D7) (Z : DivX D) : Prop := DV.MjRank D Z

theorem sum_nRows0 (D : D7) : ∑ π, D.what₂.nRows0 π = D.what₂.D0 := by
  unfold Rows.Data.nRows0
  rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]

theorem finrank_Mj_of (D : D7) (hR : IsotypicRankTransfer D) (hI : IsotypicInternalDecomp D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Module.finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  have e := LinearEquiv.ofBijective (DirectSum.coeLinearMap (D.what₂.isot j)) (hI j h1 h2)
  rw [← e.finrank_eq, Module.finrank_directSum, ← sum_nRows0 D]
  exact Finset.sum_congr rfl fun π _ => hR j h1 h2 π

theorem mjRank_of_transfer (D : D7) (Z : DivX D) (hR : IsotypicRankTransfer D) (hI : IsotypicInternalDecomp D) : MjRankSmallLevel D Z := by
  intro j h1 h2
  have hb := Z.jM_basis j
  have e1 : Module.finrank ℂ (D.what₂.Mj j) = Fintype.card (Z.MjH j).ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk hb.1 hb.2.ge)
  have e2 : (Z.MjH j).rank = Fintype.card (Z.MjH j).ι := by
    unfold HLat.rank Formalism.HN.rkK
    rw [(Z.MjH_good j).2.2, finrank_top]
    exact Module.finrank_eq_card_basis (Z.MjH j).b
  rw [e2, ← e1, finrank_Mj_of D hR hI j h1 h2]

def TypeOccursSmallLevel (D : D7) : Prop := ∀ σ : Fin D.what₂.Drows, 0 < D.what₂.nRows0 (D.what₂.ft σ)

theorem typeOccursSmallLevel_of_lemma (D : D7) (C : ℝ) (h : Formalism.BasicNotions.Lemma3 D C) : TypeOccursSmallLevel D := by
  obtain ⟨n, _, h2, _⟩ := h
  exact fun σ => h2 _

theorem smallRows_pos_of (D : D7) (h : TypeOccursSmallLevel D) (hD : 0 < D.what₂.Drows) : 0 < D.what₂.D0 := by
  have h1 := h ⟨0, hD⟩
  unfold Rows.Data.nRows0 at h1
  obtain ⟨⟨σ, _⟩⟩ := Fintype.card_pos_iff.1 h1
  exact lt_of_le_of_lt (Nat.zero_le _) σ.2

def ThetaEquivariantIdempotent (D : D7) : Prop :=
  ∀ μ, ∀ j ∈ SizeData₂.lifts D, D.what₂.thetaP μ j ∘ₗ D.what₂.eMt μ j = D.what₂.thetaP μ j

def ThetaInIdempotentImage (D : D7) : Prop :=
  ∀ μ, ∀ j ∈ SizeData₂.lifts D, LinearMap.range (D.what₂.thetaT μ j) ≤ LinearMap.range (D.what₂.eMt μ j)

theorem thetaInImage_of_equivariant (D : D7) (h : ThetaEquivariantIdempotent D) : ThetaInIdempotentImage D := by
  intro μ j hj y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨D.what₂.thetaT μ j x, ?_⟩
  refine ext_inner_right ℂ fun z => ?_
  have hs := D.what₂.eMt_sa μ j
  rw [hs (D.what₂.thetaT μ j x) z]
  unfold Rows.Data.thetaT
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  have := LinearMap.congr_fun (h μ j hj) z
  rw [LinearMap.comp_apply] at this
  rw [this]

def CentralElementPreserves (D : D7) : Prop :=
  ∀ μ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))),
    (∀ g, (z : MonoidAlgebra ℂ (G0g D.nd)).coeff g ∈ Set.range D.what₂.phiO) →
    ∀ x ∈ (D.what₂.Mtilde μ).carrier, D.ntypes.cenAmb μ z x ∈ (D.what₂.Mtilde μ).carrier

def CentralIdempotentIntegralAlt (D : D7) : Prop :=
  D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) ∧
  ∀ g, ((D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0).coeff g ∈ Set.range D.what₂.phiO

def IdempotentIntegral (D : D7) : Prop := Rows.AIntegral D.what₂

theorem center_smul_mem_Mtilde (D : D7) (h1 : CentralElementPreserves D) (E : MonoidAlgebra ℂ (G0g D.nd))
    (hE : E ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (c : ℂ)
    (hc : ∀ g, (c • E).coeff g ∈ Set.range D.what₂.phiO) (μ : D.what₂.Tup) (x : D.what₂.Amb μ)
    (hx : x ∈ (D.what₂.Mtilde μ).carrier) : c • D.ntypes.onAmb μ E x ∈ (D.what₂.Mtilde μ).carrier := by
  have h3 := h1 μ (c • ⟨E, hE⟩) hc x hx
  rw [map_smul, LinearMap.smul_apply] at h3
  unfold NTypes.onAmb
  rw [dif_pos hE]
  exact h3

theorem idempotentIntegral_of (D : D7) (h1 : CentralElementPreserves D) (h2 : CentralIdempotentIntegralAlt D) : IdempotentIntegral D := by
  intro μ x hx
  rw [D.nStage_trivialCharacter_compat.1 μ]
  exact center_smul_mem_Mtilde D h1 _ h2.1 _ h2.2 μ x hx

section SideAI

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

def CentralElementPreservesSide : Prop :=
  ∀ μ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))),
    (∀ g, (z : MonoidAlgebra ℂ (G0g D.nd)).coeff g ∈ Set.range D.what₂.phiO) →
    ∀ x ∈ (S.Mtilde μ).carrier, S.cen μ z x ∈ (S.Mtilde μ).carrier

theorem center_smul_mem_lattice (h1 : CentralElementPreservesSide S) (E : MonoidAlgebra ℂ (G0g D.nd))
    (hE : E ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (c : ℂ)
    (hc : ∀ g, (c • E).coeff g ∈ Set.range D.what₂.phiO) (μ : D.what₂.Tup) (x : S.Amb μ)
    (hx : x ∈ (S.Mtilde μ).carrier) : c • S.cen μ ⟨E, hE⟩ x ∈ (S.Mtilde μ).carrier := by
  have h3 := h1 μ (c • ⟨E, hE⟩) hc x hx
  rw [map_smul, LinearMap.smul_apply] at h3
  exact h3

theorem idempotentIntegral_side_of (h1 : CentralElementPreservesSide S) (h2 : CentralIdempotentIntegralAlt D) : S.AIntegral := by
  intro μ x hx
  rw [S.eOp_tie μ, dif_pos h2.1]
  exact center_smul_mem_lattice S h1 _ h2.1 _ h2.2 μ x hx

end SideAI

def SmallIdempotentIntegral {D : D7} (P : BaseLevelRowSide D) : Prop := P.s.AIntegral

theorem smallIdempotentIntegral_of {D : D7} (P : BaseLevelRowSide D) (h1 : CentralElementPreservesSide P.s) (h2 : CentralIdempotentIntegralAlt D) : SmallIdempotentIntegral P := idempotentIntegral_side_of P.s h1 h2

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem twFin_of (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : TwFin (Fm.D x i) :=
  (Fm.L x i).supp.finite_toSet.subset fun w hw => Fm.tw_supp x hx i w hw

def EvE (P : ∀ x, Fm.Ix x → Prop) : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, P x i

def familyFullLattices : Prop := EvE Fm fun x i => FullRowLattices (Fm.D x i)
def familyRowLatticeFull : Prop := EvE Fm fun x i => (Fm.D x i).RRFull
def familyRowRankPos : Prop := EvE Fm fun x i => 0 < (Fm.D x i).div.RR.rank
def familyTransfer : Prop := EvE Fm fun x i => Rows.IsotRank (Fm.D x i).what₂ ∧ Rows.IsotInternal (Fm.D x i).what₂
def familyThetaInImage : Prop := EvE Fm fun x i => ThetaInIdempotentImage (Fm.D x i)
def familyIdempotentIntegral : Prop := EvE Fm fun x i => Rows.AIntegral (Fm.D x i).what₂
def familyMjRank : Prop := EvE Fm fun x i => DV.MjRank (Fm.D x i) (Fm.X x i)
def familyTypeOccurs : Prop := EvE Fm fun x i => TypeOccursSmallLevel (Fm.D x i)

def familySmallLevelIntegral : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, (Fm.ex x hx i).p0.s.AIntegral

theorem familyMjRank_of_transfer (h : familyTransfer Fm) : familyMjRank Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h1 i => mjRank_of_transfer _ _ (h x hx h1 i).1 (h x hx h1 i).2⟩

theorem familyThetaInImage_of (h : EvE Fm fun x i => ThetaEquivariantIdempotent (Fm.D x i)) : familyThetaInImage Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h1 i => thetaInImage_of_equivariant _ (h x hx h1 i)⟩

theorem familyIdempotentIntegral_of (h : EvE Fm fun x i => CentralElementPreserves (Fm.D x i) ∧ CentralIdempotentIntegralAlt (Fm.D x i)) : familyIdempotentIntegral Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h1 i => idempotentIntegral_of _ (h x hx h1 i).1 (h x hx h1 i).2⟩

theorem familySmallIntegral_of (h : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x,
    CentralElementPreservesSide (Fm.ex x hx i).p0.s ∧ CentralIdempotentIntegralAlt (Fm.D x i)) : familySmallLevelIntegral Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h1 i => idempotentIntegral_side_of _ (h x hx h1 i).1 (h x hx h1 i).2⟩

def FamilyRowRankFromLattices : Prop := familyFullLattices Fm → familyRowLatticeFull Fm

def familySmallFullLattices : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, FullRowLatticeSide (Fm.ex x hx i).p0.s

def familySmallRowLatticeFull : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, (Fm.ex x hx i).p0.BaseRowLatticeFull

theorem familyFullLattices_of (h : EvE Fm fun x i => TuplesInRowRangeAll (Fm.D x i) ∧ IotaSurjective (Fm.D x i) ∧ Rows.AIntegral (Fm.D x i).what₂) :
    familyFullLattices Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h1 i => stmtRRlat _ (h x hx h1 i).1 (h x hx h1 i).2.1 (h x hx h1 i).2.2⟩

theorem familySmallFullLattices_of (h : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x,
    TuplesInRowRange (Fm.ex x hx i).p0.s ∧ LevelIotaSurjective (Fm.ex x hx i).p0.s ∧ (Fm.ex x hx i).p0.s.AIntegral) : familySmallFullLattices Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h1 i => stmtRRlatS _ (h x hx h1 i).1 (h x hx h1 i).2.1 (h x hx h1 i).2.2⟩

end Fam

end PartE

section PartEJ

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem tuplesInRowRange_side_of (D : D7) {V : AbsolutelyIrreducibleSpan.Lev D} {A : Formalism.BasicNotions.AmbForm D V.S} (X : AbsolutelyIrreducibleSpan.LocV D V A) (h1 : AbsolutelyIrreducibleSpan.Conclusion1 D X) (hR : AbsolutelyIrreducibleSpan.RRDef D X) :
    TuplesInRowRange V.S := by
  intro μ hμ y hy
  have hU : AbsolutelyIrreducibleSpan.Used D μ := by
    rcases hμ with h | ⟨w, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, h⟩
  have h2 := h1.2.2.1 μ hU hy
  rw [← hR.1] at h2
  exact h2

theorem tuplesInRowRange_of (D : D7) {A : Formalism.BasicNotions.AmbForm D (RowSide.sharp D)} (X : AbsolutelyIrreducibleSpan.Loc D A) (h1 : AbsolutelyIrreducibleSpan.Conclusion1 D X) (hR : AbsolutelyIrreducibleSpan.RRDef D X) : TuplesInRowRangeAll D := by
  intro μ hμ
  have := tuplesInRowRange_side_of D X h1 hR μ hμ
  rw [← AbsolutelyIrreducibleSpan.sharp_RRset]
  exact this

theorem iotaSurjective_of (D : D7) (Z : DivX D) (h : InnerProductFormulaField.PointsLemma D Z) : IotaSurjective D := fun μ _ => (h μ).1.2

end PartEJ

section PartF

open Formalism.BasicNotions Formalism.BasicNotions.DV

variable (D : D7)

variable {D} in
theorem onRj_nonneg {fl : ℕ → ℕ → ℝ} {r : ℕ → D.what₂.places.Pl → ℝ} (h1 : ∀ j l, 0 ≤ fl j l) (h2 : ∀ j w, 0 ≤ r j w)
    (j : ℕ) (w : D.what₂.places.Pl) : 0 ≤ PDVN.onRj D fl r j w :=
  add_nonneg (h1 _ _) (div_nonneg (add_nonneg (h2 _ _) (h2 _ _)) (Nat.cast_nonneg _))

def onCore (L : SizeData₂ D) : ℝ :=
  L.sc.L * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) * PDVN.wMax D + (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * Real.log L.sc.x

theorem onBoundJ_eq (L : SizeData₂ D) (C : ℝ) : PDVN.onBoundJ D L C = C * onCore D L := rfl

theorem onBound_eq (L : SizeData₂ D) (C : ℝ) : PDVN.onBound D L C = C * (D.R.m : ℝ) * onCore D L := rfl

def JB (L : SizeData₂ D) (CJ A : ℝ) : ℝ :=
  CJ * (D.host.T2.card : ℝ) * (D.R.m : ℝ) * L.sc.b * L.sc.x ^ (2 * L.sc.eps) + A * (D.R.m : ℝ) * L.sc.b

def admJ (L : SizeData₂ D) (X : LocalQuadraticParts.Loc D) (CJ A : ℝ) : Prop :=
  (∀ j w, 0 ≤ X.Jx j w) ∧ ∀ j ∈ SizeData₂.lifts D, ∀ T : Finset D.what₂.places.Pl,
    ∑ w ∈ T, SizeData₂.lwP w * ur D w (X.Jx j w) ≤ JB D L CJ A

def JTie (X : LocalQuadraticParts.Loc D) (J : ℕ → ℕ → ℕ) : Prop := ∀ j w, X.Jx j w = (J j (D.what₂.places.resChar w) : ℝ)

def JSum (L : SizeData₂ D) (J : ℕ → ℕ → ℕ) (CJ A : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ n : ℕ, ∑ l ∈ JumpSetsAlt.primesUpTo n, (J j l : ℝ) * Real.log l ≤ JB D L CJ A

def FibreLe : Prop := ∀ (p : ℕ), p.Prime → ∀ S : Finset D.what₂.places.Pl,
  (∀ w ∈ S, D.what₂.places.resChar w = p) → ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) ≤ Real.log p

theorem fibreLe : FibreLe D := by
  classical
  intro p hp S hS
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  have h1 : ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) =
      ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v * (eWL D.what₂.LL v : ℝ) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [D.ram_eq w]; rfl
  have hsub : S.map D.plEq.toEmbedding ⊆ T := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
    rw [hT]
    have := resChar_mem D w
    rw [hS w hw] at this
    exact this
  rw [h1, ← sum_lw_e p hp T hT]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => mul_nonneg ?_ (Nat.cast_nonneg _))
  unfold lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

variable {D} in
theorem exponentCond_of_sum {L : SizeData₂ D} {X : LocalQuadraticParts.Loc D} {J : ℕ → ℕ → ℕ} {CJ A : ℝ} (hF : FibreLe D) (hT : JTie D X J)
    (hS : JSum D L J CJ A) : admJ D L X CJ A := by
  classical
  refine ⟨fun j w => by rw [hT]; exact Nat.cast_nonneg _, fun j hj T => ?_⟩
  set n := T.sup D.what₂.places.resChar with hn
  refine le_trans ?_ (hS j hj n)
  have hmap : ∀ w ∈ T, D.what₂.places.resChar w ∈ JumpSetsAlt.primesUpTo n := fun w hw => by
    unfold JumpSetsAlt.primesUpTo
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := D.what₂.places.resChar) hw), D.what₂.places.resChar_prime w⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_le_sum fun l hl => ?_
  have hlp : l.Prime := by
    unfold JumpSetsAlt.primesUpTo at hl
    exact (Finset.mem_filter.1 hl).2
  have h1 : ∑ w ∈ T.filter (fun w => D.what₂.places.resChar w = l), SizeData₂.lwP w * ur D w (X.Jx j w) =
      (J j l : ℝ) * ∑ w ∈ T.filter (fun w => D.what₂.places.resChar w = l),
        SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hT, (Finset.mem_filter.1 hw).2]
    unfold ur; ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left (hF l hlp _ fun w hw => (Finset.mem_filter.1 hw).2) (Nat.cast_nonneg _)

def OntoSizeBound (L : SizeData₂ D) (C Cabs : ℝ) : Prop :=
  onCore D L ≤ C * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc)

def ExponentSumSize (L : SizeData₂ D) (CJ A C Cabs : ℝ) : Prop :=
  JB D L CJ A ≤ C * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc)

def admW (L : SizeData₂ D) : Prop := PDVN.wMax D ≤ 2 * (D.R.f : ℝ) * L.sc.b

theorem x_pos (L : SizeData₂ D) : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt

theorem B_zero_shape_eq_index (L : SizeData₂ D) : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.x ^ L.sc.eps := rfl

theorem Nc_nonneg (L : SizeData₂ D) : 0 ≤ L.Nc := by
  have hx := x_pos D L
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  positivity

theorem b_pos (L : SizeData₂ D) : 0 < L.sc.b := Real.exp_pos _

theorem log_k_le (L : SizeData₂ D) (hK : Formalism.MainNotions.SizeK L) : Real.log (D.R.k : ℝ) ≤ 5 * Real.log L.sc.x := by
  have hx := x_pos D L
  have hk : (0 : ℝ) < (D.R.k : ℝ) := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have h1 := Real.log_le_log hk hK.2
  rw [Real.log_rpow hx] at h1
  have h2 : 0 ≤ Real.log L.sc.x := Real.log_nonneg L.sc.one_lt_alt.le
  have h3 : 9 / 2 + 10 * L.sc.eps + Formalism.MainNotions.szTh L ≤ 5 := by
    unfold Formalism.MainNotions.szTh
    have := L.sc.eps_lt
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_right h3 h2)

theorem onsz_of (L : SizeData₂ D) (hK : Formalism.MainNotions.SizeK L) (hW : admW D L) : OntoSizeBound D L (11 / L.sc.eps) 1 := by
  have hx := x_pos D L
  have he := L.sc.eps_pos
  have hb := b_pos D L
  have hlk := log_k_le D L hK
  have hl0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg L.sc.one_lt_alt.le
  have hlx : Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps / L.sc.eps := Real.log_le_rpow_div hx.le he
  have hP : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow L.sc.one_lt_alt.le he.le
  have hf : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  unfold OntoSizeBound onCore
  rw [one_mul]
  set P := L.sc.x ^ L.sc.eps with hPdef
  have hL : L.sc.L = P := rfl
  rw [hL]
  set lx := Real.log L.sc.x
  set Q := (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have s1 : P * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) * PDVN.wMax D ≤ P * (5 * lx) * (D.R.m : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b) := by
    have a1 : P * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) ≤ P * (5 * lx) * (D.R.m : ℝ) := by gcongr
    have a0 : 0 ≤ P * (5 * lx) * (D.R.m : ℝ) := by positivity
    have w0 : 0 ≤ PDVN.wMax D := by
      unfold PDVN.wMax
      exact (Finset.le_fold_max 0).2 (Or.inl le_rfl)
    calc _ ≤ P * (5 * lx) * (D.R.m : ℝ) * PDVN.wMax D := mul_le_mul_of_nonneg_right a1 w0
      _ ≤ _ := mul_le_mul_of_nonneg_left hW a0
  have s2 : P * (5 * lx) * (D.R.m : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b) + Q * lx = Q * lx * (10 * P + 1) := by
    rw [hQ]; ring
  have s3 : Q * lx * (10 * P + 1) ≤ Q * (P / L.sc.eps) * (11 * P) := by
    have : 10 * P + 1 ≤ 11 * P := by linarith
    have h5 : 0 ≤ P / L.sc.eps := by positivity
    gcongr
  have s4 : Q * (P / L.sc.eps) * (11 * P) = 11 / L.sc.eps * P * L.B0 := by
    rw [B_zero_shape_eq_index, ← hPdef, hQ]; field_simp
  have s5 : 11 / L.sc.eps * P * L.B0 ≤ 11 / L.sc.eps * P * (L.B0 + L.Nc) := by
    have := Nc_nonneg D L
    have h6 : 0 ≤ 11 / L.sc.eps * P := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h6
  linarith

variable {D} in
theorem termwise_of {L : SizeData₂ D} {fl : ℕ → ℕ → ℝ} {r : ℕ → D.what₂.places.Pl → ℝ} {w : D.what₂.places.Pl}
    (h : PDVN.onL D L (D.what₂.muAt w) w ≤ PDVN.onR D fl r w) :
    ∑ j ∈ SizeData₂.lifts D,
        (((D.what₂.Ij (D.what₂.muAt w) j w : ℝ) + (D.what₂.Ij (D.what₂.muAt w) j (D.what₂.places.conj w) : ℝ)) /
          (D.what₂.D0 : ℝ) - 2 * ur D w (L.F j w)) ≤
      ur D w ((∑ j ∈ SizeData₂.lifts D, PDVN.onRj D fl r j w) + 2 / ((D.what₂.places.resChar w : ℝ) ^ 2)) := by
  have he : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by exact_mod_cast D.what₂.places.ramIdx_pos w
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h he.le)
  unfold PDVN.onL PDVN.inL ur
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PDVN.ramIdx_conj]
  field_simp

theorem onto_bound_of_exponents {D : D7} {L : SizeData₂ D} {X : LocalQuadraticParts.Loc D} {C1 CJ A C C' Cabs : ℝ} (hC1 : 0 ≤ C1) (hO : PDVN.ONTwJ D L C1)
    (hJ : admJ D L X CJ A) (hS1 : OntoSizeBound D L C Cabs) (hS2 : ExponentSumSize D L CJ A C' Cabs) :
    LocalQuadraticParts.ArchimedeanSignatureMatching D L X (C1 * C + C') Cabs := by
  obtain ⟨fl, r, h1, h2, h3, h4, -⟩ := hO
  have hS : PDVN.onBoundJ D L C1 + JB D L CJ A ≤ (C1 * C + C') * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc) := by
    have := mul_le_mul_of_nonneg_left hS1 hC1
    unfold ExponentSumSize at hS2
    rw [onBoundJ_eq]
    nlinarith
  refine ⟨PDVN.onRj D fl r, fl, r, h1, h2, hJ.1, fun _ _ => rfl, fun w hw => termwise_of (h3 w hw), fun j hj => ?_⟩
  have h0 : ∀ w, 0 ≤ SizeData₂.lwP w * ur D w (PDVN.onRj D fl r j w + X.Jx j w) := fun w =>
    mul_nonneg (logWeight_nonneg w) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (onRj_nonneg h1 h2 j w) (hJ.1 j w)))
  have hb : ∀ T : Finset D.what₂.places.Pl, ∑ w ∈ T, SizeData₂.lwP w * ur D w (PDVN.onRj D fl r j w + X.Jx j w) ≤
      (C1 * C + C') * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc) := fun T => by
    refine le_trans (le_of_eq ?_) (le_trans (add_le_add (h4 j hj T) (hJ.2 j hj T)) hS)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold ur; ring
  have hs : Summable fun w => SizeData₂.lwP w * ur D w (PDVN.onRj D fl r j w + X.Jx j w) := summable_of_sum_le h0 hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

def OntoBoundFromExponents (L : SizeData₂ D) (X : LocalQuadraticParts.Loc D) (C1 CJ A C C' Cabs : ℝ) : Prop :=
  0 ≤ C1 → PDVN.ONTwJ D L C1 → admJ D L X CJ A → OntoSizeBound D L C Cabs → ExponentSumSize D L CJ A C' Cabs →
    LocalQuadraticParts.ArchimedeanSignatureMatching D L X (C1 * C + C') Cabs

theorem stmtON4 (L : SizeData₂ D) (X : LocalQuadraticParts.Loc D) (C1 CJ A C C' Cabs : ℝ) : OntoBoundFromExponents D L X C1 CJ A C C' Cabs :=
  fun h0 h1 h2 h3 h4 => onto_bound_of_exponents h0 h1 h2 h3 h4

end PartF

section PartF2

open Formalism.BasicNotions Formalism.BasicNotions.DV

variable (D : D7)

theorem wSz_eq_wj (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) : wSz D j τ = wj D j τ := by
  unfold wSz wj
  rw [dif_pos ⟨h1, h2⟩, dif_pos (by omega : j - 1 < D.R.m)]

theorem two_le_b (L : SizeData₂ D) : 2 ≤ L.sc.b := by
  have h1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have h2 : L.sc.L + 1 ≤ L.sc.b := Real.add_one_le_exp _
  linarith

theorem b'_le (L : SizeData₂ D) (hS : Formalism.MainNotions.SizeLstar L) : L.sc.b' ≤ L.sc.b / 3 := by
  have hb := b_pos D L
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
  have ht : (7 : ℝ) ≤ (D.R.t : ℝ) := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m
    exact_mod_cast (by omega : 7 ≤ D.R.t)
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hN : (D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold Ranks.N
    have : D.R.m ≤ D.R.k + D.R.m * (D.R.t + 1) := by nlinarith [Nat.zero_le D.R.k, Nat.zero_le (D.R.m * D.R.t)]
    exact_mod_cast this
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hSc := L.Sc_pos
  set Den := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
      (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) with hDen
  have d1 : 3 * (D.R.m : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by
    have a1 : (3 : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 := by nlinarith
    have a2 : (D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) + D.R.t := by linarith
    have a3 : (1 : ℝ) ≤ L.sc.L ^ 2 := by nlinarith
    have a4 : 3 * (D.R.m : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) :=
      mul_le_mul a1 a2 (by linarith) (by linarith)
    nlinarith
  have d2 : 0 ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by positivity
  have d3 : 3 * (D.R.m : ℝ) ≤ Den := by rw [hDen]; linarith
  have hD0 : 0 < Den := by linarith
  have hl : Formalism.MainNotions.szlStar L ≤ L.sc.b / 3 := by
    unfold Formalism.MainNotions.szlStar
    rw [← hDen, div_le_div_iff₀ hD0 (by norm_num)]
    nlinarith
  have h1 := hS.1
  have h2 : 0 ≤ L.sc.b / Formalism.MainNotions.szlStar L := by
    refine div_nonneg hb.le ?_
    unfold Formalism.MainNotions.szlStar
    rw [← hDen]; positivity
  have h3 := L.etaSz_pos
  linarith

theorem eta_le (L : SizeData₂ D) (hE : Formalism.MainNotions.SizeEta L) : L.etaSz ≤ L.sc.b / 8 := by
  have hb := b_pos D L
  refine hE.2.1.trans ?_
  have ht : (2 : ℝ) ≤ (D.R.t : ℝ) := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m
    exact_mod_cast (by omega : 2 ≤ D.R.t)
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have h8 : (8 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by
    have a1 : (8 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := by nlinarith [mul_self_nonneg ((D.R.t : ℝ) - 2)]
    have a2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk
    have a3 : (8 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := by nlinarith
    nlinarith
  exact div_le_div_of_nonneg_left hb.le (by norm_num) h8

theorem wj_le (L : SizeData₂ D) (hE : Formalism.MainNotions.SizeEta L) (hS : Formalism.MainNotions.SizeLstar L) (hB : Formalism.MainNotions.SizeBot L)
    (hR : Formalism.MainNotions.SizeRho L) (hLa : Formalism.MainNotions.SizeLa L) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) : wj D j τ ≤ 2 * L.sc.b := by
  classical
  have hb := two_le_b D L
  have he := eta_le D L hE
  have hb' := b'_le D L hS
  have hx := x_pos D L
  have hb'0 : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := b_pos D L
    positivity
  by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
  · have := (L.win_thick j h1 h2 τ hth).2
    linarith
  by_cases htp : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · unfold Host.topPlaces at htp
    obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htp
    have h3 := (L.win_top j h1 h2 τ ⟨t, ht⟩ hte.symm).2
    have h4 := hB ⟨t, ht⟩
    have hk : (0 : ℝ) < (D.R.k : ℝ) := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 0 < D.R.k)
    have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg hx.le _) hLa.1
    have hlx : 0 ≤ Real.log L.sc.x := Real.log_nonneg L.sc.one_lt_alt.le
    have t2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k := by positivity
    have t3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos L.sc.one_lt_alt.le (by norm_num)
    have h5 : 4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) ≤ 1 := by
      have e : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have := hR
      unfold Formalism.MainNotions.SizeRho at this
      rw [e] at this
      linarith
    have h6 : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 L.sc.one_lt_alt.le
    have h7 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
    rw [h7] at h4
    have h8 : (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' ≤ 1 / 4 * L.sc.b' :=
      mul_le_mul_of_nonneg_right (by linarith) hb'0
    linarith
  · have h3 := (L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, htp, hth⟩).2
    have h4 : L.sc.w'' D.R.n ≤ L.sc.b' := by
      unfold Scale.w''
      refine div_le_self hb'0 ?_
      have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := by
        have : 1 ≤ D.R.n := D.R.ord_pos
        exact_mod_cast this
      nlinarith [L.sc.one_lt_alt]
    linarith

theorem wMax_le (L : SizeData₂ D) (hE : Formalism.MainNotions.SizeEta L) (hS : Formalism.MainNotions.SizeLstar L) (hB : Formalism.MainNotions.SizeBot L)
    (hR : Formalism.MainNotions.SizeRho L) (hLa : Formalism.MainNotions.SizeLa L) : admW D L := by
  have hb := b_pos D L
  unfold admW PDVN.wMax
  rw [Finset.fold_max_le]
  refine ⟨by positivity, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  unfold PDVN.wJ
  calc ∑ ρ : D.what₂.Tau, wSz D j ρ ≤ ∑ _ρ : D.what₂.Tau, 2 * L.sc.b :=
        Finset.sum_le_sum fun τ _ => by rw [wSz_eq_wj D j h1 h2]; exact wj_le D L hE hS hB hR hLa j h1 h2 τ
    _ = 2 * (D.R.f : ℝ) * L.sc.b := by
        rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]; ring

theorem onsz_sizes (L : SizeData₂ D) (h : Formalism.MainNotions.SizesAt L) : OntoSizeBound D L (11 / L.sc.eps) 1 := by
  obtain ⟨-, -, hK, -, -, -, -, -, hLa, hR, hB, -, -, hE, -, hS, -⟩ := h
  exact onsz_of D L hK (wMax_le D L hE hS hB hR hLa)

theorem card_T2_le_degree : (D.host.T2.card : ℝ) ≤ (D.R.f : ℝ) := by
  have h1 : D.host.T2 ⊆ Finset.range D.R.n0 := fun s hs => by
    have h := D.host.second_set_range s hs
    have h2 := D.host.two_le_Lw
    rw [Finset.mem_range]
    nlinarith
  have h2 := Finset.card_le_card h1
  rw [Finset.card_range] at h2
  have : D.host.T2.card ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.cyclic_order_le_exponent; omega
  exact_mod_cast this

theorem jsz_of (L : SizeData₂ D) {CJ : ℝ} (A : ℝ) (hCJ : 0 ≤ CJ) :
    ExponentSumSize D L CJ A (CJ + |A|) 1 := by
  have hx := x_pos D L
  have hb := b_pos D L
  have hP : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := by
      have := D.R.ord_pos
      unfold Ranks.f Ranks.n; omega
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ (D.R.m : ℝ) := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hT := card_T2_le_degree D
  unfold ExponentSumSize JB
  rw [one_mul]
  have e2 : L.sc.x ^ (2 * L.sc.eps) = L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by
    rw [← Real.rpow_add hx]; ring_nf
  set P := L.sc.x ^ L.sc.eps with hPdef
  have s1 : CJ * (D.host.T2.card : ℝ) * (D.R.m : ℝ) * L.sc.b * L.sc.x ^ (2 * L.sc.eps) ≤ CJ * P * L.B0 := by
    rw [e2, B_zero_shape_eq_index, ← hPdef]
    have : CJ * (D.host.T2.card : ℝ) * (D.R.m : ℝ) * L.sc.b * (P * P) ≤ CJ * (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * (P * P) := by
      gcongr
    linarith [this, (by ring : CJ * (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * (P * P) = CJ * P * ((D.R.f : ℝ) * D.R.m * L.sc.b * P))]
  have hmb : 0 ≤ (D.R.m : ℝ) * L.sc.b := by positivity
  have s2 : A * (D.R.m : ℝ) * L.sc.b ≤ |A| * ((D.R.m : ℝ) * L.sc.b) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self A) hmb
    linarith
  have s3 : (D.R.m : ℝ) * L.sc.b ≤ P * L.B0 := by
    rw [B_zero_shape_eq_index, ← hPdef]
    have h1 : (1 : ℝ) ≤ P * ((D.R.f : ℝ) * P) := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hmb
    nlinarith
  have s4 : |A| * ((D.R.m : ℝ) * L.sc.b) ≤ |A| * (P * L.B0) := mul_le_mul_of_nonneg_left s3 (abs_nonneg A)
  have hB0 : 0 ≤ L.B0 := by rw [B_zero_shape_eq_index]; positivity
  have s5 : (CJ + |A|) * P * L.B0 ≤ (CJ + |A|) * P * (L.B0 + L.Nc) := by
    have := Nc_nonneg D L
    have h6 : 0 ≤ (CJ + |A|) * P := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h6
  nlinarith

theorem exists_root_of_unity_preimage (A eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ x, x0 ≤ x → x ^ (A + 1) ≤ Real.exp (x ^ (eps / 3)) := by
  set n := ⌈3 * (A + 2) / eps⌉₊ with hn
  refine ⟨max 1 (n.factorial : ℝ), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxn : (n.factorial : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have h1 : A + 2 ≤ eps / 3 * n := by
    have := Nat.le_ceil (3 * (A + 2) / eps)
    rw [← hn, div_le_iff₀ he] at this
    linarith
  have h2 := Real.pow_div_factorial_le_exp (x ^ (eps / 3)) (Real.rpow_nonneg hx0.le _) n
  refine le_trans ?_ h2
  rw [le_div_iff₀ hf, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
  calc x ^ (A + 1) * (n.factorial : ℝ) ≤ x ^ (A + 1) * x := by gcongr
    _ = x ^ (A + 2) := by
        rw [← Real.rpow_add_one hx0.ne']; ring_nf
    _ ≤ x ^ (eps / 3 * n) := Real.rpow_le_rpow_of_exponent_le hx1 h1

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def familyOntoSize (Cabs : ℝ) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, OntoSizeBound (Fm.D x i) (Fm.L x i) C Cabs

theorem onszF : familyOntoSize Fm 1 :=
  ⟨11 / eps, 0, fun x _ hx i => by
    have := onsz_sizes (Fm.D x i) (Fm.L x i) (Fm.sizes x hx i)
    rwa [Fm.L_eps] at this⟩

def familyExponentSumSize (CJ A Cabs : ℝ) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, ExponentSumSize (Fm.D x i) (Fm.L x i) CJ A C Cabs

theorem jszF {CJ : ℝ} (hCJ : 0 ≤ CJ) (A : ℝ) : familyExponentSumSize Fm CJ A 1 :=
  ⟨CJ + |A|, 0, fun x _ _ i => jsz_of (Fm.D x i) (Fm.L x i) A hCJ⟩

theorem on4F (he : 0 < eps) (XF : ∀ x (i : Fm.Ix x), LocalQuadraticParts.Loc (Fm.D x i)) {C1 CJ A : ℝ} (hC1 : 0 ≤ C1) (hCJ : 0 ≤ CJ)
    (hO : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, PDVN.ONTwJ (Fm.D x i) (Fm.L x i) C1)
    (hJ : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, admJ (Fm.D x i) (Fm.L x i) (XF x i) CJ A) :
    ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LocalQuadraticParts.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) (XF x i) C 1 := by
  obtain ⟨a, hO⟩ := hO
  obtain ⟨b, hJ⟩ := hJ
  obtain ⟨C, c, h1⟩ := onszF Fm
  obtain ⟨C', d, h2⟩ := jszF Fm hCJ A
  refine ⟨C1 * C + C', max (max a b) (max c d), fun x hx0 hx i => ?_⟩
  have ga : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
  have gb : b ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
  have gc : c ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx0
  have gd : d ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  exact onto_bound_of_exponents hC1 (hO x ga hx i) (hJ x gb hx i) (h1 x gc hx i) (h2 x gd hx i)

end Fam

structure LocF (D : D7) where
  h : ℕ → ℕ
  lam : ℕ → D.what₂.Tau → DomWeight D.R.nV
  sh : ℕ → D.what₂.Tau → JumpSetsAlt.ShapeData

def LiftParameterConditions (L : SizeData₂ D) (Y : LocF D) (A0 : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, JumpSetsAlt.S2 D L A0 (Y.h j) L.etaSz L.Sc (LevelStarExponents.h0 L) (LevelStarExponents.lStar L) (Y.lam j) (Y.sh j)

variable {D} in

def InclOk (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (j : ℕ) (J : ℕ → ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Z.Lev l) (mt : Ideal (Z.Hk l c)) [mt.IsMaximal],
    JumpSetsAlt.CorIdeal L Z l (Y.h j) c mt (Y.sh j) → JumpSetsAlt.Incl Z l c (Y.lam j) mt (J l)

section IV

open NumberField IsDedekindDomain

def MtO (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).carrier}

def MtZ (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) :=
  MtO D μ j ⊓ (Idx.TjV D μ j).restrictScalars (𝓞 D.what₂.LL)

def MtDualZ (μ : D.what₂.Tup) (j : ℕ) : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j) where
  carrier := {x | x ∈ Idx.TjV D μ j ∧ ∀ a ∈ MtO D μ j, ∃ c : 𝓞 D.what₂.LL,
    inner ℂ (D.what₂.jMt μ j a) (D.what₂.jMt μ j x) = D.what₂.embLL (c : D.what₂.LL)}
  add_mem' := by
    rintro x y ⟨hx, h1⟩ ⟨hy, h2⟩
    refine ⟨(Idx.TjV D μ j).add_mem hx hy, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    obtain ⟨d, hd⟩ := h2 a ha
    exact ⟨c + d, by rw [map_add, inner_add_right, hc, hd]; simp⟩
  zero_mem' := ⟨(Idx.TjV D μ j).zero_mem, fun a _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro s x ⟨hx, h1⟩
    refine ⟨by rw [Idx.smul_def]; exact (Idx.TjV D μ j).smul_mem _ hx, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    exact ⟨s * c, by rw [Idx.smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hc]; simp⟩

def ixW (w : D.what₂.places.Pl) {μ : D.what₂.Tup} {j : ℕ} (A B : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j)) : ℤ :=
  Formalism.HermitianLatticesTheory.lidx (D.plEq w).asIdeal A B

def IdxAdd : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (w : HeightOneSpectrum (𝓞 K)) (A B C : Submodule (𝓞 K) V), A.FG → B.FG → C.FG →
    Submodule.span K (A : Set V) = Submodule.span K (B : Set V) →
    Submodule.span K (B : Set V) = Submodule.span K (C : Set V) →
    Formalism.HermitianLatticesTheory.lidx w.asIdeal A C = Formalism.HermitianLatticesTheory.lidx w.asIdeal A B + Formalism.HermitianLatticesTheory.lidx w.asIdeal B C

def IdxExp : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) (n : 𝓞 K) (d : ℕ), A.FG → B.FG →
    Submodule.span K (A : Set V) = Submodule.span K (B : Set V) →
    Module.finrank K (Submodule.span K (A : Set V)) = d → n ≠ 0 →
    (∀ x ∈ A, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • n • x ∈ B) →
    Formalism.HermitianLatticesTheory.lidx w.asIdeal A B ≤ (d : ℤ) * vAdd w (n : K)

def IndexEqualsLatticeIndex : Prop :=
  ∀ μ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.jw μ j w = Idx.jwIdx D μ j w

def EtaLengthDef : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    ur D w (D.what₂.etaJ j w : ℝ) = (ixW D w (Idx.TjL D (D.what₂.muAt w) j) (MtZ D (D.what₂.muAt w) j) : ℝ)

def ProjectionDualCond : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    Idx.TjDual D (D.what₂.muAt w) j = MtDualZ D (D.what₂.muAt w) j

def LatticesOfCommonSpace : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    (Idx.TjL D (D.what₂.muAt w) j).FG ∧ (MtZ D (D.what₂.muAt w) j).FG ∧ (MtDualZ D (D.what₂.muAt w) j).FG ∧
    Submodule.span D.what₂.LL (MtZ D (D.what₂.muAt w) j : Set (D.what₂.MtL (D.what₂.muAt w) j)) = Idx.TjV D (D.what₂.muAt w) j ∧
    Submodule.span D.what₂.LL (MtDualZ D (D.what₂.muAt w) j : Set (D.what₂.MtL (D.what₂.muAt w) j)) = Idx.TjV D (D.what₂.muAt w) j ∧
    Module.finrank D.what₂.LL (Idx.TjV D (D.what₂.muAt w) j) = D.what₂.D0

variable {D}

structure TieIV (Z : JumpSetsAlt.Prov D) (Y : LocF D) where

  lev : ∀ (_j : ℕ) (w : D.what₂.places.Pl), Z.Lev (D.what₂.places.resChar w)

  emb : ∀ w : D.what₂.places.Pl, 𝓞 D.what₂.LL →+* Z.O (D.what₂.places.resChar w)
  emb_w : ∀ w (s : 𝓞 D.what₂.LL), s ∈ (D.plEq w).asIdeal ↔ emb w s ∈ IsLocalRing.maximalIdeal (Z.O (D.what₂.places.resChar w))

  Z0 : ∀ j w, Submodule (Z.Hk (D.what₂.places.resChar w) (lev j w)) (JumpSetsAlt.Frm Z (D.what₂.places.resChar w) (lev j w) (Y.lam j))
  saturated_base : ∀ j w, JumpSetsAlt.Saturated Z (D.what₂.places.resChar w) (lev j w) (Y.lam j) (Z0 j w)

  phi : ∀ j w, MtO D (D.what₂.muAt w) j →+ JumpSetsAlt.Frm Z (D.what₂.places.resChar w) (lev j w) (Y.lam j)
  phi_smul : ∀ j w (s : 𝓞 D.what₂.LL) (x : MtO D (D.what₂.muAt w) j), phi j w (s • x) = emb w s • phi j w x

  phi_nabla : ∀ j w x, phi j w x ∈ JumpSetsAlt.MNsub Z (D.what₂.places.resChar w) (lev j w) (Y.lam j)
  phi_Z : ∀ j w (x : MtO D (D.what₂.muAt w) j),
    (x : D.what₂.MtL (D.what₂.muAt w) j) ∈ Idx.TjV D (D.what₂.muAt w) j ↔ phi j w x ∈ Z0 j w

def HeckeStableBlockSupport (L : SizeData₂ D) {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    ∀ (mt : Ideal (Z.Hk (D.what₂.places.resChar w) (T.lev j w))) [mt.IsMaximal],
      (∃ z ∈ T.Z0 j w, (LocalizedModule.mk z 1 : LocalizedModule mt.primeCompl _) ≠ 0) →
        @JumpSetsAlt.CorIdeal D L Z (D.what₂.places.resChar w) ⟨D.what₂.places.resChar_prime w⟩ (Y.h j) (T.lev j w) mt (Y.sh j)

def dualExp (D : D7) (w : D.what₂.places.Pl) : ℕ :=
  padicValNat (D.what₂.places.resChar w) (D.mem D.u₀).C.DGam +
    (if ∃ i, D.what₂.places.resChar w = D.host.g i then 2 * D.R.f * D.R.N D.R.m ^ 2 else 0)

def DualityUpToStabilisers {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ x : MtO D (D.what₂.muAt w) j,
    (x : D.what₂.MtL (D.what₂.muAt w) j) ∈ Idx.TjV D (D.what₂.muAt w) j →
    T.phi j w x ∈ JumpSetsAlt.MDsub Z (D.what₂.places.resChar w) (T.lev j w) (Y.lam j) →
    ∃ s : 𝓞 D.what₂.LL, s ∉ (D.plEq w).asIdeal ∧
      s • ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ dualExp D w • (x : D.what₂.MtL (D.what₂.muAt w) j) ∈
        MtDualZ D (D.what₂.muAt w) j

theorem mem_of_locSet {T M : Type} [CommRing T] [AddCommGroup M] [Module T M] (N : Submodule T M) (y : M)
    (h : ∀ (mt : Ideal T) [mt.IsMaximal],
      (LocalizedModule.mk y 1 : LocalizedModule mt.primeCompl M) ∈ JumpSetsAlt.locSet mt.primeCompl (N : Set M)) : y ∈ N := by
  by_contra hy
  let I : Ideal T := N.comap (LinearMap.toSpanSingleton T M y)
  have hI : I ≠ ⊤ := by
    intro h1
    have : (1 : T) ∈ I := by rw [h1]; trivial
    exact hy (by simpa [I] using this)
  obtain ⟨mt, hm, hle⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨x, hx, s, hs⟩ := h mt
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hs
  have h2 : ((u : T) * (s : T)) ∈ I := by
    show LinearMap.toSpanSingleton T M y ((u : T) * (s : T)) ∈ N
    have e : ((u : T) * (s : T)) • y = (u : T) • x := by
      have := hu
      simp only [Submonoid.smul_def, one_smul] at this
      rw [mul_smul]; exact this.symm
    rw [LinearMap.toSpanSingleton_apply, e]
    exact N.smul_mem _ hx
  exact (u * s).2 (hle h2)

theorem vAdd_lpow (D : D7) (w : D.what₂.places.Pl) (k : ℕ) :
    vAdd (D.plEq w) ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) =
      (D.what₂.places.ramIdx w : ℤ) * k := by
  have hl : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D.what₂.places.resChar_prime w).ne_zero
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k ≠ 0 := pow_ne_zero _ hl
  have e1 : ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) =
      ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k := by simp
  rw [e1]
  have h1 := D.val_eq w _ hne
  rw [AddValuation.map_pow, D.what₂.places.val_resChar] at h1
  have h2 : (((k • ((D.what₂.places.ramIdx w : ℕ) : ℤ)) : ℤ) : WithTop ℤ) =
      ((vAdd (D.plEq w) (((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ k) : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_nsmul]; exact h1
  rw [← WithTop.coe_inj.mp h2, nsmul_eq_mul]
  ring

def IndexOk (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (j : ℕ) (J : ℕ → ℕ) : Prop :=
  JumpSetsAlt.CorIndex L Z (Y.h j) (Y.lam j) (Y.sh j) J

theorem h11 {L : SizeData₂ D} {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) (hB : HeckeStableBlockSupport L T)
    {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {w : D.what₂.places.Pl} (hw : D.what₂.muAt w ≠ D.what₂.mu0) {Jj : ℕ → ℕ}
    (hI : IndexOk L Z Y j Jj) (x : MtO D (D.what₂.muAt w) j)
    (hx : (x : D.what₂.MtL (D.what₂.muAt w) j) ∈ Idx.TjV D (D.what₂.muAt w) j) :
    T.phi j w ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ Jj (D.what₂.places.resChar w)) • x) ∈
      JumpSetsAlt.MDsub Z (D.what₂.places.resChar w) (T.lev j w) (Y.lam j) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hZ := (T.phi_Z j w x).1 hx
  have hN := T.phi_nabla j w x
  have key : (algebraMap (Z.O (D.what₂.places.resChar w)) (Z.Hk (D.what₂.places.resChar w) (T.lev j w))
      (((D.what₂.places.resChar w : ℕ) : Z.O (D.what₂.places.resChar w)) ^ Jj (D.what₂.places.resChar w))) • T.phi j w x ∈
        T.Z0 j w ⊓ JumpSetsAlt.MDsub Z (D.what₂.places.resChar w) (T.lev j w) (Y.lam j) := by
    apply mem_of_locSet
    intro mt _
    have h0 := (hI (D.what₂.places.resChar w) (T.lev j w) (T.Z0 j w) (T.saturated_base j w)
      (fun mt' _ h => hB j hj w hw mt' h) mt).1 (LocalizedModule.mk (T.phi j w x) 1) ⟨T.phi j w x, ⟨hZ, hN⟩, 1, rfl⟩
    rw [LocalizedModule.smul'_mk] at h0
    exact h0
  rw [T.phi_smul, map_pow, map_natCast]
  rw [algebraMap_smul] at key
  exact key.2

def AdmIV (L : SizeData₂ D) {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) : Prop :=
  IdxAdd ∧ IdxExp ∧ IndexEqualsLatticeIndex D ∧ EtaLengthDef D ∧ ProjectionDualCond D ∧ LatticesOfCommonSpace D ∧ HeckeStableBlockSupport L T ∧ DualityUpToStabilisers T

def ExponentIndexAnyExponents (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) : Prop :=
  ∀ J : ℕ → ℕ → ℕ, (∀ j ∈ SizeData₂.lifts D, IndexOk L Z Y j (J j)) →
    LocalQuadraticParts.TwistedIndexValuationBound D ⟨fun j w => (J j (D.what₂.places.resChar w) : ℝ)⟩

theorem ivAny_of {L : SizeData₂ D} {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) (h : AdmIV L T) : ExponentIndexAnyExponents L Z Y := by
  obtain ⟨hAdd, hExp, hJw, hD8, hL31, hLat, hB, hDual⟩ := h
  intro J hJ j hj w hw
  have hj' := Finset.mem_Icc.mp hj
  obtain ⟨fT, fZ, fH, sZ, sH, rk⟩ := hLat j hj w hw
  set μ := D.what₂.muAt w with hμ
  set l := D.what₂.places.resChar w with hl
  set k := J j l + dualExp D w with hk
  have hn : (((l : ℕ) : 𝓞 D.what₂.LL) ^ k) ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h0
    have : ((l : ℕ) : D.what₂.LL) = 0 := by
      have := congrArg (fun t : 𝓞 D.what₂.LL => (t : D.what₂.LL)) h0
      simpa using this
    exact (Nat.cast_ne_zero.mpr (D.what₂.places.resChar_prime w).ne_zero) this
  have hloc : ∀ y ∈ MtZ D μ j, ∃ s : 𝓞 D.what₂.LL, s ∉ (D.plEq w).asIdeal ∧
      s • ((l : ℕ) : 𝓞 D.what₂.LL) ^ k • y ∈ MtDualZ D μ j := by
    intro y hy
    obtain ⟨hyO, hyV⟩ := hy
    let x : MtO D μ j := ⟨y, hyO⟩
    let x' : MtO D μ j := (((l : ℕ) : 𝓞 D.what₂.LL) ^ J j l) • x
    have hx'V : (x' : D.what₂.MtL μ j) ∈ Idx.TjV D μ j := by
      show ((((l : ℕ) : 𝓞 D.what₂.LL) ^ J j l) • y) ∈ Idx.TjV D μ j
      rw [Idx.smul_def]
      exact (Idx.TjV D μ j).smul_mem _ hyV
    have hMD := h11 T hB hj hw (hJ j hj) x hyV
    obtain ⟨s, hs, hsx⟩ := hDual j hj w hw x' hx'V hMD
    refine ⟨s, hs, ?_⟩
    have e : ((l : ℕ) : 𝓞 D.what₂.LL) ^ k • y =
        ((l : ℕ) : 𝓞 D.what₂.LL) ^ dualExp D w • (x' : D.what₂.MtL μ j) := by
      show _ = ((l : ℕ) : 𝓞 D.what₂.LL) ^ dualExp D w • ((((l : ℕ) : 𝓞 D.what₂.LL) ^ J j l) • y)
      rw [smul_smul, ← pow_add, hk, add_comm]
    rw [e]
    exact hsx
  have hspan : Submodule.span D.what₂.LL (Idx.TjL D μ j : Set (D.what₂.MtL μ j)) =
      Submodule.span D.what₂.LL (MtZ D μ j : Set (D.what₂.MtL μ j)) := by
    rw [sZ]; rfl
  have hrk : Module.finrank D.what₂.LL (Submodule.span D.what₂.LL (MtZ D μ j : Set (D.what₂.MtL μ j))) = D.what₂.D0 := by
    rw [sZ]; exact rk
  have i1 := hExp D.what₂.LL (D.what₂.MtL μ j) (D.plEq w) (MtZ D μ j) (MtDualZ D μ j) _ D.what₂.D0 fZ fH (sZ.trans sH.symm)
    hrk hn hloc
  have i2 := hAdd D.what₂.LL (D.what₂.MtL μ j) (D.plEq w) (Idx.TjL D μ j) (MtZ D μ j) (MtDualZ D μ j) fT fZ fH hspan
    (sZ.trans sH.symm)
  rw [vAdd_lpow] at i1
  have hjw := hJw μ j w hj'.1 hj'.2
  have hd8 := hD8 j hj w hw
  unfold Idx.jwIdx at hjw
  rw [hL31 j hj w hw] at hjw
  rw [hjw, i2]
  unfold ixW at hd8
  unfold ur at hd8 ⊢
  have i1' : ((Formalism.HermitianLatticesTheory.lidx (D.plEq w).asIdeal (MtZ D μ j) (MtDualZ D μ j) : ℤ) : ℝ) ≤
      (D.what₂.D0 : ℝ) * ((D.what₂.places.ramIdx w : ℝ) * (k : ℝ)) := by exact_mod_cast i1
  have hkR : (k : ℝ) = (J j l : ℝ) + (padicValNat l (D.mem D.u₀).C.DGam : ℝ) +
      (if ∃ i, l = D.host.g i then 2 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 else 0) := by
    rw [hk]; unfold dualExp; rw [← hl]
    push_cast
    split_ifs <;> simp [add_assoc]
  push_cast
  rw [← hd8]
  show _ ≤ (D.what₂.places.ramIdx w : ℝ) * ((D.what₂.etaJ j w : ℝ) + (D.what₂.D0 : ℝ) *
      ((J j l : ℝ) + (padicValNat l (D.mem D.u₀).C.DGam : ℝ) +
        (if ∃ i, l = D.host.g i then 2 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 else 0)))
  rw [← hkR]
  nlinarith [i1']

theorem exponentAny_of_inputs {L : SizeData₂ D} {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) (h : AdmIV L T) : ExponentIndexAnyExponents L Z Y :=
  ivAny_of T h

end IV

variable {D} in

theorem exists_J {L : SizeData₂ D} {Z : JumpSetsAlt.Prov D} {Y : LocF D} {A0 CJ A : ℝ} (h : JumpSetsAlt.PointsLemma D L Z A0 CJ A)
    (hS : LiftParameterConditions D L Y A0) :
    ∃ J : ℕ → ℕ → ℕ, JSum D L J CJ A ∧ ∀ j ∈ SizeData₂.lifts D, InclOk L Z Y j (J j) ∧ IndexOk L Z Y j (J j) := by
  classical
  have : ∀ j, ∃ Jj : ℕ → ℕ, j ∈ SizeData₂.lifts D →
      (∀ n : ℕ, ∑ l ∈ JumpSetsAlt.primesUpTo n, (Jj l : ℝ) * Real.log l ≤ JB D L CJ A) ∧ InclOk L Z Y j Jj ∧ IndexOk L Z Y j Jj :=
    fun j => by
    by_cases hj : j ∈ SizeData₂.lifts D
    · obtain ⟨J, h1, h2, h3⟩ := h _ _ _ _ _ _ _ (hS j hj)
      exact ⟨J, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hj⟩
  choose J hJ using this
  exact ⟨J, fun j hj => (hJ j hj).1, fun j hj => (hJ j hj).2⟩

variable {D} in

theorem exists_Jx {L : SizeData₂ D} {Z : JumpSetsAlt.Prov D} {Y : LocF D} {A0 CJ A : ℝ}
    (h : JumpSetsAlt.PointsLemma D L Z A0 CJ A) (hS : LiftParameterConditions D L Y A0) :
    ∃ (X : LocalQuadraticParts.Loc D) (J : ℕ → ℕ → ℕ), JTie D X J ∧ admJ D L X CJ A ∧
      ∀ j ∈ SizeData₂.lifts D, InclOk L Z Y j (J j) ∧ IndexOk L Z Y j (J j) := by
  obtain ⟨J, hJ, hI⟩ := exists_J h hS
  exact ⟨⟨fun j w => (J j (D.what₂.places.resChar w) : ℝ)⟩, J, fun _ _ => rfl, exponentCond_of_sum (fibreLe D) (fun _ _ => rfl) hJ, hI⟩

def ExponentBoundIV (X : LocalQuadraticParts.Loc D) : Prop := LocalQuadraticParts.TwistedIndexValuationBound D X

def ExponentAnyForm (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) : Prop := ExponentIndexAnyExponents L Z Y

theorem exponentClause_of_inputs {L : SizeData₂ D} {Z : JumpSetsAlt.Prov D} {Y : LocF D} (T : TieIV Z Y) (h : AdmIV L T) : ExponentAnyForm D L Z Y :=
  ivAny_of T h

def ExponentChoiceBounds (L : SizeData₂ D) (CJ A : ℝ) : Prop := ∃ X : LocalQuadraticParts.Loc D, admJ D L X CJ A ∧ ExponentBoundIV D X

def ExponentBoundAnyExponents (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (A0 CJ A : ℝ) : Prop :=
  JumpSetsAlt.PointsLemma D L Z A0 CJ A → LiftParameterConditions D L Y A0 → ExponentAnyForm D L Z Y → ExponentChoiceBounds D L CJ A

theorem stmtJIV (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (A0 CJ A : ℝ) : ExponentBoundAnyExponents D L Z Y A0 CJ A := by
  intro h hS hIV
  obtain ⟨J, hJ, hI⟩ := exists_J h hS
  exact ⟨⟨fun j w => (J j (D.what₂.places.resChar w) : ℝ)⟩, exponentCond_of_sum (fibreLe D) (fun _ _ => rfl) hJ,
    hIV J (fun j hj => (hI j hj).2)⟩

def ExponentBoundFromCorollary (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (T : TieIV Z Y) (A0 CJ A : ℝ) : Prop :=
  JumpSetsAlt.PointsLemma D L Z A0 CJ A → LiftParameterConditions D L Y A0 → AdmIV L T → ExponentChoiceBounds D L CJ A

theorem stmtJIVT (L : SizeData₂ D) (Z : JumpSetsAlt.Prov D) (Y : LocF D) (T : TieIV Z Y) (A0 CJ A : ℝ) :
    ExponentBoundFromCorollary D L Z Y T A0 CJ A :=
  fun h hS hA => stmtJIV D L Z Y A0 CJ A h hS (exponentClause_of_inputs D T hA)

section FamJ

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

open Classical in

theorem jivF {CJ A : ℝ}
    (h : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, ExponentChoiceBounds (Fm.D x i) (Fm.L x i) CJ A) :
    ∃ XF : ∀ x (i : Fm.Ix x), LocalQuadraticParts.Loc (Fm.D x i), ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
      admJ (Fm.D x i) (Fm.L x i) (XF x i) CJ A ∧ ExponentBoundIV (Fm.D x i) (XF x i) := by
  obtain ⟨x0, h⟩ := h
  refine ⟨fun x i => if h' : ExponentChoiceBounds (Fm.D x i) (Fm.L x i) CJ A then h'.choose else ⟨fun _ _ => 0⟩, x0, fun x hx h1 i => ?_⟩
  have h' := h x hx h1 i
  show admJ (Fm.D x i) (Fm.L x i) (dite _ _ _) CJ A ∧ ExponentBoundIV (Fm.D x i) (dite _ _ _)
  rw [dif_pos h']
  exact h'.choose_spec

theorem on4ivF (he : 0 < eps) (ZF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), JumpSetsAlt.Prov (Fm.D x i))
    (YF : ∀ x (i : Fm.Ix x), LocF (Fm.D x i))
    {C1 CJ A A0 : ℝ} (hC1 : 0 ≤ C1) (hCJ : 0 ≤ CJ)
    (hO : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, PDVN.ONTwJ (Fm.D x i) (Fm.L x i) C1)
    (h37 : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), JumpSetsAlt.PointsLemma (Fm.D x i) (Fm.L x i) (ZF x hx i) A0 CJ A)
    (hS : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LiftParameterConditions (Fm.D x i) (Fm.L x i) (YF x i) A0)
    (hIV : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ExponentAnyForm (Fm.D x i) (Fm.L x i) (ZF x hx i) (YF x i)) :
    ∃ XF : ∀ x (i : Fm.Ix x), LocalQuadraticParts.Loc (Fm.D x i),
      (∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LocalQuadraticParts.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) (XF x i) C 1) ∧
      ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LocalQuadraticParts.TwistedIndexValuationBound (Fm.D x i) (XF x i) := by
  obtain ⟨a, h37⟩ := h37
  obtain ⟨b, hS⟩ := hS
  obtain ⟨c, hIV⟩ := hIV
  obtain ⟨XF, x0, hX⟩ := jivF Fm (CJ := CJ) (A := A) ⟨max a (max b c), fun x hx h1 i =>
    stmtJIV _ _ _ _ A0 CJ A (h37 x (le_trans (le_max_left _ _) hx) h1 i)
      (hS x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) h1 i)
      (hIV x (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) h1 i)⟩
  exact ⟨XF, on4F Fm he XF hC1 hCJ hO ⟨x0, fun x hx h1 i => (hX x hx h1 i).1⟩, x0, fun x hx h1 i => (hX x hx h1 i).2⟩

end FamJ

end PartF2

end Formalism.MainNotions.WeightDegreeSizes

end
