import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionVerticalPerturbationBoundStatement
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqDiag
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.PZeroSetNull
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.sq_R

open GroundTheory.Heights₂.Heights.Inter GroundTheory.Heights₂.Heights.Inter.DiagRAux

theorem smooth_pull {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hb : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (hp : IsPullHerm κ v A A') : IsSmoothHerm A' := by
  have hfun : A'.h = fun z => A.h (fun p => z (v p)) := funext hp.2
  unfold IsSmoothHerm
  rw [hfun]
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι' k) → ℂ => fun p => z (v p)) :=
    contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)
  refine hA.comp hlin.contDiffOn ?_
  intro z hz k
  obtain ⟨i, hi⟩ := hz (κ k)
  obtain ⟨⟨k1, i1⟩, hp1⟩ := hb.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
  have h1 : κ k1 = κ k := by
    have := hb.2.2.1 ⟨k1, i1⟩
    rw [hp1] at this
    exact this.symm
  obtain rfl := hb.1 h1
  exact ⟨i1, by show z (v ⟨k1, i1⟩) ≠ 0; rw [hp1]; exact hi⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cons_eq_snoc {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} {A : HermLine ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) :
    I P (n + 1) (Fin.cons A L) = I P (n + 1) (Fin.snoc L A) := by
  have hrot := hI.1 P (n + 1) (Fin.cons A L) (finRotate (n + 1)) hP (smooth_cons hA hL)
  have hsnoc : (Fin.cons A L : Fin (n + 1) → HermLine ι) ∘ finRotate (n + 1) = Fin.snoc L A :=
    (Fin.snoc_eq_cons_rotate L A).symm
  rw [hsnoc] at hrot
  exact hrot.symm

theorem sq_sub {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hF : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} {X₀ X₁ : HermLine ι} (hW : IsArithVar P (n + 2))
    (hL : ∀ j, IsSmoothHerm (L j)) (hs0 : IsSmoothHerm X₀) (hs1 : IsSmoothHerm X₁) (c : K → ℤ)
    (hdeg : ∀ k, 2 * c k = -(X₀.a k + X₁.a k)) :
    I P (n + 2) (Fin.cons X₀ (Fin.cons X₀ L)) - I P (n + 2) (Fin.cons X₁ (Fin.cons X₁ L)) =
      -2 * (I P (n + 2) (Fin.snoc (Fin.cons X₀ L : Fin (n + 1) → HermLine ι) (halfInvLine X₀ X₁ c hdeg)) -
        I P (n + 2) (Fin.snoc (Fin.cons X₁ L : Fin (n + 1) → HermLine ι) (halfInvLine X₀ X₁ c hdeg))) := by
  set Q := X₀.tensor X₁ with hQ
  set LL := halfInvLine X₀ X₁ c hdeg with hLL
  have hsQ : IsSmoothHerm Q := DiagRAux.isSmoothHerm_tensor hs0 hs1
  have hsLL : IsSmoothHerm LL := isSmoothHerm_halfInvLine hs0 hs1 _ hdeg
  set T2 := Q.tensor (LL.tensor LL) with hT2
  have hsT2 : IsSmoothHerm T2 := DiagRAux.isSmoothHerm_tensor hsQ (DiagRAux.isSmoothHerm_tensor hsLL hsLL)
  have aT2 : T2.a = 0 := by
    funext k
    have := hdeg k
    simp only [hT2, hQ, hLL, HermLine.tensor, halfInvLine, Pi.add_apply, Pi.zero_apply]
    linarith
  have hT2h : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → T2.h z = 1 := by
    intro z hz
    have hpos : 0 < X₀.h z * X₁.h z := mul_pos (X₀.pos z hz) (X₁.pos z hz)
    simp only [hT2, hQ, hLL, HermLine.tensor]
    rw [halfInvLine_h_of_pos _ _ _ _ z hz, ← Real.rpow_add hpos]
    norm_num
    rw [Real.rpow_neg_one]
    exact mul_inv_cancel₀ hpos.ne'
  set G : HermLine ι → HermLine ι → ℝ :=
    fun A B => I P (n + 2) (Fin.snoc (Fin.cons A L : Fin (n + 1) → HermLine ι) B) with hG
  have G_add : ∀ {A B C'}, IsSmoothHerm A → IsSmoothHerm B → IsSmoothHerm C' →
      G A (B.tensor C') = G A B + G A C' := fun hA hB hC =>
    hF.2.1 P (n + 1) _ _ _ hW (smooth_cons hA hL) hB hC
  have G_symm : ∀ {A B}, IsSmoothHerm A → IsSmoothHerm B → G A B = G B A := by
    intro A B hA hB
    have := hF.1 P (n + 2) (Fin.snoc (Fin.cons B L : Fin (n + 1) → HermLine ι) A)
      (Equiv.swap 0 (Fin.last (n + 1))) hW (smooth_snoc hA (smooth_cons hB hL))
    rw [snoc_cons_comp_swap] at this
    exact this
  have e6 : ∀ {M}, IsSmoothHerm M → G M X₀ + G M X₁ + G M LL + G M LL = 0 := by
    intro M hsM
    rw [← G_add hsM hs0 hs1, add_assoc, ← G_add hsM hsLL hsLL,
      ← G_add hsM hsQ (DiagRAux.isSmoothHerm_tensor hsLL hsLL)]
    exact I_snoc_triv hF hW (smooth_cons hsM hL) hsT2 aT2 fun z hz => hT2h z hz.1
  have e0 := e6 hs0
  have e1 := e6 hs1
  have e5 : G X₀ X₁ = G X₁ X₀ := G_symm hs0 hs1
  have r0 : I P (n + 2) (Fin.cons X₀ (Fin.cons X₀ L)) = G X₀ X₀ :=
    cons_eq_snoc hF hW (smooth_cons hs0 hL) hs0
  have r1 : I P (n + 2) (Fin.cons X₁ (Fin.cons X₁ L)) = G X₁ X₁ :=
    cons_eq_snoc hF hW (smooth_cons hs1 hL) hs1
  rw [r0, r1]
  show G X₀ X₀ - G X₁ X₁ = -2 * (G X₀ LL - G X₁ LL)
  linarith

end PositivityTheory.Xgp.sq_R

theorem PositivityTheory.Xgp.t_sq_R : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ T : Fin (d + 1) → HermLine Q.ιW, (∀ j, IsSmoothHerm (T j)) → II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₀ (Fin.cons X₀ T)) - II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₁ (Fin.cons X₁ T)) = 2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  intro hIn II hII K _ ι _ P d k₀ xi2 Q Xi X₀ X₁ hXa hX hp0 hp1 T hT
  have hF : IsIntersectionFamily (II Q.KW Q.ιW) := hII.1 Q.KW Q.ιW
  have hW : IsArithVar Q.PW (d + 3) := Q.arithW
  have hWp : Q.PW.IsPrime := hW.2.1.1
  have hs0 : IsSmoothHerm X₀ := PositivityTheory.Xgp.sq_R.smooth_pull (Q.block 0) hX hp0
  have hs1 : IsSmoothHerm X₁ := PositivityTheory.Xgp.sq_R.smooth_pull (Q.block 1) hX hp1
  have hdeg : ∀ k, 2 * ((Q.dg k : ℤ) - Q.dh k) = -(X₀.a k + X₁.a k) := by
    intro k
    rw [hp0.1, hp1.1, hXa]
    exact Q.deg_eq k
  set LL := GroundTheory.Heights₂.Heights.Inter.DiagRAux.halfInvLine X₀ X₁ (fun k => (Q.dg k : ℤ) - Q.dh k) hdeg with hLL
  have hsLL : IsSmoothHerm LL := GroundTheory.Heights₂.Heights.Inter.DiagRAux.isSmoothHerm_halfInvLine hs0 hs1 _ hdeg
  have hrat : IsRatSectionOn Q.PW LL Q.g Q.h :=
    ⟨_, _, Q.g_deg, Q.h_deg, Q.g_nmem, Q.h_nmem, fun k => rfl⟩
  have hdiv : ReciprocityTheory.ChartRestriction.G.AI.T.toZCycle (divCycle Q.PW Q.g) - ReciprocityTheory.ChartRestriction.G.AI.T.toZCycle (divCycle Q.PW Q.h) =
      Finsupp.single Q.Δ 1 := by
    classical
    ext W
    simp only [Q.div_eq, ReciprocityTheory.ChartRestriction.G.AI.T.toZCycle, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply,
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    split_ifs <;> push_cast <;> ring
  have key : ∀ A : HermLine Q.ιW, IsSmoothHerm A →
      II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW) LL) =
        II Q.KW Q.ιW Q.Δ (d + 2) (Fin.snoc T A) -
          ptsIntegral Q.PW (pot (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) := by
    intro A hA
    have e7 := hIn.ratR Q.KW Q.ιW (II Q.KW Q.ιW) hF Q.PW (d + 2) (Fin.cons A T) LL Q.g Q.h hW
      (GroundTheory.Heights₂.Heights.Inter.DiagRAux.smooth_cons hA hT) hsLL hrat
    have e8 := GroundTheory.Heights₂.Heights.Inter.DiagRAux.cycR_sub_eq (II Q.KW Q.ιW) Q.PW
      (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW) Q.g Q.h Q.Δ hdiv Q.arithΔ.2.2.1
    have e9 := PositivityTheory.Xgp.sq_R.cons_eq_snoc hF Q.arithΔ hT hA
    have e10 : ptsIntegral Q.PW (pot (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW)) (logNormRat LL Q.g Q.h) =
        ptsIntegral Q.PW (pot (Fin.cons A T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) := by
      refine GroundTheory.Heights₂.Heights.Inter.ZeroSetNull.proof Q.KW Q.ιW Q.PW (d + 2) (Q.g * Q.h) (Q.dg + Q.dh) _ _ _ hW
        (by classical exact GroundTheory.Heights₂.Heights.Inter.exHomog_mul Q.g_deg Q.h_deg)
        (fun hm => (hWp.mem_or_mem hm).elim Q.g_nmem Q.h_nmem) ?_
      intro z hz hne
      have hz' := hz.1
      rw [map_mul, eval_mul] at hne
      have hgz : ‖eval z (map (Int.castRingHom ℂ) Q.g)‖ ≠ 0 := norm_ne_zero_iff.2 (left_ne_zero_of_mul hne)
      have hhz : ‖eval z (map (Int.castRingHom ℂ) Q.h)‖ ≠ 0 := norm_ne_zero_iff.2 (right_ne_zero_of_mul hne)
      have h0 := X₀.pos z hz'
      have h1 := X₁.pos z hz'
      unfold logNormRat AlgSq.logNormT
      rw [← hp0.2 z, ← hp1.2 z, hLL, GroundTheory.Heights₂.Heights.Inter.DiagRAux.halfInvLine_h_of_pos _ _ _ _ z hz',
        Real.log_div (div_ne_zero hgz hhz) (Real.rpow_pos_of_pos (mul_pos h0 h1) _).ne',
        Real.log_rpow (mul_pos h0 h1), Real.log_mul h0.ne' h1.ne']
      ring
    rw [e7, recRRat, e8, e9, e10]
  have hV := GlobalTheory.T.intersection_vertical_perturbation_bound hIn II hII Q.KW Q.ιW Q.Δ (d + 1) T X₀ X₁ ∅ (fun _ => 0) Q.arithΔ hT hs0 hs1
    (by simp) (PositivityTheory.Xgp.t_sq_diag K ι P d k₀ xi2 Q Xi X₀ X₁ hp0 hp1) (by simp)
  rw [Finset.sum_empty, zero_mul, abs_nonpos_iff] at hV
  have hsq := PositivityTheory.Xgp.sq_R.sq_sub hF (n := d + 1) hW hT hs0 hs1 _ hdeg
  have k0 := key X₀ hs0
  have k1 := key X₁ hs1
  rw [← hLL] at hsq
  linarith
