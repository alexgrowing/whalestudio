import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RhoAntitoneOfInterlacing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResidueForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L0ConstantPartCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2RmatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EnergyEstimateFromParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivedCoefficientIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelWordsAssemble
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.StatementMA
import Formalism.HermitianCurvature.StatementR
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PolyInMul

section S_T1
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MeasureTheory

theorem one_act (P : M.Par) (j : M.Ty P → SmQ P.r P.TT) : actA P (1 : A P (DQ P)) j = j := by
  funext π
  classical
  show ∑ π', ((1 : Matrix (M.Ty P) (M.Ty P) (DQ P).Pr) π π').1 (j π') = j π
  rw [Finset.sum_eq_single π]
  · rw [Matrix.one_apply_eq]; rfl
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb)]; rfl
  · simp

theorem dens_nil (P : M.Par) (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ) (ω : Qp P.r P.TT) :
    (sysQ P l L j lam α β Lb c Ntot).dens [] ω = ∑ π, ‖(j π : Qp P.r P.TT → ℂ) ω‖ ^ 2 := by
  simp only [LE.Sys.dens, LE.sq]
  refine Finset.sum_congr rfl fun a _ => ?_
  show (Wq P ω ^ 0 * ((1 : ℂ)).re) * ‖(j a : Qp P.r P.TT → ℂ) ω‖ ^ 2 = _
  simp

end Formalism.FourierDecayAlt.P.MAx3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MeasureTheory

theorem roots_outside : Formalism.FourierDecayAlt.MA.RootsOutQ :=
  roots_outside_of_parts_alt roots_outside_jointly

theorem jacobi_base : Formalism.FourierDecayAlt.MA.EmptyWordEnergyDensity := by
  intro P l L j lam α β Lb c Ntot hH ω
  exact MAx3.dens_nil P l L j lam α β Lb c Ntot ω

theorem jacobi_square_integrable : Formalism.FourierDecayAlt.MA.SourceSquareIntegrable := by
  intro P l L j lam α β Lb c Ntot hH
  have hD := hH.2.1
  show Integrable ((sysQ P l L j lam α β Lb c Ntot).dens []) (mu0 P.r P.TT)
  rw [show (sysQ P l L j lam α β Lb c Ntot).dens [] = fun ω => ∑ π, ‖(j π : Qp P.r P.TT → ℂ) ω‖ ^ 2 from
    funext (MAx3.dens_nil P l L j lam α β Lb c Ntot)]
  refine integrable_finset_sum _ fun π _ => ?_
  have := hD [] (by simp) (by simp) π
  rw [List.prod_nil, MAx3.one_act] at this
  exact this

theorem polynomial_regular : Formalism.FourierDecayAlt.MA.PRegQ := by
  intro P l L j lam α β Lb c Ntot hH w hw hl
  obtain ⟨_, _, _, _, _, _, hL2, hn, h6⟩ := id hH
  exact (imported_results_hold ratio_middle_range boxes_fit (sysQ P l L j lam α β Lb c Ntot) hL2 h6 hn
    (roots_outside P l L j lam α β Lb c Ntot hH) w hl).1

theorem probability_ratio : Formalism.FourierDecayAlt.MA.PRatioQ := by
  intro P l L j lam α β Lb c Ntot hH w hw hl
  obtain ⟨_, _, _, _, _, _, hL2, hn, h6⟩ := id hH
  exact (imported_results_hold ratio_middle_range boxes_fit (sysQ P l L j lam α β Lb c Ntot) hL2 h6 hn
    (roots_outside P l L j lam α β Lb c Ntot hH) w hl).2

end Formalism.FourierDecayAlt.P

end S_T1

section S_T2
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MeasureTheory Formalism.FourierDecayAlt.P.MAx1.An

section
variable (P : M.Par)

theorem evQ_cont (f : SmQ P.r P.TT) : Continuous (evQ P f) := by
  have h1 := continuousOn_iff_continuous_domRestrict.1 ((f.2 : ContDiffOn ℝ sm (ext f.1) (Qset P.r P.TT)).continuousOn)
  refine h1.congr fun q => ?_
  simp only [Set.domRestrict_apply]
  rw [ext_of_mem _ q.2]
  rfl

theorem apply_matrix_eval {N : ℕ} (b : Wd.SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (U : Qp P.r P.TT → Iota P N → ℂ) (q : Qp P.r P.TT)
    (i : Iota P N) : wordModuleApply P b U q i =
      evQ P (∑ e', ∑ π', ((b (ixOf P N i).1 e') (ixOf P N i).2 π').1 (toSm P fun q' => U q' (iotaOf P N e' π'))) q := by
  rw [MAx2.Jet.evQ_sum]
  exact Finset.sum_congr rfl fun e' _ => (MAx2.Jet.evQ_sum P _ _ q).symm

theorem gL_ev (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (w : List ℝ) (Y : ℝ)
    (U : Qp P.r P.TT → Iota P w.length → ℂ) (bi : Iota P (w.length + 1)) :
    ∃ f : SmQ P.r P.TT, ∀ q, gL P l L w Y U q bi = evQ P f q := by
  obtain ⟨b, i⟩ := bi
  exact ⟨_, fun q => apply_matrix_eval P _ U q i⟩

theorem gL_cont (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (w : List ℝ) (Y : ℝ)
    (U : Qp P.r P.TT → Iota P w.length → ℂ) (bi : Iota P (w.length + 1)) :
    Continuous fun q => gL P l L w Y U q bi := by
  obtain ⟨f, hf⟩ := gL_ev P l L w Y U bi
  exact (evQ_cont P f).congr fun q => (hf q).symm

theorem Xw_ev (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) :
    ∀ (w : List ℝ) (i : Iota P w.length), ∃ f : SmQ P.r P.TT, ∀ q, Xw P l L (ju P j) w q i = evQ P f q
  | [], i => ⟨j i, fun q => rfl⟩
  | Y :: w, i => gL_ev P l L w Y _ i

theorem Xw_cont (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (w : List ℝ)
    (i : Iota P w.length) : Continuous fun q => Xw P l L (ju P j) w q i := by
  obtain ⟨f, hf⟩ := Xw_ev P l L j w i
  exact (evQ_cont P f).congr fun q => (hf q).symm

theorem Gq_cont : Continuous (Gq P) := by
  unfold Gq; fun_prop

theorem Wq_meas : Measurable (Wq P) := by
  unfold Wq
  have h : Continuous fun q : Qp P.r P.TT => Complex.normSq q.1.2 := by fun_prop
  exact h.measurable.div (h.measurable.sub measurable_const)

theorem Wq_pos (hTT : 0 ≤ P.TT) (q : Qp P.r P.TT) : 0 < Wq P q := by
  have h : P.TT < Complex.normSq q.1.2 := q.2.2
  show 0 < Complex.normSq q.1.2 / (Complex.normSq q.1.2 - P.TT)
  exact div_pos (by linarith) (by linarith)

theorem dwW_meas (l : ℕ) (w : List ℝ) (i : Iota P w.length) : Measurable fun q => dwW P l w q i :=
  ((Wq_meas P).pow_const _).mul_const _

theorem jf_jet {N : ℕ} {X : (ℝ → ℝ) → Qp P.r P.TT → Iota P N → ℂ} (h : MAx2.Jet.JF P N X) :
    ∃ (m : ℕ) (cc : ℕ → Qp P.r P.TT → Iota P N → ℂ), ∀ φ : ℝ → ℝ, LE.SmoothLog φ → ∀ ω a,
      X φ ω a = ∑ q ∈ Finset.range (m + 1), ((LE.ld q φ (Gq P ω) : ℝ) : ℂ) * cc q ω a := by
  have hJ : ∀ a : Iota P N, ∃ (n : ℕ) (qs : Fin n → ℕ) (cc : Fin n → SmQ P.r P.TT), ∀ φ, LE.SmoothLog φ →
      ∀ x, X φ x a = ∑ t, ((LE.ld (qs t) φ (Gq P x) : ℝ) : ℂ) * evQ P (cc t) x := by
    intro a
    obtain ⟨F, ⟨n, qs, cc, hF⟩, hh⟩ := h a
    refine ⟨n, qs, cc, fun φ hφ x => ?_⟩
    refine (hh φ hφ x).trans ?_
    rw [hF φ hφ, MAx2.Jet.evQ_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [MAx2.Jet.evQ_mul, MAx2.Jet.ev_Phi P hφ]
  choose n qs cc hcc using hJ
  refine ⟨Finset.univ.sup fun a => Finset.univ.sup (qs a),
    fun q ω a => ∑ t ∈ Finset.univ.filter (fun t => qs a t = q), evQ P (cc a t) ω, fun φ hφ ω a => ?_⟩
  rw [hcc a φ hφ ω]
  have hmaps : ∀ t ∈ (Finset.univ : Finset (Fin (n a))),
      qs a t ∈ Finset.range ((Finset.univ.sup fun a => Finset.univ.sup (qs a)) + 1) := fun t _ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le ((Finset.le_sup (f := qs a) (Finset.mem_univ t)).trans
      (Finset.le_sup (f := fun a => Finset.univ.sup (qs a)) (Finset.mem_univ a))))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_filter.1 ht).2]

theorem mulF_JF (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (w : List ℝ) :
    MAx2.Jet.JF P w.length (fun φ => LE.mulF (baseQ P) φ (Xw P l L (ju P j) w)) := by
  intro i
  obtain ⟨f, hf⟩ := Xw_ev P l L j w i
  refine ⟨fun φ => MAx2.Jet.Phi P φ 0 * f, ⟨1, fun _ => 0, fun _ => f, fun φ hφ => by simp⟩, fun φ hφ x => ?_⟩
  rw [MAx2.Jet.evQ_mul, MAx2.Jet.ev_Phi P hφ]
  simp only [LE.mulF, LE.ld, iteratedDeriv_zero, Real.exp_log (Gq_pos P x)]
  rw [hf]
  rfl

end

end Formalism.FourierDecayAlt.P.MAx3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MeasureTheory

theorem jet_module_closed : Formalism.FourierDecayAlt.MA.JetQ := by
  intro P l L j lam α β Lb c Ntot hH w hw hl Y hY
  have hL := hH.1.2.2.2.1
  obtain ⟨m, cc, h⟩ := MAx3.jf_jet P (MAx2.Jet.gL_JF P l hL w Y (MAx3.mulF_JF P l L j w))
  exact ⟨m, cc, fun φ hφ ω a => h φ hφ ω a⟩

end Formalism.FourierDecayAlt.P

end S_T2

section S_T3
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MeasureTheory Formalism.FourierDecayAlt.Fr

theorem cwPos (P : M.Par) (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ)
    (hH : Hyps P l L j lam α β Lb Ntot) (w : List ℝ) (hw : (sysQ P l L j lam α β Lb c Ntot).OnBoxes w)
    (hlen : w.length ≤ Ntot) (i : Iota P w.length) :
    0 < (cs (M.x0 P l (ixOf P w.length i).2) (M.qC P) (wordP w) (ixOf P w.length i).1).re := by
  obtain ⟨⟨hOK, hl1, hlk, _, hu, hu', hαβ, hcut⟩, _, _, _, _, _, hL2, _, h6⟩ := hH
  have hBF := Formalism.FourierDecayAlt.P.boxes_fit (sysQ P l L j lam α β Lb c Ntot) hL2 h6
  have hAdm := hBF.2.2 w hw hlen
  have hYI : ∀ Y ∈ w, Y ∈ Set.Icc α β := fun Y hY => hAdm.1 (true, Y) (List.mem_map.2 ⟨Y, hY, rfl⟩)
  have hpw : w.Pairwise fun Y Y' => 2 < |Y - Y'| := by
    have h2 := hAdm.2
    unfold LE.plus at h2
    rw [List.pairwise_map] at h2
    exact h2
  have hcutw : ∀ a ∈ wordP w, a.pt.im = 0 ∧ I.OnCut P.u P.u' l a.pt.re := by
    intro a ha
    obtain ⟨Y', hY', e⟩ := MAx2.mem_wordP ha
    rw [e]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hcut _ (hYI _ hY')⟩
  have hπ := Formalism.FourierDecayAlt.P.types_interlace P hOK (ixOf P w.length i).2
  have hpos := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
    Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true (Fin w.length) P.k P.u P.u'
    (M.rho P (ixOf P w.length i).2) l P.T P.T' (wordP w) hl1 hlk hπ hOK.T_pos hOK.T'_pos hcutw
    (MAx2.pairwise_wordP hpw) (ixOf P w.length i).1
  exact hpos.1

theorem TT_nonneg (P : M.Par) (hOK : P.OK) : 0 ≤ P.TT := (mul_pos hOK.T_pos hOK.T'_pos).le

end Formalism.FourierDecayAlt.P.MAx3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MeasureTheory

theorem weight_positive : Formalism.FourierDecayAlt.MA.WPosQ := by
  intro P l L j lam α β Lb c Ntot hH w hw hl
  have hTT := MAx3.TT_nonneg P hH.1.1
  refine ⟨fun ω i => ?_, fun Y hY ω k => ?_⟩
  · exact mul_pos (pow_pos (MAx3.Wq_pos P hTT ω) _)
      (MAx3.cwPos P l L j lam α β Lb c Ntot hH w hw hl.le i)
  · have hw' : (sysQ P l L j lam α β Lb c Ntot).OnBoxes (Y :: w) := ⟨hY, hw⟩
    exact mul_pos (pow_pos (MAx3.Wq_pos P hTT ω) _)
      (MAx3.cwPos P l L j lam α β Lb c Ntot hH (Y :: w) hw' hl k)

theorem measure_regular : Formalism.FourierDecayAlt.MA.MeasQ := by
  intro P l L j lam α β Lb c Ntot hH w hw hl
  refine ⟨fun i => (MAx3.Xw_cont P l L j w i).measurable, fun i => MAx3.dwW_meas P l w i,
    fun Y hY => ⟨fun k => MAx3.dwW_meas P l (Y :: w) k, fun s k => ?_⟩⟩
  show Measurable fun ω => (((Gq P ω) ^ (-s) : ℝ) : ℂ) * gL P l L w Y _ ω k
  refine Measurable.mul ?_ (MAx3.gL_cont P l L w Y _ k).measurable
  refine Complex.measurable_ofReal.comp ?_
  exact ((MAx3.Gq_cont P).rpow_const fun x => Or.inl (Gq_pos P x).ne').measurable

end Formalism.FourierDecayAlt.P

end S_T3

section S_G_G1
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.G

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable (P : M.Par)

theorem ixOf_iotaOf : ∀ (N : ℕ) (e : Ix (Fin N)) (π : M.Ty P), ixOf P N (iotaOf P N e π) = (e, π)
  | 0, e, π => by
    simp only [ixOf, iotaOf]
    congr 1
    funext i; exact i.elim0
  | N + 1, e, π => by
    simp only [iotaOf, ixOf, ixOf_iotaOf N]
    have h : (if decide (e (Fin.last N) = 1) = true then (1 : Fin 2) else 0) = e (Fin.last N) := by
      generalize e (Fin.last N) = x
      fin_cases x <;> rfl
    simp only [h, Fin.snoc_init_self]

theorem iotaOf_ixOf : ∀ (N : ℕ) (i : Iota P N), iotaOf P N (ixOf P N i).1 (ixOf P N i).2 = i
  | 0, π => rfl
  | N + 1, (b, i) => by
    simp only [ixOf, iotaOf, Fin.snoc_last, Fin.init_snoc, iotaOf_ixOf N i]
    cases b <;> rfl

def iotaEquiv (N : ℕ) : Iota P N ≃ Ix (Fin N) × M.Ty P where
  toFun := ixOf P N
  invFun p := iotaOf P N p.1 p.2
  left_inv := iotaOf_ixOf P N
  right_inv p := ixOf_iotaOf P N p.1 p.2

theorem sum_iota {N : ℕ} (F : Ix (Fin N) → M.Ty P → ℂ) :
    ∑ i : Iota P N, F (ixOf P N i).1 (ixOf P N i).2 = ∑ e, ∑ π, F e π := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (iotaEquiv P N) _ _ fun i => rfl

def fstP : (DQ P).Pr →+* (DQ P).Op := RingHom.fst (DQ P).Op (DQ P).Opᵐᵒᵖ

theorem firstProjection_apply₂ (x : (DQ P).Pr) : fstP P x = x.1 := rfl
theorem pfst_add (x y : (DQ P).Pr) : (x + y).1 = x.1 + y.1 := rfl
theorem pfst_sub (x y : (DQ P).Pr) : (x - y).1 = x.1 - y.1 := rfl
theorem pfst_mul (x y : (DQ P).Pr) : (x * y).1 = x.1 * y.1 := rfl
theorem pfst_zero : (0 : (DQ P).Pr).1 = 0 := rfl
theorem pfst_one : (1 : (DQ P).Pr).1 = 1 := rfl
theorem pfst_neg (x : (DQ P).Pr) : (-x).1 = -x.1 := rfl
theorem pfst_alg (z : ℂ) : (algebraMap ℂ (DQ P).Pr z).1 = algebraMap ℂ (DQ P).Op z := rfl
theorem pfst_smul (z : ℂ) (x : (DQ P).Pr) : (z • x).1 = z • x.1 := by
  rw [Algebra.smul_def, pfst_mul, pfst_alg, ← Algebra.smul_def]
theorem pfst_sum {ι : Type} (s : Finset ι) (x : ι → (DQ P).Pr) : (∑ t ∈ s, x t).1 = ∑ t ∈ s, (x t).1 :=
  map_sum (fstP P) x s

theorem matrix_mul_entry {S : Type} [Fintype S] [DecidableEq S] (b c : SlopeTestRemainingChoices S (A P (DQ P))) (e e' : Ix S)
    (π π' : M.Ty P) : (((b * c) e e') π π').1 = ∑ e'', ∑ π'', ((b e e'') π π'').1 * ((c e'' e') π'' π').1 := by
  show (((b * c : Matrix (Ix S) (Ix S) (Matrix (M.Ty P) (M.Ty P) (DQ P).Pr)) e e') π π').1 = _
  rw [Matrix.mul_apply, Matrix.sum_apply, pfst_sum]
  refine Finset.sum_congr rfl fun e'' _ => ?_
  show (((b e e'' : Matrix (M.Ty P) (M.Ty P) (DQ P).Pr) * c e'' e') π π').1 = _
  rw [Matrix.mul_apply, pfst_sum]
  rfl

theorem matrix_add_entry {S : Type} [Fintype S] [DecidableEq S] (b c : SlopeTestRemainingChoices S (A P (DQ P))) (e e' : Ix S)
    (π π' : M.Ty P) : (((b + c) e e') π π').1 = ((b e e') π π').1 + ((c e e') π π').1 := rfl

theorem matrix_smul_entry {S : Type} [Fintype S] [DecidableEq S] (z : ℂ) (b : SlopeTestRemainingChoices S (A P (DQ P))) (e e' : Ix S)
    (π π' : M.Ty P) : (((z • b) e e') π π').1 = z • ((b e e') π π').1 := pfst_smul P z _

theorem evQ_add (f g : SmQ P.r P.TT) (q : Qp P.r P.TT) : evQ P (f + g) q = evQ P f q + evQ P g q := rfl
theorem evQ_smul (z : ℂ) (f : SmQ P.r P.TT) (q : Qp P.r P.TT) : evQ P (z • f) q = z * evQ P f q := rfl
theorem evQ_zero (q : Qp P.r P.TT) : evQ P 0 q = 0 := rfl

theorem toSm_of_mem {u : Qp P.r P.TT → ℂ} (h : u ∈ smSub P.r P.TT) : toSm P u = ⟨u, h⟩ := by
  unfold toSm; rw [dif_pos h]

theorem evQ_toSm {u : Qp P.r P.TT → ℂ} (h : u ∈ smSub P.r P.TT) (q : Qp P.r P.TT) : evQ P (toSm P u) q = u q := by
  rw [toSm_of_mem P h]; rfl

theorem apply_matrix_def {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (U : Qp P.r P.TT → Iota P N → ℂ) (q : Qp P.r P.TT)
    (i : Iota P N) : wordModuleApply P b U q i = ∑ e', ∑ π', evQ P (((b (ixOf P N i).1 e') (ixOf P N i).2 π').1
      (toSm P fun q' => U q' (iotaOf P N e' π'))) q := rfl

theorem apply_matrix_add {N : ℕ} (b c : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (U : Qp P.r P.TT → Iota P N → ℂ) (q : Qp P.r P.TT)
    (i : Iota P N) : wordModuleApply P (b + c) U q i = wordModuleApply P b U q i + wordModuleApply P c U q i := by
  simp only [wordModuleApply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun π' _ => ?_
  rw [matrix_add_entry]
  rfl

theorem apply_matrix_smul {N : ℕ} (z : ℂ) (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (U : Qp P.r P.TT → Iota P N → ℂ)
    (q : Qp P.r P.TT) (i : Iota P N) : wordModuleApply P (z • b) U q i = z * wordModuleApply P b U q i := by
  simp only [wordModuleApply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun π' _ => ?_
  rw [matrix_smul_entry]
  rfl

theorem apply_matrix_zero {N : ℕ} (U : Qp P.r P.TT → Iota P N → ℂ) (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P 0 U q i = 0 := by
  simp only [wordModuleApply]
  refine Finset.sum_eq_zero fun e' _ => Finset.sum_eq_zero fun π' _ => ?_
  rfl

theorem apply_matrix_sub {N : ℕ} (b c : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (U : Qp P.r P.TT → Iota P N → ℂ) (q : Qp P.r P.TT)
    (i : Iota P N) : wordModuleApply P (b - c) U q i = wordModuleApply P b U q i - wordModuleApply P c U q i := by
  have h := apply_matrix_add P (b - c) c U q i
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem apply_matrix_sum {N : ℕ} {ι : Type} (s : Finset ι) (b : ι → SlopeTestRemainingChoices (Fin N) (A P (DQ P)))
    (U : Qp P.r P.TT → Iota P N → ℂ) (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P (∑ t ∈ s, b t) U q i = ∑ t ∈ s, wordModuleApply P (b t) U q i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [apply_matrix_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, apply_matrix_add, ih]

theorem apply_matrix_smooth {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (U : Qp P.r P.TT → Iota P N → ℂ) (i : Iota P N) :
    (fun q => wordModuleApply P b U q i) ∈ smSub P.r P.TT := by
  have h : (fun q => wordModuleApply P b U q i) = evQ P (∑ e', ∑ π', ((b (ixOf P N i).1 e') (ixOf P N i).2 π').1
      (toSm P fun q' => U q' (iotaOf P N e' π'))) := funext fun q => apply_matrix_eval P b U q i
  rw [h]; exact Subtype.property _

theorem sum4 {α β γ δ X : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid X]
    (f : α → β → γ → δ → X) : ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem op_sum_apply {ι : Type} (s : Finset ι) (T : ι → (DQ P).Op) (f : SmQ P.r P.TT) :
    (∑ t ∈ s, T t) f = ∑ t ∈ s, T t f := LinearMap.sum_apply s T f
theorem op_mul_apply (S T : (DQ P).Op) (f : SmQ P.r P.TT) : (S * T) f = S (T f) := rfl

def actS {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (F : Ix (Fin N) × M.Ty P → SmQ P.r P.TT) :
    Ix (Fin N) × M.Ty P → SmQ P.r P.TT :=
  fun p => ∑ e', ∑ π', ((b p.1 e') p.2 π').1 (F (e', π'))

theorem actS_mul {N : ℕ} (b c : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (F : Ix (Fin N) × M.Ty P → SmQ P.r P.TT) :
    actS P (b * c) F = actS P b (actS P c F) := by
  funext p
  show ∑ e', ∑ π', (((b * c) p.1 e') p.2 π').1 (F (e', π')) =
    ∑ e'', ∑ π'', ((b p.1 e'') p.2 π'').1 (∑ e', ∑ π', ((c e'' e') π'' π').1 (F (e', π')))
  simp only [matrix_mul_entry, op_sum_apply, op_mul_apply, map_sum]
  exact sum4 (fun e' π' e'' π'' => ((b p.1 e'') p.2 π'').1 (((c e'' e') π'' π').1 (F (e', π'))))

theorem apply_matrix_action {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (U : Qp P.r P.TT → Iota P N → ℂ)
    (q : Qp P.r P.TT) (i : Iota P N) : wordModuleApply P b U q i =
      evQ P (actS P b (fun p => toSm P fun q' => U q' (iotaOf P N p.1 p.2)) (ixOf P N i)) q := by
  rw [apply_matrix_def]; unfold actS; rw [MAx2.Jet.evQ_sum]
  exact Finset.sum_congr rfl fun e' _ => (MAx2.Jet.evQ_sum P _ _ q).symm

theorem apply_matrix_mul {N : ℕ} (b c : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (U : Qp P.r P.TT → Iota P N → ℂ)
    (q : Qp P.r P.TT) (i : Iota P N) : wordModuleApply P (b * c) U q i = wordModuleApply P b (wordModuleApply P c U) q i := by
  have hin : ∀ e'' π'', toSm P (fun q' => wordModuleApply P c U q' (iotaOf P N e'' π'')) =
      ∑ e', ∑ π', ((c e'' e') π'' π').1 (toSm P fun q' => U q' (iotaOf P N e' π')) := by
    intro e'' π''
    have h : (fun q' => wordModuleApply P c U q' (iotaOf P N e'' π'')) = evQ P (∑ e', ∑ π',
        ((c (ixOf P N (iotaOf P N e'' π'')).1 e') (ixOf P N (iotaOf P N e'' π'')).2 π').1
          (toSm P fun q' => U q' (iotaOf P N e' π'))) := funext fun q' => apply_matrix_eval P c U q' _
    rw [h, MAx2.Jet.toSm_ev, ixOf_iotaOf]
    rfl
  have hG : actS P c (fun p => toSm P fun q' => U q' (iotaOf P N p.1 p.2)) =
      fun p => toSm P fun q' => wordModuleApply P c U q' (iotaOf P N p.1 p.2) := by
    funext p; rw [hin]; rfl
  rw [apply_matrix_action P (b * c), apply_matrix_action P b (wordModuleApply P c U), actS_mul, hG]

end

end Formalism.FourierDecayAlt.P.MAx3.G

end S_G_G1

section S_G_G2
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.G

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable (P : M.Par)

def mulSub : Subalgebra ℂ (DQ P).Op where
  carrier := {T | ∃ f, T = (DQ P).mulOp f}
  mul_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f * g, MAx1.mulOp_mul _ f g⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f + g, MAx1.mulOp_add _ f g⟩
  algebraMap_mem' z := ⟨algebraMap ℂ _ z, LinearMap.ext fun h => by
    simp [DAlg.mulOp, Algebra.smul_def]⟩

def pr0 : Subalgebra ℂ (DQ P).Pr where
  carrier := {a | a.1 ∈ mulSub P}
  mul_mem' {a b} ha hb := by show a.1 * b.1 ∈ mulSub P; exact mul_mem ha hb
  add_mem' {a b} ha hb := by show a.1 + b.1 ∈ mulSub P; exact add_mem ha hb
  algebraMap_mem' z := Subalgebra.algebraMap_mem (mulSub P) z

abbrev BaseMatrixAlgebra : Subalgebra ℂ (A P (DQ P)) := MAx2.Jet.matSub (pr0 P) (M.Ty P)
abbrev BlockMatrixAlgebra (S : Type) [Fintype S] [DecidableEq S] : Subalgebra ℂ (SlopeTestRemainingChoices S (A P (DQ P))) :=
  MAx2.Jet.matSub (BaseMatrixAlgebra P) (Ix S)

theorem function_mem_base (f fb : SmQ P.r P.TT) : (DQ P).fnP f fb ∈ pr0 P := ⟨f, rfl⟩

theorem scalar_mem_base {w : (DQ P).Pr} (h : w ∈ pr0 P) : sc P (DQ P) w ∈ BaseMatrixAlgebra P := MAx2.Jet.scalar_mem _ _ h

theorem kappa_mem_base (f : M.Ty P → ℂ) : kap P (DQ P) f ∈ BaseMatrixAlgebra P :=
  MAx2.Jet.diag_mem _ _ fun _ => Subalgebra.algebraMap_mem _ _

theorem shift_matrix_mem_base (i : ℕ) : SS P (DQ P) i ∈ BaseMatrixAlgebra P := fun π π' => by
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

section FrobeniusSplitPrimeDatum
variable {S : Type} [Fintype S] [DecidableEq S]

theorem scalar_embed_mem_base {x : A P (DQ P)} (h : x ∈ BaseMatrixAlgebra P) : (io x : SlopeTestRemainingChoices S (A P (DQ P))) ∈ BlockMatrixAlgebra P S :=
  MAx2.Jet.scalar_mem _ _ h

theorem elementary_matrix_mem_base (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S (A P (DQ P))) ∈ BlockMatrixAlgebra P S := fun x y => by
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem insert_mem_base (a : S) (M : Matrix (Fin 2) (Fin 2) (SlopeTestRemainingChoices S (A P (DQ P)))) (h : ∀ i j, M i j ∈ BlockMatrixAlgebra P S) :
    ins a M ∈ BlockMatrixAlgebra P S :=
  Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => mul_mem (elementary_matrix_mem_base P a i j) (h i j)

theorem insert_two_mem_base (a : S) (x y z w : SlopeTestRemainingChoices S (A P (DQ P))) (hx : x ∈ BlockMatrixAlgebra P S) (hy : y ∈ BlockMatrixAlgebra P S)
    (hz : z ∈ BlockMatrixAlgebra P S) (hw : w ∈ BlockMatrixAlgebra P S) : ins a !![x, y; z, w] ∈ BlockMatrixAlgebra P S :=
  insert_mem_base P a _ (MAx2.Jet.matrix_two_mem_sub (BlockMatrixAlgebra P S) x y z w hx hy hz hw)

theorem frame_mem_base (l : ℕ) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) :
    ∀ w : List (Letter ℂ S), (∀ Y, (ofWord L (startM P (DQ P) l) w).ee Y ∈ BlockMatrixAlgebra P S) ∧
      (∀ Y, (ofWord L (startM P (DQ P) l) w).x Y ∈ BlockMatrixAlgebra P S) ∧ (∀ Y, (ofWord L (startM P (DQ P) l) w).xi Y ∈ BlockMatrixAlgebra P S)
  | [] => by
    refine ⟨fun Y => scalar_embed_mem_base P ?_, fun Y => scalar_embed_mem_base P (kappa_mem_base P _), fun Y => scalar_embed_mem_base P (kappa_mem_base P _)⟩
    show eeA P (DQ P) Y ∈ BaseMatrixAlgebra P
    exact mul_mem (mul_mem (scalar_mem_base P (function_mem_base P _ _)) (scalar_mem_base P (function_mem_base P _ _)))
      (Subalgebra.sum_mem _ fun j _ => mul_mem (kappa_mem_base P _) (shift_matrix_mem_base P j))
  | lt :: w => by
    obtain ⟨he, hx, hxi⟩ := frame_mem_base l hL w
    have hzbi : L.ζbi ∈ BaseMatrixAlgebra P := by rw [hL.2.2.2.2.2.2.2.2.2.1]; exact scalar_mem_base P (function_mem_base P _ _)
    have htz : (tz L : SlopeTestRemainingChoices S (A P (DQ P))) ∈ BlockMatrixAlgebra P S := scalar_embed_mem_base P (Subalgebra.smul_mem _ hzbi _)
    have hDD : ∀ Y Ya, (ofWord L (startM P (DQ P) l) w).DD Y Ya ∈ BlockMatrixAlgebra P S := fun Y Ya =>
      Subalgebra.smul_mem _ (sub_mem (he Y) (he Ya)) _
    have h1 : (1 : SlopeTestRemainingChoices S (A P (DQ P))) ∈ BlockMatrixAlgebra P S := Subalgebra.one_mem _
    have h0 : (0 : SlopeTestRemainingChoices S (A P (DQ P))) ∈ BlockMatrixAlgebra P S := Subalgebra.zero_mem _
    simp only [ofWord]
    split_ifs
    · refine ⟨fun Y => ?_, fun Y => ?_, fun Y => ?_⟩
      · exact insert_two_mem_base P _ _ _ _ _ (add_mem (sub_mem (he Y) (hDD Y _)) htz) (neg_mem (Subalgebra.smul_mem _ h1 _)) h0
          (mul_mem (mul_mem (hxi _) (he Y)) (hx _))
      · exact mul_mem (hx Y) (insert_two_mem_base P _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
      · exact mul_mem (hxi Y) (insert_two_mem_base P _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
    · refine ⟨fun Y => ?_, fun Y => ?_, fun Y => ?_⟩
      · exact insert_two_mem_base P _ _ _ _ _ (he Y) h0 (neg_mem (Subalgebra.smul_mem _ (mul_mem (hxi _) (hxi _)) _))
          (add_mem (sub_mem (mul_mem (mul_mem (hxi _) (he Y)) (hx _)) (hDD Y _)) htz)
      · exact mul_mem (hx Y) (insert_two_mem_base P _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
      · exact mul_mem (hxi Y) (insert_two_mem_base P _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)

end FrobeniusSplitPrimeDatum

theorem io_sc_entry {S : Type} [Fintype S] [DecidableEq S] (w : (DQ P).Pr) (e e' : Ix S) (π π' : M.Ty P) :
    (((io (sc P (DQ P) w) : SlopeTestRemainingChoices S (A P (DQ P))) e e') π π').1 = if e = e' ∧ π = π' then w.1 else 0 := by
  by_cases h1 : e = e'
  · subst h1
    by_cases h2 : π = π'
    · subst h2; simp [io, sc, Matrix.scalar_apply]
    · simp only [io, sc, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ h2, h2,
        and_false, if_false]
      rfl
  · simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h1, h1, false_and, if_false]
    rfl

theorem apply_matrix_function {N : ℕ} (g gb : SmQ P.r P.TT) (U : Qp P.r P.TT → Iota P N → ℂ)
    (hU : ∀ i, (fun q => U q i) ∈ smSub P.r P.TT) (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P (io (sc P (DQ P) ((DQ P).fnP g gb))) U q i = evQ P g q * U q i := by
  rw [apply_matrix_def]
  simp only [io_sc_entry]
  rw [Finset.sum_eq_single (ixOf P N i).1]
  · rw [Finset.sum_eq_single (ixOf P N i).2]
    · rw [if_pos ⟨rfl, rfl⟩, iotaOf_ixOf]
      show evQ P g q * evQ P (toSm P fun q' => U q' i) q = _
      rw [evQ_toSm P (hU i)]
    · intro π' _ h; rw [if_neg (fun h' => h h'.2.symm)]; rfl
    · simp
  · intro e' _ h
    refine Finset.sum_eq_zero fun π' _ => ?_
    rw [if_neg (fun h' => h h'.1.symm)]; rfl
  · simp

theorem apply_matrix_pointwise {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (hb : b ∈ BlockMatrixAlgebra P (Fin N))
    (U : Qp P.r P.TT → Iota P N → ℂ) (hU : ∀ i, (fun q => U q i) ∈ smSub P.r P.TT) (q : Qp P.r P.TT)
    (i : Iota P N) : wordModuleApply P b U q i = ∑ i', ptMat P b q i i' * U q i' := by
  have key : ∀ e' π', ∃ f : SmQ P.r P.TT, ((b (ixOf P N i).1 e') (ixOf P N i).2 π').1 = (DQ P).mulOp f :=
    fun e' π' => hb _ _ _ _
  rw [apply_matrix_def]
  have hr : ∑ i', ptMat P b q i i' * U q i' = ∑ i' : Iota P N,
      (fun e' π' => ptMat P b q i (iotaOf P N e' π') * U q (iotaOf P N e' π')) (ixOf P N i').1 (ixOf P N i').2 := by
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [iotaOf_ixOf]
  rw [hr]
  refine Eq.trans ?_ (sum_iota P (fun e' π' => ptMat P b q i (iotaOf P N e' π') * U q (iotaOf P N e' π'))).symm
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun π' _ => ?_
  obtain ⟨f, hf⟩ := key e' π'
  simp only [ptMat, ixOf_iotaOf]
  rw [hf]
  show evQ P f q * evQ P (toSm P fun q' => U q' (iotaOf P N e' π')) q = evQ P f q * 1 * U q (iotaOf P N e' π')
  rw [evQ_toSm P (hU _), mul_one]

end

end Formalism.FourierDecayAlt.P.MAx3.G

end S_G_G2

section S_G_G3
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.G

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable (P : M.Par)

theorem smoothLog_rpow (s : ℝ) : LE.SmoothLog (fun x : ℝ => x ^ s) := by
  unfold LE.SmoothLog
  have h : (fun u : ℝ => (fun x : ℝ => x ^ s) (Real.exp u)) = fun u => Real.exp (u * s) :=
    funext fun u => (Real.exp_mul u s).symm
  rw [h]
  exact Real.contDiff_exp.comp (contDiff_id.mul contDiff_const)

def Gpow (s : ℝ) : SmQ P.r P.TT := MAx2.Jet.Phi P (fun x : ℝ => x ^ s) 0

theorem ev_Gpow (s : ℝ) (q : Qp P.r P.TT) : evQ P (Gpow P s) q = ((Gq P q ^ s : ℝ) : ℂ) := by
  rw [Gpow, MAx2.Jet.ev_Phi P (smoothLog_rpow s)]
  simp only [LE.ld, iteratedDeriv_zero, Real.exp_log (Gq_pos P q)]

theorem log_derivative_rpow (s x : ℝ) (hx : 0 < x) : LE.ld 1 (fun x : ℝ => x ^ s) x = s * x ^ s := by
  unfold LE.ld
  rw [iteratedDeriv_one]
  have h : (fun u : ℝ => (fun x : ℝ => x ^ s) (Real.exp u)) = fun u => Real.exp (u * s) :=
    funext fun u => (Real.exp_mul u s).symm
  rw [h]
  have hd := ((hasDerivAt_id' (Real.log x)).mul_const s).exp
  rw [hd.deriv, Real.rpow_def_of_pos hx]
  ring

theorem Phi1 (s : ℝ) : MAx2.Jet.Phi P (fun x : ℝ => x ^ s) 1 = (s : ℂ) • Gpow P s := by
  apply Subtype.ext; funext q
  show evQ P (MAx2.Jet.Phi P _ 1) q = evQ P ((s : ℂ) • Gpow P s) q
  rw [MAx2.Jet.ev_Phi P (smoothLog_rpow s), evQ_smul, ev_Gpow, log_derivative_rpow s _ (Gq_pos P q)]
  push_cast; ring

theorem euler_Gpow (s : ℝ) (v : M.Var P.r) : eulerQ v (Gpow P s) = ((s : ℂ) • Gpow P s) * MAx2.Jet.kapG P v := by
  have h := MAx2.Jet.euler_Phi P (smoothLog_rpow s) 0 v
  rw [zero_add] at h
  rw [Gpow, h, Phi1]
  rfl

def GpD (s : ℝ) : (DQ P).R := Gpow P s

theorem Gpow_mul_neg (s : ℝ) : Gpow P s * Gpow P (-s) = 1 := by
  apply Subtype.ext; funext q
  show evQ P (Gpow P s * Gpow P (-s)) q = 1
  rw [MAx2.Jet.evQ_mul, ev_Gpow, ev_Gpow, ← Complex.ofReal_mul, ← Real.rpow_add (Gq_pos P q)]
  simp

def cc (m : Fin P.r) : SmQ P.r P.TT := coordQ (M.vc m) * coordQ (M.vcb m)

theorem GQ_eq : MAx2.Jet.GQ P = (∏ m, cc P m) * ggQ P.r P.TT := by
  apply Subtype.ext; funext q
  have h1 : ∀ m, MAx2.Adj.evq q (cc P m) = ((Complex.normSq (q.1.1 m) : ℝ) : ℂ) := by
    intro m
    rw [cc, map_mul, MAx2.Adj.evq_apply, MAx2.Adj.evq_apply]
    show coordE (M.vc m) q.1 * coordE (M.vcb m) q.1 = _
    rw [MAx2.Adj.coordE_vc, MAx2.Adj.coordE_vcb, Complex.mul_conj]
  have h2 : MAx2.Adj.evq q (ggQ P.r P.TT) = ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ) := by
    rw [MAx2.Adj.evq_apply, gg_apply, coordE_vz, coordE_vzb, Complex.mul_conj]
    push_cast; ring
  show ((Gq P q : ℝ) : ℂ) = MAx2.Adj.evq q ((∏ m, cc P m) * ggQ P.r P.TT)
  rw [map_mul, map_prod]
  simp only [h1, h2]
  unfold Gq
  push_cast
  ring

theorem euler_mul (v : M.Var P.r) (f g : SmQ P.r P.TT) : eulerQ v (f * g) = eulerQ v f * g + f * eulerQ v g :=
  Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT v f g

theorem euler_coord (v w : M.Var P.r) : eulerQ (TT := P.TT) v (coordQ w) = if v = w then coordQ w else 0 :=
  Formalism.FourierDecayAlt.P.analytic_coordinates P.r P.TT v w

section Laws
variable {P} (hL : (DQ P).Laws P.TT)
include hL

theorem euler_one (v : M.Var P.r) : eulerQ (TT := P.TT) v (1 : SmQ P.r P.TT) = 0 := MAx1.ev_one hL v

theorem ev_prod_gen (v : M.Var P.r) (f : Fin P.r → SmQ P.r P.TT) (c : Fin P.r → Prop) [DecidablePred c]
    (h : ∀ m, eulerQ v (f m) = if c m then f m else 0) (s : Finset (Fin P.r)) :
    eulerQ v (∏ m ∈ s, f m) = (((s.filter c).card : ℕ) : ℂ) • ∏ m ∈ s, f m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [euler_one hL]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, euler_mul, ih, h a, Finset.filter_insert]
    by_cases hc : c a
    · rw [if_pos hc, if_pos hc, Finset.card_insert_of_notMem (fun h' => ha (Finset.mem_filter.1 h').1)]
      push_cast
      rw [add_smul, one_smul, mul_smul_comm]
      abel
    · rw [if_neg hc, if_neg hc, zero_mul, zero_add, mul_smul_comm]

theorem ev_cc (v : M.Var P.r) (m : Fin P.r) : eulerQ v (cc P m) =
    if v = M.vc m ∨ v = M.vcb m then cc P m else 0 := by
  rw [cc, euler_mul, euler_coord, euler_coord]
  by_cases h1 : v = M.vc m
  · subst h1
    simp only [if_true, MAx1.vc_vcb m m, if_false, true_or]; ring
  · by_cases h2 : v = M.vcb m
    · subst h2
      simp only [(MAx1.vc_vcb m m).symm, if_true, if_false, or_true]; ring
    · simp only [h1, h2, if_false, or_self]; ring

theorem ev_GQ_c (l : Fin P.r) : eulerQ (M.vc l) (MAx2.Jet.GQ P) = MAx2.Jet.GQ P := by
  classical
  have hg : eulerQ (M.vc l) (ggQ P.r P.TT) = 0 := MAx1.euler_gamma_vanish hL _ (MAx1.vc_vz l) (MAx1.vc_vzb l)
  have hc : (Finset.univ.filter fun m => M.vc l = M.vc m ∨ M.vc l = M.vcb m) = {l} := by
    ext m; simp [MAx1.vc_inj, MAx1.vc_vcb, eq_comm]
  rw [GQ_eq, euler_mul, ev_prod_gen hL (M.vc l) (cc P) (fun m => M.vc l = M.vc m ∨ M.vc l = M.vcb m)
    (ev_cc hL _) Finset.univ, hg, hc, Finset.card_singleton]
  simp

theorem ev_GQ_cb (l : Fin P.r) : eulerQ (M.vcb l) (MAx2.Jet.GQ P) = MAx2.Jet.GQ P := by
  classical
  have hg : eulerQ (M.vcb l) (ggQ P.r P.TT) = 0 := MAx1.euler_gamma_vanish hL _ (MAx1.vcb_vz l) (MAx1.vcb_vzb l)
  have hc : (Finset.univ.filter fun m => M.vcb l = M.vc m ∨ M.vcb l = M.vcb m) = {l} := by
    ext m; simp [MAx1.vcb_inj, (MAx1.vc_vcb _ _).symm, eq_comm]
  rw [GQ_eq, euler_mul, ev_prod_gen hL (M.vcb l) (cc P) (fun m => M.vcb l = M.vc m ∨ M.vcb l = M.vcb m)
    (ev_cc hL _) Finset.univ, hg, hc, Finset.card_singleton]
  simp

theorem euler_gamma_product_zeta (v : M.Var P.r) (hv : v = M.vz ∨ v = M.vzb) :
    eulerQ v (MAx2.Jet.GQ P) = (∏ m, cc P m) * (coordQ M.vz * coordQ M.vzb) := by
  classical
  have hc : (Finset.univ.filter fun m => v = M.vc m ∨ v = M.vcb m) = ∅ := by
    ext m
    rcases hv with rfl | rfl <;> simp [(MAx1.vc_vz m).symm, (MAx1.vcb_vz m).symm, (MAx1.vc_vzb m).symm,
      (MAx1.vcb_vzb m).symm]
  have hg : eulerQ v (ggQ P.r P.TT) = coordQ M.vz * coordQ M.vzb := by
    rcases hv with rfl | rfl
    · exact MAx1.euler_GG_z hL
    · exact MAx1.euler_gg_zb hL
  rw [GQ_eq, euler_mul, ev_prod_gen hL v (cc P) (fun m => v = M.vc m ∨ v = M.vcb m) (ev_cc hL _) Finset.univ, hc, hg]
  simp

theorem prod_cc_inv : (∏ m, cc P m) * Ring.inverse (MAx2.Jet.GQ P) = Ring.inverse (ggQ P.r P.TT) := by
  have e1 : ((∏ m, cc P m) * ggQ P.r P.TT) * Ring.inverse (MAx2.Jet.GQ P) = 1 := by
    rw [← GQ_eq]; exact Ring.mul_inverse_cancel _ (MAx2.Jet.GQ_unit P)
  have e2 : ggQ P.r P.TT * Ring.inverse (ggQ P.r P.TT) = 1 := Ring.mul_inverse_cancel _ hL.unit_gg
  linear_combination (Ring.inverse (ggQ P.r P.TT)) * e1 - ((∏ m, cc P m) * Ring.inverse (MAx2.Jet.GQ P)) * e2

theorem kapG_c (l : Fin P.r) : MAx2.Jet.kapG P (M.vc l) = 1 := by
  rw [MAx2.Jet.kapG, ev_GQ_c hL]; exact Ring.mul_inverse_cancel _ (MAx2.Jet.GQ_unit P)

theorem kapG_cb (l : Fin P.r) : MAx2.Jet.kapG P (M.vcb l) = 1 := by
  rw [MAx2.Jet.kapG, ev_GQ_cb hL]; exact Ring.mul_inverse_cancel _ (MAx2.Jet.GQ_unit P)

theorem kapG_alt (v : M.Var P.r) (hv : v = M.vz ∨ v = M.vzb) :
    MAx2.Jet.kapG P v = coordQ M.vz * coordQ M.vzb * Ring.inverse (ggQ P.r P.TT) := by
  rw [MAx2.Jet.kapG, euler_gamma_product_zeta hL v hv, ← prod_cc_inv hL]; ring

theorem ev_Gpow_c (s : ℝ) (l : Fin P.r) : eulerQ (M.vc l) (Gpow P s) = (s : ℂ) • Gpow P s := by
  rw [euler_Gpow, kapG_c hL, mul_one]
theorem ev_Gpow_cb (s : ℝ) (l : Fin P.r) : eulerQ (M.vcb l) (Gpow P s) = (s : ℂ) • Gpow P s := by
  rw [euler_Gpow, kapG_cb hL, mul_one]
theorem ev_Gpow_alt (s : ℝ) (v : M.Var P.r) (hv : v = M.vz ∨ v = M.vzb) : eulerQ v (Gpow P s) =
    ((s : ℂ) • Gpow P s) * (coordQ M.vz * coordQ M.vzb * Ring.inverse (ggQ P.r P.TT)) := by
  rw [euler_Gpow, kapG_alt hL v hv]

theorem pP_Gpow (s : ℝ) (l : Fin P.r) : (DQ P).pP l * (DQ P).fnP (GpD P s) (GpD P s) =
    (DQ P).fnP (GpD P s) (GpD P s) * (DQ P).pP l + algebraMap ℂ (DQ P).Pr (s : ℂ) * (DQ P).fnP (GpD P s) (GpD P s) := by
  rw [MAx1.partialDeriv_mul_fn hL, ← Algebra.smul_def, MAx1.smul_fnP]
  congr 2
  · exact ev_Gpow_c hL s l
  · exact ev_Gpow_cb hL s l

theorem pbP_Gpow (s : ℝ) (l : Fin P.r) : (DQ P).pbP l * (DQ P).fnP (GpD P s) (GpD P s) =
    (DQ P).fnP (GpD P s) (GpD P s) * (DQ P).pbP l + algebraMap ℂ (DQ P).Pr (s : ℂ) * (DQ P).fnP (GpD P s) (GpD P s) := by
  rw [MAx1.partialDerivBar_mul_fn hL, ← Algebra.smul_def, MAx1.smul_fnP]
  congr 2
  · exact ev_Gpow_cb hL s l
  · exact ev_Gpow_c hL s l

theorem coordinate_inverse_zeta : Ring.inverse (coordQ (r := P.r) (TT := P.TT) M.vz) * coordQ M.vz = 1 := MAx1.hz hL
theorem inv_zb : Ring.inverse (coordQ (r := P.r) (TT := P.TT) M.vzb) * coordQ M.vzb = 1 := MAx1.hzb hL

theorem nab_Gpow (s a : ℝ) : MAx1.nabE (DQ P) a P.TT * (DQ P).fnP (GpD P s) (GpD P s) =
    (DQ P).fnP (GpD P s) (GpD P s) * MAx1.nabE (DQ P) a P.TT +
      algebraMap ℂ (DQ P).Pr (s : ℂ) * ((DQ P).zbP * (DQ P).ggiP P.TT * (DQ P).fnP (GpD P s) (GpD P s)) := by
  rw [MAx1.nabE_fn hL, DAlg.zbP, DAlg.ggiP, MAx1.multiplierPair_mul, MAx1.multiplierPair_mul, ← Algebra.smul_def, MAx1.smul_fnP]
  have e1 := ev_Gpow_alt hL s _ (Or.inl rfl)
  have e2 := ev_Gpow_alt hL s _ (Or.inr rfl)
  have hz := coordinate_inverse_zeta hL
  have hzb := inv_zb hL
  congr 2
  · have key : Ring.inverse (coordQ (r := P.r) (TT := P.TT) M.vz) * eulerQ M.vz (Gpow P s) = (s : ℂ) • (coordQ M.vzb * Ring.inverse (ggQ P.r P.TT) * Gpow P s) := by
      rw [e1]; simp only [Algebra.smul_def]
      linear_combination (algebraMap ℂ _ (s : ℂ) * Gpow P s * coordQ M.vzb * Ring.inverse (ggQ P.r P.TT)) * hz
    exact key
  · have key : Ring.inverse (coordQ (r := P.r) (TT := P.TT) M.vzb) * eulerQ M.vzb (Gpow P s) = (s : ℂ) • (coordQ M.vz * Ring.inverse (ggQ P.r P.TT) * Gpow P s) := by
      rw [e2]; simp only [Algebra.smul_def]
      linear_combination (algebraMap ℂ _ (s : ℂ) * Gpow P s * coordQ M.vz * Ring.inverse (ggQ P.r P.TT)) * hzb
    exact key

theorem nabs_Gpow (s a : ℝ) : MAx1.nabsE (DQ P) a P.TT * (DQ P).fnP (GpD P s) (GpD P s) =
    (DQ P).fnP (GpD P s) (GpD P s) * MAx1.nabsE (DQ P) a P.TT -
      algebraMap ℂ (DQ P).Pr (s : ℂ) * ((DQ P).zP * (DQ P).ggiP P.TT * (DQ P).fnP (GpD P s) (GpD P s)) := by
  rw [MAx1.nabsE_fn hL, DAlg.zP, DAlg.ggiP, MAx1.multiplierPair_mul, MAx1.multiplierPair_mul, ← Algebra.smul_def, MAx1.smul_fnP]
  have e1 := ev_Gpow_alt hL s _ (Or.inl rfl)
  have e2 := ev_Gpow_alt hL s _ (Or.inr rfl)
  have hz := coordinate_inverse_zeta hL
  have hzb := inv_zb hL
  congr 2
  · have key : Ring.inverse (coordQ (r := P.r) (TT := P.TT) M.vzb) * eulerQ M.vzb (Gpow P s) = (s : ℂ) • (coordQ M.vz * Ring.inverse (ggQ P.r P.TT) * Gpow P s) := by
      rw [e2]; simp only [Algebra.smul_def]
      linear_combination (algebraMap ℂ _ (s : ℂ) * Gpow P s * coordQ M.vz * Ring.inverse (ggQ P.r P.TT)) * hzb
    exact key
  · have key : Ring.inverse (coordQ (r := P.r) (TT := P.TT) M.vz) * eulerQ M.vz (Gpow P s) = (s : ℂ) • (coordQ M.vzb * Ring.inverse (ggQ P.r P.TT) * Gpow P s) := by
      rw [e1]; simp only [Algebra.smul_def]
      linear_combination (algebraMap ℂ _ (s : ℂ) * Gpow P s * coordQ M.vzb * Ring.inverse (ggQ P.r P.TT)) * hz
    exact key

end Laws

end

end Formalism.FourierDecayAlt.P.MAx3.G

end S_G_G3

section S_G_G4
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.G

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable (P : M.Par)

def Gs (s : ℝ) : A P (DQ P) := sc P (DQ P) ((DQ P).fnP (GpD P s) (GpD P s))

theorem sc_mul (a b : (DQ P).Pr) : sc P (DQ P) a * sc P (DQ P) b = sc P (DQ P) (a * b) := by
  unfold sc; rw [map_mul]
theorem sc_add (a b : (DQ P).Pr) : sc P (DQ P) a + sc P (DQ P) b = sc P (DQ P) (a + b) := by
  unfold sc; rw [map_add]
theorem sc_diag (w : (DQ P).Pr) : sc P (DQ P) w = Matrix.diagonal fun _ => w := by
  unfold sc; rw [Matrix.scalar_apply]
theorem alg_diag (z : ℂ) : algebraMap ℂ (A P (DQ P)) z = Matrix.diagonal fun _ => algebraMap ℂ (DQ P).Pr z := by
  rw [Matrix.algebraMap_eq_diagonal]; rfl
theorem alg_sc (z : ℂ) : algebraMap ℂ (A P (DQ P)) z = sc P (DQ P) (algebraMap ℂ (DQ P).Pr z) := by
  rw [alg_diag, sc_diag]

theorem Gs_mul_neg (s : ℝ) : Gs P s * Gs P (-s) = 1 := by
  rw [Gs, Gs, sc_mul, MAx1.multiplierPair_mul, show GpD P s * GpD P (-s) = 1 from Gpow_mul_neg P s, MAx1.multiplierPair_one]
  unfold sc; exact map_one _

theorem Gs_neg_mul (s : ℝ) : Gs P (-s) * Gs P s = 1 := by
  have := Gs_mul_neg P (-s); rwa [neg_neg] at this

section Lev
variable {P} {L : LevelData (A P (DQ P)) P.r} (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L)
include hTT hL

theorem fns_comm (s : ℝ) : ∀ x ∈ L.fns, x * Gs P s = Gs P s * x := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  have key : ∀ f fb, sc P (DQ P) ((DQ P).fnP f fb) * Gs P s = Gs P s * sc P (DQ P) ((DQ P).fnP f fb) :=
    fun f fb => by rw [Gs, sc_mul, sc_mul, MAx1.multiplierPair_comm]
  intro x hx
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | h)
  · rw [hc]; exact key _ _
  · rw [hci]; exact key _ _
  · rw [hcb]; exact key _ _
  · rw [hcbi]; exact key _ _
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact key _ _
    · rw [hzi]; exact key _ _
    · rw [hzb]; exact key _ _
    · rw [hzbi]; exact key _ _
    · rw [hg]; exact key _ _
    · rw [hgi]; exact key _ _

theorem conj_hat (s : ℝ) (Y : ℂ) :
    Gs P (-s) * L.Ahat Y * Gs P s = L.Ahat (Y + s) ∧ Gs P (-s) * L.R0 Y * Gs P s = L.R0 (Y + s) := by
  have hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL'
  have hpr : ∀ l, L.p l * Gs P s = Gs P s * L.p l + algebraMap ℂ (A P (DQ P)) (s : ℂ) * Gs P s := by
    intro l
    rw [hp]
    show sc P (DQ P) ((DQ P).pP l) * Gs P s = Gs P s * sc P (DQ P) ((DQ P).pP l) + _
    rw [Gs, alg_sc, sc_mul, sc_mul, sc_mul, sc_add, pP_Gpow hLaw]
  have hpbr : ∀ l, L.pb l * Gs P s = Gs P s * L.pb l + algebraMap ℂ (A P (DQ P)) (s : ℂ) * Gs P s := by
    intro l
    rw [hpb]
    show sc P (DQ P) ((DQ P).pbP l) * Gs P s = Gs P s * sc P (DQ P) ((DQ P).pbP l) + _
    rw [Gs, alg_sc, sc_mul, sc_mul, sc_mul, sc_add, pbP_Gpow hLaw]
  have hnr : L.nab * Gs P s = Gs P s * L.nab + algebraMap ℂ (A P (DQ P)) (s : ℂ) * (L.ζb * L.GGi * Gs P s) := by
    rw [hn, hzb, hgi]
    simp only [nabA, zbA, ggiA, Gs, sc_diag, alg_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    congr 1; funext π
    exact nab_Gpow hLaw s (M.aC P π)
  have hnsr : L.nabs * Gs P s = Gs P s * L.nabs - algebraMap ℂ (A P (DQ P)) (s : ℂ) * (L.ζ * L.GGi * Gs P s) := by
    rw [hns, hz, hgi]
    simp only [nabsA, zA, ggiA, Gs, sc_diag, alg_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]
    congr 1; funext π
    exact nabs_Gpow hLaw s (M.aC P π)
  have h := Formalism.FourierDecayAlt.P.gaugeConjugation (A P (DQ P)) P.r L (s : ℂ) (Gs P s) (Gs P (-s)) (Gs_mul_neg P s)
    (Gs_neg_mul P s) (fns_comm hTT hL s) hpr hpbr hnr hnsr Y
  exact ⟨h.1, h.2.1⟩

theorem hat_Gs (s : ℝ) (Y : ℂ) :
    L.Ahat Y * Gs P s = Gs P s * L.Ahat (Y + s) ∧ L.R0 Y * Gs P s = Gs P s * L.R0 (Y + s) := by
  obtain ⟨h1, h2⟩ := conj_hat hTT hL s Y
  constructor
  · rw [← h1, ← mul_assoc, ← mul_assoc, Gs_mul_neg, one_mul]
  · rw [← h2, ← mul_assoc, ← mul_assoc, Gs_mul_neg, one_mul]

theorem D_comm (s : ℝ) : Commute L.Di (Gs P s) ∧ Commute L.Dbi (Gs P s) := by
  have hC : ∀ x ∈ L.fns, Commute x (Gs P s) := fun x hx => fns_comm hTT hL s x hx
  constructor
  · refine (hC _ (by simp [LevelData.fns])).mul_left (Commute.list_prod_left _ _ fun x hx => hC x ?_)
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
    simp [LevelData.fns]
  · refine (hC _ (by simp [LevelData.fns])).mul_left (Commute.list_prod_left _ _ fun x hx => hC x ?_)
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
    simp [LevelData.fns]

end Lev

theorem io_mul {S : Type} [Fintype S] [DecidableEq S] (x y : A P (DQ P)) :
    (io (x * y) : SlopeTestRemainingChoices S (A P (DQ P))) = io x * io y := by unfold io; rw [map_mul]

theorem apply_matrix_gamma_power {N : ℕ} (s : ℝ) (U : Qp P.r P.TT → Iota P N → ℂ) (hU : ∀ i, (fun q => U q i) ∈ smSub P.r P.TT)
    (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P (io (Gs P s)) U q i = ((Gq P q ^ s : ℝ) : ℂ) * U q i := by
  rw [Gs, apply_matrix_function P (GpD P s) (GpD P s) U hU q i]
  unfold GpD
  rw [ev_Gpow]

theorem apply_matrix_gamma_power_left {N : ℕ} (s : ℝ) (B : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (U : Qp P.r P.TT → Iota P N → ℂ)
    (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P (io (Gs P s) * B) U q i = ((Gq P q ^ s : ℝ) : ℂ) * wordModuleApply P B U q i := by
  rw [apply_matrix_mul, apply_matrix_gamma_power P s _ (fun i => apply_matrix_smooth P B U i)]

theorem apply_matrix_gamma_power_mid {N : ℕ} (s : ℝ) (ee B : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (hee : ee ∈ BlockMatrixAlgebra P (Fin N))
    (U : Qp P.r P.TT → Iota P N → ℂ) (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P (ee * (io (Gs P s) * B)) U q i = ((Gq P q ^ s : ℝ) : ℂ) * wordModuleApply P (ee * B) U q i := by
  rw [apply_matrix_mul, apply_matrix_pointwise P ee hee _ (fun i => apply_matrix_smooth P _ U i), apply_matrix_mul,
    apply_matrix_pointwise P ee hee _ (fun i => apply_matrix_smooth P _ U i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [apply_matrix_gamma_power_left]; ring

theorem rpow_neg_mul (x s : ℝ) (hx : 0 < x) : ((x ^ (-s) : ℝ) : ℂ) * ((x ^ s : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero, Complex.ofReal_one]

theorem conjS_gL {l : ℕ} {L : LevelData (A P (DQ P)) P.r} (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L)
    (w : List ℝ) (Y s : ℝ) (X : Qp P.r P.TT → Iota P w.length → ℂ) (hX : ∀ i, (fun q => X q i) ∈ smSub P.r P.TT)
    (q : Qp P.r P.TT) (b : Bool) (i : Iota P w.length) :
    LE.conjS (baseQ P) (gL P l L w Y) X s q (b, i) =
      wordModuleApply P (if b then io (L.Dbi * L.R0 ((Y : ℂ) + s)) + (frW P l L w).ee (Y : ℂ) * io (L.Di * L.Ahat ((Y : ℂ) + s))
        else io (L.Di * L.Ahat ((Y : ℂ) + s))) X q i := by
  have hM : LE.mulF (baseQ P) (fun x => x ^ s) X = wordModuleApply P (io (Gs P s)) X := by
    funext q' i'
    exact (apply_matrix_gamma_power P s X hX q' i').symm
  have hee : (frW P l L w).ee (Y : ℂ) ∈ BlockMatrixAlgebra P (Fin w.length) := (frame_mem_base P l hL (wordP w)).1 _
  obtain ⟨hA, hR⟩ := hat_Gs hTT hL s (Y : ℂ)
  obtain ⟨hDi, hDbi⟩ := D_comm hTT hL s
  unfold LE.conjS
  rw [hM]
  show (((Gq P q) ^ (-s) : ℝ) : ℂ) * wordModuleApply P (if b then g2 P l L w Y else g1 P L w Y) (wordModuleApply P (io (Gs P s)) X) q i = _
  rw [← apply_matrix_mul]
  cases b
  · simp only [Bool.false_eq_true, if_false, g1]
    have e : (io (L.Di * L.Ahat (Y : ℂ)) : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))) * io (Gs P s) =
        io (Gs P s) * io (L.Di * L.Ahat ((Y : ℂ) + s)) := by
      rw [← io_mul, ← io_mul, mul_assoc, hA, ← mul_assoc, hDi.eq, mul_assoc]
    rw [e, apply_matrix_gamma_power_left, ← mul_assoc, rpow_neg_mul _ _ (Gq_pos P q), one_mul]
  · simp only [if_true, g2]
    have e : (io (L.Dbi * L.R0 (Y : ℂ)) + (frW P l L w).ee (Y : ℂ) * io (L.Di * L.Ahat (Y : ℂ)) :
        SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))) * io (Gs P s) =
        io (Gs P s) * io (L.Dbi * L.R0 ((Y : ℂ) + s)) +
          (frW P l L w).ee (Y : ℂ) * (io (Gs P s) * io (L.Di * L.Ahat ((Y : ℂ) + s))) := by
      rw [add_mul, mul_assoc, ← io_mul, ← io_mul, ← io_mul, ← io_mul, mul_assoc, hR, ← mul_assoc, hDbi.eq,
        mul_assoc, mul_assoc (L.Di), hA, ← mul_assoc L.Di, hDi.eq, mul_assoc]
    rw [e, apply_matrix_add, apply_matrix_gamma_power_left, apply_matrix_gamma_power_mid P s _ _ hee, ← mul_add, ← mul_assoc,
      rpow_neg_mul _ _ (Gq_pos P q), one_mul, apply_matrix_add]

end

end Formalism.FourierDecayAlt.P.MAx3.G

end S_G_G4

section S_G_G5
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.G

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

section Poly
variable {R : Type} [Ring R] [Algebra ℂ R]

def PolyIn (f : ℂ → R) (d : ℕ) : Prop := ∃ a : ℕ → R, ∀ s, f s = ∑ k ∈ Finset.range (d + 1), s ^ k • a k

theorem polyIn_const (x : R) : PolyIn (fun _ => x) 0 := ⟨fun _ => x, fun s => by simp⟩

theorem polyIn_mono {f : ℂ → R} {d d' : ℕ} (h : PolyIn f d) (hd : d ≤ d') : PolyIn f d' := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun k => if k ≤ d then a k else 0, fun s => ?_⟩
  rw [ha]
  calc ∑ k ∈ Finset.range (d + 1), s ^ k • a k
      = ∑ k ∈ Finset.range (d + 1), s ^ k • (if k ≤ d then a k else 0) :=
        Finset.sum_congr rfl fun k hk => by rw [if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
    _ = _ := Finset.sum_subset (fun x hx => Finset.mem_range.2 (by have := Finset.mem_range.1 hx; omega)) fun k _ hk => by
        rw [if_neg (fun h => hk (Finset.mem_range.2 (Nat.lt_succ_of_le h))), smul_zero]

theorem polyIn_add {f g : ℂ → R} {d : ℕ} (hf : PolyIn f d) (hg : PolyIn g d) : PolyIn (fun s => f s + g s) d := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨fun k => a k + b k, fun s => by dsimp only; rw [ha, hb, ← Finset.sum_add_distrib]; simp only [smul_add]⟩

theorem polyIn_mul_const {f : ℂ → R} {d : ℕ} (hf : PolyIn f d) (x : R) : PolyIn (fun s => f s * x) d := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => a k * x, fun s => by dsimp only; rw [ha, Finset.sum_mul]; simp only [smul_mul_assoc]⟩

theorem polyIn_const_mul {f : ℂ → R} {d : ℕ} (x : R) (hf : PolyIn f d) : PolyIn (fun s => x * f s) d := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => x * a k, fun s => by dsimp only; rw [ha, Finset.mul_sum]; simp only [mul_smul_comm]⟩

theorem polyIn_smul_var {f : ℂ → R} {d : ℕ} (hf : PolyIn f d) : PolyIn (fun s => s • f s) (d + 1) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun k => if k = 0 then 0 else a (k - 1), fun s => ?_⟩
  dsimp only
  rw [ha, Finset.sum_range_succ' (fun k => s ^ k • (if k = 0 then (0 : R) else a (k - 1))) (d + 1), if_pos rfl,
    smul_zero, add_zero, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, pow_succ, mul_comm, mul_smul]

theorem polyIn_mul_affine {f : ℂ → R} {d : ℕ} (hf : PolyIn f d) (u v : R) :
    PolyIn (fun s => f s * (s • u + v)) (d + 1) := by
  have h := polyIn_add (polyIn_smul_var (polyIn_mul_const hf u)) (polyIn_mono (polyIn_mul_const hf v) (Nat.le_succ d))
  refine (congrArg (fun F => PolyIn F (d + 1)) (funext fun s => ?_)).mp h
  simp only [mul_add, mul_smul_comm]

theorem polyIn_affine_mul {f : ℂ → R} {d : ℕ} (u v : R) (hf : PolyIn f d) :
    PolyIn (fun s => (s • u + v) * f s) (d + 1) := by
  have h := polyIn_add (polyIn_smul_var (polyIn_const_mul u hf)) (polyIn_mono (polyIn_const_mul v hf) (Nat.le_succ d))
  refine (congrArg (fun F => PolyIn F (d + 1)) (funext fun s => ?_)).mp h
  simp only [add_mul, smul_mul_assoc]

theorem polyIn_list_prod : ∀ (l : List (ℂ → R)), (∀ g ∈ l, ∃ u v : R, ∀ s, g s = s • u + v) →
    PolyIn (fun s => (l.map fun g => g s).prod) l.length
  | [], _ => by simpa using polyIn_const (1 : R)
  | g :: l, h => by
    obtain ⟨u, v, huv⟩ := h g List.mem_cons_self
    have ih := polyIn_list_prod l fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    have := polyIn_affine_mul u v ih
    refine (congrArg (fun F => PolyIn F (l.length + 1)) (funext fun s => ?_)).mp this
    simp only [List.map_cons, List.prod_cons, huv]

theorem polyIn_entry {n : Type} [Fintype n] [DecidableEq n] {F : ℂ → Matrix n n R} {d : ℕ} (hF : PolyIn F d)
    (i j : n) : PolyIn (fun s => F s i j) d := by
  obtain ⟨a, ha⟩ := hF
  exact ⟨fun k => a k i j, fun s => by
    show F s i j = _
    rw [ha, Matrix.sum_apply]; rfl⟩

end Poly

variable (P : M.Par)

section Hat
variable (L : LevelData (A P (DQ P)) P.r) (Y0 : ℂ)

theorem Tl_affine (l : Fin P.r) : ∃ u v : Matrix (Fin 2) (Fin 2) (A P (DQ P)),
    ∀ s : ℂ, L.Tl (Y0 + s) l = s • u + v := by
  refine ⟨!![1, 0; 0, 0], L.Tl Y0 l, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, map_add, Algebra.algebraMap_eq_smul_one] <;> abel

theorem Tprod_poly : PolyIn (fun s : ℂ => L.Tprod (Y0 + s)) P.r := by
  have h := polyIn_list_prod ((List.ofFn fun l : Fin P.r => fun s : ℂ => L.Tl (Y0 + s) l).reverse)
    (fun g hg => by
      obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hg)
      exact Tl_affine P L Y0 l)
  rw [List.length_reverse, List.length_ofFn] at h
  refine (congrArg (fun F => PolyIn F P.r) (funext fun s => ?_)).mp h
  simp only [LevelData.Tprod, List.map_reverse, List.map_ofFn]
  rfl

theorem Ahat_poly : PolyIn (fun s : ℂ => L.Ahat (Y0 + s)) P.r :=
  polyIn_const_mul L.Dr (polyIn_entry (Tprod_poly P L Y0) 0 0)

theorem lowering_affine : ∃ u v : A P (DQ P), ∀ s : ℂ, L.l0 (Y0 + s) = s • u + v := by
  refine ⟨-(L.ζb * L.GGi), L.l0 Y0, fun s => ?_⟩
  simp only [LevelData.l0, map_add, Algebra.algebraMap_eq_smul_one, add_mul, smul_mul_assoc, one_mul, smul_neg]
  abel

theorem raising_operator_polynomial : PolyIn (fun s : ℂ => L.R0 (Y0 + s)) (P.r + 1) := by
  obtain ⟨u, v, huv⟩ := lowering_affine P L Y0
  have h1 := polyIn_affine_mul u v (polyIn_entry (Tprod_poly P L Y0) 0 0)
  have h2 := polyIn_mono (polyIn_entry (Tprod_poly P L Y0) 1 0) (Nat.le_succ P.r)
  have h3 := polyIn_const_mul (L.Drb * L.GG) (polyIn_add h1 h2)
  refine (congrArg (fun F => PolyIn F (P.r + 1)) (funext fun s => ?_)).mp h3
  simp only [LevelData.R0, LevelData.Ar, LevelData.Br, huv]

end Hat

theorem io_smul {S : Type} [Fintype S] [DecidableEq S] (z : ℂ) (x : A P (DQ P)) :
    (io (z • x) : SlopeTestRemainingChoices S (A P (DQ P))) = z • io x := by
  unfold io
  simp only [Matrix.scalar_apply]
  ext e e' : 2
  by_cases h : e = e'
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem polyIn_io {S : Type} [Fintype S] [DecidableEq S] {f : ℂ → A P (DQ P)} {d : ℕ} (hf : PolyIn f d) :
    PolyIn (fun s => (io (f s) : SlopeTestRemainingChoices S (A P (DQ P)))) d := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun k => io (a k), fun s => ?_⟩
  dsimp only
  rw [ha]
  unfold io
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := io_smul P (S := S) (s ^ k) (a k)
  unfold io at this
  exact this

end

end Formalism.FourierDecayAlt.P.MAx3.G

end S_G_G5

section S_G_G6
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.G

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable (P : M.Par)

theorem Xw_mem (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (w : List ℝ)
    (i : Iota P w.length) : (fun q => Xw P l L (ju P j) w q i) ∈ smSub P.r P.TT := by
  obtain ⟨f, hf⟩ := MAx3.Xw_ev P l L j w i
  rw [show (fun q => Xw P l L (ju P j) w q i) = evQ P f from funext hf]
  exact f.2

theorem gX_split {l : ℕ} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (w : List ℝ) (Y : ℝ)
    (X : Qp P.r P.TT → Iota P w.length → ℂ) (q : Qp P.r P.TT) (i : Iota P w.length) :
    gL P l L w Y X q (true, i) = wordModuleApply P (io (L.Dbi * L.R0 (Y : ℂ))) X q i +
      ∑ j, ptMat P ((frW P l L w).ee (Y : ℂ)) q i j * gL P l L w Y X q (false, j) := by
  show wordModuleApply P (g2 P l L w Y) X q i = _
  rw [g2, apply_matrix_add, apply_matrix_mul,
    apply_matrix_pointwise P ((frW P l L w).ee (Y : ℂ)) ((frame_mem_base P l hL (wordP w)).1 (Y : ℂ)) (wordModuleApply P (io (L.Di * L.Ahat (Y : ℂ))) X)
      (fun i => apply_matrix_smooth P _ X i)]
  rfl

theorem conjugation_shift_identity {l : ℕ} {L : LevelData (A P (DQ P)) P.r} (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L)
    (w : List ℝ) (X : Qp P.r P.TT → Iota P w.length → ℂ) (hX : ∀ i, (fun q => X q i) ∈ smSub P.r P.TT)
    (Y s : ℝ) (q : Qp P.r P.TT) (i : Iota P w.length) :
    LE.conjS (baseQ P) (gL P l L w Y) X s q (false, i) = gL P l L w (Y + s) X q (false, i) ∧
    LE.conjS (baseQ P) (gL P l L w Y) X s q (true, i) = gL P l L w (Y + s) X q (true, i) +
      ∑ j', (ptMat P ((frW P l L w).ee (Y : ℂ)) q i j' - ptMat P ((frW P l L w).ee ((Y + s : ℝ) : ℂ)) q i j') *
        gL P l L w (Y + s) X q (false, j') := by
  have hc : ((Y + s : ℝ) : ℂ) = (Y : ℂ) + (s : ℂ) := by push_cast; ring
  have hf : ∀ j', gL P l L w (Y + s) X q (false, j') = wordModuleApply P (io (L.Di * L.Ahat ((Y : ℂ) + s))) X q j' :=
    fun j' => by
      show wordModuleApply P (g1 P L w (Y + s)) X q j' = _
      rw [g1, hc]
  refine ⟨?_, ?_⟩
  · rw [conjS_gL P hTT hL w Y s X hX q false i, hf]
    rfl
  · rw [conjS_gL P hTT hL w Y s X hX q true i, gX_split P hL w (Y + s) X q i]
    simp only [if_true, hf, hc]
    rw [apply_matrix_add, apply_matrix_mul,
      apply_matrix_pointwise P ((frW P l L w).ee (Y : ℂ)) ((frame_mem_base P l hL (wordP w)).1 (Y : ℂ)) (wordModuleApply P (io (L.Di * L.Ahat ((Y : ℂ) + s))) X)
        (fun i => apply_matrix_smooth P _ X i), add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j' _ => ?_
    ring

theorem polynomial_shift_identity {l : ℕ} {L : LevelData (A P (DQ P)) P.r} (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L)
    (w : List ℝ) (X : Qp P.r P.TT → Iota P w.length → ℂ) (hX : ∀ i, (fun q => X q i) ∈ smSub P.r P.TT)
    (Y : ℝ) : LE.PolyS (baseQ P) (gL P l L w Y) X (P.r + 1) := by
  have hA := polyIn_io P (S := Fin w.length) (polyIn_const_mul L.Di (Ahat_poly P L (Y : ℂ)))
  have hR := polyIn_io P (S := Fin w.length) (polyIn_const_mul L.Dbi (raising_operator_polynomial P L (Y : ℂ)))
  have hT := polyIn_add hR (polyIn_mono (polyIn_const_mul ((frW P l L w).ee (Y : ℂ)) hA) (Nat.le_succ P.r))
  have hF := polyIn_mono hA (Nat.le_succ P.r)
  obtain ⟨aT, haT⟩ := hT
  obtain ⟨aF, haF⟩ := hF
  dsimp only at haT haF
  refine ⟨fun k q bi => wordModuleApply P (if bi.1 then aT k else aF k) X q bi.2, fun s (q : Qp P.r P.TT) bi => ?_⟩
  obtain ⟨b, i⟩ := bi
  rw [conjS_gL P hTT hL w Y s X hX q b i]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [haF, apply_matrix_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [apply_matrix_smul]
  · simp only [if_true]
    rw [haT, apply_matrix_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [apply_matrix_smul]

end

end Formalism.FourierDecayAlt.P.MAx3.G

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd MAx3.G

theorem fifth_identity_first : Formalism.FourierDecayAlt.MA.EnergyShiftDifference := by
  intro P l L j lam α β Lb c Ntot hH w hw hl Y s hY hYs ω i
  have hOK := hH.1.1
  have hTT : 0 ≤ P.TT := (mul_pos hOK.T_pos hOK.T'_pos).le
  exact conjugation_shift_identity P hTT hH.1.2.2.2.1 w _ (Xw_mem P l L j w) Y s ω i

theorem fourth_identity : Formalism.FourierDecayAlt.MA.EnergyPolynomialInParameter := by
  intro P l L j lam α β Lb c Ntot hH w hw hl Y hY
  have hOK := hH.1.1
  have hTT : 0 ≤ P.TT := (mul_pos hOK.T_pos hOK.T'_pos).le
  exact polynomial_shift_identity P hTT hH.1.2.2.2.1 w _ (Xw_mem P l L j w) Y

end Formalism.FourierDecayAlt.P

end S_G_G6

section S_F_F1
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Wd MeasureTheory

theorem level_unique (P : M.Par) (D : DAlg P.r) (L L' : R.LevelData (A P D) P.r)
    (h : IsModelLevel P D L) (h' : IsModelLevel P D L') : L = L' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ := h'
  cases L; cases L'
  dsimp only at *
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15
  rfl

theorem wordS_length : ∀ v : List (Bool × ℝ), (wordS v).length = v.length
  | [] => rfl
  | x :: v => by simp [wordS, wordS_length v]

theorem plusWord_length (w : List ℝ) : (wordP w).length = w.length := by
  simp [wordP, wordS_length, LE.plus]

theorem wordS_position_lt : ∀ (v : List (Bool × ℝ)), ∀ a ∈ (wordS v), (a.intersection_update_fsHerm_neg_one : ℕ) < v.length
  | [], a, h => by simp [wordS] at h
  | x :: v, a, h => by
    simp only [wordS, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨b, hb, rfl⟩
    · simp
    · have := wordS_position_lt v b hb
      simp only [Fin.coe_castSucc, List.length_cons]
      omega

theorem wordS_nodup : ∀ v : List (Bool × ℝ), ((wordS v).map Letter.intersection_update_fsHerm_neg_one).Nodup
  | [] => by simp [wordS]
  | x :: v => by
    simp only [wordS, List.map_cons, List.map_map, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hm
      rw [List.mem_map] at hm
      obtain ⟨b, hb, e⟩ := hm
      have h1 := wordS_position_lt v b hb
      have h2 := congrArg Fin.val e
      simp only [Function.comp_apply, Fin.coe_castSucc, Fin.val_last] at h2
      omega
    · have := wordS_nodup v
      convert this.map (Fin.castSucc_injective _) using 1
      · rfl
      · rw [List.map_map]
        rfl

theorem plusWord_slots_nodup (w : List ℝ) : ((wordP w).map Letter.intersection_update_fsHerm_neg_one).Nodup := by
  unfold wordP
  rw [List.map_map]
  have e : (wordS (LE.plus w)).map (Letter.intersection_update_fsHerm_neg_one ∘ fun lt => (⟨lt.plus, Fin.cast (by simp [LE.plus]) lt.intersection_update_fsHerm_neg_one, lt.pt⟩ :
      Letter ℂ (Fin w.length))) = ((wordS (LE.plus w)).map Letter.intersection_update_fsHerm_neg_one).map (Fin.cast (by simp [LE.plus])) := by
    simp [List.map_map, Function.comp_def]
  rw [e]
  exact (wordS_nodup _).map (Fin.cast_injective _)

theorem wordS_plus : ∀ v : List (Bool × ℝ), (∀ x ∈ v, x.1 = true) → ∀ a ∈ wordS v, a.plus = true
  | [], _, a, h => by simp [wordS] at h
  | x :: v, hv, a, h => by
    simp only [wordS, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨b, hb, rfl⟩
    · exact hv x (by simp)
    · exact wordS_plus v (fun y hy => hv y (by simp [hy])) b hb

theorem plusWord_letters_plus (w : List ℝ) : ∀ a ∈ wordP w, a.plus = true := by
  intro a ha
  unfold wordP at ha
  rw [List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact wordS_plus _ (fun x hx => by simp [LE.plus] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl) b hb

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F1

section S_F_F2
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Wd MeasureTheory

theorem sum4 {M : Type*} [AddCommMonoid M] {ι : Type*} [Fintype ι] (T : ι → ι → ι → ι → M) :
    ∑ a, ∑ b, ∑ e, ∑ e', T a b e e' = ∑ e, ∑ e', ∑ a, ∑ b, T a b e e' := by
  calc ∑ a, ∑ b, ∑ e, ∑ e', T a b e e' = ∑ a, ∑ e, ∑ e', ∑ b, T a b e e' :=
        Finset.sum_congr rfl fun a _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = ∑ e, ∑ a, ∑ e', ∑ b, T a b e e' := Finset.sum_comm
    _ = ∑ e, ∑ e', ∑ a, ∑ b, T a b e e' := Finset.sum_congr rfl fun e _ => Finset.sum_comm

theorem sandwich {R : Type*} [Ring R] [StarRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F d : Matrix ι ι R) (u : ι → R) :
    ∑ a, ∑ b, star (u a) * (star F * d * F) a b * u b =
      ∑ e, ∑ e', star (∑ e'', F e e'' * u e'') * d e e' * ∑ e'', F e' e'' * u e'' := by
  have h1 : ∀ a b, star (u a) * (star F * d * F) a b * u b =
      ∑ e, ∑ e', star (u a) * (star (F e a) * (d e e' * (F e' b * u b))) := by
    intro a b
    simp only [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have h2 : ∀ e e', star (∑ e'', F e e'' * u e'') * d e e' * ∑ e'', F e' e'' * u e'' =
      ∑ a, ∑ b, star (u a) * (star (F e a) * (d e e' * (F e' b * u b))) := by
    intro e e'
    simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b,
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => h2 e e']
  exact sum4 _

theorem cutWord_of {P : M.Par} {l : ℕ} {L : R.LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
    {lam : Fin (P.k + 2 * P.r + 1) → ℝ} {α β Lb : ℝ} {Ntot : ℕ} (hH : Hyps P l L j lam α β Lb Ntot) (c : LE.Cut)
    (w : List ℝ) (hw : (sysQ P l L j lam α β Lb c Ntot).OnBoxes w) (hlen : w.length ≤ Ntot) :
    M.CutWord P l (wordP w) := by
  obtain ⟨⟨hOK, hl1, hlk, _, hu, hu', hαβ, hcut⟩, _, _, _, _, _, hL2, _, h6⟩ := hH
  have hBF := Formalism.FourierDecayAlt.P.boxes_fit (sysQ P l L j lam α β Lb c Ntot) hL2 h6
  have hAdm := hBF.2.2 w hw hlen
  have hYI : ∀ y ∈ w, y ∈ Set.Icc α β := fun y hy => hAdm.1 (true, y) (List.mem_map.2 ⟨y, hy, rfl⟩)
  have hpw : w.Pairwise fun y y' => 2 < |y - y'| := by
    have := hAdm.2
    unfold LE.plus at this
    rw [List.pairwise_map] at this
    exact this
  refine ⟨plusWord_slots_nodup w, fun a ha => ?_, MAx2.pairwise_wordP hpw⟩
  obtain ⟨y, hy, e⟩ := MAx2.mem_wordP ha
  rw [e]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hcut _ (hYI y hy)⟩

theorem good_of_cut {P : M.Par} {l : ℕ} (w : List ℝ) (h : M.CutWord P l (wordP w)) : Good (wordP w) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun a ha => ?_, ?_⟩
  · exact Complex.conj_eq_iff_im.2 (h2 a ha).1
  · refine h3.imp_of_mem fun {a b} ha hb hab => ?_
    unfold RegL
    rw [if_pos (plusWord_letters_plus w b hb)]
    intro e
    have : a.pt.re - b.pt.re = 1 := by
      have := congrArg Complex.re e
      simpa using this
    rw [this] at hab
    norm_num at hab

theorem prod_eq {B : Type*} [Monoid B] (f : ℂ → B) (w : List ℝ) :
    ((wordP w).reverse.map fun a => f a.pt).prod = ((LE.plus w).reverse.map fun x => f ((x.2 : ℝ) : ℂ)).prod := by
  have e1 : (wordP w).reverse.map (fun a => f a.pt) = (w.map fun y => f ((y : ℝ) : ℂ)).reverse := by
    rw [List.map_reverse]
    congr 1
    have := congrArg (List.map f) (MAx2.plusWord_points w)
    simpa [List.map_map, Function.comp_def] using this
  have e2 : (LE.plus w).reverse.map (fun x => f ((x.2 : ℝ) : ℂ)) = (w.map fun y => f ((y : ℝ) : ℂ)).reverse := by
    rw [List.map_reverse]
    simp [LE.plus, List.map_map, Function.comp_def]
  rw [e1, e2]

end Formalism.FourierDecayAlt.P.MAx3.F

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Wd

theorem theorem_P_form : Formalism.FourierDecayAlt.MA.ThmPForm := by
  intro P l L j lam α β Lb c Ntot hH N Y hN hB ε hε
  obtain ⟨⟨hOK, hl1, hlk, hML, hu, hu', hαβ, hcut⟩, _⟩ := id hH
  have hTT : 0 ≤ P.TT := (mul_pos hOK.T_pos hOK.T'_pos).le
  have hcw := MAx3.F.cutWord_of hH c (List.ofFn Y) hB (by simpa using hN)
  obtain ⟨L', hL', -, -, hFC⟩ := model_frame_analytic P hOK l hl1 hlk
  have hLL := MAx3.F.level_unique P (DQ P) L' L hL' hML
  subst hLL
  have hFr := (hFC (Fin (List.ofFn Y).length) (wordP (List.ofFn Y)) hcw).2.1
  have hMW := (model_words P hOK (DQ P) (analytic_laws P.r P.TT hTT) l (Fin (List.ofFn Y).length)
    (wordP (List.ofFn Y)) (MAx3.F.good_of_cut _ hcw)).1
  rw [MAx3.F.prod_eq] at hMW
  rw [hFr, MAx3.F.plusWord_length] at hMW
  unfold cutoffEnergyForm formFdF
  rw [← hMW, MAx3.F.sandwich]
  rfl

end Formalism.FourierDecayAlt.P

end S_F_F2

section S_F_F3
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd

section Emb

variable {A : Type} [Ring A] {N : ℕ}

def snocE (N : ℕ) : (Ix (Fin N)) × Fin 2 ≃ Ix (Fin (N + 1)) where
  toFun p := Fin.snoc (α := fun _ => Fin 2) p.1 p.2
  invFun E := (Fin.init E, E (Fin.last N))
  left_inv p := by
    obtain ⟨e, b⟩ := p
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv E := Fin.snoc_init_self (α := fun _ => Fin 2) E

theorem sum_snoc {M : Type*} [AddCommMonoid M] (f : Ix (Fin (N + 1)) → M) :
    ∑ E, f E = ∑ e : Ix (Fin N), ∑ b : Fin 2, f (Fin.snoc (α := fun _ => Fin 2) e b) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (snocE N) _ _ fun p => rfl).symm

def embM (M : SlopeTestRemainingChoices (Fin N) A) : SlopeTestRemainingChoices (Fin (N + 1)) A :=
  Matrix.of fun E E' => if E (Fin.last N) = E' (Fin.last N) then M (Fin.init E) (Fin.init E') else 0

theorem embM_apply (M : SlopeTestRemainingChoices (Fin N) A) (E E' : Ix (Fin (N + 1))) :
    embM M E E' = if E (Fin.last N) = E' (Fin.last N) then M (Fin.init E) (Fin.init E') else 0 := rfl

theorem embM_snoc (M : SlopeTestRemainingChoices (Fin N) A) (e e' : Ix (Fin N)) (b b' : Fin 2) :
    embM M (Fin.snoc (α := fun _ => Fin 2) e b) (Fin.snoc (α := fun _ => Fin 2) e' b') = if b = b' then M e e' else 0 := by
  simp [embM_apply, Fin.init_snoc, Fin.snoc_last]

theorem embM_zero : embM (0 : SlopeTestRemainingChoices (Fin N) A) = 0 := by
  ext E E'; simp [embM_apply]

theorem embM_add (M M' : SlopeTestRemainingChoices (Fin N) A) : embM (M + M') = embM M + embM M' := by
  ext E E'; simp only [embM_apply, Matrix.add_apply]; split_ifs <;> simp

theorem init_eq_iff (E E' : Ix (Fin (N + 1))) :
    E = E' ↔ Fin.init E = Fin.init E' ∧ E (Fin.last N) = E' (Fin.last N) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← Fin.snoc_init_self (α := fun _ => Fin 2) E, ← Fin.snoc_init_self (α := fun _ => Fin 2) E', h1, h2]

theorem embM_one : embM (1 : SlopeTestRemainingChoices (Fin N) A) = 1 := by
  ext E E'
  simp only [embM_apply, Matrix.one_apply, init_eq_iff E E']
  by_cases h1 : Fin.init E = Fin.init E' <;> by_cases h2 : E (Fin.last N) = E' (Fin.last N) <;> simp [h1, h2]

theorem embM_mul (M M' : SlopeTestRemainingChoices (Fin N) A) : embM (M * M') = embM M * embM M' := by
  ext E E''
  rw [Matrix.mul_apply, sum_snoc]
  simp only [embM_apply, Fin.init_snoc, Fin.snoc_last, Matrix.mul_apply]
  by_cases h : E (Fin.last N) = E'' (Fin.last N)
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_eq_single (E (Fin.last N))]
    · rw [if_pos rfl, if_pos h]
    · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
    · simp
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases h1 : E (Fin.last N) = b
    · subst h1; rw [if_neg h, mul_zero]
    · rw [if_neg h1, zero_mul]

def embR (A : Type) [Ring A] (N : ℕ) : SlopeTestRemainingChoices (Fin N) A →+* SlopeTestRemainingChoices (Fin (N + 1)) A where
  toFun := embM
  map_one' := embM_one
  map_mul' := embM_mul
  map_zero' := embM_zero
  map_add' := embM_add

theorem embR_apply (M : SlopeTestRemainingChoices (Fin N) A) : embR A N M = embM M := rfl

theorem embM_sum {ι : Type*} (s : Finset ι) (f : ι → SlopeTestRemainingChoices (Fin N) A) : embM (∑ i ∈ s, f i) = ∑ i ∈ s, embM (f i) :=
  map_sum (embR A N) f s

theorem embM_neg (M : SlopeTestRemainingChoices (Fin N) A) : embM (-M) = -embM M := map_neg (embR A N) M

theorem embM_sub (M M' : SlopeTestRemainingChoices (Fin N) A) : embM (M - M') = embM M - embM M' := map_sub (embR A N) M M'

theorem embM_pow (M : SlopeTestRemainingChoices (Fin N) A) (n : ℕ) : embM (M ^ n) = embM M ^ n := map_pow (embR A N) M n

theorem embM_diagonal (d : Ix (Fin N) → A) :
    embM (Matrix.diagonal d) = Matrix.diagonal fun E => d (Fin.init E) := by
  ext E E'
  simp only [embM_apply, Matrix.diagonal_apply, init_eq_iff E E']
  by_cases h1 : Fin.init E = Fin.init E' <;> by_cases h2 : E (Fin.last N) = E' (Fin.last N) <;> simp [h1, h2]

theorem embM_io (x : A) : embM (io x : SlopeTestRemainingChoices (Fin N) A) = io x := by
  unfold io
  rw [Matrix.scalar_apply, Matrix.scalar_apply, embM_diagonal]

theorem embM_smul {K : Type*} [Monoid K] [DistribMulAction K A] (z : K) (M : SlopeTestRemainingChoices (Fin N) A) :
    embM (z • M) = z • embM M := by
  ext E E'; simp only [embM_apply, Matrix.smul_apply]; split_ifs <;> simp

theorem embM_eU (a : Fin N) (i j : Fin 2) : embM (eU a i j : SlopeTestRemainingChoices (Fin N) A) = eU a.castSucc i j := by
  ext E E'
  simp only [embM_apply, eU, Matrix.of_apply]
  have key : (E a.castSucc = i ∧ E' a.castSucc = j ∧ ∀ b, b ≠ a.castSucc → E b = E' b) ↔
      (E (Fin.last N) = E' (Fin.last N) ∧ (Fin.init E a = i ∧ Fin.init E' a = j ∧ ∀ b, b ≠ a → Fin.init E b = Fin.init E' b)) := by
    simp only [Fin.init]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h3 _ (Fin.castSucc_lt_last a).ne', h1, h2, fun b hb => h3 _ ?_⟩
      exact fun e => hb (Fin.castSucc_injective _ e)
    · rintro ⟨h0, h1, h2, h3⟩
      refine ⟨h1, h2, fun b hb => ?_⟩
      induction b using Fin.lastCases with
      | last => exact h0
      | cast b => exact h3 b (fun e => hb (by rw [e]))
  by_cases h : E a.castSucc = i ∧ E' a.castSucc = j ∧ ∀ b, b ≠ a.castSucc → E b = E' b
  · rw [if_pos h]
    obtain ⟨h0, h1⟩ := key.1 h
    rw [if_pos h0, if_pos h1]
  · rw [if_neg h]
    by_cases h0 : E (Fin.last N) = E' (Fin.last N)
    · rw [if_pos h0, if_neg (fun h1 => h (key.2 ⟨h0, h1⟩))]
    · rw [if_neg h0]

theorem embM_ins (a : Fin N) (M : M2 (SlopeTestRemainingChoices (Fin N) A)) : embM (ins a M) = ins a.castSucc (M.map embM) := by
  unfold ins
  rw [embM_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [embM_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [embM_mul, embM_eU]
  rfl

theorem embM_injective : Function.Injective (embM : SlopeTestRemainingChoices (Fin N) A → SlopeTestRemainingChoices (Fin (N + 1)) A) := by
  intro M M' h
  ext e e'
  have := congrFun (congrFun h (Fin.snoc (α := fun _ => Fin 2) e 0)) (Fin.snoc (α := fun _ => Fin 2) e' 0)
  simpa [embM_snoc] using this

theorem embM_star [StarRing A] (M : SlopeTestRemainingChoices (Fin N) A) : embM (star M) = star (embM M) := by
  ext E E'
  simp only [embM_apply, Matrix.star_apply]
  by_cases h : E (Fin.last N) = E' (Fin.last N)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

end Emb

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F3

section S_F_F4
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA

section Rel

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r N : ℕ} (L : LevelData A r)

def liftL (l : Letter ℂ (Fin N)) : Letter ℂ (Fin (N + 1)) := ⟨l.plus, l.intersection_update_fsHerm_neg_one.castSucc, l.pt⟩

structure Rel (f : FrameData (Fin N) A) (f' : FrameData (Fin (N + 1)) A) : Prop where
  F : f'.F = embM f.F
  Fi : f'.Fi = embM f.Fi
  x : ∀ Y, f'.x Y = embM (f.x Y)
  xi : ∀ Y, f'.xi Y = embM (f.xi Y)
  c : f'.c = embM f.c
  ci : f'.ci = embM f.ci
  ee : ∀ Y, f'.ee Y = embM (f.ee Y)
  q : f'.q = f.q
  N : f'.N = f.N
  inv : f'.inv = f.inv
  reg : f'.reg = f.reg

theorem matrix_two_map {α β : Type*} (g : α → β) (a b c d : α) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) α).map g = !![g a, g b; g c, g d] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem embM_mat_mul (M M' : Matrix (Fin 2) (Fin 2) (SlopeTestRemainingChoices (Fin N) A)) :
    (M * M').map embM = M.map embM * M'.map embM := by
  exact Matrix.ext fun i j => RingHom.map_matrix_mul M M' i j (embR A N)

theorem embM_kapL : embM (kapL L : SlopeTestRemainingChoices (Fin N) A) = kapL L := embM_io _
theorem embM_tz : embM (tz L : SlopeTestRemainingChoices (Fin N) A) = tz L := embM_io _
theorem embM_wt : embM (wt L : SlopeTestRemainingChoices (Fin N) A) = wt L := embM_io _

theorem rel_l {f : FrameData (Fin N) A} {f' : FrameData (Fin (N + 1)) A} (h : Rel f f') (Y : ℂ) :
    f'.l L Y = embM (f.l L Y) := by
  unfold FrameData.l
  rw [embM_add, embM_mul, embM_io, embM_kapL, h.ee]

theorem rel_DD {f : FrameData (Fin N) A} {f' : FrameData (Fin (N + 1)) A} (h : Rel f f') (Y Ya : ℂ) :
    f'.DD Y Ya = embM (f.DD Y Ya) := by
  unfold FrameData.DD
  rw [embM_smul, embM_sub, h.ee, h.ee]

theorem embM_scal1 (z : ℂ) : embM (z • (1 : SlopeTestRemainingChoices (Fin N) A)) = z • 1 := by rw [embM_smul, embM_one]

theorem rel_plus {f : FrameData (Fin N) A} {f' : FrameData (Fin (N + 1)) A} (h : Rel f f') (a : Fin N) (Ya : ℂ) :
    Rel (f.plus L a Ya) (f'.plus L a.castSucc Ya) where
  F := by
    show ins a.castSucc _ * f'.F = embM (ins a _ * f.F)
    rw [embM_mul, embM_ins, embM_mat_mul, matrix_two_map, matrix_two_map, h.F, rel_l L h]
    simp only [embM_io, embM_zero, embM_one, embM_mul]
  Fi := by
    show f'.Fi * ins a.castSucc _ = embM (f.Fi * ins a _)
    rw [embM_mul, embM_ins, embM_mat_mul, matrix_two_map, matrix_two_map, h.Fi, rel_l L h]
    simp only [embM_io, embM_zero, embM_one, embM_neg]
  x Y := by
    show f'.x Y * ins a.castSucc _ = embM (f.x Y * ins a _)
    rw [embM_mul, embM_ins, matrix_two_map, h.x]
    simp only [embM_zero, embM_one, embM_scal1]
  xi Y := by
    show f'.xi Y * ins a.castSucc _ = embM (f.xi Y * ins a _)
    rw [embM_mul, embM_ins, matrix_two_map, h.xi]
    simp only [embM_zero, embM_one, embM_scal1]
  c := by
    show f'.c * ins a.castSucc _ = embM (f.c * ins a _)
    rw [embM_mul, embM_ins, matrix_two_map, h.c, h.q, h.xi, h.x]
    simp only [embM_zero, embM_smul]
  ci := by
    show f'.ci * ins a.castSucc _ = embM (f.ci * ins a _)
    rw [embM_mul, embM_ins, matrix_two_map, h.ci, h.q, h.xi, h.x]
    simp only [embM_zero, embM_smul]
  ee Y := by
    show ins a.castSucc _ = embM (ins a _)
    rw [embM_ins, matrix_two_map]
    simp only [embM_zero, embM_add, embM_sub, embM_neg, embM_mul, embM_smul, embM_one, embM_tz, rel_DD h, h.ee,
      h.x, h.xi]
  q := by
    show (fun Y => f'.q Y * _) = fun Y => f.q Y * _
    rw [h.q]
  N := by show f'.N + 1 = f.N + 1; rw [h.N]
  inv := by show f'.inv ∩ _ = f.inv ∩ _; rw [h.inv]
  reg := by show f'.reg ∩ _ = f.reg ∩ _; rw [h.reg]

theorem rel_start (st : Start A) : Rel (st.frame : FrameData (Fin N) A) (st.frame : FrameData (Fin (N + 1)) A) where
  F := embM_one.symm
  Fi := embM_one.symm
  x Y := (embM_io _).symm
  xi Y := (embM_io _).symm
  c := embM_one.symm
  ci := embM_one.symm
  ee Y := (embM_io _).symm
  q := rfl
  N := rfl
  inv := rfl
  reg := rfl

theorem rel_ofWord (st : Start A) :
    ∀ w : List (Letter ℂ (Fin N)), (∀ l ∈ w, l.plus = true) → Rel (ofWord L st w) (ofWord L st (w.map liftL))
  | [], _ => rel_start st
  | l :: w, h => by
    have hl : l.plus = true := h l (by simp)
    have ih := rel_ofWord st w (fun l' hl' => h l' (by simp [hl']))
    simp only [List.map_cons, ofWord]
    rw [if_pos hl, if_pos (show (liftL l).plus = true from hl)]
    exact rel_plus L ih l.intersection_update_fsHerm_neg_one l.pt

end Rel

theorem plusWord_cons (Y : ℝ) (w : List ℝ) :
    wordP (Y :: w) = ⟨true, Fin.last w.length, ((Y : ℝ) : ℂ)⟩ :: (wordP w).map liftL := by
  show List.map _ (Letter.mk true (Fin.last _) _ :: List.map _ (wordS (LE.plus w))) = _
  apply congrArg₂ (· :: ·)
  · show Letter.mk _ _ _ = _
    congr 1
    exact Fin.ext (by rw [Fin.coe_cast, Fin.val_last, List.length_map, Fin.val_last])
  · unfold wordP
    erw [List.map_map, List.map_map]
    refine List.map_congr_left fun lt _ => ?_
    show Letter.mk _ _ _ = Letter.mk _ _ _
    congr 1

theorem mem_of_nodup_of_length_eq {N : ℕ} (l : List (Fin N)) (hn : l.Nodup) (hl : l.length = N) (c : Fin N) : c ∈ l := by
  have h1 : l.toFinset.card = N := by rw [List.toFinset_card_of_nodup hn, hl]
  have h2 : l.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by rw [h1, Fintype.card_fin])
  rw [← List.mem_toFinset, h2]
  exact Finset.mem_univ c

theorem wordP_all_positions (w : List ℝ) (c : Fin w.length) : c ∈ (wordP w).map Letter.intersection_update_fsHerm_neg_one :=
  mem_of_nodup_of_length_eq _ (plusWord_slots_nodup w) (by rw [List.length_map, plusWord_length]) c

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F4

section S_F_F5
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T
open Formalism.FourierDecayAlt.P.MAx2.Jet (matSub mem_matSub diag_mem scalar_mem matrix_two_mem_sub)

section V

variable (P : M.Par) (D : DAlg P.r)

theorem sites_Ts (L : LevelData (A P D) P.r) (hL : IsModelLevel P D L) (Y : ℂ) :
    ((sites P D).map fun σ => Ts σ Y).prod = L.Tprod Y := by
  obtain ⟨hp, hpb, hc, hci, -⟩ := hL
  unfold sites LevelData.Tprod
  rw [List.map_reverse, List.map_ofFn]
  congr 2
  refine congrArg List.ofFn (funext fun l => ?_)
  simp only [Function.comp_apply, Ts, siteA, Tm, LevelData.Tl, hp, hc, hci]

theorem site_vector_first (L : LevelData (A P D) P.r) (hL : IsModelLevel P D L) (Y : ℂ) :
    v0 (sites P D) Y 0 = L.Ar Y := by
  unfold v0 LevelData.Ar; rw [sites_Ts P D L hL]

theorem site_vector_second (L : LevelData (A P D) P.r) (hL : IsModelLevel P D L) (Y : ℂ) :
    v0 (sites P D) Y 1 = L.Br Y := by
  unfold v0 LevelData.Br; rw [sites_Ts P D L hL]

theorem uw_prod (l : ℕ) (hS : SitesOK (K := ℂ) (startM P D l).QQ (sites P D)) (w : List ℝ) (hG : Good (wordP w))
    (z : Ix (Fin w.length)) :
    uw (sites P D) (wordP w) z = ((wordP w).map fun a => v0 (sites P D) a.pt (z a.intersection_update_fsHerm_neg_one)).prod := by
  rw [Formalism.FourierDecayAlt.P.word_product_formula ℂ (A P D) (Fin w.length) _ (sites P D) (wordP w) hS hG z]
  rw [if_pos (fun c hc => absurd (wordP_all_positions w c) hc)]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  rw [if_pos (plusWord_letters_plus w a ha)]

theorem uw_cons (l : ℕ) (hS : SitesOK (K := ℂ) (startM P D l).QQ (sites P D)) (Y : ℝ) (w : List ℝ)
    (hG : Good (wordP (Y :: w))) (hG' : Good (wordP w)) (E : Ix (Fin (w.length + 1))) :
    uw (sites P D) (wordP (Y :: w)) E = v0 (sites P D) ((Y : ℝ) : ℂ) (E (Fin.last w.length)) *
      uw (sites P D) (wordP w) (Fin.init E) := by
  rw [uw_prod P D l hS (Y :: w) hG E, uw_prod P D l hS w hG' (Fin.init E)]
  rw [plusWord_cons, List.map_cons, List.prod_cons, List.map_map]
  rfl

end V

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F5

section S_F_F6
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T
open Formalism.FourierDecayAlt.P.MAx2.Jet (matSub mem_matSub diag_mem scalar_mem matrix_two_mem_sub)

noncomputable section

section Comm

variable (P : M.Par) (D : DAlg P.r) (L : LevelData (A P D) P.r)

def sgen : Set (A P D) :=
  Set.range L.p ∪ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.pb ∪ Set.range L.cb ∪ Set.range L.cbi

def Cz : Subalgebra ℂ (A P D) := Subalgebra.centralizer ℂ (sgen P D L)

theorem mem_Cz {x : A P D} : x ∈ Cz P D L ↔ ∀ y ∈ sgen P D L, y * x = x * y := Subalgebra.mem_centralizer_iff ℂ

theorem fn_mem {x : A P D} (hx : x ∈ L.fns) (hp : ∀ l, L.p l * x = x * L.p l) (hpb : ∀ l, L.pb l * x = x * L.pb l) :
    x ∈ Cz P D L := by
  rw [mem_Cz]
  rintro y (((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
  · exact hp l
  · exact L.fns_comm _ (by simp) _ hx
  · exact L.fns_comm _ (by simp) _ hx
  · exact hpb l
  · exact L.fns_comm _ (by simp) _ hx
  · exact L.fns_comm _ (by simp) _ hx

theorem z_mem : L.ζ ∈ Cz P D L := fn_mem P D L (by unfold LevelData.fns; simp) L.p_ζ L.pb_ζ
theorem zi_mem : L.ζi ∈ Cz P D L := fn_mem P D L (by unfold LevelData.fns; simp) L.p_ζi L.pb_ζi
theorem zb_mem : L.ζb ∈ Cz P D L := fn_mem P D L (by unfold LevelData.fns; simp) L.p_ζb L.pb_ζb
theorem zbi_mem : L.ζbi ∈ Cz P D L := fn_mem P D L (by unfold LevelData.fns; simp) L.p_ζbi L.pb_ζbi
theorem gg_mem : L.GG ∈ Cz P D L := fn_mem P D L (by unfold LevelData.fns; simp) L.p_GG L.pb_GG
theorem ggi_mem : L.GGi ∈ Cz P D L := fn_mem P D L (by unfold LevelData.fns; simp) L.p_GGi L.pb_GGi

theorem nab_mem : L.nab ∈ Cz P D L := by
  rw [mem_Cz]
  rintro y (((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
  · exact L.p_nab l
  · exact (L.nab_c l).symm
  · exact (L.nab_ci l).symm
  · exact L.pb_nab l
  · exact (L.nab_cb l).symm
  · exact (L.nab_cbi l).symm

theorem lowering_mem_centralizer (Y : ℂ) : L.l0 Y ∈ Cz P D L := by
  unfold LevelData.l0
  exact sub_mem (neg_mem (nab_mem P D L)) (mul_mem (Subalgebra.algebraMap_mem _ _)
    (mul_mem (zb_mem P D L) (ggi_mem P D L)))

theorem sc_comm_central (w : D.Pr) (M : A P D) (h : ∀ i j, ∃ z : ℂ, M i j = algebraMap ℂ D.Pr z) :
    sc P D w * M = M * sc P D w := by
  ext i j
  unfold sc
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  obtain ⟨z, hz⟩ := h i j
  rw [hz, Algebra.commutes]

variable {P D L}

theorem central_mem (hL : IsModelLevel P D L) (M : A P D) (h : ∀ i j, ∃ z : ℂ, M i j = algebraMap ℂ D.Pr z) :
    M ∈ Cz P D L := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  rw [mem_Cz]
  rintro y (((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
  · rw [hp]; exact sc_comm_central P D _ M h
  · rw [hc]; exact sc_comm_central P D _ M h
  · rw [hci]; exact sc_comm_central P D _ M h
  · rw [hpb]; exact sc_comm_central P D _ M h
  · rw [hcb]; exact sc_comm_central P D _ M h
  · rw [hcbi]; exact sc_comm_central P D _ M h

theorem kap_mem (hL : IsModelLevel P D L) (f : M.Ty P → ℂ) : kap P D f ∈ Cz P D L := by
  refine central_mem hL _ fun i j => ?_
  rw [show kap P D f = Matrix.diagonal fun π => algebraMap ℂ D.Pr (f π) from rfl]
  by_cases h : i = j
  · subst h; rw [Matrix.diagonal_apply_eq]; exact ⟨f i, rfl⟩
  · rw [Matrix.diagonal_apply_ne _ h]; exact ⟨0, (map_zero _).symm⟩

theorem SS_mem' (hL : IsModelLevel P D L) (i : ℕ) : SS P D i ∈ Cz P D L := by
  refine central_mem hL _ fun a b => ?_
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, (map_zero _).symm⟩

theorem eeA_mem (hL : IsModelLevel P D L) (Y : ℂ) : eeA P D Y ∈ Cz P D L := by
  have hz := hL.2.2.2.2.2.2.1
  have hzbi := hL.2.2.2.2.2.2.2.2.2.1
  unfold eeA
  rw [← hz, ← hzbi]
  refine mul_mem (mul_mem (z_mem P D L) (zbi_mem P D L)) (Subalgebra.sum_mem _ fun j _ => ?_)
  exact mul_mem (kap_mem hL _) (SS_mem' hL j)

end Comm

section GrothendieckCommutativity

variable {P : M.Par} {D : DAlg P.r} {L : LevelData (A P D) P.r} {S : Type} [Fintype S] [DecidableEq S]

abbrev CA (P : M.Par) (D : DAlg P.r) (L : LevelData (A P D) P.r) (S : Type) [Fintype S] [DecidableEq S] :
    Subalgebra ℂ (SlopeTestRemainingChoices S (A P D)) := matSub (Cz P D L) (Ix S)

theorem io_memCA {x : A P D} (h : x ∈ Cz P D L) : (io x : SlopeTestRemainingChoices S (A P D)) ∈ CA P D L S := scalar_mem _ _ h

theorem eU_memCA (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S (A P D)) ∈ CA P D L S := fun x y => by
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact (Cz P D L).one_mem
  · exact (Cz P D L).zero_mem

theorem ins_memCA (a : S) (M : M2 (SlopeTestRemainingChoices S (A P D))) (h : ∀ i j, M i j ∈ CA P D L S) : ins a M ∈ CA P D L S := by
  unfold ins
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => mul_mem (eU_memCA a i j) (h i j)

theorem matrix_two_mem_closure {a b c d : SlopeTestRemainingChoices S (A P D)} (ha : a ∈ CA P D L S) (hb : b ∈ CA P D L S) (hc : c ∈ CA P D L S)
    (hd : d ∈ CA P D L S) : ∀ i j, (!![a, b; c, d] : M2 (SlopeTestRemainingChoices S (A P D))) i j ∈ CA P D L S := by
  intro i j; fin_cases i <;> fin_cases j <;> simpa

theorem mat_mul_memCA {M M' : M2 (SlopeTestRemainingChoices S (A P D))} (h : ∀ i j, M i j ∈ CA P D L S) (h' : ∀ i j, M' i j ∈ CA P D L S) :
    ∀ i j, (M * M') i j ∈ CA P D L S := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subalgebra.sum_mem _ fun k _ => mul_mem (h i k) (h' k j)

theorem smul_memCA (z : ℂ) {M : SlopeTestRemainingChoices S (A P D)} (h : M ∈ CA P D L S) : z • M ∈ CA P D L S := Subalgebra.smul_mem _ h z

structure FOK (f : FrameData S (A P D)) : Prop where
  F : f.F ∈ CA P D L S
  Fi : f.Fi ∈ CA P D L S
  x : ∀ Y, f.x Y ∈ CA P D L S
  xi : ∀ Y, f.xi Y ∈ CA P D L S
  c : f.c ∈ CA P D L S
  ci : f.ci ∈ CA P D L S
  ee : ∀ Y, f.ee Y ∈ CA P D L S

theorem l_memCA {f : FrameData S (A P D)} (h : FOK (L := L) f) (Y : ℂ) : f.l L Y ∈ CA P D L S := by
  unfold FrameData.l kapL
  exact add_mem (io_memCA (lowering_mem_centralizer P D L Y))
    (mul_mem (io_memCA (mul_mem (mul_mem (zb_mem P D L) (zi_mem P D L)) (ggi_mem P D L))) (h.ee Y))

theorem fok_plus {f : FrameData S (A P D)} (h : FOK (L := L) f) (a : S) (Ya : ℂ) : FOK (L := L) (f.plus L a Ya) where
  F := mul_mem (ins_memCA a _ (mat_mul_memCA
    (matrix_two_mem_closure (io_memCA (zi_mem P D L)) (zero_mem _) (zero_mem _) (io_memCA (zbi_mem P D L)))
    (matrix_two_mem_closure (one_mem _) (zero_mem _) (mul_mem (io_memCA (gg_mem P D L)) (l_memCA h Ya)) (io_memCA (gg_mem P D L)))))
    h.F
  Fi := mul_mem h.Fi (ins_memCA a _ (mat_mul_memCA
    (matrix_two_mem_closure (one_mem _) (zero_mem _) (neg_mem (l_memCA h Ya)) (io_memCA (ggi_mem P D L)))
    (matrix_two_mem_closure (io_memCA (z_mem P D L)) (zero_mem _) (zero_mem _) (io_memCA (zb_mem P D L)))))
  x Y := mul_mem (h.x Y) (ins_memCA a _ (matrix_two_mem_closure (smul_memCA _ (one_mem _)) (zero_mem _) (zero_mem _) (one_mem _)))
  xi Y := mul_mem (h.xi Y) (ins_memCA a _ (matrix_two_mem_closure (smul_memCA _ (one_mem _)) (zero_mem _) (zero_mem _) (one_mem _)))
  c := mul_mem h.c (ins_memCA a _ (matrix_two_mem_closure (smul_memCA _ (h.xi _)) (zero_mem _) (zero_mem _) (h.x _)))
  ci := mul_mem h.ci (ins_memCA a _ (matrix_two_mem_closure (smul_memCA _ (h.x _)) (zero_mem _) (zero_mem _) (h.xi _)))
  ee Y := by
    refine ins_memCA a _ (matrix_two_mem_closure ?_ (neg_mem (smul_memCA _ (one_mem _))) (zero_mem _)
      (mul_mem (mul_mem (h.xi _) (h.ee Y)) (h.x _)))
    unfold FrameData.DD tz
    exact add_mem (sub_mem (h.ee Y) (smul_memCA _ (sub_mem (h.ee Y) (h.ee Ya))))
      (io_memCA (Subalgebra.smul_mem _ (zbi_mem P D L) _))

theorem fok_start (hL : IsModelLevel P D L) (l : ℕ) :
    FOK (L := L) ((startM P D l).frame : FrameData S (A P D)) where
  F := one_mem _
  Fi := one_mem _
  x Y := io_memCA (kap_mem hL _)
  xi Y := io_memCA (kap_mem hL _)
  c := one_mem _
  ci := one_mem _
  ee Y := io_memCA (eeA_mem hL Y)

theorem fok_ofWord (hL : IsModelLevel P D L) (l : ℕ) :
    ∀ w : List (Letter ℂ S), (∀ a ∈ w, a.plus = true) → FOK (L := L) (ofWord L (startM P D l) w)
  | [], _ => fok_start hL l
  | a :: w, h => by
    have ha : a.plus = true := h a (by simp)
    simp only [ofWord]
    rw [if_pos ha]
    exact fok_plus (fok_ofWord hL l w fun b hb => h b (by simp [hb])) a.intersection_update_fsHerm_neg_one a.pt

end GrothendieckCommutativity

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F6

section S_F_F7
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T
open Formalism.FourierDecayAlt.P.MAx2.Jet (matSub mem_matSub diag_mem scalar_mem matrix_two_mem_sub)

noncomputable section

section Gen

variable {P : M.Par} {D : DAlg P.r} {L : LevelData (A P D) P.r} {S : Type} [Fintype S] [DecidableEq S]

theorem io_mul_apply (x : A P D) (M : SlopeTestRemainingChoices S (A P D)) (E E' : Ix S) : ((io x : SlopeTestRemainingChoices S (A P D)) * M) E E' = x * M E E' := by
  unfold io; rw [Matrix.scalar_apply, Matrix.diagonal_mul]

theorem mul_io_apply (x : A P D) (M : SlopeTestRemainingChoices S (A P D)) (E E' : Ix S) : (M * (io x : SlopeTestRemainingChoices S (A P D))) E E' = M E E' * x := by
  unfold io; rw [Matrix.scalar_apply, Matrix.mul_diagonal]

theorem commute_io {M : SlopeTestRemainingChoices S (A P D)} (hM : M ∈ CA P D L S) {x : A P D} (hx : x ∈ Algebra.adjoin ℂ (sgen P D L)) :
    Commute M (io x) := by
  refine Matrix.ext fun E E' => ?_
  rw [mul_io_apply, io_mul_apply]
  have h : Commute (M E E') x := Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun y hy =>
    (((mem_Cz P D L).1 (hM E E')) y hy).symm
  exact h.eq

theorem Tl_mem (Y : ℂ) (l : Fin P.r) : ∀ i j, L.Tl Y l i j ∈ Algebra.adjoin ℂ (sgen P D L) := by
  have hs : ∀ y ∈ sgen P D L, y ∈ Algebra.adjoin ℂ (sgen P D L) := fun y hy => Algebra.subset_adjoin hy
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (Subalgebra.algebraMap_mem _ _) (hs _ (by simp [sgen]))
  · exact neg_mem (hs _ (by simp [sgen]))
  · exact hs _ (by simp [sgen])
  · exact zero_mem _

theorem Tprod_mem (Y : ℂ) : L.Tprod Y ∈ matSub (Algebra.adjoin ℂ (sgen P D L)) (Fin 2) := by
  unfold LevelData.Tprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  exact Tl_mem Y l

theorem Ar_mem (Y : ℂ) : L.Ar Y ∈ Algebra.adjoin ℂ (sgen P D L) := Tprod_mem Y 0 0
theorem Br_mem (Y : ℂ) : L.Br Y ∈ Algebra.adjoin ℂ (sgen P D L) := Tprod_mem Y 1 0

end Gen

section Idx

variable (P : M.Par)

theorem ixOf_iotaOf : ∀ (N : ℕ) (e : Ix (Fin N)) (π : M.Ty P), ixOf P N (iotaOf P N e π) = (e, π)
  | 0, e, π => by
    show ((fun i => i.elim0), π) = (e, π)
    congr 1; funext i; exact i.elim0
  | N + 1, e, π => by
    show (Fin.snoc (α := fun _ => Fin 2) (ixOf P N (iotaOf P N (Fin.init e) π)).1
      (if decide (e (Fin.last N) = 1) then 1 else 0), (ixOf P N (iotaOf P N (Fin.init e) π)).2) = (e, π)
    rw [ixOf_iotaOf N (Fin.init e) π]
    have hb : (if decide (e (Fin.last N) = 1) then (1 : Fin 2) else 0) = e (Fin.last N) := by
      rcases Fin.exists_fin_two.1 ⟨e (Fin.last N), rfl⟩ with h | h <;> rw [h] <;> rfl
    rw [hb, Fin.snoc_init_self]

theorem ixOf_succ (N : ℕ) (b : Bool) (i : Iota P N) :
    ixOf P (N + 1) (b, i) = (Fin.snoc (α := fun _ => Fin 2) (ixOf P N i).1 (if b then 1 else 0), (ixOf P N i).2) := rfl

end Idx

section Act

variable (P : M.Par)

def fstH : (DQ P).Pr →+ (DQ P).Op where
  toFun x := x.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem actA_mul (a b : A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT) : actA P (a * b) j = actA P a (actA P b j) := by
  funext π
  have h : ∀ π', ((a * b : Matrix (M.Ty P) (M.Ty P) (DQ P).Pr) π π').1 = ∑ k, (a π k).1 * (b k π').1 := fun π' => by
    rw [Matrix.mul_apply]; exact map_sum (fstH P) (fun k => a π k * b k π') Finset.univ
  show ∑ π', ((a * b : Matrix (M.Ty P) (M.Ty P) (DQ P).Pr) π π').1 (j π') = ∑ π', (a π π').1 (∑ π'', (b π' π'').1 (j π''))
  have h2 : ∀ x, (∑ k, (a π k).1 * (b k x).1) (j x) = ∑ k, (a π k).1 ((b k x).1 (j x)) := fun x => by
    exact (LinearMap.sum_apply Finset.univ (fun k => (a π k).1 * (b k x).1) (j x)).trans rfl
  simp only [h, map_sum]
  rw [Finset.sum_congr rfl fun x _ => h2 x]
  exact Finset.sum_comm

end Act

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F7

section S_F_F8
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T
open Formalism.FourierDecayAlt.P.MAx2.Jet (matSub mem_matSub diag_mem scalar_mem matrix_two_mem_sub)

noncomputable section

section InsLast

variable {A : Type} [Ring A] {N : ℕ}

theorem eU_last_snoc (i j : Fin 2) (e e' : Ix (Fin N)) (c c' : Fin 2) :
    (eU (Fin.last N) i j : SlopeTestRemainingChoices (Fin (N + 1)) A) (Fin.snoc (α := fun _ => Fin 2) e c) (Fin.snoc (α := fun _ => Fin 2) e' c') =
      if c = i ∧ c' = j ∧ e = e' then 1 else 0 := by
  have key : (∀ b, b ≠ Fin.last N → Fin.snoc (α := fun _ => Fin 2) e c b = Fin.snoc (α := fun _ => Fin 2) e' c' b) ↔ e = e' := by
    constructor
    · intro h
      funext k
      have := h k.castSucc (Fin.castSucc_lt_last k).ne
      simpa using this
    · rintro rfl b hb
      induction b using Fin.lastCases with
      | last => exact absurd rfl hb
      | cast k => simp
  simp only [eU, Matrix.of_apply, Fin.snoc_last]
  by_cases h : c = i ∧ c' = j ∧ e = e'
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, key.2 h.2.2⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.1, key.1 h'.2.2⟩)]

theorem ins_last_apply (M : M2 (SlopeTestRemainingChoices (Fin N) A)) (e e' : Ix (Fin N)) (c c' : Fin 2) :
    ins (Fin.last N) (M.map embM) (Fin.snoc (α := fun _ => Fin 2) e c) (Fin.snoc (α := fun _ => Fin 2) e' c') = M c c' e e' := by
  unfold ins
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.map_apply]
  simp only [sum_snoc, eU_last_snoc, embM_snoc, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single c (fun i _ hi => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun e1 _ =>
    Finset.sum_eq_zero fun b _ => if_neg (fun h => hi h.1.symm)) (by simp)]
  rw [Finset.sum_eq_single c' (fun j _ hj => Finset.sum_eq_zero fun e1 _ => Finset.sum_eq_zero fun b _ => by
      by_cases h1 : c = c ∧ b = j ∧ e = e1
      · rw [if_pos h1, if_neg (fun h2 => hj (h1.2.1.symm.trans h2))]
      · rw [if_neg h1]) (by simp)]
  rw [Finset.sum_eq_single e (fun e1 _ he => Finset.sum_eq_zero fun b _ => if_neg (fun h => he h.2.2.symm)) (by simp)]
  rw [Finset.sum_eq_single c' (fun b _ hb => if_neg (fun h => hb h.2.1)) (by simp)]
  simp

end InsLast

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F8

section S_F_F9
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

section abelian₂

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

def abelian₂ {S : Type} [Fintype S] [DecidableEq S] (f : FrameData S A) (Y : ℂ) : M2 (SlopeTestRemainingChoices S A) :=
  !![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Y, io L.GG]

theorem lam_rel {N : ℕ} {f : FrameData (Fin N) A} {f' : FrameData (Fin (N + 1)) A} (h : Rel f f') (Y : ℂ) :
    abelian₂ L f' Y = (abelian₂ L f Y).map embM := by
  unfold abelian₂
  rw [embM_mat_mul, matrix_two_map, matrix_two_map, rel_l L h]
  simp only [embM_io, embM_zero, embM_one, embM_mul]

theorem F_cons (st : Start A) (Y : ℝ) (w : List ℝ) :
    (ofWord L st (wordP (Y :: w))).F =
      ins (Fin.last w.length) ((abelian₂ L (ofWord L st (wordP w)) ((Y : ℝ) : ℂ)).map embM) * embM (ofWord L st (wordP w)).F := by
  have hR := rel_ofWord L st (wordP w) (plusWord_letters_plus w)
  rw [plusWord_cons]
  show ins (Fin.last w.length) (abelian₂ L (ofWord L st ((wordP w).map liftL)) ((Y : ℝ) : ℂ)) *
    (ofWord L st ((wordP w).map liftL)).F = _
  rw [lam_rel L hR, hR.F]

end abelian₂

theorem reorg {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [Fintype κ] (X : κ → ι → R) (F : ι → ι → R) (u : ι → R)
    (vv : κ → R) (hc : ∀ b e' e'', vv b * F e' e'' = F e' e'' * vv b) :
    ∑ e', (∑ b, X b e' * vv b) * ∑ e'', F e' e'' * u e'' = ∑ e'', ∑ b, (∑ e', X b e' * F e' e'') * (vv b * u e'') := by
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  have hc2 : ∀ b e' e'', vv b * (F e' e'' * u e'') = F e' e'' * (vv b * u e'') := fun b e' e'' => by
    rw [← mul_assoc, hc, mul_assoc]
  simp only [hc2]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

section Gw

variable (P : M.Par) (D : DAlg P.r) (L : LevelData (A P D) P.r) (l : ℕ)

def gRw (w : List ℝ) (e : Ix (Fin w.length)) : A P D :=
  ∑ e'', (ofWord L (startM P D l) (wordP w)).F e e'' * uw (sites P D) (wordP w) e''

variable {P D L l}

theorem key_alg (hL : IsModelLevel P D L) (hS : SitesOK (K := ℂ) (startM P D l).QQ (sites P D)) (Y : ℝ) (w : List ℝ)
    (hG : Good (wordP (Y :: w))) (hG' : Good (wordP w)) (c : Fin 2) (e : Ix (Fin w.length)) :
    ∑ e', ((abelian₂ L (ofWord L (startM P D l) (wordP w)) ((Y : ℝ) : ℂ) *ᵥ
        ![io (L.Ar ((Y : ℝ) : ℂ)), io (L.Br ((Y : ℝ) : ℂ))]) c) e e' * gRw P D L l w e' =
      gRw P D L l (Y :: w) (Fin.snoc (α := fun _ => Fin 2) e c) := by
  set f := ofWord L (startM P D l) (wordP w) with hf
  set Λ := abelian₂ L f ((Y : ℝ) : ℂ) with hΛ
  set vv : Fin 2 → A P D := ![L.Ar ((Y : ℝ) : ℂ), L.Br ((Y : ℝ) : ℂ)] with hvv
  have hv : ∀ b, v0 (sites P D) ((Y : ℝ) : ℂ) b = vv b := by
    intro b; fin_cases b
    · exact site_vector_first P D L hL _
    · exact site_vector_second P D L hL _
  have hvi : ∀ b, (![io (L.Ar ((Y : ℝ) : ℂ)), io (L.Br ((Y : ℝ) : ℂ))] : Fin 2 → SlopeTestRemainingChoices (Fin w.length) (A P D)) b = io (vv b) := by
    intro b; fin_cases b <;> rfl
  have hvm : ∀ b, vv b ∈ Algebra.adjoin ℂ (sgen P D L) := by
    intro b; fin_cases b
    · exact Ar_mem _
    · exact Br_mem _
  have hfok := fok_ofWord (L := L) (S := Fin w.length) hL l (wordP w) (plusWord_letters_plus w)
  have hcomm : ∀ b e' e'', vv b * f.F e' e'' = f.F e' e'' * vv b := fun b e' e'' =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hvm b) fun y hy =>
      (((mem_Cz P D L).1 (hfok.F e' e'')) y hy).symm).eq.symm

  have hL1 : ∀ e', ((Λ *ᵥ ![io (L.Ar ((Y : ℝ) : ℂ)), io (L.Br ((Y : ℝ) : ℂ))]) c) e e' = ∑ b, Λ c b e e' * vv b := by
    intro e'
    simp only [Matrix.mulVec, dotProduct, hvi, Matrix.sum_apply, mul_io_apply]

  have hF : ∀ e'' b'', (ofWord L (startM P D l) (wordP (Y :: w))).F (Fin.snoc (α := fun _ => Fin 2) e c)
      (Fin.snoc (α := fun _ => Fin 2) e'' b'') = ∑ e', Λ c b'' e e' * f.F e' e'' := by
    intro e'' b''
    rw [F_cons L (startM P D l) Y w, Matrix.mul_apply, sum_snoc]
    refine Finset.sum_congr rfl fun e' _ => ?_
    simp only [ins_last_apply, embM_snoc, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  unfold gRw
  refine Eq.trans ?_ (sum_snoc (N := w.length) (fun E => (ofWord L (startM P D l) (wordP (Y :: w))).F
    (Fin.snoc (α := fun _ => Fin 2) e c) E * uw (sites P D) (wordP (Y :: w)) E)).symm
  have hR : ∀ e'' b'', (ofWord L (startM P D l) (wordP (Y :: w))).F (Fin.snoc (α := fun _ => Fin 2) e c)
      (Fin.snoc (α := fun _ => Fin 2) e'' b'') * uw (sites P D) (wordP (Y :: w)) (Fin.snoc (α := fun _ => Fin 2) e'' b'') =
      (∑ e', Λ c b'' e e' * f.F e' e'') * (vv b'' * uw (sites P D) (wordP w) e'') := by
    intro e'' b''
    rw [hF, uw_cons P D l hS Y w hG hG', Fin.snoc_last, Fin.init_snoc, hv]
  rw [Finset.sum_congr rfl fun e'' _ => Finset.sum_congr rfl fun b'' _ => hR e'' b'']
  rw [Finset.sum_congr rfl fun e' _ => congrArg (· * _) (hL1 e')]
  exact reorg (fun b e' => Λ c b e e') f.F (uw (sites P D) (wordP w)) vv hcomm

end Gw

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F9

section S_F_F10
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

section Act2

variable (P : M.Par)

theorem actA_zero (j : M.Ty P → SmQ P.r P.TT) : actA P (0 : A P (DQ P)) j = 0 := by
  funext π
  show ∑ π', ((0 : Matrix (M.Ty P) (M.Ty P) (DQ P).Pr) π π').1 (j π') = 0
  exact Finset.sum_eq_zero fun π' _ => rfl

theorem actA_add (a b : A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT) : actA P (a + b) j = actA P a j + actA P b j := by
  funext π
  show ∑ π', ((a + b : Matrix (M.Ty P) (M.Ty P) (DQ P).Pr) π π').1 (j π') =
    ∑ π', (a π π').1 (j π') + ∑ π', (b π π').1 (j π')
  rw [← Finset.sum_add_distrib]
  rfl

theorem actA_sum {ι : Type} (s : Finset ι) (f : ι → A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT) :
    actA P (∑ i ∈ s, f i) j = ∑ i ∈ s, actA P (f i) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [actA_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, actA_add, ih]

theorem apply_matrix_vector {N : ℕ} (Mx : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (g : Ix (Fin N) → A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT)
    (U : Qp P.r P.TT → Iota P N → ℂ)
    (hU : ∀ i q, U q i = evQ P (actA P (g (ixOf P N i).1) j (ixOf P N i).2) q) (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P Mx U q i = evQ P (actA P (∑ e', Mx (ixOf P N i).1 e' * g e') j (ixOf P N i).2) q := by
  have h1 : ∀ e' π', toSm P (fun q' => U q' (iotaOf P N e' π')) = actA P (g e') j π' := by
    intro e' π'
    have : (fun q' => U q' (iotaOf P N e' π')) = evQ P (actA P (g e') j π') := funext fun q' => by
      rw [hU, ixOf_iotaOf]
    rw [this]
    exact MAx2.Jet.toSm_ev P _
  unfold wordModuleApply
  simp only [h1]
  rw [actA_sum, Finset.sum_apply, MAx2.Jet.evQ_sum]
  refine Finset.sum_congr rfl fun e' _ => ?_
  rw [actA_mul]
  show _ = evQ P (∑ π', ((Mx (ixOf P N i).1 e') (ixOf P N i).2 π').1 (actA P (g e') j π')) q
  exact (MAx2.Jet.evQ_sum P _ _ q).symm

end Act2

section Cut

theorem cut_tail {P : M.Par} {l : ℕ} (Y : ℝ) (w : List ℝ) (h : M.CutWord P l (wordP (Y :: w))) :
    M.CutWord P l (wordP w) := by
  obtain ⟨_, h2, h3⟩ := h
  rw [plusWord_cons] at h2 h3
  refine ⟨plusWord_slots_nodup w, fun a ha => ?_, ?_⟩
  · exact h2 (liftL a) (List.mem_cons_of_mem _ (List.mem_map_of_mem ha))
  · have := (List.pairwise_cons.1 h3).2
    rw [List.pairwise_map] at this
    exact this

end Cut

section XwEq

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

theorem Xw_eq (hL : IsModelLevel P (DQ P) L) (hS : SitesOK (K := ℂ) (startM P (DQ P) l).QQ (sites P (DQ P)))
    (hFr : ∀ w : List ℝ, M.CutWord P l (wordP w) → IsFrame L (ofWord L (startM P (DQ P) l) (wordP w)))
    (j : M.Ty P → SmQ P.r P.TT) :
    ∀ w : List ℝ, M.CutWord P l (wordP w) → ∀ i q,
      Xw P l L (ju P j) w q i = evQ P (actA P (gRw P (DQ P) L l w (ixOf P _ i).1) j (ixOf P _ i).2) q
  | [], _, i, q => by
    have hu : ∀ e'', uw (sites P (DQ P)) (wordP []) e'' = 1 := fun e'' => by
      rw [uw_prod P (DQ P) l hS [] ⟨List.nodup_nil, fun a ha => absurd ha List.not_mem_nil, List.Pairwise.nil⟩]
      rfl
    have hg : ∀ e : Ix (Fin ([] : List ℝ).length), gRw P (DQ P) L l [] e = 1 := by
      intro e
      unfold gRw
      simp only [hu, mul_one]
      refine (Finset.sum_eq_single_of_mem e (Finset.mem_univ e) ?_).trans (Matrix.one_apply_eq e)
      intro b _ hb
      exact absurd (funext fun k => Fin.elim0 k) hb
    rw [hg, MAx3.one_act]
    rfl
  | Y :: w, hcw, ⟨b, i⟩, q => by
    have hcw' := cut_tail Y w hcw
    have IH := Xw_eq hL hS hFr j w hcw'
    show wordModuleApply P (if b then g2 P l L w Y else g1 P L w Y) (Xw P l L (ju P j) w) q i = _
    rw [apply_matrix_vector P _ _ j _ IH]
    have hNL := Formalism.FourierDecayAlt.P.new_vector_letter_plus (A P (DQ P)) (Fin w.length) P.r L
      (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) ((hFr w hcw').ee_fn _)
    have hG := good_of_cut (Y :: w) hcw
    have hG' := good_of_cut w hcw'
    have hsum : ∀ (c : Fin 2) (G : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))),
        G = (abelian₂ L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) *ᵥ
          ![io (L.Ar ((Y : ℝ) : ℂ)), io (L.Br ((Y : ℝ) : ℂ))]) c →
        ∑ e', G (ixOf P w.length i).1 e' * gRw P (DQ P) L l w e' =
          gRw P (DQ P) L l (Y :: w) (Fin.snoc (α := fun _ => Fin 2) (ixOf P w.length i).1 c) := by
      rintro c G rfl
      exact key_alg hL hS Y w hG hG' c (ixOf P w.length i).1
    cases b
    · exact congrArg (fun X => evQ P (actA P X j (ixOf P w.length i).2) q) (hsum 0 _ (congrFun hNL 0).symm)
    · exact congrArg (fun X => evQ P (actA P X j (ixOf P w.length i).2) q) (hsum 1 _ (congrFun hNL 1).symm)

end XwEq

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F10

section S_F_F11
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd

section Free

variable {A : Type} [Ring A] {N : ℕ}

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

theorem eU_mul_snoc (i j : Fin 2) (X : SlopeTestRemainingChoices (Fin (N + 1)) A) (e e' : Ix (Fin N)) (b b' : Fin 2) :
    ((eU (Fin.last N) i j : SlopeTestRemainingChoices (Fin (N + 1)) A) * X) (sn e b) (sn e' b') = if b = i then X (sn e j) (sn e' b') else 0 := by
  rw [Matrix.mul_apply, sum_snoc]
  simp only [eU_last_snoc, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single e (fun e1 _ he => Finset.sum_eq_zero fun c1 _ => if_neg fun h => he h.2.2.symm) (by simp)]
  rw [Finset.sum_eq_single j (fun c1 _ hc => if_neg fun h => hc h.2.1) (by simp)]
  by_cases h : b = i
  · rw [if_pos ⟨h, rfl, rfl⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

theorem mul_eU_snoc (i j : Fin 2) (X : SlopeTestRemainingChoices (Fin (N + 1)) A) (e e' : Ix (Fin N)) (b b' : Fin 2) :
    (X * (eU (Fin.last N) i j : SlopeTestRemainingChoices (Fin (N + 1)) A)) (sn e b) (sn e' b') = if b' = j then X (sn e b) (sn e' i) else 0 := by
  rw [Matrix.mul_apply, sum_snoc]
  simp only [eU_last_snoc, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single e' (fun e1 _ he => Finset.sum_eq_zero fun c1 _ => if_neg fun h => he h.2.2) (by simp)]
  rw [Finset.sum_eq_single i (fun c1 _ hc => if_neg fun h => hc h.1) (by simp)]
  by_cases h : b' = j
  · rw [if_pos ⟨rfl, h, rfl⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2.1), if_neg h]

def resM (X : SlopeTestRemainingChoices (Fin (N + 1)) A) : SlopeTestRemainingChoices (Fin N) A := fun e e' => X (sn e 0) (sn e' 0)

theorem free_embM {X : SlopeTestRemainingChoices (Fin (N + 1)) A} (hX : FreeOf (Fin.last N) X) : X = embM (resM X) := by
  have key : ∀ e e' b b', X (sn e b) (sn e' b') = if b = b' then X (sn e 0) (sn e' 0) else 0 := by
    intro e e' b b'
    by_cases h : b = b'
    · subst h
      rw [if_pos rfl]
      have := congrFun (congrFun (hX b 0).eq (sn e b)) (sn e' 0)
      rw [eU_mul_snoc, mul_eU_snoc, if_pos rfl, if_pos rfl] at this
      exact this.symm
    · rw [if_neg h]
      have := congrFun (congrFun (hX b b).eq (sn e b)) (sn e' b')
      rw [eU_mul_snoc, mul_eU_snoc, if_pos rfl, if_neg (Ne.symm h)] at this
      exact this
  ext E E'
  rw [← Fin.snoc_init_self (α := fun _ => Fin 2) E, ← Fin.snoc_init_self (α := fun _ => Fin 2) E', key, embM_snoc]
  rfl

theorem embM_free (X : SlopeTestRemainingChoices (Fin N) A) : FreeOf (Fin.last N) (embM X) := by
  intro i j
  show (eU (Fin.last N) i j : SlopeTestRemainingChoices (Fin (N + 1)) A) * embM X = embM X * eU (Fin.last N) i j
  ext E E'
  rw [← Fin.snoc_init_self (α := fun _ => Fin 2) E, ← Fin.snoc_init_self (α := fun _ => Fin 2) E', eU_mul_snoc,
    mul_eU_snoc, embM_snoc, embM_snoc]
  generalize Fin.init E = e; generalize Fin.init E' = e'
  generalize E (Fin.last N) = b; generalize E' (Fin.last N) = b'
  by_cases h1 : b = i <;> by_cases h2 : b' = j <;> by_cases h3 : j = b' <;> by_cases h4 : b = i <;> simp_all

theorem ins_inj_last {M1 M2 : M2 (SlopeTestRemainingChoices (Fin (N + 1)) A)} (h1 : FreeOf2 (Fin.last N) M1) (h2 : FreeOf2 (Fin.last N) M2)
    (h : ins (Fin.last N) M1 = ins (Fin.last N) M2) : M1 = M2 := by
  have e1 : M1 = (M1.map resM).map embM := Matrix.ext fun i j => free_embM (h1 i j)
  have e2 : M2 = (M2.map resM).map embM := Matrix.ext fun i j => free_embM (h2 i j)
  have key : M1.map resM = M2.map resM := by
    ext i j e e'
    have := congrFun (congrFun h (sn e i)) (sn e' j)
    rw [e1, e2, ins_last_apply, ins_last_apply] at this
    exact this
  rw [e1, e2, key]

end Free

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F11

section S_F_F12
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

section Lift

variable {A : Type} [Ring A] {N : ℕ}

theorem free_of_last_map (M : M2 (SlopeTestRemainingChoices (Fin N) A)) : FreeOf2 (Fin.last N) (M.map embM) := fun i j => embM_free (M i j)

theorem free_of_last_diagonal {b : SlopeTestRemainingChoices (Fin (N + 1)) A} (hb : FreeOf (Fin.last N) b) : FreeOf2 (Fin.last N) (d0 b) := by
  intro i j k l
  unfold d0
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hb k l
  · exact Commute.zero_right _

theorem free_mul {a : Fin (N + 1)} {x y : SlopeTestRemainingChoices (Fin (N + 1)) A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x * y) :=
  fun i j => (hx i j).mul_right (hy i j)

theorem free_add {a : Fin (N + 1)} {x y : SlopeTestRemainingChoices (Fin (N + 1)) A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x + y) :=
  fun i j => (hx i j).add_right (hy i j)

theorem freeOf2_mul {a : Fin (N + 1)} {M M' : M2 (SlopeTestRemainingChoices (Fin (N + 1)) A)} (h : FreeOf2 a M) (h' : FreeOf2 a M') :
    FreeOf2 a (M * M') := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact free_add (free_mul (h i 0) (h' 0 j)) (free_mul (h i 1) (h' 1 j))

theorem map_embM_mul (M M' : M2 (SlopeTestRemainingChoices (Fin N) A)) : (M * M').map embM = M.map embM * M'.map embM :=
  Matrix.ext fun i j => RingHom.map_matrix_mul M M' i j (embR A N)

theorem map_embM_conjT [StarRing A] (M : M2 (SlopeTestRemainingChoices (Fin N) A)) : (Mᴴ).map embM = (M.map embM)ᴴ := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, embM_star]

theorem diffZero_natural (b : SlopeTestRemainingChoices (Fin N) A) : (d0 b).map embM = d0 (embM b) := by
  ext i j : 1
  simp only [d0, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact embM_zero

end Lift

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F12

section S_F_F13
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

section Words

variable {P : M.Par} {l : ℕ}

theorem cut_lift_tail (Y : ℝ) (w : List ℝ) (h : M.CutWord P l (wordP (Y :: w))) :
    M.CutWord P l ((wordP w).map liftL) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [plusWord_cons] at h1 h2 h3
  rw [List.map_cons] at h1
  exact ⟨(List.nodup_cons.1 h1).2, fun a ha => h2 a (List.mem_cons_of_mem _ ha), (List.pairwise_cons.1 h3).2⟩

theorem good_of_cutW {S : Type} (w : List (Letter ℂ S)) (hp : ∀ a ∈ w, a.plus = true) (h : M.CutWord P l w) : Good w := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun a ha => Complex.conj_eq_iff_im.2 (h2 a ha).1, ?_⟩
  refine h3.imp_of_mem fun {a b} ha hb hab => ?_
  unfold RegL
  rw [if_pos (hp b hb)]
  intro e
  have : a.pt.re - b.pt.re = 1 := by
    have := congrArg Complex.re e
    simpa using this
  rw [this] at hab
  norm_num at hab

theorem liftL_plus (w : List ℝ) : ∀ a ∈ (wordP w).map liftL, a.plus = true := by
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact plusWord_letters_plus w b hb

theorem reg_new (Y : ℝ) (w : List ℝ) (h : M.CutWord P l (wordP (Y :: w))) :
    Reg ((wordP w).map liftL) ((Y : ℝ) : ℂ) := by
  obtain ⟨-, h2, h3⟩ := h
  rw [plusWord_cons] at h3
  have hh := (List.pairwise_cons.1 h3).1
  intro a ha
  unfold RegL
  rw [if_pos (liftL_plus w a ha)]
  intro e
  have h4 := hh a ha
  have : ((Y : ℝ) : ℂ).re - a.pt.re = 1 := by
    have := congrArg Complex.re e
    simpa using this
  simp only at h4
  rw [this] at h4
  norm_num at h4

end Words

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F13

section S_F_F14
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

section Defs

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r) {S : Type} [Fintype S] [DecidableEq S]

def Dg (f : FrameData S A) (Y : ℂ) : M2 (SlopeTestRemainingChoices S A) := !![f.q Y • f.xi (Y + 1), 0; 0, f.x Y]

def DnM (f : FrameData S A) (n : ℕ) (Y : ℂ) : M2 (SlopeTestRemainingChoices S A) := d0 (wt L ^ (n + 1) * f.c) * Dg f Y

def gv (f : FrameData S A) (Y : ℂ) : Fin 2 → SlopeTestRemainingChoices S A := abelian₂ L f Y *ᵥ ![io (L.Ar Y), io (L.Br Y)]

def Kop (f : FrameData S A) (n : ℕ) (Y : ℂ) : SlopeTestRemainingChoices S A := ∑ b, star (gv L f Y b) * DnM L f n Y b b * gv L f Y b

end Defs

section DescentVanishingReductions

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

theorem core1 (hFC : ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), M.CutWord P l w →
      FrameConcl P (DQ P) l L w)
    (Y : ℝ) (w : List ℝ) (hcw : M.CutWord P l (wordP (Y :: w))) :
    star (ins (Fin.last w.length) (abelian₂ L (ofWord L (startM P (DQ P) l) ((wordP w).map liftL)) ((Y : ℝ) : ℂ))) *
        (wt L ^ (w.length + 1) * ((ofWord L (startM P (DQ P) l) ((wordP w).map liftL)).c *
          ins (Fin.last w.length) (Dg (ofWord L (startM P (DQ P) l) ((wordP w).map liftL)) ((Y : ℝ) : ℂ)))) *
        ins (Fin.last w.length) (abelian₂ L (ofWord L (startM P (DQ P) l) ((wordP w).map liftL)) ((Y : ℝ) : ℂ)) =
      (wt L ^ w.length * (ofWord L (startM P (DQ P) l) ((wordP w).map liftL)).c) *
        (ofWord L (startM P (DQ P) l) ((wordP w).map liftL)).F *
        ins (Fin.last w.length) (TTw (startM P (DQ P) l).QQ ((wordP w).map liftL) ((Y : ℝ) : ℂ)) *
        (ofWord L (startM P (DQ P) l) ((wordP w).map liftL)).Fi := by
  set st := startM P (DQ P) l
  set wl := (wordP w).map liftL
  set f' := ofWord L st wl
  have hcwl : M.CutWord P l wl := cut_lift_tail Y w hcw
  have hFCn := hFC (Fin (w.length + 1)) (wordP (Y :: w)) hcw
  have hFCl := hFC (Fin (w.length + 1)) wl hcwl
  have hF'' : (ofWord L st (wordP (Y :: w))).F = ins (Fin.last w.length) (abelian₂ L f' ((Y : ℝ) : ℂ)) * f'.F := by
    rw [plusWord_cons]; rfl
  have hc'' : (ofWord L st (wordP (Y :: w))).c = f'.c * ins (Fin.last w.length) (Dg f' ((Y : ℝ) : ℂ)) := by
    rw [plusWord_cons]; rfl
  have hRR : RRw st.QQ (wordP (Y :: w)) = RRw st.QQ wl * ins (Fin.last w.length) (TTw st.QQ wl ((Y : ℝ) : ℂ)) := by
    rw [plusWord_cons]; rfl
  have e1 := hFCn.2.1
  have e2 := hFCl.2.1
  have hlen1 : (wordP (Y :: w)).length = w.length + 1 := plusWord_length _
  have hlen2 : wl.length = w.length := by rw [List.length_map, plusWord_length]
  rw [hlen1, hF'', hc''] at e1
  rw [hlen2] at e2
  have hFr := hFCl.1
  set Λ := ins (Fin.last w.length) (abelian₂ L f' ((Y : ℝ) : ℂ))
  set X := wt L ^ (w.length + 1) * (f'.c * ins (Fin.last w.length) (Dg f' ((Y : ℝ) : ℂ)))
  set T := ins (Fin.last w.length) (TTw st.QQ wl ((Y : ℝ) : ℂ))
  have h0 : star f'.F * (star Λ * X * Λ) * f'.F = star f'.F * ((wt L ^ w.length * f'.c) * f'.F * T * f'.Fi) * f'.F := by
    have h1 : star f'.F * (star Λ * X * Λ) * f'.F = RRw st.QQ (wordP (Y :: w)) := by
      rw [e1, star_mul]; simp only [mul_assoc]
    have h2 : star f'.F * ((wt L ^ w.length * f'.c) * f'.F * T * f'.Fi) * f'.F = RRw st.QQ (wordP (Y :: w)) := by
      rw [hRR, e2]
      simp only [mul_assoc]
      rw [hFr.Fi_F, mul_one]
    rw [h1, h2]
  have hc : ∀ Z, Z = star f'.Fi * (star f'.F * Z * f'.F) * f'.Fi := fun Z => by
    have h1 : star f'.Fi * star f'.F = 1 := by rw [← star_mul, hFr.F_Fi, star_one]
    calc Z = (star f'.Fi * star f'.F) * Z * (f'.F * f'.Fi) := by rw [h1, hFr.F_Fi, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  rw [hc (star Λ * X * Λ), h0, ← hc]

end DescentVanishingReductions

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F14

section S_F_F15
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

section Core2

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

theorem last_not_mem (w : List ℝ) : Fin.last w.length ∉ ((wordP w).map liftL).map Letter.intersection_update_fsHerm_neg_one := by
  intro h
  rw [List.map_map, List.mem_map] at h
  obtain ⟨a, _, ha⟩ := h
  have := congrArg Fin.val ha
  simp only [Function.comp_apply, liftL, Fin.coe_castSucc, Fin.val_last] at this
  have := a.intersection_update_fsHerm_neg_one.2
  omega

theorem TT_free (L : LevelData (A P (DQ P)) P.r) (Y : ℝ) (w : List ℝ) :
    FreeOf2 (Fin.last w.length) (TTw (startM P (DQ P) l).QQ ((wordP w).map liftL) ((Y : ℝ) : ℂ)) := by
  have h1 := (Formalism.FourierDecayAlt.P.frame_free_of_new_position (A P (DQ P)) (Fin (w.length + 1)) P.r L (startM P (DQ P) l)
    ((wordP w).map liftL) (Fin.last w.length) (last_not_mem w)).2.1 ((Y : ℝ) : ℂ)
  rwa [(Formalism.FourierDecayAlt.P.frame_module_of_word (A P (DQ P)) (Fin (w.length + 1)) P.r L (startM P (DQ P) l)
    ((wordP w).map liftL)).2.1] at h1

theorem core2 (hFC : ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), M.CutWord P l w →
      FrameConcl P (DQ P) l L w)
    (Y : ℝ) (w : List ℝ) (hcw : M.CutWord P l (wordP (Y :: w))) :
    (abelian₂ L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ))ᴴ *
        DnM L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) *
        abelian₂ L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) =
      d0 (wt L ^ w.length * (ofWord L (startM P (DQ P) l) (wordP w)).c * (ofWord L (startM P (DQ P) l) (wordP w)).F) *
        (TTw (startM P (DQ P) l).QQ ((wordP w).map liftL) ((Y : ℝ) : ℂ)).map resM *
        d0 (ofWord L (startM P (DQ P) l) (wordP w)).Fi := by
  set st := startM P (DQ P) l
  set f := ofWord L st (wordP w)
  set f' := ofWord L st ((wordP w).map liftL)
  have hR : Rel f f' := rel_ofWord L st (wordP w) (plusWord_letters_plus w)
  have hΛ : abelian₂ L f' ((Y : ℝ) : ℂ) = (abelian₂ L f ((Y : ℝ) : ℂ)).map embM := lam_rel L hR _
  have hDg : Dg f' ((Y : ℝ) : ℂ) = (Dg f ((Y : ℝ) : ℂ)).map embM := by
    unfold Dg; rw [matrix_two_map, hR.q, hR.xi, hR.x]; simp only [embM_zero, embM_smul]
  have hTT := TT_free (P := P) (l := l) L Y w
  set TT := TTw st.QQ ((wordP w).map liftL) ((Y : ℝ) : ℂ)
  have hc1 := core1 hFC Y w hcw
  rw [hΛ, hDg, hR.c, hR.F, hR.Fi] at hc1

  have hb1 : FreeOf (Fin.last w.length) (wt L ^ (w.length + 1) * embM f.c) := by
    rw [← embM_wt, ← embM_pow, ← embM_mul]; exact embM_free _
  have hb2 : FreeOf (Fin.last w.length) (wt L ^ w.length * embM f.c * embM f.F) := by
    rw [← embM_wt, ← embM_pow, ← embM_mul, ← embM_mul]; exact embM_free _
  have hL1 : star (ins (Fin.last w.length) ((abelian₂ L f ((Y : ℝ) : ℂ)).map embM)) *
      (wt L ^ (w.length + 1) * (embM f.c * ins (Fin.last w.length) ((Dg f ((Y : ℝ) : ℂ)).map embM))) *
      ins (Fin.last w.length) ((abelian₂ L f ((Y : ℝ) : ℂ)).map embM) =
      ins (Fin.last w.length) (((abelian₂ L f ((Y : ℝ) : ℂ)).map embM)ᴴ *
        (d0 (wt L ^ (w.length + 1) * embM f.c) * (Dg f ((Y : ℝ) : ℂ)).map embM) *
        (abelian₂ L f ((Y : ℝ) : ℂ)).map embM) := by
    rw [Formalism.FourierDecayAlt.P.Wd1.ins_star _ _ (free_of_last_map _), ← mul_assoc (wt L ^ (w.length + 1)),
      ← Formalism.FourierDecayAlt.P.Wd7.insert_diagScalar_mul_of_free _ _ _ hb1]
    rw [← Formalism.FourierDecayAlt.P.Wd1.ins_mul _ _ _ (by rw [← map_embM_conjT]; exact free_of_last_map _)]
    rw [← Formalism.FourierDecayAlt.P.Wd1.ins_mul _ _ _ (freeOf2_mul (by rw [← map_embM_conjT]; exact free_of_last_map _)
      (freeOf2_mul (free_of_last_diagonal hb1) (free_of_last_map _)))]
  have hR1 : (wt L ^ w.length * embM f.c) * embM f.F * ins (Fin.last w.length) TT * embM f.Fi =
      ins (Fin.last w.length) (d0 (wt L ^ w.length * embM f.c * embM f.F) * TT * d0 (embM f.Fi)) := by
    rw [Formalism.FourierDecayAlt.P.Wd7.insert_mul_diagScalar, Formalism.FourierDecayAlt.P.Wd7.insert_diagScalar_mul_of_free _ _ _ hb2]
  rw [hL1, hR1] at hc1
  have hinj := ins_inj_last (freeOf2_mul (freeOf2_mul (by rw [← map_embM_conjT]; exact free_of_last_map _)
      (freeOf2_mul (free_of_last_diagonal hb1) (free_of_last_map _))) (free_of_last_map _))
    (freeOf2_mul (freeOf2_mul (free_of_last_diagonal hb2) hTT) (free_of_last_diagonal (embM_free _))) hc1

  have hTTe : TT = (TT.map resM).map embM := Matrix.ext fun i j => free_embM (hTT i j)
  have hL2 : ((abelian₂ L f ((Y : ℝ) : ℂ)).map embM)ᴴ * (d0 (wt L ^ (w.length + 1) * embM f.c) * (Dg f ((Y : ℝ) : ℂ)).map embM) *
      (abelian₂ L f ((Y : ℝ) : ℂ)).map embM =
      ((abelian₂ L f ((Y : ℝ) : ℂ))ᴴ * DnM L f w.length ((Y : ℝ) : ℂ) * abelian₂ L f ((Y : ℝ) : ℂ)).map embM := by
    rw [map_embM_mul, map_embM_mul, map_embM_conjT]
    unfold DnM
    rw [map_embM_mul, diffZero_natural, embM_mul, embM_pow, embM_wt]
  have hR2 : d0 (wt L ^ w.length * embM f.c * embM f.F) * TT * d0 (embM f.Fi) =
      (d0 (wt L ^ w.length * f.c * f.F) * TT.map resM * d0 f.Fi).map embM := by
    rw [map_embM_mul, map_embM_mul, diffZero_natural, diffZero_natural, ← hTTe, embM_mul, embM_mul, embM_pow, embM_wt]
  rw [hL2, hR2] at hinj
  exact Matrix.ext fun i j => embM_injective (congrFun (congrFun hinj i) j)

end Core2

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F15

section S_F_F16
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

section Star

variable {A : Type} [Ring A] [StarRing A] {S : Type} [Fintype S] [DecidableEq S]

theorem star_io (x : A) : star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
  ext E E'
  unfold io
  simp only [Matrix.star_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h : E = E'
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

end Star

section StarModel

variable (P : M.Par) (D : DAlg P.r)

theorem star_sc (w : D.Pr) : star (sc P D w) = sc P D (star w) := by
  ext i j
  unfold sc
  simp only [Matrix.star_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem star_pP (l : Fin P.r) : star (D.pP l) = -(D.pbP l) := by
  show ((D.pP l).2.unop, MulOpposite.op (D.pP l).1) = -(D.pbP l)
  refine Prod.ext rfl ?_
  show MulOpposite.op (D.ev (M.vc l)) = -(MulOpposite.op (-(D.ev (M.vc l))))
  rw [MulOpposite.op_neg, neg_neg]

theorem star_pbP (l : Fin P.r) : star (D.pbP l) = -(D.pP l) := by
  show ((D.pbP l).2.unop, MulOpposite.op (D.pbP l).1) = -(D.pP l)
  refine Prod.ext rfl ?_
  show MulOpposite.op (D.ev (M.vcb l)) = -(MulOpposite.op (-(D.ev (M.vcb l))))
  rw [MulOpposite.op_neg, neg_neg]

variable {P D}

theorem star_sgen_mem {L : LevelData (A P D) P.r} (hL : IsModelLevel P D L) :
    ∀ y ∈ sgen P D L, star y ∈ Algebra.adjoin ℂ (sgen P D L) := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have hs : ∀ y ∈ sgen P D L, y ∈ Algebra.adjoin ℂ (sgen P D L) := fun y hy => Algebra.subset_adjoin hy
  rintro y (((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
  · have : star (L.p l) = -(L.pb l) := by
      rw [hp, hpb]; show star (sc P D (D.pP l)) = -sc P D (D.pbP l)
      rw [star_sc, star_pP]; unfold sc; simp
    rw [this]; exact neg_mem (hs _ (by simp [sgen]))
  · have : star (L.c l) = L.cb l := by
      rw [hc, hcb]; show star (sc P D (D.cP l)) = sc P D (D.cbP l); rw [star_sc]; rfl
    rw [this]; exact hs _ (by simp [sgen])
  · have : star (L.ci l) = L.cbi l := by
      rw [hci, hcbi]; show star (sc P D (D.ciP l)) = sc P D (D.cbiP l); rw [star_sc]; rfl
    rw [this]; exact hs _ (by simp [sgen])
  · have : star (L.pb l) = -(L.p l) := by
      rw [hp, hpb]; show star (sc P D (D.pbP l)) = -sc P D (D.pP l)
      rw [star_sc, star_pbP]; unfold sc; simp
    rw [this]; exact neg_mem (hs _ (by simp [sgen]))
  · have : star (L.cb l) = L.c l := by
      rw [hc, hcb]; show star (sc P D (D.cbP l)) = sc P D (D.cP l); rw [star_sc]; rfl
    rw [this]; exact hs _ (by simp [sgen])
  · have : star (L.cbi l) = L.ci l := by
      rw [hci, hcbi]; show star (sc P D (D.cbiP l)) = sc P D (D.ciP l); rw [star_sc]; rfl
    rw [this]; exact hs _ (by simp [sgen])

theorem star_adjoin {L : LevelData (A P D) P.r} (hL : IsModelLevel P D L) {x : A P D}
    (hx : x ∈ Algebra.adjoin ℂ (sgen P D L)) : star x ∈ Algebra.adjoin ℂ (sgen P D L) := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact star_sgen_mem hL y hy
  | algebraMap z => rw [← algebraMap_star_comm]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [star_mul]; exact mul_mem hy hx

end StarModel

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F16

section S_F_F17
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

section Contract

variable {A : Type} [Ring A] [StarRing A] {S : Type} [Fintype S] [DecidableEq S]

theorem contractR {R : Type*} [Ring R] (X Xs : Fin 2 → Fin 2 → R) (q s v : Fin 2 → R) :
    ∑ b, (∑ c, s c * Xs b c) * q b * (∑ c', X b c' * v c') = ∑ c, ∑ c', s c * (∑ b, Xs b c * q b * X b c') * v c' := by
  simp only [Fin.sum_univ_two, add_mul, mul_add, mul_assoc]
  abel

theorem contract (Λ Q : M2 (SlopeTestRemainingChoices S A)) (vv : Fin 2 → A) (hQ1 : Q 0 1 = 0) (hQ2 : Q 1 0 = 0) :
    ∑ b, star ((Λ *ᵥ fun c => (io (vv c) : SlopeTestRemainingChoices S A)) b) * Q b b * (Λ *ᵥ fun c => (io (vv c) : SlopeTestRemainingChoices S A)) b =
      ∑ c, ∑ c', io (star (vv c)) * (Λᴴ * Q * Λ) c c' * io (vv c') := by
  have hQ : ∀ b b', b ≠ b' → Q b b' = 0 := by
    intro b b' h; fin_cases b <;> fin_cases b' <;> simp_all
  have hE : ∀ c c', (Λᴴ * Q * Λ) c c' = ∑ b, star (Λ b c) * Q b b * Λ b c' := by
    intro c c'
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_eq_single b (fun b'' _ hb => by rw [hQ b'' b hb, mul_zero]) (by simp),
      Matrix.conjTranspose_apply]
  have hS : ∀ b, star ((Λ *ᵥ fun c => (io (vv c) : SlopeTestRemainingChoices S A)) b) = ∑ c, io (star (vv c)) * star (Λ b c) := by
    intro b
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul, star_io]
  simp only [hS, hE]
  exact contractR (fun b c => Λ b c) (fun b c => star (Λ b c)) (fun b => Q b b) (fun c => io (star (vv c)))
    (fun c => io (vv c))

theorem move4 {R : Type*} [Ring R] (a d t fi b : R) (h1 : a * d = d * a) (h2 : fi * b = b * fi) :
    a * (d * t * fi) * b = d * (a * t * b) * fi := by
  calc a * (d * t * fi) * b = (a * d) * t * (fi * b) := by simp only [mul_assoc]
    _ = (d * a) * t * (b * fi) := by rw [h1, h2]
    _ = d * (a * t * b) * fi := by simp only [mul_assoc]

theorem diagonal_sandwich_entry (b b' : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) (c c' : Fin 2) : (d0 b * M * d0 b') c c' = b * M c c' * b' := by
  unfold d0
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

end Contract

section Kop

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r) {S : Type} [Fintype S] [DecidableEq S]

theorem frame_power_upper_zero (f : FrameData S A) (n : ℕ) (Y : ℂ) : DnM L f n Y 0 1 = 0 := by
  simp [DnM, Dg, d0, Matrix.mul_apply, Fin.sum_univ_two]

theorem frame_power_lower_zero (f : FrameData S A) (n : ℕ) (Y : ℂ) : DnM L f n Y 1 0 = 0 := by
  simp [DnM, Dg, d0, Matrix.mul_apply, Fin.sum_univ_two]

theorem vec_io (Y : ℂ) : (![io (L.Ar Y), io (L.Br Y)] : Fin 2 → SlopeTestRemainingChoices S A) = fun c => io ((![L.Ar Y, L.Br Y] : Fin 2 → A) c) := by
  funext c; fin_cases c <;> rfl

theorem Kop_contract (f : FrameData S A) (n : ℕ) (Y : ℂ) :
    Kop L f n Y = ∑ c, ∑ c', io (star ((![L.Ar Y, L.Br Y] : Fin 2 → A) c)) *
      ((abelian₂ L f Y)ᴴ * DnM L f n Y * abelian₂ L f Y) c c' * io ((![L.Ar Y, L.Br Y] : Fin 2 → A) c') := by
  unfold Kop gv
  rw [vec_io]
  exact contract _ _ _ (frame_power_upper_zero L f n Y) (frame_power_lower_zero L f n Y)

end Kop

section Core3

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

def CwR (L : LevelData (A P (DQ P)) P.r) (l : ℕ) (Y : ℝ) (w : List ℝ) : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P)) :=
  ∑ k, ∑ k', io (star ((![L.Ar ((Y : ℝ) : ℂ), L.Br ((Y : ℝ) : ℂ)] : Fin 2 → A P (DQ P)) k)) *
    ((TTw (startM P (DQ P) l).QQ ((wordP w).map liftL) ((Y : ℝ) : ℂ)).map resM) k k' *
    io ((![L.Ar ((Y : ℝ) : ℂ), L.Br ((Y : ℝ) : ℂ)] : Fin 2 → A P (DQ P)) k')

theorem core3 (hL : IsModelLevel P (DQ P) L)
    (hFC : ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), M.CutWord P l w →
      FrameConcl P (DQ P) l L w)
    (Y : ℝ) (w : List ℝ) (hcw : M.CutWord P l (wordP (Y :: w))) :
    Kop L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) =
      (wt L ^ w.length * (ofWord L (startM P (DQ P) l) (wordP w)).c * (ofWord L (startM P (DQ P) l) (wordP w)).F) *
        CwR L l Y w * (ofWord L (startM P (DQ P) l) (wordP w)).Fi := by
  set f := ofWord L (startM P (DQ P) l) (wordP w)
  set vv : Fin 2 → A P (DQ P) := ![L.Ar ((Y : ℝ) : ℂ), L.Br ((Y : ℝ) : ℂ)]
  rw [Kop_contract, core2 hFC Y w hcw]

  have hfok := fok_ofWord (L := L) (S := Fin w.length) hL l (wordP w) (plusWord_letters_plus w)
  have hwt : (wt L : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))) ∈ CA P (DQ P) L (Fin w.length) :=
    io_memCA (mul_mem (mul_mem (z_mem P (DQ P) L) (zb_mem P (DQ P) L)) (ggi_mem P (DQ P) L))
  have hdF : wt L ^ w.length * f.c * f.F ∈ CA P (DQ P) L (Fin w.length) :=
    mul_mem (mul_mem (pow_mem hwt _) hfok.c) hfok.F
  have hvm : ∀ c, vv c ∈ Algebra.adjoin ℂ (sgen P (DQ P) L) := by
    intro c; fin_cases c
    · exact Ar_mem _
    · exact Br_mem _
  have h1 : ∀ c, io (star (vv c)) * (wt L ^ w.length * f.c * f.F) = (wt L ^ w.length * f.c * f.F) * io (star (vv c)) :=
    fun c => (commute_io hdF (star_adjoin hL (hvm c))).eq.symm
  have h2 : ∀ c', f.Fi * io (vv c') = io (vv c') * f.Fi := fun c' => (commute_io hfok.Fi (hvm c')).eq
  unfold CwR
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  exact (congrArg (fun X => io (star (vv c)) * X * io (vv c'))
    (diagonal_sandwich_entry (wt L ^ w.length * f.c * f.F) f.Fi
      ((TTw (startM P (DQ P) l).QQ ((wordP w).map liftL) ((Y : ℝ) : ℂ)).map resM) c c')).trans
    (move4 _ _ _ _ _ (h1 c) (h2 c'))

end Core3

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F17

section S_F_F18
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

section Core4

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

theorem mem_lift_positions (w : List ℝ) (k : Fin w.length) : k.castSucc ∈ ((wordP w).map liftL).map Letter.intersection_update_fsHerm_neg_one := by
  rw [List.map_map]
  have := wordP_all_positions w k
  rw [List.mem_map] at this ⊢
  obtain ⟨a, ha, e⟩ := this
  exact ⟨a, ha, by simp [liftL, e]⟩

theorem uw_lift (hS : SitesOK (K := ℂ) (startM P (DQ P) l).QQ (sites P (DQ P))) (w : List ℝ)
    (hG : Good (wordP w)) (hGl : Good ((wordP w).map liftL)) (e : Ix (Fin w.length)) (b : Fin 2) :
    uw (sites P (DQ P)) ((wordP w).map liftL) (sn e b) = if b = 0 then uw (sites P (DQ P)) (wordP w) e else 0 := by
  rw [Formalism.FourierDecayAlt.P.word_product_formula ℂ (A P (DQ P)) (Fin (w.length + 1)) _ (sites P (DQ P)) _ hS hGl (sn e b)]
  by_cases hb : b = 0
  · subst hb
    rw [if_pos (fun c hc => ?_), if_pos rfl, uw_prod P (DQ P) l hS w hG e, List.map_map]
    · congr 1
      refine List.map_congr_left fun a ha => ?_
      simp only [Function.comp_apply, liftL, if_pos (plusWord_letters_plus w a ha), Fin.snoc_castSucc]
    · induction c using Fin.lastCases with
      | last => simp
      | cast k => exact absurd (mem_lift_positions w k) hc
  · rw [if_neg (fun h => hb (by have := h _ (last_not_mem w); simpa using this)), if_neg hb]

theorem core4 (hL : IsModelLevel P (DQ P) L) (hOK : P.OK) (hS : SitesOK (K := ℂ) (startM P (DQ P) l).QQ (sites P (DQ P)))
    (Y : ℝ) (w : List ℝ) (hcw : M.CutWord P l (wordP (Y :: w))) (e : Ix (Fin w.length)) :
    ∑ e', CwR L l Y w e e' * uw (sites P (DQ P)) (wordP w) e' =
      uw (sites P (DQ P)) (wordP w) e * C0 (startM P (DQ P) l).QQ (sites P (DQ P)) ((Y : ℝ) : ℂ) := by
  have hTT : 0 ≤ P.TT := (mul_pos hOK.T_pos hOK.T'_pos).le
  have hcwl := cut_lift_tail Y w hcw
  have hGl : Good ((wordP w).map liftL) := good_of_cutW _ (liftL_plus w) hcwl
  have hG : Good (wordP w) := good_of_cut w (cut_tail Y w hcw)
  have hMW := (Formalism.FourierDecayAlt.P.model_words P hOK (DQ P) (Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT) l
    (Fin (w.length + 1)) ((wordP w).map liftL) hGl).2 ((Y : ℝ) : ℂ) (reg_new Y w hcw) (Complex.conj_ofReal _) (sn e 0)

  have hTTf := TT_free (P := P) (l := l) L Y w
  have hCw : Cw (startM P (DQ P) l).QQ (sites P (DQ P)) ((wordP w).map liftL) ((Y : ℝ) : ℂ) = embM (CwR L l Y w) := by
    unfold Cw CwR
    rw [embM_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [embM_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [embM_mul, embM_mul, embM_io, embM_io]
    have hv : ∀ c, v0 (sites P (DQ P)) ((Y : ℝ) : ℂ) c = (![L.Ar ((Y : ℝ) : ℂ), L.Br ((Y : ℝ) : ℂ)] : Fin 2 → A P (DQ P)) c := by
      intro c; fin_cases c
      · exact site_vector_first P (DQ P) L hL _
      · exact site_vector_second P (DQ P) L hL _
    exact congr (congrArg (· * ·) (congrArg₂ (· * ·)
      (congrArg (fun x => (io (star x) : SlopeTestRemainingChoices (Fin (w.length + 1)) (A P (DQ P)))) (hv k)) (free_embM (hTTf k k'))))
      (congrArg (fun x => (io x : SlopeTestRemainingChoices (Fin (w.length + 1)) (A P (DQ P)))) (hv k'))
  rw [hCw, uw_lift hS w hG hGl e 0, if_pos rfl, sum_snoc] at hMW
  simp only [embM_snoc, uw_lift hS w hG hGl, ite_mul, zero_mul] at hMW
  rw [← hMW]
  refine Finset.sum_congr rfl fun e' _ => ?_
  rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg (Ne.symm hb)]) (by simp), if_pos rfl, if_pos rfl]

end Core4

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F18

section S_F_F19
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

theorem vecmul {R ι : Type*} [Ring R] [Fintype ι] (Mx Cx : Matrix ι ι R) (u : ι → R) (c : R)
    (h : ∀ e1, ∑ e'', Cx e1 e'' * u e'' = u e1 * c) (e : ι) :
    ∑ e'', (Mx * Cx) e e'' * u e'' = (∑ e1, Mx e e1 * u e1) * c := by
  simp only [Matrix.mul_apply, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e1 _ => ?_
  rw [← Finset.mul_sum, h]

section CoreI3

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

theorem third_identity_frame_sum (hL : IsModelLevel P (DQ P) L) (hOK : P.OK)
    (hS : SitesOK (K := ℂ) (startM P (DQ P) l).QQ (sites P (DQ P)))
    (hFC : ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), M.CutWord P l w →
      FrameConcl P (DQ P) l L w)
    (Y : ℝ) (w : List ℝ) (hcw : M.CutWord P l (wordP (Y :: w))) (e : Ix (Fin w.length)) :
    ∑ e'', (Kop L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) *
        (ofWord L (startM P (DQ P) l) (wordP w)).F) e e'' * uw (sites P (DQ P)) (wordP w) e'' =
      (∑ e'', (wt L ^ w.length * (ofWord L (startM P (DQ P) l) (wordP w)).c * (ofWord L (startM P (DQ P) l) (wordP w)).F :
        SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))) e e'' * uw (sites P (DQ P)) (wordP w) e'') *
        C0 (startM P (DQ P) l).QQ (sites P (DQ P)) ((Y : ℝ) : ℂ) := by
  have hFr := (hFC (Fin w.length) (wordP w) (cut_tail Y w hcw)).1
  have hKF : Kop L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) *
      (ofWord L (startM P (DQ P) l) (wordP w)).F =
      (wt L ^ w.length * (ofWord L (startM P (DQ P) l) (wordP w)).c * (ofWord L (startM P (DQ P) l) (wordP w)).F) *
        CwR L l Y w := by
    rw [core3 hL hFC Y w hcw, mul_assoc _ (ofWord L (startM P (DQ P) l) (wordP w)).Fi, hFr.Fi_F, mul_one]
  rw [hKF]
  exact vecmul _ _ _ _ (core4 hL hOK hS Y w hcw) e

end CoreI3

section Relabel

variable {N : ℕ}

theorem xs_lift (x0 : ℂ → ℂ) : ∀ (ws : List (Letter ℂ (Fin N))) (e : Ix (Fin N)) (b : Fin 2) (Y : ℂ),
    xs x0 (ws.map liftL) (sn e b) Y = xs x0 ws e Y
  | [], e, b, Y => rfl
  | a :: ws, e, b, Y => by
    simp only [List.map_cons, xs]
    rw [xs_lift x0 ws e b Y]
    simp only [liftL, Fin.snoc_castSucc]
    rfl

theorem qw_lift (q0 : ℂ → ℂ) : ∀ (ws : List (Letter ℂ (Fin N))) (Y : ℂ), qw q0 (ws.map liftL) Y = qw q0 ws Y
  | [], Y => rfl
  | a :: ws, Y => by
    simp only [List.map_cons, qw]
    rw [qw_lift q0 ws Y]
    rfl

theorem cs_lift (x0 q0 : ℂ → ℂ) : ∀ (ws : List (Letter ℂ (Fin N))) (e : Ix (Fin N)) (b : Fin 2),
    cs x0 q0 (ws.map liftL) (sn e b) = cs x0 q0 ws e
  | [], e, b => rfl
  | a :: ws, e, b => by
    simp only [List.map_cons, cs]
    simp only [cs_lift x0 q0 ws e b, qw_lift, xs_lift, liftL, Fin.snoc_castSucc]

theorem cs_cons (x0 q0 : ℂ → ℂ) (Y : ℝ) (w : List ℝ) (e : Ix (Fin w.length)) (b : Fin 2) :
    cs x0 q0 (wordP (Y :: w)) (sn e b) = cs x0 q0 (wordP w) e *
      (if b = 0 then qw q0 (wordP w) ((Y : ℝ) : ℂ) / xs x0 (wordP w) e (((Y : ℝ) : ℂ) + 1)
       else xs x0 (wordP w) e ((Y : ℝ) : ℂ)) := by
  rw [plusWord_cons]
  show cs x0 q0 ((wordP w).map liftL) (sn e b) * (if true then (if (sn e b) (Fin.last w.length) = 0 then _ else _) else _) = _
  rw [cs_lift, if_pos rfl, Fin.snoc_last, qw_lift, xs_lift, xs_lift]

end Relabel

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F19

section S_F_F20
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix Formalism.FourierDecayAlt.P.MAx1.An
open scoped ComplexConjugate

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

section Eval

variable (P : M.Par)

theorem act_sc (w : (DQ P).Pr) (Mx : A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT) (π : M.Ty P) :
    actA P (sc P (DQ P) w * Mx) j π = w.1 (actA P Mx j π) := by
  show ∑ π', ((Matrix.scalar (M.Ty P) w * Mx : Matrix (M.Ty P) (M.Ty P) (DQ P).Pr) π π').1 (j π') =
    w.1 (∑ π', (Mx π π').1 (j π'))
  rw [map_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Matrix.scalar_apply, Matrix.diagonal_mul]
  rfl

theorem act_kap (c : M.Ty P → ℂ) (Mx : A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT) (π : M.Ty P) :
    actA P (kap P (DQ P) c * Mx) j π = c π • actA P Mx j π := by
  show ∑ π', ((Matrix.diagonal (fun π => algebraMap ℂ (DQ P).Pr (c π)) * Mx : Matrix (M.Ty P) (M.Ty P) (DQ P).Pr) π π').1 (j π') =
    c π • ∑ π', (Mx π π').1 (j π')
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Matrix.diagonal_mul]
  rfl

def zw : (DQ P).Pr := (DQ P).zP * (DQ P).zbP * (DQ P).ggiP P.TT

theorem zw_apply (hTT : 0 ≤ P.TT) (h : SmQ P.r P.TT) (q : Qp P.r P.TT) :
    evQ P ((zw P).1 h) q = ((Wq P q : ℝ) : ℂ) * evQ P h q := by
  have hu : IsUnit ((anQ P.r P.TT).gg P.TT) := (Formalism.FourierDecayAlt.P.analytic_units_hold P.r P.TT hTT).2
  have e0 : evQ P ((zw P).1 h) q = ((coordQ M.vz : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q *
      (((coordQ M.vzb : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q *
      (((Ring.inverse ((anQ P.r P.TT).gg P.TT) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q * (h : Qp P.r P.TT → ℂ) q)) := rfl
  rw [e0, MAx2.Jet.ev_inverse P _ hu]
  have hg := gg_apply (r := P.r) (TT := P.TT) q
  have hz : ((coordQ M.vz : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = q.1.2 := coordE_vz q.1
  have hzb : ((coordQ M.vzb : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = conj q.1.2 := coordE_vzb q.1
  rw [coordE_vz, coordE_vzb] at hg
  have hne := gg_ne (r := P.r) (TT := P.TT) q
  rw [gg_apply, coordE_vz, coordE_vzb] at hne
  show _ = ((Complex.normSq q.1.2 / (Complex.normSq q.1.2 - P.TT) : ℝ) : ℂ) * _
  rw [hz, hzb]
  change q.1.2 * (conj q.1.2 * ((((ggQ P.r P.TT : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q)⁻¹ * _)) = _
  rw [hg]
  have hmc : q.1.2 * conj q.1.2 = ((Complex.normSq q.1.2 : ℝ) : ℂ) := Complex.mul_conj _
  rw [Complex.mul_conj] at hne
  have e1 : q.1.2 * (conj q.1.2 * ((q.1.2 * conj q.1.2 - (P.TT : ℂ))⁻¹ * (h : Qp P.r P.TT → ℂ) q)) =
      (q.1.2 * conj q.1.2) * (q.1.2 * conj q.1.2 - (P.TT : ℂ))⁻¹ * (h : Qp P.r P.TT → ℂ) q := by ring
  rw [e1, hmc]
  push_cast
  rw [div_eq_mul_inv]
  rfl

theorem zw_pow_apply (hTT : 0 ≤ P.TT) (n : ℕ) (h : SmQ P.r P.TT) (q : Qp P.r P.TT) :
    evQ P (((zw P) ^ n).1 h) q = ((Wq P q : ℝ) : ℂ) ^ n * evQ P h q := by
  induction n generalizing h with
  | zero => show evQ P h q = _; simp
  | succ n ih =>
    show evQ P (((zw P) ^ n).1 ((zw P).1 h)) q = _
    have := ih ((zw P).1 h)
    rw [zw_apply P hTT] at this
    exact this.trans (by rw [pow_succ]; ring)

end Eval

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F20

section S_F_F21
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

theorem matvec_assoc {R ι : Type*} [Ring R] [Fintype ι] (Mx Nx : Matrix ι ι R) (g : ι → R) (e : ι) :
    ∑ e', Mx e e' * ∑ e1, Nx e' e1 * g e1 = ∑ e1, (Mx * Nx) e e1 * g e1 := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem diag_vec {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι] (d : ι → R) (Nx : Matrix ι ι R) (g : ι → R)
    (e : ι) : ∑ e1, (Matrix.diagonal d * Nx) e e1 * g e1 = d e * ∑ e1, Nx e e1 * g e1 := by
  simp only [Matrix.diagonal_mul, Finset.mul_sum, mul_assoc]

section Model

variable (P : M.Par)

theorem sc_mul' (a b : (DQ P).Pr) : sc P (DQ P) a * sc P (DQ P) b = sc P (DQ P) (a * b) :=
  ((Matrix.scalar (M.Ty P)).map_mul a b).symm

theorem sc_pow' (a : (DQ P).Pr) (n : ℕ) : sc P (DQ P) a ^ n = sc P (DQ P) (a ^ n) :=
  ((Matrix.scalar (M.Ty P)).map_pow a n).symm

theorem io_pow' {S : Type} [Fintype S] [DecidableEq S] (x : A P (DQ P)) (n : ℕ) :
    (io x : SlopeTestRemainingChoices S (A P (DQ P))) ^ n = io (x ^ n) :=
  ((Matrix.scalar (Ix S)).map_pow x n).symm

variable {P}

theorem wt_sc {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) {S : Type} [Fintype S] [DecidableEq S] :
    (wt L : SlopeTestRemainingChoices S (A P (DQ P))) = io (sc P (DQ P) (zw P)) := by
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, hggi, -⟩ := hL
  unfold wt
  rw [hz, hzb, hggi]
  show io (sc P (DQ P) _ * sc P (DQ P) _ * sc P (DQ P) _) = _
  rw [sc_mul', sc_mul']
  rfl

theorem cocycle_smul (s : ℂ) (Q : ℂ → M2 (A P (DQ P))) (sts : List (Site (A P (DQ P)))) (Y : ℂ) :
    C0 (fun Y => s • Q Y) sts Y = s • C0 Q sts Y := by
  unfold C0
  simp only [Finset.smul_sum, Matrix.smul_apply, smul_mul_assoc, mul_smul_comm]

theorem actA_smul_mat (s : ℂ) (Mx : A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT) :
    actA P (s • Mx) j = fun π => s • actA P Mx j π := by
  funext π
  show ∑ π', ((s • Mx : Matrix (M.Ty P) (M.Ty P) (DQ P).Pr) π π').1 (j π') = s • ∑ π', (Mx π π').1 (j π')
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Matrix.smul_apply, Algebra.smul_def]
  show (algebraMap ℂ (DQ P).Op s * (Mx π π').1) (j π') = _
  rfl

theorem actA_smul_fun (a : ℂ) (Mx : A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT) :
    actA P Mx (fun π => a • j π) = fun π => a • actA P Mx j π := by
  funext π
  show ∑ π', (Mx π π').1 (a • j π') = a • ∑ π', (Mx π π').1 (j π')
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun π' _ => map_smul _ a _

end Model

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F21

section S_F_F22
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

section Diag

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

theorem io_diag {S : Type} [Fintype S] [DecidableEq S] (x : A P (DQ P)) :
    (io x : SlopeTestRemainingChoices S (A P (DQ P))) = Matrix.diagonal fun _ => x := by
  unfold io; rw [Matrix.scalar_apply]

theorem DnM_diag (hL : IsModelLevel P (DQ P) L) (Y : ℝ) (w : List ℝ)
    (hc : (ofWord L (startM P (DQ P) l) (wordP w)).c =
      Matrix.diagonal fun e => kap P (DQ P) fun π => cs (M.x0 P l π) (M.qC P) (wordP w) e)
    (hx : ∀ Y, (ofWord L (startM P (DQ P) l) (wordP w)).x Y =
      Matrix.diagonal fun e => kap P (DQ P) fun π => xs (M.x0 P l π) (wordP w) e Y)
    (hxi : ∀ Y, (ofWord L (startM P (DQ P) l) (wordP w)).xi Y =
      Matrix.diagonal fun e => kap P (DQ P) fun π => (xs (M.x0 P l π) (wordP w) e Y)⁻¹)
    (hq : (ofWord L (startM P (DQ P) l) (wordP w)).q = qw (M.qC P) (wordP w)) (b : Fin 2) :
    DnM L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) b b =
      Matrix.diagonal fun e => sc P (DQ P) (zw P ^ (w.length + 1)) *
        kap P (DQ P) (fun π => cs (M.x0 P l π) (M.qC P) (wordP (Y :: w)) (sn e b)) := by
  unfold DnM d0
  rw [Matrix.diagonal_mul, wt_sc hL, io_pow', ← sc_pow' P, io_diag, hc, Matrix.diagonal_mul_diagonal]
  unfold Dg
  fin_cases b
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hq, hxi, ← Matrix.diagonal_smul, Matrix.diagonal_mul_diagonal]
    congr 1
    funext e
    rw [Pi.smul_apply, ← map_smul, mul_assoc, ← map_mul]
    congr 2
    funext π
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [cs_cons, if_pos rfl, div_eq_mul_inv]
  · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hx, Matrix.diagonal_mul_diagonal]
    congr 1
    funext e
    rw [mul_assoc, ← map_mul]
    congr 2
    funext π
    simp only [Pi.mul_apply]
    rw [cs_cons, if_neg (by decide)]

theorem wtc_diag (hL : IsModelLevel P (DQ P) L) (w : List ℝ)
    (hc : (ofWord L (startM P (DQ P) l) (wordP w)).c =
      Matrix.diagonal fun e => kap P (DQ P) fun π => cs (M.x0 P l π) (M.qC P) (wordP w) e) :
    wt L ^ w.length * (ofWord L (startM P (DQ P) l) (wordP w)).c =
      Matrix.diagonal fun e => sc P (DQ P) (zw P ^ w.length) *
        kap P (DQ P) (fun π => cs (M.x0 P l π) (M.qC P) (wordP w) e) := by
  rw [wt_sc hL, io_pow', ← sc_pow' P, io_diag, hc, Matrix.diagonal_mul_diagonal]

end Diag

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F22

section S_F_F23
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

local notation "sn" => Fin.snoc (α := fun _ => Fin 2)

section Eval2

variable {P : M.Par}

theorem act_diag (hTT : 0 ≤ P.TT) (n : ℕ) {N : ℕ} (cc : Ix (Fin N) → M.Ty P → ℂ) (Nx : SlopeTestRemainingChoices (Fin N) (A P (DQ P)))
    (g : Ix (Fin N) → A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT) (e : Ix (Fin N)) (π : M.Ty P) (q : Qp P.r P.TT) :
    evQ P (actA P (∑ e1, (Matrix.diagonal (fun e => sc P (DQ P) (zw P ^ n) * kap P (DQ P) (cc e)) * Nx) e e1 * g e1) j π) q =
      ((Wq P q : ℝ) : ℂ) ^ n * cc e π * evQ P (actA P (∑ e1, Nx e e1 * g e1) j π) q := by
  rw [diag_vec, mul_assoc, act_sc, act_kap]
  rw [zw_pow_apply P hTT]
  show _ * (cc e π * _) = _
  rw [← mul_assoc]
  rfl

theorem cs_real (hOK : P.OK) {l : ℕ} (hl1 : 1 ≤ l) (hlk : l ≤ P.k) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Letter ℂ S)) (h : M.CutWord P l w) (π : M.Ty P) (e : Ix S) :
    (((cs (M.x0 P l π) (M.qC P) w e).re : ℝ) : ℂ) = cs (M.x0 P l π) (M.qC P) w e := by
  have hπ := Formalism.FourierDecayAlt.P.types_interlace P hOK π
  have hpos := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
    Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true S P.k P.u P.u' (M.rho P π) l P.T P.T' w hl1 hlk hπ
    hOK.T_pos hOK.T'_pos h.2.1 h.2.2 e
  exact Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact hpos.2.symm)

end Eval2

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F23

section S_F_F24
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

section Parts

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {N : ℕ}

theorem part_sum (j : M.Ty P → SmQ P.r P.TT) (f : FrameData (Fin N) (A P (DQ P))) (Y : ℂ)
    (gR : Ix (Fin N) → A P (DQ P)) (e0 : Ix (Fin N)) (π0 : M.Ty P) (ω : Qp P.r P.TT) :
    evQ P (actA P (∑ e', star (gv L f Y 0) e0 e' * ∑ e1, (DnM L f N Y 0 0 * gv L f Y 0) e' e1 * gR e1) j π0) ω +
      evQ P (actA P (∑ e', star (gv L f Y 1) e0 e' * ∑ e1, (DnM L f N Y 1 1 * gv L f Y 1) e' e1 * gR e1) j π0) ω =
      evQ P (actA P (∑ e1, Kop L f N Y e0 e1 * gR e1) j π0) ω := by
  have hK : (∑ e', star (gv L f Y 0) e0 e' * ∑ e1, (DnM L f N Y 0 0 * gv L f Y 0) e' e1 * gR e1) +
      (∑ e', star (gv L f Y 1) e0 e' * ∑ e1, (DnM L f N Y 1 1 * gv L f Y 1) e' e1 * gR e1) =
      ∑ e1, Kop L f N Y e0 e1 * gR e1 := by
    rw [matvec_assoc, matvec_assoc]
    unfold Kop
    simp only [Fin.sum_univ_two, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [← hK, actA_add]
  rfl

theorem part_eigen (j : M.Ty P → SmQ P.r P.TT) (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (hE : JEigen P j lam)
    (V : A P (DQ P)) (Y : ℝ) (π0 : M.Ty P) (ω : Qp P.r P.TT) :
    evQ P (actA P (V * C0 (startM P (DQ P) l).QQ (sites P (DQ P)) ((Y : ℝ) : ℂ)) j π0) ω =
      (M.sgn P l * ∏ s, (((Y : ℝ) : ℂ) + (lam s : ℂ))) * evQ P (actA P V j π0) ω := by
  have e1 : C0 (startM P (DQ P) l).QQ (sites P (DQ P)) ((Y : ℝ) : ℂ) =
      M.sgn P l • C0 (QQr P (DQ P)) (sites P (DQ P)) ((Y : ℝ) : ℂ) :=
    cocycle_smul (M.sgn P l) (QQr P (DQ P)) (sites P (DQ P)) _
  have e2 : actA P (C0 (startM P (DQ P) l).QQ (sites P (DQ P)) ((Y : ℝ) : ℂ)) j =
      fun π => (M.sgn P l * ∏ s, (((Y : ℝ) : ℂ) + (lam s : ℂ))) • j π := by
    rw [e1, actA_smul_mat, hE Y]
    funext π
    rw [smul_smul]
  rw [actA_mul, e2, actA_smul_fun]
  rfl

end Parts

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F24

section S_F_F25
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

section Parts2

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

theorem part_U (hTT : 0 ≤ P.TT) (hOK : P.OK) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (j : M.Ty P → SmQ P.r P.TT)
    (Y : ℝ) (w : List ℝ) (hcw : M.CutWord P l (wordP (Y :: w)))
    (hX : ∀ (i : Iota P w.length) (q : Qp P.r P.TT),
      Xw P l L (ju P j) w q i = evQ P (actA P (gRw P (DQ P) L l w (ixOf P w.length i).1) j (ixOf P w.length i).2) q)
    (hg1 : g1 P L w Y = gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 0)
    (hg2 : g2 P l L w Y = gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 1)
    (hDn : ∀ b : Fin 2, DnM L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) b b =
      Matrix.diagonal fun e => sc P (DQ P) (zw P ^ (w.length + 1)) *
        kap P (DQ P) (fun π => cs (M.x0 P l π) (M.qC P) (wordP (Y :: w)) (Fin.snoc (α := fun _ => Fin 2) e b)))
    (b : Fin 2) (B : Bool) (hB : (if B then (1 : Fin 2) else 0) = b) (i' : Iota P w.length) (q : Qp P.r P.TT) :
    ((dwW P l (Y :: w) q (B, i') : ℝ) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) q (B, i') =
      evQ P (actA P (∑ e1, (DnM L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) b b *
        gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) b) (ixOf P w.length i').1 e1 *
        gRw P (DQ P) L l w e1) j (ixOf P w.length i').2) q := by
  have hgX : gL P l L w Y (Xw P l L (ju P j) w) q (B, i') =
      evQ P (actA P (∑ e1, gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) b (ixOf P w.length i').1 e1 *
        gRw P (DQ P) L l w e1) j (ixOf P w.length i').2) q := by
    show wordModuleApply P (if B then g2 P l L w Y else g1 P L w Y) (Xw P l L (ju P j) w) q i' = _
    rw [apply_matrix_vector P _ _ j _ hX q i']
    subst hB
    cases B
    · rw [if_neg (by decide), hg1]; rfl
    · rw [if_pos rfl, hg2]; rfl
  rw [hgX, hDn b, act_diag hTT]
  have hre := cs_real hOK hl1 hlk (wordP (Y :: w)) hcw (ixOf P w.length i').2
    (Fin.snoc (α := fun _ => Fin 2) (ixOf P w.length i').1 b)
  show ((Wq P q ^ (w.length + 1) * (cs (M.x0 P l (ixOf P w.length i').2) (M.qC P) (wordP (Y :: w))
    (Fin.snoc (α := fun _ => Fin 2) (ixOf P w.length i').1 (if B then 1 else 0))).re : ℝ) : ℂ) * _ = _
  rw [hB]
  push_cast
  rw [hre]

theorem part_alt_alt (hTT : 0 ≤ P.TT) (hOK : P.OK) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hL : IsModelLevel P (DQ P) L)
    (j : M.Ty P → SmQ P.r P.TT) (w : List ℝ) (hcw : M.CutWord P l (wordP w))
    (hc : (ofWord L (startM P (DQ P) l) (wordP w)).c =
      Matrix.diagonal fun e => kap P (DQ P) fun π => cs (M.x0 P l π) (M.qC P) (wordP w) e)
    (e0 : Ix (Fin w.length)) (π0 : M.Ty P) (ω : Qp P.r P.TT) :
    evQ P (actA P (∑ e'', (wt L ^ w.length * (ofWord L (startM P (DQ P) l) (wordP w)).c *
      (ofWord L (startM P (DQ P) l) (wordP w)).F : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))) e0 e'' *
      uw (sites P (DQ P)) (wordP w) e'') j π0) ω =
      ((((Wq P ω ^ w.length * (cs (M.x0 P l π0) (M.qC P) (wordP w) e0).re) : ℝ)) : ℂ) *
        evQ P (actA P (gRw P (DQ P) L l w e0) j π0) ω := by
  rw [wtc_diag hL w hc, act_diag hTT]
  have hre := cs_real hOK hl1 hlk (wordP w) hcw π0 e0
  push_cast
  rw [hre]
  rfl

end Parts2

end

end Formalism.FourierDecayAlt.P.MAx3.F

end S_F_F25

section S_F_F26
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Formalism.FourierDecayAlt.P.MAx3.F

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.MA Formalism.YangianSpanCharacter.T Matrix

noncomputable section

section Main

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

theorem third_identity_frame (hTT : 0 ≤ P.TT) (hOK : P.OK) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hL : IsModelLevel P (DQ P) L)
    (hS : SitesOK (K := ℂ) (startM P (DQ P) l).QQ (sites P (DQ P)))
    (hFC : ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Letter ℂ S)), M.CutWord P l w →
      FrameConcl P (DQ P) l L w)
    (j : M.Ty P → SmQ P.r P.TT) (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (hE : JEigen P j lam)
    (Y : ℝ) (w : List ℝ) (hcw : M.CutWord P l (wordP (Y :: w))) (ω : Qp P.r P.TT) (i : Iota P w.length) :
    gstL P l L w Y (fun ω k => ((dwW P l (Y :: w) ω k : ℝ) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) ω k) ω i =
      ((((-1 : ℝ) ^ (P.k - l) * ∏ s, (Y + lam s)) * dwW P l w ω i : ℝ) : ℂ) * Xw P l L (ju P j) w ω i := by
  have hcw' := cut_tail Y w hcw
  have hX := Xw_eq hL hS (fun w h => (hFC _ _ h).1) j w hcw'
  have hFr : IsFrame L (ofWord L (startM P (DQ P) l) (wordP w)) := (hFC _ _ hcw').1
  have hCD := Formalism.FourierDecayAlt.P.c_diagonal (A P (DQ P)) (Fin w.length) P.r L (startM P (DQ P) l) (M.Ty P) (kap P (DQ P))
    (M.x0 P l) (fun Y => rfl) (fun Y => rfl) (wordP w)
  have hq : (ofWord L (startM P (DQ P) l) (wordP w)).q = qw (startM P (DQ P) l).q (wordP w) :=
    (Formalism.FourierDecayAlt.P.frame_module_of_word (A P (DQ P)) (Fin w.length) P.r L (startM P (DQ P) l) (wordP w)).2.2.1
  have hNLP := Formalism.FourierDecayAlt.P.new_vector_letter_plus (A P (DQ P)) (Fin w.length) P.r L
    (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) (hFr.ee_fn _)
  have hg1 : g1 P L w Y = gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 0 := (congrFun hNLP 0).symm
  have hg2 : g2 P l L w Y = gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 1 := (congrFun hNLP 1).symm
  have hDn := DnM_diag (l := l) hL Y w hCD.2.2 hCD.1 hCD.2.1 hq
  have h0 : ∀ (i' : Iota P w.length) (q : Qp P.r P.TT),
      ((dwW P l (Y :: w) q (false, i') : ℝ) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) q (false, i') =
      evQ P (actA P (∑ e1, (DnM L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) 0 0 *
        gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 0) (ixOf P w.length i').1 e1 *
        gRw P (DQ P) L l w e1) j (ixOf P w.length i').2) q :=
    fun i' q => part_U hTT hOK hl1 hlk j Y w hcw hX hg1 hg2 hDn 0 false rfl i' q
  have h1 : ∀ (i' : Iota P w.length) (q : Qp P.r P.TT),
      ((dwW P l (Y :: w) q (true, i') : ℝ) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) q (true, i') =
      evQ P (actA P (∑ e1, (DnM L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) 1 1 *
        gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 1) (ixOf P w.length i').1 e1 *
        gRw P (DQ P) L l w e1) j (ixOf P w.length i').2) q :=
    fun i' q => part_U hTT hOK hl1 hlk j Y w hcw hX hg1 hg2 hDn 1 true rfl i' q
  have e0 := apply_matrix_vector P (star (gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 0))
    (fun e' => ∑ e1, (DnM L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) 0 0 *
        gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 0) e' e1 * gRw P (DQ P) L l w e1) j
    (fun q' i' => ((dwW P l (Y :: w) q' (false, i') : ℝ) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) q' (false, i'))
    h0 ω i
  have e1 := apply_matrix_vector P (star (gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 1))
    (fun e' => ∑ e1, (DnM L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) 1 1 *
        gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 1) e' e1 * gRw P (DQ P) L l w e1) j
    (fun q' i' => ((dwW P l (Y :: w) q' (true, i') : ℝ) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) q' (true, i'))
    h1 ω i
  have hsplit : gstL P l L w Y (fun ω k => ((dwW P l (Y :: w) ω k : ℝ) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) ω k) ω i =
      wordModuleApply P (star (gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 0))
        (fun q' i' => ((dwW P l (Y :: w) q' (false, i') : ℝ) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) q' (false, i')) ω i +
      wordModuleApply P (star (gv L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) 1))
        (fun q' i' => ((dwW P l (Y :: w) q' (true, i') : ℝ) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) q' (true, i')) ω i := by
    unfold gstL
    rw [hg1, hg2]
  rw [hsplit, e0, e1, part_sum]
  have hKF := (matvec_assoc (Kop L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ))
    (ofWord L (startM P (DQ P) l) (wordP w)).F (uw (sites P (DQ P)) (wordP w)) (ixOf P w.length i).1).trans
    (third_identity_frame_sum hL hOK hS hFC Y w hcw (ixOf P w.length i).1)
  rw [show ∑ e1, Kop L (ofWord L (startM P (DQ P) l) (wordP w)) w.length ((Y : ℝ) : ℂ) (ixOf P w.length i).1 e1 *
      gRw P (DQ P) L l w e1 = _ from hKF]
  rw [part_eigen j lam hE, part_alt_alt hTT hOK hl1 hlk hL j w hcw' hCD.2.2, ← hX]
  show _ = ((((-1 : ℝ) ^ (P.k - l) * ∏ s, (Y + lam s)) * (Wq P ω ^ w.length *
    (cs (M.x0 P l (ixOf P w.length i).2) (M.qC P) (wordP w) (ixOf P w.length i).1).re) : ℝ) : ℂ) * _
  unfold M.sgn
  push_cast
  ring

end Main

end

end Formalism.FourierDecayAlt.P.MAx3.F

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA

theorem third_identity_signed : Formalism.FourierDecayAlt.MA.SignedEnergyIdentity := by
  intro P l L j lam α β Lb c Ntot hH w hw hl Y hY ω i
  obtain ⟨⟨hOK, hl1, hlk, hML, -⟩, -, -, hE, -⟩ := id hH
  have hTT : 0 ≤ P.TT := (mul_pos hOK.T_pos hOK.T'_pos).le
  have hLaws := analytic_laws P.r P.TT hTT
  obtain ⟨L', hL', -, -, hFC'⟩ := model_frame_analytic P hOK l hl1 hlk
  have hLL := MAx3.F.level_unique P (DQ P) L' L hL' hML
  subst hLL
  have hS := sites_admissible P (DQ P) hLaws l
  have hcw : M.CutWord P l (wordP (Y :: w)) := MAx3.F.cutWord_of hH c (Y :: w) ⟨hY, hw⟩ (by simp; omega)
  exact MAx3.F.third_identity_frame hTT hOK hl1 hlk hL' hS hFC' j lam hE Y w hcw ω i

end Formalism.FourierDecayAlt.P

end S_F_F26

section S_F_F27
namespace Formalism.FourierDecayAlt.P

theorem third_identity : Formalism.FourierDecayAlt.MA.EnergyAbsoluteIdentity :=
  third_identity_of_parts third_identity_signed polynomial_sign types_interlace boxes_fit

end Formalism.FourierDecayAlt.P

end S_F_F27

section S_R_W0
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

def tl (w : List ℝ) : List (Letter ℂ (Fin (w.length + 1))) :=
  ((wordS (LE.plus w)).map fun lt => (⟨lt.plus, lt.intersection_update_fsHerm_neg_one.castSucc, lt.pt⟩ : Letter ℂ (Fin ((LE.plus w).length + 1)))).map
    fun lt => ⟨lt.plus, Fin.cast (by simp [LE.plus]) lt.intersection_update_fsHerm_neg_one, lt.pt⟩

theorem plusWord_cons (Y : ℝ) (w : List ℝ) :
    wordP (Y :: w) = ⟨true, Fin.last w.length, (Y : ℂ)⟩ :: tl w := by
  unfold wordP tl
  generalize_proofs h1 h2
  show List.map (fun lt => (⟨lt.plus, Fin.cast h1 lt.intersection_update_fsHerm_neg_one, lt.pt⟩ : Letter ℂ (Fin (Y :: w).length)))
    ((⟨true, Fin.last (LE.plus w).length, (Y : ℂ)⟩ : Letter ℂ (Fin ((LE.plus w).length + 1))) ::
      ((wordS (LE.plus w)).map fun lt => (⟨lt.plus, lt.intersection_update_fsHerm_neg_one.castSucc, lt.pt⟩ : Letter ℂ (Fin ((LE.plus w).length + 1))))) = _
  rw [List.map_cons, List.map_map]
  congr 1
  · congr 1
    ext
    show ((Fin.last _ : Fin _) : ℕ) = w.length
    simp [LE.plus]
  · rw [List.map_map]; rfl

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_W0

section S_R_W1
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

section Lists

variable {S : Type} [Fintype S] [DecidableEq S]

def phR (v : List (Letter ℂ S)) (e : Ix S) (Y : ℝ) : ℝ :=
  (v.map fun a => if e a.intersection_update_fsHerm_neg_one = 0 then (Y - a.pt.re) / (Y - a.pt.re - 1) else 1).prod

def psR (v : List (Letter ℂ S)) (Y : ℝ) : ℝ :=
  (v.map fun a => (Y - a.pt.re + 1) / (Y - a.pt.re)).prod

theorem pt_eq {a : Letter ℂ S} (h : a.pt.im = 0) : a.pt = ((a.pt.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [h]

theorem xs_real (x0 : ℂ → ℂ) : ∀ (v : List (Letter ℂ S)), (∀ a ∈ v, a.plus = true ∧ a.pt.im = 0) →
    ∀ (e : Ix S) (Y : ℝ), xs x0 v e (Y : ℂ) = x0 (Y : ℂ) * ((phR v e Y : ℝ) : ℂ)
  | [], _, e, Y => by simp [xs, phR]
  | a :: v, h, e, Y => by
    have ha := h a (List.mem_cons_self)
    have ih := xs_real x0 v (fun b hb => h b (List.mem_cons_of_mem _ hb)) e Y
    simp only [xs, ih, phR, List.map_cons, List.prod_cons]
    by_cases he : e a.intersection_update_fsHerm_neg_one = 0
    · simp only [he, if_true, phiL, ha.1, if_true]
      have hp := pt_eq ha.2
      set p := a.pt.re
      rw [hp]
      push_cast
      ring
    · simp only [he, if_false]
      push_cast
      ring

theorem qw_real (q0 : ℂ → ℂ) : ∀ (v : List (Letter ℂ S)), (∀ a ∈ v, a.plus = true ∧ a.pt.im = 0) →
    ∀ (Y : ℝ), qw q0 v (Y : ℂ) = q0 (Y : ℂ) * ((psR v Y : ℝ) : ℂ)
  | [], _, Y => by simp [qw, psR]
  | a :: v, h, Y => by
    have ha := h a (List.mem_cons_self)
    have ih := qw_real q0 v (fun b hb => h b (List.mem_cons_of_mem _ hb)) Y
    simp only [qw, ih, psR, List.map_cons, List.prod_cons, ha.1, if_true]
    have hp := pt_eq ha.2
    set p := a.pt.re
    rw [hp]
    push_cast
    ring

theorem phR_bounds (L : ℝ) (hL : 2 ≤ L) : ∀ (v : List (Letter ℂ S)) (e : Ix S) (Y : ℝ),
    (∀ a ∈ v, L ≤ Y - a.pt.re) → 1 ≤ phR v e Y ∧ phR v e Y ≤ (1 + 2 / L) ^ v.length
  | [], e, Y, _ => by simp [phR]
  | a :: v, e, Y, h => by
    have ih := phR_bounds L hL v e Y (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    have hf : 1 ≤ (if e a.intersection_update_fsHerm_neg_one = 0 then (Y - a.pt.re) / (Y - a.pt.re - 1) else 1) ∧
        (if e a.intersection_update_fsHerm_neg_one = 0 then (Y - a.pt.re) / (Y - a.pt.re - 1) else 1) ≤ 1 + 2 / L := by
      by_cases he : e a.intersection_update_fsHerm_neg_one = 0
      · simp only [he, if_true]
        have h1 : 0 < Y - a.pt.re - 1 := by linarith
        constructor
        · rw [le_div_iff₀ h1]; linarith
        · rw [div_le_iff₀ h1]
          have h2 : 2 / L * (Y - a.pt.re - 1) ≥ 1 := by
            rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
          nlinarith
      · simp only [he, if_false]
        constructor
        · exact le_refl _
        · have : 0 ≤ 2 / L := by positivity
          linarith
    have hpos : (0 : ℝ) ≤ 1 + 2 / L := by positivity
    simp only [phR, List.map_cons, List.prod_cons, List.length_cons] at ih ⊢
    constructor
    · nlinarith [ih.1, hf.1]
    · rw [pow_succ']
      exact mul_le_mul hf.2 ih.2 (by linarith [ih.1]) hpos

theorem psR_bounds (L : ℝ) (hL : 2 ≤ L) : ∀ (v : List (Letter ℂ S)) (Y : ℝ),
    (∀ a ∈ v, L ≤ Y - a.pt.re) → 1 ≤ psR v Y ∧ psR v Y ≤ (1 + 1 / L) ^ v.length
  | [], Y, _ => by simp [psR]
  | a :: v, Y, h => by
    have ih := psR_bounds L hL v Y (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    have h1 : 0 < Y - a.pt.re := by linarith
    have hf : 1 ≤ (Y - a.pt.re + 1) / (Y - a.pt.re) ∧ (Y - a.pt.re + 1) / (Y - a.pt.re) ≤ 1 + 1 / L := by
      constructor
      · rw [le_div_iff₀ h1]; linarith
      · rw [div_le_iff₀ h1]
        have h2 : 1 / L * (Y - a.pt.re) ≥ 1 := by
          rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
        nlinarith
    have hpos : (0 : ℝ) ≤ 1 + 1 / L := by positivity
    simp only [psR, List.map_cons, List.prod_cons, List.length_cons] at ih ⊢
    constructor
    · nlinarith [ih.1, hf.1]
    · rw [pow_succ']
      exact mul_le_mul hf.2 ih.2 (by linarith [ih.1]) hpos

end Lists

theorem prodRatio {ι : Type} (T : Finset ι) (lam : ι → ℝ) (α β L Y s : ℝ) (hαβ : α < β)
    (hR : ∀ t ∈ T, -lam t ∉ Set.Ioo α β) (hL : 0 ≤ L) (hc : (T.card : ℝ) * L ≤ β - α) (hs : |s| ≤ L)
    (h3 : α + (β - α) / 3 ≤ Y + s) (h4 : Y + s ≤ β - (β - α) / 3) :
    |∏ t ∈ T, (Y + lam t)| ≤ Real.exp 3 * |∏ t ∈ T, (Y + s + lam t)| := by
  have hI : 0 < β - α := by linarith
  rw [Finset.abs_prod, Finset.abs_prod]
  have hx0 : 0 ≤ 3 * L / (β - α) := by positivity
  have hfac : ∀ t ∈ T, |Y + lam t| ≤ (1 + 3 * L / (β - α)) * |Y + s + lam t| := by
    intro t ht
    have hdist : (β - α) / 3 ≤ |Y + s + lam t| := by
      by_contra hc'
      push Not at hc'
      apply hR t ht
      rw [abs_lt] at hc'
      constructor <;> linarith [hc'.1, hc'.2]
    have h5 : |Y + lam t| ≤ |Y + s + lam t| + |s| := by
      rcases abs_cases (Y + lam t) with h | h <;> rcases abs_cases (Y + s + lam t) with h' | h' <;>
        rcases abs_cases s with h'' | h'' <;> linarith [h.1, h'.1, h''.1]
    have h3L : L ≤ 3 * L / (β - α) * |Y + s + lam t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI]; nlinarith
    nlinarith
  calc ∏ t ∈ T, |Y + lam t| ≤ ∏ t ∈ T, (1 + 3 * L / (β - α)) * |Y + s + lam t| :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) hfac
    _ = (1 + 3 * L / (β - α)) ^ T.card * ∏ t ∈ T, |Y + s + lam t| := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ Real.exp 3 * ∏ t ∈ T, |Y + s + lam t| := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        have h6 : 1 + 3 * L / (β - α) ≤ Real.exp (3 * L / (β - α)) := by
          linarith [Real.add_one_le_exp (3 * L / (β - α))]
        calc (1 + 3 * L / (β - α)) ^ T.card ≤ (Real.exp (3 * L / (β - α))) ^ T.card :=
              pow_le_pow_left₀ (by positivity) h6 _
          _ = Real.exp (T.card * (3 * L / (β - α))) := by rw [Real.exp_nat_mul]
          _ ≤ Real.exp 3 := by
              apply Real.exp_le_exp.mpr
              rw [mul_div_assoc', div_le_iff₀ hI]; nlinarith

theorem pow_le_exp (x : ℝ) (n : ℕ) (L : ℝ) (hL : 0 < L) (hx : 0 ≤ x) (hn : (n : ℝ) ≤ L) :
    (1 + x / L) ^ n ≤ Real.exp x := by
  have h6 : 1 + x / L ≤ Real.exp (x / L) := by linarith [Real.add_one_le_exp (x / L)]
  calc (1 + x / L) ^ n ≤ (Real.exp (x / L)) ^ n := pow_le_pow_left₀ (by positivity) h6 n
    _ = Real.exp (n * (x / L)) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp x := by
        apply Real.exp_le_exp.mpr
        rw [mul_div_assoc', div_le_iff₀ hL]; nlinarith

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_W1

section S_R_W2
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

theorem wordS_plus : ∀ v : List (Bool × ℝ), (wordS v).map Letter.plus = v.map Prod.fst
  | [] => rfl
  | x :: v => by
    simp only [wordS, List.map_cons, List.map_map]
    congr 1
    rw [← wordS_plus v]
    rfl

theorem plusWord_letters_plus (w : List ℝ) : ∀ a ∈ wordP w, a.plus = true := by
  intro a ha
  have h1 : a.plus ∈ (wordP w).map Letter.plus := List.mem_map_of_mem ha
  have h2 : (wordP w).map Letter.plus = (LE.plus w).map Prod.fst := by
    unfold wordP
    rw [List.map_map, ← wordS_plus]
    rfl
  rw [h2, LE.plus, List.map_map, List.mem_map] at h1
  obtain ⟨_, _, h⟩ := h1
  exact h.symm

theorem tl_pts (w : List ℝ) : (tl w).map Letter.pt = w.map fun Y : ℝ => (Y : ℂ) := by
  have h := MAx2.plusWord_points (0 :: w)
  rw [plusWord_cons, List.map_cons, List.map_cons] at h
  exact (List.cons.inj h).2

theorem tl_plus (w : List ℝ) : ∀ a ∈ tl w, a.plus = true := fun a ha =>
  plusWord_letters_plus (0 :: w) a (by rw [plusWord_cons]; exact List.mem_cons_of_mem _ ha)

theorem tl_mem (w : List ℝ) {a : Letter ℂ (Fin (w.length + 1))} (ha : a ∈ tl w) : ∃ p ∈ w, a.pt = (p : ℂ) := by
  have : a.pt ∈ (tl w).map Letter.pt := List.mem_map_of_mem ha
  rw [tl_pts, List.mem_map] at this
  obtain ⟨p, hp, e⟩ := this
  exact ⟨p, hp, e.symm⟩

theorem tl_length (w : List ℝ) : (tl w).length = w.length := by
  have h := congrArg List.length (tl_pts w)
  simpa using h

theorem tl_real (w : List ℝ) : ∀ a ∈ tl w, a.plus = true ∧ a.pt.im = 0 := fun a ha =>
  ⟨tl_plus w a ha, by obtain ⟨p, _, e⟩ := tl_mem w ha; rw [e]; simp⟩

theorem onBoxes_mem (S : LE.Sys) : ∀ w : List ℝ, S.OnBoxes w → ∀ p ∈ w, ∃ a < w.length, p ∈ S.box a
  | [], _, p, hp => absurd hp List.not_mem_nil
  | Y :: w, h, p, hp => by
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨w.length, by simp, h1⟩
    · obtain ⟨a, ha, hpa⟩ := onBoxes_mem S w h2 p hp
      exact ⟨a, by simp; omega, hpa⟩

def sx (P : M.Par) (l : ℕ) (π : M.Ty P) (Y : ℝ) : ℝ := (-1 : ℝ) ^ (P.k - l) * I.xpoly P.k (M.rho P π) Y

def qp (P : M.Par) (Y : ℝ) : ℝ := I.qpoly P.k P.T P.T' P.u P.u' Y

theorem coordinate_real (P : M.Par) (l : ℕ) (π : M.Ty P) (Y : ℝ) : M.x0 P l π (Y : ℂ) = ((sx P l π Y : ℝ) : ℂ) := by
  simp [M.x0, sx, I.xpoly]

theorem qC_real (P : M.Par) (Y : ℝ) : M.qC P (Y : ℂ) = ((qp P Y : ℝ) : ℂ) := by
  simp [M.qC, qp, I.qpoly]

theorem ixOf_last (P : M.Par) (N : ℕ) (b : Bool) (i : Iota P N) :
    (ixOf P (N + 1) (b, i)).1 (Fin.last N) = if b then 1 else 0 := by
  simp [ixOf]

theorem ixOf_snd (P : M.Par) (N : ℕ) (b : Bool) (i : Iota P N) :
    (ixOf P (N + 1) (b, i)).2 = (ixOf P N i).2 := rfl

theorem dw_true (P : M.Par) (l : ℕ) (w : List ℝ) (Y : ℝ) (q : Qp P.r P.TT) (i : Iota P w.length) :
    dwW P l (Y :: w) q (true, i) = Wq P q ^ (w.length + 1) *
      (cs (M.x0 P l (ixOf P w.length i).2) (M.qC P) (tl w) (ixOf P (w.length + 1) (true, i)).1 *
        xs (M.x0 P l (ixOf P w.length i).2) (tl w) (ixOf P (w.length + 1) (true, i)).1 (Y : ℂ)).re := by
  simp only [dwW, plusWord_cons, cs]
  rw [if_pos trivial, if_neg]
  · rfl
  · show ¬ (Fin.snoc (α := fun _ => Fin 2) (ixOf P w.length i).1 (if true then 1 else 0) (Fin.last w.length) = 0)
    simp

theorem dw_false (P : M.Par) (l : ℕ) (w : List ℝ) (Y : ℝ) (q : Qp P.r P.TT) (i : Iota P w.length) :
    dwW P l (Y :: w) q (false, i) = Wq P q ^ (w.length + 1) *
      (cs (M.x0 P l (ixOf P w.length i).2) (M.qC P) (tl w) (ixOf P (w.length + 1) (false, i)).1 *
        (qw (M.qC P) (tl w) (Y : ℂ) /
          xs (M.x0 P l (ixOf P w.length i).2) (tl w) (ixOf P (w.length + 1) (false, i)).1 ((Y : ℂ) + 1))).re := by
  simp only [dwW, plusWord_cons, cs]
  rw [if_pos trivial, if_pos]
  · rfl
  · show Fin.snoc (α := fun _ => Fin 2) (ixOf P w.length i).1 (if false then 1 else 0) (Fin.last w.length) = 0
    simp

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_W2

section S_R_W3
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

theorem sx_abs (P : M.Par) (l : ℕ) (π : M.Ty P) (Z : ℝ) (h : 0 < sx P l π Z) :
    sx P l π Z = |I.xpoly P.k (M.rho P π) Z| := by
  rw [← abs_of_pos h, sx, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

theorem qp_split (P : M.Par) (Z : ℝ) : qp P Z = -(P.T * P.T') *
    ((∏ i ∈ Finset.Icc 1 P.k, (Z + (1 / 2 + P.u i))) * ∏ i ∈ Finset.Icc 1 P.k, (Z + (1 / 2 + P.u' i))) := by
  unfold qp I.qpoly
  rw [← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem qp_abs (P : M.Par) (hT : 0 < P.T * P.T') (Z : ℝ) (h : 0 < qp P Z) :
    qp P Z = P.T * P.T' * (|∏ i ∈ Finset.Icc 1 P.k, (Z + (1 / 2 + P.u i))| *
      |∏ i ∈ Finset.Icc 1 P.k, (Z + (1 / 2 + P.u' i))|) := by
  rw [← abs_of_pos h, qp_split, abs_mul, abs_mul, abs_neg, abs_of_pos hT]

theorem real_false (W c0 qY qYs psY psYs sY sYs phY phYs : ℝ) (hW : 0 ≤ W) (hc0 : 0 < c0)
    (hqYs : 0 ≤ qYs) (hpsYs : 0 ≤ psYs) (hsY : 0 < sY) (hsYs : 0 < sYs) (hphY : 0 < phY) (hphYs : 0 < phYs)
    (hqY : 0 ≤ qY) (hpsY : 0 ≤ psY)
    (hq : qY ≤ Real.exp 6 * qYs) (hps : psY ≤ Real.exp 1 * psYs) (hs : sYs ≤ Real.exp 3 * sY)
    (hph : phYs ≤ Real.exp 2 * phY) :
    W * (c0 * (qY * psY / (sY * phY))) ≤ Real.exp 12 * (W * (c0 * (qYs * psYs / (sYs * phYs)))) := by
  have he : Real.exp 12 = Real.exp 6 * Real.exp 1 * Real.exp 3 * Real.exp 2 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
  have key : qY * psY * (sYs * phYs) ≤ Real.exp 12 * (qYs * psYs) * (sY * phY) := by
    calc qY * psY * (sYs * phYs) ≤ (Real.exp 6 * qYs) * (Real.exp 1 * psYs) * ((Real.exp 3 * sY) * (Real.exp 2 * phY)) := by
          gcongr
      _ = Real.exp 12 * (qYs * psYs) * (sY * phY) := by rw [he]; ring
  have h2 : qY * psY / (sY * phY) ≤ Real.exp 12 * (qYs * psYs / (sYs * phYs)) := by
    rw [div_le_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith [key]
  calc W * (c0 * (qY * psY / (sY * phY))) ≤ W * (c0 * (Real.exp 12 * (qYs * psYs / (sYs * phYs)))) := by gcongr
    _ = Real.exp 12 * (W * (c0 * (qYs * psYs / (sYs * phYs)))) := by ring

theorem real_true (W c0 sY sYs phY phYs : ℝ) (hW : 0 ≤ W) (hc0 : 0 < c0) (hsY : 0 ≤ sY) (hsYs : 0 ≤ sYs)
    (hphY : 0 ≤ phY) (hphYs : 0 ≤ phYs)
    (hs : sY ≤ Real.exp 3 * sYs) (hph : phY ≤ Real.exp 2 * phYs) :
    W * (c0 * (sY * phY)) ≤ Real.exp 12 * (W * (c0 * (sYs * phYs))) := by
  have he : Real.exp 12 = Real.exp 3 * Real.exp 2 * Real.exp 7 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h7 : 1 ≤ Real.exp 7 := Real.one_le_exp (by norm_num)
  have key : sY * phY ≤ Real.exp 12 * (sYs * phYs) := by
    calc sY * phY ≤ (Real.exp 3 * sYs) * (Real.exp 2 * phYs) := by gcongr
      _ ≤ (Real.exp 3 * sYs) * (Real.exp 2 * phYs) * Real.exp 7 := le_mul_of_one_le_right (by positivity) h7
      _ = Real.exp 12 * (sYs * phYs) := by rw [he]; ring
  calc W * (c0 * (sY * phY)) ≤ W * (c0 * (Real.exp 12 * (sYs * phYs))) := by gcongr
    _ = Real.exp 12 * (W * (c0 * (sYs * phYs))) := by ring

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_W3

section S_R_W4
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

theorem ofReal_add_one (Y : ℝ) : (Y : ℂ) + 1 = ((Y + 1 : ℝ) : ℂ) := by push_cast; ring

theorem weightRatio : WeightRatioQ := by
  refine ⟨Real.exp 12, (Real.exp_pos _).le, ?_⟩
  intro P l L j lam α β Lb c Ntot hH w hw hl Y s hY hYs (ω : Qp P.r P.TT) (k : Iota P (w.length + 1))
  obtain ⟨b, i⟩ := k
  obtain ⟨⟨hOK, hl1, hlk, _, hu, hu', hαβ, hcut⟩, _, _, _, _, hNL, hL2, hn, h6⟩ := hH
  have hBF := Formalism.FourierDecayAlt.P.boxes_fit (sysQ P l L j lam α β Lb c Ntot) hL2 h6
  have hYb : Y ∈ (sysQ P l L j lam α β Lb c Ntot).box w.length := hY
  have hYsb : Y + s ∈ (sysQ P l L j lam α β Lb c Ntot).box w.length := hYs
  have hY' : α + (β - α) / 3 + 2 * (w.length : ℝ) * Lb ≤ Y ∧ Y ≤ α + (β - α) / 3 + 2 * (w.length : ℝ) * Lb + Lb := hY
  have hYs' : α + (β - α) / 3 + 2 * (w.length : ℝ) * Lb ≤ Y + s ∧
      Y + s ≤ α + (β - α) / 3 + 2 * (w.length : ℝ) * Lb + Lb := hYs
  have hYm : α + (β - α) / 3 ≤ Y ∧ Y ≤ β - (β - α) / 3 := hBF.1 w.length hl hYb
  have hYsm : α + (β - α) / 3 ≤ Y + s ∧ Y + s ≤ β - (β - α) / 3 := hBF.1 w.length hl hYsb
  have hsL : |s| ≤ Lb := by rw [abs_le]; constructor <;> linarith [hY'.1, hY'.2, hYs'.1, hYs'.2]
  have hsL' : |-s| ≤ Lb := by rw [abs_neg]; exact hsL
  have hYI : Y ∈ Set.Icc α β := ⟨by linarith [hYm.1], by linarith [hYm.2]⟩
  have hYsI : Y + s ∈ Set.Icc α β := ⟨by linarith [hYsm.1], by linarith [hYsm.2]⟩
  have hfar : ∀ p ∈ w, Lb ≤ Y - p ∧ Lb ≤ Y + s - p := fun p hp => by
    obtain ⟨a, ha, hpa⟩ := onBoxes_mem _ w hw p hp
    exact ⟨hBF.2.1 a w.length ha p hpa Y hYb, hBF.2.1 a w.length ha p hpa (Y + s) hYsb⟩
  have htl : ∀ Z : ℝ, (∀ p ∈ w, Lb ≤ Z - p) → ∀ a ∈ tl w, Lb ≤ Z - a.pt.re := fun Z hZ a ha => by
    obtain ⟨p, hp, e⟩ := tl_mem w ha
    rw [e, Complex.ofReal_re]; exact hZ p hp
  have hNLb : ((tl w).length : ℝ) ≤ Lb := by
    rw [tl_length]
    have : (w.length : ℝ) + 1 ≤ Ntot := by exact_mod_cast hl
    linarith
  have hL2' : (2 : ℝ) ≤ Lb := hL2.le
  have hLpos : (0 : ℝ) < Lb := by linarith
  have hph : ∀ (e : Wd.Ix (Fin (w.length + 1))) (Z : ℝ), (∀ p ∈ w, Lb ≤ Z - p) →
      1 ≤ phR (tl w) e Z ∧ phR (tl w) e Z ≤ Real.exp 2 := fun e Z hZ => by
    obtain ⟨h1, h2⟩ := phR_bounds Lb hL2' (tl w) e Z (htl Z hZ)
    exact ⟨h1, h2.trans (pow_le_exp 2 _ Lb hLpos (by norm_num) hNLb)⟩
  have hps : ∀ Z : ℝ, (∀ p ∈ w, Lb ≤ Z - p) → 1 ≤ psR (tl w) Z ∧ psR (tl w) Z ≤ Real.exp 1 := fun Z hZ => by
    obtain ⟨h1, h2⟩ := psR_bounds Lb hL2' (tl w) Z (htl Z hZ)
    exact ⟨h1, h2.trans (pow_le_exp 1 _ Lb hLpos (by norm_num) hNLb)⟩
  have hY1 : ∀ p ∈ w, Lb ≤ Y - p := fun p hp => (hfar p hp).1
  have hYs1 : ∀ p ∈ w, Lb ≤ Y + s - p := fun p hp => (hfar p hp).2
  have hY1' : ∀ p ∈ w, Lb ≤ Y + 1 - p := fun p hp => by linarith [(hfar p hp).1]
  have hYs1' : ∀ p ∈ w, Lb ≤ Y + s + 1 - p := fun p hp => by linarith [(hfar p hp).2]

  set π := (ixOf P w.length i).2 with hπdef
  have hπ := Formalism.FourierDecayAlt.P.types_interlace P hOK π
  have hsx : ∀ Z ∈ Set.Icc α β, 0 < sx P l π Z ∧ 0 < sx P l π (Z + 1) := fun Z hZ => by
    have h0 := Formalism.FourierDecayAlt.P.interlacing_sign P.k P.u P.u' (M.rho P π) l Z hl1 hlk hπ (hcut Z hZ) 0 (by simp)
    have h1 := Formalism.FourierDecayAlt.P.interlacing_sign P.k P.u P.u' (M.rho P π) l Z hl1 hlk hπ (hcut Z hZ) 1 (by simp)
    rw [add_zero] at h0
    exact ⟨h0, h1⟩
  have hT : 0 < P.T * P.T' := mul_pos hOK.T_pos hOK.T'_pos
  have hqp : ∀ Z ∈ Set.Icc α β, 0 < qp P Z := fun Z hZ =>
    Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' (M.rho P π) l Z P.T P.T' hl1 hlk hπ (hcut Z hZ) hOK.T_pos hOK.T'_pos
  have hnn : ((P.k + 2 * P.r + 1 : ℕ) : ℝ) * Lb ≤ β - α := hn
  have hcardx : (((Finset.Icc 1 (P.k - 1)).card : ℕ) : ℝ) * Lb ≤ β - α := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hLpos.le) hnn
    rw [Nat.card_Icc]; exact_mod_cast (by omega)
  have hcardq : (((Finset.Icc 1 P.k).card : ℕ) : ℝ) * Lb ≤ β - α := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hLpos.le) hnn
    rw [Nat.card_Icc]; exact_mod_cast (by omega)

  have hrx : ∀ t ∈ Finset.Icc 1 (P.k - 1), -(M.rho P π t) ∉ Set.Ioo α β := fun t ht hin => by
    have h := (hsx _ ⟨hin.1.le, hin.2.le⟩).1
    have h0 : I.xpoly P.k (M.rho P π) (-(M.rho P π t)) = 0 := Finset.prod_eq_zero ht (by ring)
    rw [sx, h0, mul_zero] at h
    exact lt_irrefl _ h
  have hrx1 : ∀ t ∈ Finset.Icc 1 (P.k - 1), -(M.rho P π t + 1) ∉ Set.Ioo α β := fun t ht hin => by
    have h := (hsx _ ⟨hin.1.le, hin.2.le⟩).2
    have h0 : I.xpoly P.k (M.rho P π) (-(M.rho P π t + 1) + 1) = 0 := Finset.prod_eq_zero ht (by ring)
    rw [sx, h0, mul_zero] at h
    exact lt_irrefl _ h
  have hru : ∀ t ∈ Finset.Icc 1 P.k, -(1 / 2 + P.u t) ∉ Set.Ioo α β := fun t ht hin => by
    have h := hqp _ ⟨hin.1.le, hin.2.le⟩
    have h0 : ∏ i ∈ Finset.Icc 1 P.k, (-(1 / 2 + P.u t) + (1 / 2 + P.u i)) = 0 :=
      Finset.prod_eq_zero ht (by ring)
    rw [qp_split, h0, zero_mul, mul_zero] at h
    exact lt_irrefl _ h
  have hru' : ∀ t ∈ Finset.Icc 1 P.k, -(1 / 2 + P.u' t) ∉ Set.Ioo α β := fun t ht hin => by
    have h := hqp _ ⟨hin.1.le, hin.2.le⟩
    have h0 : ∏ i ∈ Finset.Icc 1 P.k, (-(1 / 2 + P.u' t) + (1 / 2 + P.u' i)) = 0 :=
      Finset.prod_eq_zero ht (by ring)
    rw [qp_split, h0, mul_zero, mul_zero] at h
    exact lt_irrefl _ h

  have hsxr : sx P l π Y ≤ Real.exp 3 * sx P l π (Y + s) := by
    rw [sx_abs P l π Y (hsx Y hYI).1, sx_abs P l π (Y + s) (hsx (Y + s) hYsI).1]
    exact prodRatio _ _ α β Lb Y s (by linarith) hrx hLpos.le hcardx hsL hYsm.1 hYsm.2
  have hsxr1 : sx P l π (Y + s + 1) ≤ Real.exp 3 * sx P l π (Y + 1) := by
    rw [sx_abs P l π _ (hsx (Y + s) hYsI).2, sx_abs P l π _ (hsx Y hYI).2]
    have h := prodRatio (Finset.Icc 1 (P.k - 1)) (fun t => M.rho P π t + 1) α β Lb (Y + s) (-s) (by linarith) hrx1
      hLpos.le hcardx hsL' (by linarith [hYm.1]) (by linarith [hYm.2])
    have e1 : ∀ Z : ℝ, I.xpoly P.k (M.rho P π) (Z + 1) = ∏ t ∈ Finset.Icc 1 (P.k - 1), (Z + (M.rho P π t + 1)) :=
      fun Z => Finset.prod_congr rfl fun t _ => by ring
    rw [e1, e1]
    convert h using 3
    ring
  have hqr : qp P Y ≤ Real.exp 6 * qp P (Y + s) := by
    rw [qp_abs P hT Y (hqp Y hYI), qp_abs P hT (Y + s) (hqp (Y + s) hYsI)]
    have h1 := prodRatio (Finset.Icc 1 P.k) (fun t => 1 / 2 + P.u t) α β Lb Y s (by linarith) hru hLpos.le hcardq
      hsL hYsm.1 hYsm.2
    have h2 := prodRatio (Finset.Icc 1 P.k) (fun t => 1 / 2 + P.u' t) α β Lb Y s (by linarith) hru' hLpos.le hcardq
      hsL hYsm.1 hYsm.2
    have he : Real.exp 6 = Real.exp 3 * Real.exp 3 := by rw [← Real.exp_add]; norm_num
    rw [he]
    calc P.T * P.T' * (|∏ i ∈ Finset.Icc 1 P.k, (Y + (1 / 2 + P.u i))| * |∏ i ∈ Finset.Icc 1 P.k, (Y + (1 / 2 + P.u' i))|)
        ≤ P.T * P.T' * ((Real.exp 3 * |∏ i ∈ Finset.Icc 1 P.k, (Y + s + (1 / 2 + P.u i))|) *
            (Real.exp 3 * |∏ i ∈ Finset.Icc 1 P.k, (Y + s + (1 / 2 + P.u' i))|)) := by gcongr
      _ = Real.exp 3 * Real.exp 3 * (P.T * P.T' * (|∏ i ∈ Finset.Icc 1 P.k, (Y + s + (1 / 2 + P.u i))| *
            |∏ i ∈ Finset.Icc 1 P.k, (Y + s + (1 / 2 + P.u' i))|)) := by ring

  have hAdm := hBF.2.2 w hw hl.le
  have hwI : ∀ p ∈ w, p ∈ Set.Icc α β := fun p hp => hAdm.1 (true, p) (List.mem_map.2 ⟨p, hp, rfl⟩)
  have hpw : w.Pairwise fun Y Y' => 2 < |Y - Y'| := by
    have h2 := hAdm.2
    unfold LE.plus at h2
    rw [List.pairwise_map] at h2
    exact h2
  have hcutw : ∀ a ∈ tl w, a.pt.im = 0 ∧ I.OnCut P.u P.u' l a.pt.re := fun a ha => by
    obtain ⟨p, hp, e⟩ := tl_mem w ha
    rw [e]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hcut _ (hwI _ hp)⟩
  have hpwt : (tl w).Pairwise fun a a' => 2 < |a.pt.re - a'.pt.re| := by
    have h2 : ((tl w).map Letter.pt).Pairwise fun z z' : ℂ => 2 < |z.re - z'.re| := by
      rw [tl_pts, List.pairwise_map]
      exact hpw.imp fun h => by simpa using h
    rwa [List.pairwise_map] at h2
  have hcs : ∀ e, Pos (cs (M.x0 P l π) (M.qC P) (tl w) e) := fun e =>
    Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
      Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true (Fin (w.length + 1)) P.k P.u P.u'
      (M.rho P π) l P.T P.T' (tl w) hl1 hlk hπ hOK.T_pos hOK.T'_pos hcutw hpwt e
  have hcsr : ∀ e, cs (M.x0 P l π) (M.qC P) (tl w) e = (((cs (M.x0 P l π) (M.qC P) (tl w) e).re : ℝ) : ℂ) :=
    fun e => Complex.ext (by simp) (by simp [(hcs e).2])
  have hW : 0 ≤ Wq P ω ^ (w.length + 1) := pow_nonneg (MAx3.Wq_pos P (mul_pos hOK.T_pos hOK.T'_pos).le ω).le _
  cases b
  · show dwW P l (Y :: w) ω (false, i) ≤ Real.exp 12 * dwW P l ((Y + s) :: w) ω (false, i)
    rw [dw_false, dw_false]
    set e := (ixOf P (w.length + 1) (false, i)).1
    rw [ofReal_add_one, ofReal_add_one, qw_real _ _ (tl_real w), qw_real _ _ (tl_real w),
      xs_real _ _ (tl_real w), xs_real _ _ (tl_real w), coordinate_real, coordinate_real, qC_real, qC_real, hcsr e]
    have hform : ∀ (c0 a b' c' d : ℝ), ((c0 : ℂ) * ((a : ℂ) * (b' : ℂ) / ((c' : ℂ) * (d : ℂ)))).re =
        c0 * (a * b' / (c' * d)) := fun c0 a b' c' d => by
      rw [show ((c0 : ℂ) * ((a : ℂ) * (b' : ℂ) / ((c' : ℂ) * (d : ℂ)))) = ((c0 * (a * b' / (c' * d)) : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re]
    rw [hform, hform]
    have hph1 := hph e (Y + 1) hY1'
    have hph2 := hph e (Y + s + 1) hYs1'
    have hps1 := hps Y hY1
    have hps2 := hps (Y + s) hYs1
    have hpsr : psR (tl w) Y ≤ Real.exp 1 * psR (tl w) (Y + s) :=
      calc psR (tl w) Y ≤ Real.exp 1 := hps1.2
        _ = Real.exp 1 * 1 := (mul_one _).symm
        _ ≤ Real.exp 1 * psR (tl w) (Y + s) := mul_le_mul_of_nonneg_left hps2.1 (Real.exp_pos 1).le
    have hphr : phR (tl w) e (Y + s + 1) ≤ Real.exp 2 * phR (tl w) e (Y + 1) :=
      calc phR (tl w) e (Y + s + 1) ≤ Real.exp 2 := hph2.2
        _ = Real.exp 2 * 1 := (mul_one _).symm
        _ ≤ Real.exp 2 * phR (tl w) e (Y + 1) := mul_le_mul_of_nonneg_left hph1.1 (Real.exp_pos 2).le
    exact real_false (Wq P ω ^ (w.length + 1)) (cs (M.x0 P l π) (M.qC P) (tl w) e).re (qp P Y) (qp P (Y + s))
      (psR (tl w) Y) (psR (tl w) (Y + s)) (sx P l π (Y + 1)) (sx P l π (Y + s + 1)) (phR (tl w) e (Y + 1))
      (phR (tl w) e (Y + s + 1)) hW (hcs e).1 (hqp _ hYsI).le (zero_le_one.trans hps2.1) (hsx Y hYI).2
      (hsx _ hYsI).2 (zero_lt_one.trans_le hph1.1) (zero_lt_one.trans_le hph2.1) (hqp _ hYI).le
      (zero_le_one.trans hps1.1) hqr hpsr hsxr1 hphr
  · show dwW P l (Y :: w) ω (true, i) ≤ Real.exp 12 * dwW P l ((Y + s) :: w) ω (true, i)
    rw [dw_true, dw_true]
    set e := (ixOf P (w.length + 1) (true, i)).1
    rw [xs_real _ _ (tl_real w), xs_real _ _ (tl_real w), coordinate_real, coordinate_real, hcsr e]
    have hform : ∀ (c0 a b' : ℝ), ((c0 : ℂ) * ((a : ℂ) * (b' : ℂ))).re = c0 * (a * b') := fun c0 a b' => by
      rw [show ((c0 : ℂ) * ((a : ℂ) * (b' : ℂ))) = ((c0 * (a * b') : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    rw [hform, hform]
    have hph1 := hph e Y hY1
    have hph2 := hph e (Y + s) hYs1
    have hphr : phR (tl w) e Y ≤ Real.exp 2 * phR (tl w) e (Y + s) :=
      calc phR (tl w) e Y ≤ Real.exp 2 := hph1.2
        _ = Real.exp 2 * 1 := (mul_one _).symm
        _ ≤ Real.exp 2 * phR (tl w) e (Y + s) := mul_le_mul_of_nonneg_left hph2.1 (Real.exp_pos 2).le
    exact real_true (Wq P ω ^ (w.length + 1)) (cs (M.x0 P l π) (M.qC P) (tl w) e).re (sx P l π Y) (sx P l π (Y + s))
      (phR (tl w) e Y) (phR (tl w) e (Y + s)) hW (hcs e).1 (hsx Y hYI).1.le (hsx _ hYsI).1.le
      (zero_le_one.trans hph1.1) (zero_le_one.trans hph2.1) hsxr hphr

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_W4

section S_R_C1
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset

theorem hasDerivAt_prodLin (a : ℕ → ℝ) (T : ℝ) : ∀ (s : Finset ℕ), (∀ i ∈ s, T ≠ a i) →
    HasDerivAt (fun T => ∏ i ∈ s, (T - a i)) ((∏ i ∈ s, (T - a i)) * ∑ i ∈ s, 1 / (T - a i)) T := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simpa using hasDerivAt_const T (1 : ℝ)
  | insert x s hx ih =>
    intro h
    have hx' : T - a x ≠ 0 := sub_ne_zero.2 (h x (mem_insert_self x s))
    have h1 := ih (fun i hi => h i (mem_insert_of_mem hi))
    have h2 : HasDerivAt (fun T => T - a x) 1 T := (hasDerivAt_id T).sub_const (a x)
    have h3 := h2.mul h1
    simp only [prod_insert hx, sum_insert hx]
    refine h3.congr_deriv ?_
    have e : (T - a x) * (1 / (T - a x)) = 1 := mul_one_div_cancel hx'
    linear_combination -(∏ i ∈ s, (T - a i)) * e

theorem hasDerivAt_ratioLin (s t : Finset ℕ) (a b : ℕ → ℝ) (T : ℝ) (ha : ∀ i ∈ s, T ≠ a i)
    (hb : ∀ j ∈ t, T ≠ b j) :
    HasDerivAt (fun T => (∏ i ∈ s, (T - a i)) / ∏ j ∈ t, (T - b j))
      ((∏ i ∈ s, (T - a i)) / (∏ j ∈ t, (T - b j)) *
        (∑ i ∈ s, 1 / (T - a i) - ∑ j ∈ t, 1 / (T - b j))) T := by
  have hD : ∏ j ∈ t, (T - b j) ≠ 0 := prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hb j hj)
  have h := (hasDerivAt_prodLin a T s ha).div (hasDerivAt_prodLin b T t hb) hD
  refine h.congr_deriv ?_
  field_simp

theorem tele_left (T D : ℝ) (hD : 0 < D) (A B : ℕ → ℝ) : ∀ n : ℕ,
    (∀ j < n, A j ≤ B j) → (∀ j, j + 1 < n → B j ≤ A (j + 1)) → (∀ j < n, D ≤ T - B j) →
    -(1 / D) ≤ ∑ j ∈ range n, (1 / (T - A j) - 1 / (T - B j)) ∧
      ∑ j ∈ range n, (1 / (T - A j) - 1 / (T - B j)) ≤ 0 := by
  intro n h1 h2 h3
  have key : ∀ m, m ≤ n → 0 < m →
      1 / (T - A 0) - 1 / (T - B (m - 1)) ≤ ∑ j ∈ range m, (1 / (T - A j) - 1 / (T - B j)) ∧
        ∑ j ∈ range m, (1 / (T - A j) - 1 / (T - B j)) ≤ 0 := by
    intro m
    induction m with
    | zero => intro _ h; omega
    | succ m ih =>
      intro hm _
      have hBm : D ≤ T - B m := h3 m (by omega)
      have hAm : A m ≤ B m := h1 m (by omega)
      have hterm : 1 / (T - A m) - 1 / (T - B m) ≤ 0 := by
        rw [sub_nonpos]; apply one_div_le_one_div_of_le (by linarith); linarith
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp only [zero_add, range_one, sum_singleton, Nat.sub_self]
        exact ⟨le_refl _, hterm⟩
      · obtain ⟨ih1, ih2⟩ := ih (by omega) hm0
        rw [sum_range_succ]
        have hB' : B (m - 1) ≤ A m := by have := h2 (m - 1) (by omega); rwa [Nat.sub_add_cancel hm0] at this
        have hBm1 : D ≤ T - B (m - 1) := h3 (m - 1) (by omega)
        have hmono : 1 / (T - B (m - 1)) ≤ 1 / (T - A m) := one_div_le_one_div_of_le (by linarith) (by linarith)
        refine ⟨?_, by linarith⟩
        simp only [Nat.add_sub_cancel]
        linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [range_zero, sum_empty]
    exact ⟨by have : 0 < 1 / D := by positivity
              linarith, le_refl _⟩
  · obtain ⟨k1, k2⟩ := key n le_rfl hn
    refine ⟨?_, k2⟩
    have hA0 : 0 < 1 / (T - A 0) := by
      have := h1 0 hn; have := h3 0 hn; apply one_div_pos.2; linarith
    have hBn : 1 / (T - B (n - 1)) ≤ 1 / D := one_div_le_one_div_of_le hD (h3 (n - 1) (by omega))
    linarith

theorem tele_right (T D : ℝ) (hD : 0 < D) (A B : ℕ → ℝ) : ∀ n : ℕ,
    (∀ j < n, B j ≤ A j) → (∀ j, j + 1 < n → A j ≤ B (j + 1)) → (∀ j < n, D ≤ B j - T) →
    0 ≤ ∑ j ∈ range n, (1 / (B j - T) - 1 / (A j - T)) ∧
      ∑ j ∈ range n, (1 / (B j - T) - 1 / (A j - T)) ≤ 1 / D := by
  intro n h1 h2 h3
  have key : ∀ m, m ≤ n → 0 < m →
      ∑ j ∈ range m, (1 / (B j - T) - 1 / (A j - T)) ≤ 1 / (B 0 - T) - 1 / (A (m - 1) - T) ∧
        0 ≤ ∑ j ∈ range m, (1 / (B j - T) - 1 / (A j - T)) := by
    intro m
    induction m with
    | zero => intro _ h; omega
    | succ m ih =>
      intro hm _
      have hBm : D ≤ B m - T := h3 m (by omega)
      have hAm : B m ≤ A m := h1 m (by omega)
      have hterm : 0 ≤ 1 / (B m - T) - 1 / (A m - T) := by
        rw [sub_nonneg]; apply one_div_le_one_div_of_le (by linarith); linarith
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp only [zero_add, range_one, sum_singleton, Nat.sub_self]
        exact ⟨le_refl _, hterm⟩
      · obtain ⟨ih1, ih2⟩ := ih (by omega) hm0
        rw [sum_range_succ]
        have hA' : A (m - 1) ≤ B m := by have := h2 (m - 1) (by omega); rwa [Nat.sub_add_cancel hm0] at this
        have hBm1 : D ≤ B (m - 1) - T := h3 (m - 1) (by omega)
        have hAm1 : B (m - 1) ≤ A (m - 1) := h1 (m - 1) (by omega)
        have hmono : 1 / (B m - T) ≤ 1 / (A (m - 1) - T) := one_div_le_one_div_of_le (by linarith) (by linarith)
        refine ⟨?_, by linarith⟩
        simp only [Nat.add_sub_cancel]
        linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [range_zero, sum_empty]
    exact ⟨le_refl _, by positivity⟩
  · obtain ⟨k1, k2⟩ := key n le_rfl hn
    refine ⟨k2, ?_⟩
    have hAn : 0 < 1 / (A (n - 1) - T) := by
      have := h1 (n - 1) (by omega); have := h3 (n - 1) (by omega); apply one_div_pos.2; linarith
    have hB0 : 1 / (B 0 - T) ≤ 1 / D := one_div_le_one_div_of_le hD (h3 0 hn)
    linarith

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_C1

section S_R_C2
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset Polynomial

theorem partialFrac (s t : Finset ℕ) (a b : ℕ → ℝ) (hcard : s.card = t.card + 1) (hinj : Set.InjOn b t) :
    ∃ c0 : ℝ, ∀ T : ℝ, (∀ j ∈ t, T ≠ b j) →
      (∏ i ∈ s, (T - a i)) / (∏ j ∈ t, (T - b j)) =
        T + c0 + ∑ j ∈ t, (∏ i ∈ s, (b j - a i)) / ((∏ m ∈ t.erase j, (b j - b m)) * (T - b j)) := by
  classical
  set Pp : ℝ[X] := ∏ i ∈ s, (X - C (a i)) with hPp
  set Dp : ℝ[X] := ∏ j ∈ t, (X - C (b j)) with hDp
  have hDm : Dp.Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hPm : Pp.Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hPd : Pp.natDegree = s.card := by
    rw [hPp, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]; simp
  have hDd : Dp.natDegree = t.card := by
    rw [hDp, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]; simp
  set q := Pp /ₘ Dp with hq
  set r := Pp %ₘ Dp with hr
  have hdecomp : r + Dp * q = Pp := modByMonic_add_div Pp Dp
  have hqd : q.natDegree = 1 := by rw [hq, natDegree_divByMonic Pp hDm, hPd, hDd, hcard]; omega
  have hq0 : q ≠ 0 := by intro h; rw [h] at hqd; simp at hqd
  have hrlt : r.degree < Dp.degree := degree_modByMonic_lt Pp hDm
  have hlt2 : r.degree < (Dp * q).degree := by
    rw [degree_mul]
    refine lt_of_lt_of_le hrlt ?_
    have : (0 : WithBot ℕ) ≤ q.degree := by
      rw [degree_eq_natDegree hq0]; exact WithBot.coe_le_coe.2 (Nat.zero_le _)
    calc Dp.degree = Dp.degree + 0 := (add_zero _).symm
      _ ≤ Dp.degree + q.degree := add_le_add_right this _
  have hqm : q.leadingCoeff = 1 := by
    have h1 : Pp.leadingCoeff = (r + Dp * q).leadingCoeff := by rw [hdecomp]
    rw [leadingCoeff_add_of_degree_lt hlt2, leadingCoeff_mul, hDm.leadingCoeff, one_mul, hPm.leadingCoeff] at h1
    exact h1.symm
  have hqform : q = X + C (q.coeff 0) := by
    have := eq_X_add_C_of_natDegree_le_one (le_of_eq hqd)
    rw [this]
    have hc1 : q.coeff 1 = 1 := by
      have : q.leadingCoeff = q.coeff 1 := by rw [leadingCoeff, hqd]
      rw [← this, hqm]
    simp [hc1]
  refine ⟨q.coeff 0, fun T hT => ?_⟩
  have hrdeg : r.degree < (t.card : WithBot ℕ) := by
    rw [degree_eq_natDegree hDm.ne_zero, hDd] at hrlt; exact hrlt
  have hinterp := Lagrange.eq_interpolate hinj hrdeg
  have hevalP : ∀ x : ℝ, Pp.eval x = ∏ i ∈ s, (x - a i) := fun x => by rw [hPp, eval_prod]; simp
  have hevalD : ∀ x : ℝ, Dp.eval x = ∏ j ∈ t, (x - b j) := fun x => by rw [hDp, eval_prod]; simp
  have hD0 : ∏ j ∈ t, (T - b j) ≠ 0 := prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hT j hj)
  have hrb : ∀ j ∈ t, r.eval (b j) = ∏ i ∈ s, (b j - a i) := fun j hj => by
    have h := congrArg (eval (b j)) hdecomp
    rw [eval_add, eval_mul, hevalD, prod_eq_zero hj (sub_self _), zero_mul, add_zero, hevalP] at h
    exact h
  have hrT : r.eval T = (∏ j ∈ t, (T - b j)) *
      ∑ j ∈ t, (∏ m ∈ t.erase j, (b j - b m))⁻¹ * (T - b j)⁻¹ * ∏ i ∈ s, (b j - a i) := by
    rw [hinterp, Lagrange.eval_interpolate_not_at_node _ hT, Lagrange.eval_nodal]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [Lagrange.nodalWeight, prod_inv_distrib, hrb j hj]
  have hPT : ∏ i ∈ s, (T - a i) = r.eval T + (∏ j ∈ t, (T - b j)) * (T + q.coeff 0) := by
    have h := congrArg (eval T) hdecomp
    rw [eval_add, eval_mul, hevalD, hevalP] at h
    rw [← h, hqform]; simp
  rw [hPT, hrT, add_div, mul_div_cancel_left₀ _ hD0, mul_div_cancel_left₀ _ hD0]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [div_eq_mul_inv, mul_inv]
  ring

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_C2

section S_R_C3
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset

theorem sum_Ico_range (f : ℕ → ℝ) (m n : ℕ) : ∑ i ∈ Ico m n, f i = ∑ j ∈ range (n - m), f (m + j) :=
  sum_Ico_eq_sum_range f m n

theorem sum_Icc_split3 (f : ℕ → ℝ) (k l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ k) :
    ∑ i ∈ Icc 1 k, f i = ∑ n ∈ range (l - 1), f (1 + n) + f l + ∑ n ∈ range (k - l), f (l + 1 + n) := by
  have e1 : Icc 1 k = Ico 1 (k + 1) := by ext i; simp
  have e3 : Ico l (l + 1) = {l} := by ext i; simp
  have s1 := sum_Ico_consecutive f hl1 (by omega : l ≤ k + 1)
  have s2 := sum_Ico_consecutive f (Nat.le_succ l) (by omega : l + 1 ≤ k + 1)
  rw [e1, ← s1, ← s2, sum_Ico_range f 1 l, sum_Ico_range f (l + 1) (k + 1), e3, sum_singleton]
  have : k + 1 - (l + 1) = k - l := by omega
  rw [this]
  ring

theorem sum_Icc_split2 (f : ℕ → ℝ) (k l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ k) :
    ∑ j ∈ Icc 1 (k - 1), f j = ∑ n ∈ range (l - 1), f (1 + n) + ∑ n ∈ range (k - l), f (l + n) := by
  have e1 : Icc 1 (k - 1) = Ico 1 k := by ext i; simp; omega
  have s1 := sum_Ico_consecutive f hl1 hlk
  rw [e1, ← s1, sum_Ico_range f 1 l, sum_Ico_range f l k]

theorem logDeriv_bound (k l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ k) (a b : ℕ → ℝ) (α β T : ℝ) (hαβ : α < β)
    (hab : ∀ j ∈ Icc 1 (k - 1), a j ≤ b j ∧ b j ≤ a (j + 1))
    (haL : ∀ i, 1 ≤ i → i < l → a i ≤ α) (haR : ∀ i, l < i → i ≤ k → β ≤ a i) (hal : a l ≤ α ∨ β ≤ a l)
    (hbL : ∀ j, 1 ≤ j → j < l → b j ≤ α) (hbR : ∀ j, l ≤ j → j ≤ k - 1 → β ≤ b j)
    (hT1 : α + (β - α) / 3 ≤ T) (hT2 : T ≤ β - (β - α) / 3) :
    |∑ i ∈ Icc 1 k, 1 / (T - a i) - ∑ j ∈ Icc 1 (k - 1), 1 / (T - b j)| ≤ 6 / (β - α) := by
  set D := (β - α) / 3 with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  have h6 : 6 / (β - α) = 2 * (1 / D) := by rw [hD]; field_simp; ring
  rw [sum_Icc_split3 _ k l hl1 hlk, sum_Icc_split2 _ k l hl1 hlk]
  have hL := tele_left T D hDpos (fun n => a (1 + n)) (fun n => b (1 + n)) (l - 1)
    (fun j hj => (hab (1 + j) (by simp [mem_Icc]; omega)).1)
    (fun j hj => by have := (hab (1 + j) (by simp [mem_Icc]; omega)).2; rwa [show 1 + j + 1 = 1 + (j + 1) by ring] at this)
    (fun j hj => by have := hbL (1 + j) (by omega) (by omega); linarith)
  have hR := tele_right T D hDpos (fun n => a (l + 1 + n)) (fun n => b (l + n)) (k - l)
    (fun j hj => by have := (hab (l + j) (by simp [mem_Icc]; omega)).2; rwa [show l + j + 1 = l + 1 + j by ring] at this)
    (fun j hj => by
      have := (hab (l + 1 + j) (by simp [mem_Icc]; omega)).1
      show a (l + 1 + j) ≤ b (l + (j + 1))
      rw [show l + (j + 1) = l + 1 + j by ring]; exact this)
    (fun j hj => by have := hbR (l + j) (by omega) (by omega); linarith)
  have hmid : |1 / (T - a l)| ≤ 1 / D := by
    rcases hal with h | h
    · rw [abs_of_pos (one_div_pos.2 (by linarith))]
      exact one_div_le_one_div_of_le hDpos (by linarith)
    · rw [abs_of_neg (one_div_neg.2 (by linarith)), ← one_div_neg_eq_neg_one_div, neg_sub]
      exact one_div_le_one_div_of_le hDpos (by linarith)
  have eR : ∑ n ∈ range (k - l), 1 / (T - a (l + 1 + n)) - ∑ n ∈ range (k - l), 1 / (T - b (l + n)) =
      ∑ n ∈ range (k - l), (1 / (b (l + n) - T) - 1 / (a (l + 1 + n) - T)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [show T - a (l + 1 + n) = -(a (l + 1 + n) - T) by ring, show T - b (l + n) = -(b (l + n) - T) by ring,
      one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
    ring
  have eL : ∑ n ∈ range (l - 1), 1 / (T - a (1 + n)) - ∑ n ∈ range (l - 1), 1 / (T - b (1 + n)) =
      ∑ n ∈ range (l - 1), (1 / (T - a (1 + n)) - 1 / (T - b (1 + n))) := by
    rw [← sum_sub_distrib]
  have e : ∑ n ∈ range (l - 1), 1 / (T - a (1 + n)) + 1 / (T - a l) + ∑ n ∈ range (k - l), 1 / (T - a (l + 1 + n)) -
      (∑ n ∈ range (l - 1), 1 / (T - b (1 + n)) + ∑ n ∈ range (k - l), 1 / (T - b (l + n))) =
      (∑ n ∈ range (l - 1), 1 / (T - a (1 + n)) - ∑ n ∈ range (l - 1), 1 / (T - b (1 + n))) + 1 / (T - a l) +
      (∑ n ∈ range (k - l), 1 / (T - a (l + 1 + n)) - ∑ n ∈ range (k - l), 1 / (T - b (l + n))) := by ring
  rw [e, eL, eR, h6]
  rw [abs_le] at hmid ⊢
  constructor <;> linarith [hL.1, hL.2, hR.1, hR.2, hmid.1, hmid.2]

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_C3

section S_R_C4
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset

noncomputable def resA (s t : Finset ℕ) (a b : ℕ → ℝ) (j : ℕ) : ℝ :=
  -(∏ i ∈ s, (b j - a i)) / (∏ m ∈ t.erase j, (b j - b m))

noncomputable def ratF (s t : Finset ℕ) (a b : ℕ → ℝ) (T : ℝ) : ℝ := (∏ i ∈ s, (T - a i)) / ∏ j ∈ t, (T - b j)

theorem ratF_pf (s t : Finset ℕ) (a b : ℕ → ℝ) (hcard : s.card = t.card + 1) (hinj : Set.InjOn b t) :
    ∃ c0 : ℝ, ∀ T : ℝ, (∀ j ∈ t, T ≠ b j) →
      ratF s t a b T = T + c0 - ∑ j ∈ t, resA s t a b j / (T - b j) := by
  obtain ⟨c0, h⟩ := partialFrac s t a b hcard hinj
  refine ⟨c0, fun T hT => ?_⟩
  rw [ratF, h T hT, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [resA, div_div, neg_div, neg_neg]

theorem ratF_deriv_id (s t : Finset ℕ) (a b : ℕ → ℝ) (hcard : s.card = t.card + 1) (hinj : Set.InjOn b t)
    (T : ℝ) (ha : ∀ i ∈ s, T ≠ a i) (hb : ∀ j ∈ t, T ≠ b j) :
    1 + ∑ j ∈ t, resA s t a b j / (T - b j) ^ 2 =
      ratF s t a b T * (∑ i ∈ s, 1 / (T - a i) - ∑ j ∈ t, 1 / (T - b j)) := by
  obtain ⟨c0, hpf⟩ := ratF_pf s t a b hcard hinj
  have h1 := hasDerivAt_ratioLin s t a b T ha hb
  have hpfd : HasDerivAt (fun T => T + c0 - ∑ j ∈ t, resA s t a b j / (T - b j))
      (1 + ∑ j ∈ t, resA s t a b j / (T - b j) ^ 2) T := by
    have hj' : ∀ j ∈ t, HasDerivAt (fun T => resA s t a b j / (T - b j)) (-(resA s t a b j / (T - b j) ^ 2)) T := by
      intro j hj
      have hne : T - b j ≠ 0 := sub_ne_zero.2 (hb j hj)
      have := ((hasDerivAt_id T).sub_const (b j)).inv hne
      have h2 := this.const_mul (resA s t a b j)
      refine (h2.congr_deriv ?_).congr_of_eventuallyEq ?_
      · simp only [id]; field_simp
      · exact Filter.Eventually.of_forall fun x => by simp [div_eq_mul_inv]
    have hs : HasDerivAt (fun T => ∑ j ∈ t, resA s t a b j / (T - b j))
        (∑ j ∈ t, -(resA s t a b j / (T - b j) ^ 2)) T := by
      have hsum := HasDerivAt.sum (u := t) hj'
      have e : (∑ j ∈ t, fun T => resA s t a b j / (T - b j)) = fun T => ∑ j ∈ t, resA s t a b j / (T - b j) := by
        funext T; simp [Finset.sum_apply]
      rw [e] at hsum; exact hsum
    have := ((hasDerivAt_id T).add_const c0).sub hs
    refine this.congr_deriv ?_
    simp [sum_neg_distrib]
  have hopen : IsOpen {x : ℝ | ∀ j ∈ t, x ≠ b j} := by
    have : {x : ℝ | ∀ j ∈ t, x ≠ b j} = ⋂ j ∈ t, {x | x ≠ b j} := by ext; simp
    rw [this]
    exact isOpen_biInter_finset fun j _ => isOpen_ne
  have heq : (fun T => T + c0 - ∑ j ∈ t, resA s t a b j / (T - b j)) =ᶠ[nhds T]
      (fun T => (∏ i ∈ s, (T - a i)) / ∏ j ∈ t, (T - b j)) := by
    filter_upwards [hopen.mem_nhds hb] with x hx
    rw [← ratF, hpf x hx]
  have h3 := hpfd.congr_of_eventuallyEq heq.symm
  exact (h3.unique h1).trans rfl

theorem ratF_two (s t : Finset ℕ) (a b : ℕ → ℝ) (hcard : s.card = t.card + 1) (hinj : Set.InjOn b t)
    (Y Z : ℝ) (hY : ∀ j ∈ t, Y ≠ b j) (hZ : ∀ j ∈ t, Z ≠ b j) :
    ratF s t a b Z - ratF s t a b Y = (Z - Y) * (1 + ∑ j ∈ t, resA s t a b j / ((Z - b j) * (Y - b j))) := by
  obtain ⟨c0, hpf⟩ := ratF_pf s t a b hcard hinj
  rw [hpf Z hZ, hpf Y hY, mul_add, mul_one, mul_sum]
  have : ∀ j ∈ t, resA s t a b j / (Y - b j) - resA s t a b j / (Z - b j) =
      (Z - Y) * (resA s t a b j / ((Z - b j) * (Y - b j))) := fun j hj => by
    have h1 : Z - b j ≠ 0 := sub_ne_zero.2 (hZ j hj)
    have h2 : Y - b j ≠ 0 := sub_ne_zero.2 (hY j hj)
    field_simp
    ring
  rw [← sum_congr rfl this, sum_sub_distrib]
  ring

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_C4

section S_R_C5
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset

theorem prod_neg_flip (s : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) :
    ∏ i ∈ s, (x - c i) = (-1) ^ s.card * ∏ i ∈ s, (c i - x) := by
  rw [← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => by ring

theorem resA_nonneg (k : ℕ) (hk : 1 ≤ k) (a b : ℕ → ℝ)
    (hab : ∀ j ∈ Icc 1 (k - 1), a j ≤ b j ∧ b j ≤ a (j + 1))
    (hbinc : ∀ i ∈ Icc 1 (k - 1), ∀ j ∈ Icc 1 (k - 1), i < j → b i < b j)
    (j : ℕ) (hj : j ∈ Icc 1 (k - 1)) : 0 ≤ resA (Icc 1 k) (Icc 1 (k - 1)) a b j := by
  have hj' := mem_Icc.1 hj

  have hmono : ∀ n, ∀ i, 1 ≤ i → i + n ≤ k → a i ≤ a (i + n) := by
    intro n
    induction n with
    | zero => intro i _ _; simp
    | succ n ih =>
      intro i hi hin
      have h1 := ih i hi (by omega)
      have h2 := hab (i + n) (by simp [mem_Icc]; omega)
      rw [show i + (n + 1) = i + n + 1 by ring]; linarith [h2.1, h2.2]
  have hle : ∀ i i', 1 ≤ i → i ≤ i' → i' ≤ k → a i ≤ a i' := fun i i' h1 h2 h3 => by
    have := hmono (i' - i) i h1 (by omega); rwa [Nat.add_sub_cancel' h2] at this
  unfold resA
  rw [← prod_filter_mul_prod_filter_not (Icc 1 k) (fun i => i ≤ j),
    ← prod_filter_mul_prod_filter_not ((Icc 1 (k - 1)).erase j) (fun m => m < j)]
  set N1 := ∏ i ∈ (Icc 1 k).filter (fun i => i ≤ j), (b j - a i)
  rw [prod_neg_flip ((Icc 1 k).filter (fun i => ¬ i ≤ j)) a (b j),
    prod_neg_flip (((Icc 1 (k - 1)).erase j).filter (fun m => ¬ m < j)) b (b j)]
  have hc1 : ((Icc 1 k).filter (fun i => ¬ i ≤ j)).card = k - j := by
    have : (Icc 1 k).filter (fun i => ¬ i ≤ j) = Ioc j k := by ext i; simp [mem_Ioc]; omega
    rw [this, Nat.card_Ioc]
  have hc2 : (((Icc 1 (k - 1)).erase j).filter (fun m => ¬ m < j)).card = k - 1 - j := by
    have : ((Icc 1 (k - 1)).erase j).filter (fun m => ¬ m < j) = Ioc j (k - 1) := by ext i; simp [mem_Ioc]; omega
    rw [this, Nat.card_Ioc]
  rw [hc1, hc2]
  have hN1 : 0 ≤ N1 := prod_nonneg fun i hi => by
    have := mem_filter.1 hi; have h := mem_Icc.1 this.1
    have := hle i j h.1 this.2 (by omega); linarith [(hab j hj).1]
  have hN2 : 0 ≤ ∏ i ∈ (Icc 1 k).filter (fun i => ¬ i ≤ j), (a i - b j) := prod_nonneg fun i hi => by
    have := mem_filter.1 hi; have h := mem_Icc.1 this.1
    have := hle (j + 1) i (by omega) (by omega) h.2; linarith [(hab j hj).2]
  have hP1 : 0 < ∏ m ∈ ((Icc 1 (k - 1)).erase j).filter (fun m => m < j), (b j - b m) := prod_pos fun m hm => by
    have h := mem_filter.1 hm; have h2 := mem_erase.1 h.1
    have := hbinc m h2.2 j hj h.2; linarith
  have hP2 : 0 < ∏ m ∈ ((Icc 1 (k - 1)).erase j).filter (fun m => ¬ m < j), (b m - b j) := prod_pos fun m hm => by
    have h := mem_filter.1 hm; have h2 := mem_erase.1 h.1
    have := hbinc j hj m h2.2 (by omega); linarith
  have hpow : ((-1 : ℝ) ^ (k - j)) = -((-1) ^ (k - 1 - j)) := by
    rw [show k - j = k - 1 - j + 1 by omega, pow_succ]; ring
  rw [hpow]
  have hsq : ((-1 : ℝ) ^ (k - 1 - j)) * ((-1) ^ (k - 1 - j)) = 1 := by
    rw [← mul_pow]; norm_num
  have e : -(N1 * (-((-1 : ℝ) ^ (k - 1 - j)) * ∏ i ∈ (Icc 1 k).filter (fun i => ¬ i ≤ j), (a i - b j))) /
      ((∏ m ∈ ((Icc 1 (k - 1)).erase j).filter (fun m => m < j), (b j - b m)) *
        ((-1) ^ (k - 1 - j) * ∏ m ∈ ((Icc 1 (k - 1)).erase j).filter (fun m => ¬ m < j), (b m - b j))) =
      (N1 * ∏ i ∈ (Icc 1 k).filter (fun i => ¬ i ≤ j), (a i - b j)) /
      ((∏ m ∈ ((Icc 1 (k - 1)).erase j).filter (fun m => m < j), (b j - b m)) *
        ∏ m ∈ ((Icc 1 (k - 1)).erase j).filter (fun m => ¬ m < j), (b m - b j)) := by
    have hσ : ((-1 : ℝ) ^ (k - 1 - j)) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [e]
  positivity

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_C5

section S_R_C6
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset

structure Side (k l : ℕ) (a b : ℕ → ℝ) (α β : ℝ) : Prop where
  inter : ∀ j ∈ Icc 1 (k - 1), a j ≤ b j ∧ b j ≤ a (j + 1)
  inc : ∀ i ∈ Icc 1 (k - 1), ∀ j ∈ Icc 1 (k - 1), i < j → b i < b j
  aL : ∀ i, 1 ≤ i → i < l → a i ≤ α
  aR : ∀ i, l < i → i ≤ k → β ≤ a i
  al : a l ≤ α ∨ β ≤ a l
  bL : ∀ j, 1 ≤ j → j < l → b j ≤ α
  bR : ∀ j, l ≤ j → j ≤ k - 1 → β ≤ b j

section
variable {k l : ℕ} {a b : ℕ → ℝ} {α β : ℝ}

theorem Side.card (hk : 1 ≤ k) : (Icc 1 k).card = (Icc 1 (k - 1)).card + 1 := by
  simp only [Nat.card_Icc]; omega

theorem Side.inj (h : Side k l a b α β) : Set.InjOn b (Icc 1 (k - 1) : Finset ℕ) := by
  intro i hi j hj e
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have := h.inc i hi j hj h1; rw [e] at this; exact lt_irrefl _ this
  · have := h.inc j hj i hi h1; rw [e] at this; exact lt_irrefl _ this

theorem Side.dist_a (h : Side k l a b α β) (hl1 : 1 ≤ l) (hlk : l ≤ k) (hαβ : α < β) (T : ℝ)
    (hT1 : α + (β - α) / 3 ≤ T) (hT2 : T ≤ β - (β - α) / 3) (i : ℕ) (hi : i ∈ Icc 1 k) :
    (β - α) / 3 ≤ |T - a i| := by
  have hi' := mem_Icc.1 hi
  rcases lt_trichotomy i l with h1 | rfl | h1
  · have := h.aL i hi'.1 h1; rw [abs_of_pos (by linarith)]; linarith
  · rcases h.al with h2 | h2
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
  · have := h.aR i h1 hi'.2; rw [abs_of_neg (by linarith)]; linarith

theorem Side.dist_b (h : Side k l a b α β) (hl1 : 1 ≤ l) (hlk : l ≤ k) (hαβ : α < β) (T : ℝ)
    (hT1 : α + (β - α) / 3 ≤ T) (hT2 : T ≤ β - (β - α) / 3) (j : ℕ) (hj : j ∈ Icc 1 (k - 1)) :
    (β - α) / 3 ≤ |T - b j| := by
  have hj' := mem_Icc.1 hj
  rcases lt_or_ge j l with h1 | h1
  · have := h.bL j hj'.1 h1; rw [abs_of_pos (by linarith)]; linarith
  · have := h.bR j h1 hj'.2; rw [abs_of_neg (by linarith)]; linarith

theorem Side.logDeriv (h : Side k l a b α β) (hl1 : 1 ≤ l) (hlk : l ≤ k) (hαβ : α < β) (T : ℝ)
    (hT1 : α + (β - α) / 3 ≤ T) (hT2 : T ≤ β - (β - α) / 3) :
    |∑ i ∈ Icc 1 k, 1 / (T - a i) - ∑ j ∈ Icc 1 (k - 1), 1 / (T - b j)| ≤ 6 / (β - α) :=
  logDeriv_bound k l hl1 hlk a b α β T hαβ h.inter h.aL h.aR h.al h.bL h.bR hT1 hT2

theorem Side.deriv_bounds (h : Side k l a b α β) (hl1 : 1 ≤ l) (hlk : l ≤ k) (hαβ : α < β) (T : ℝ)
    (hT1 : α + (β - α) / 3 ≤ T) (hT2 : T ≤ β - (β - α) / 3) :
    1 + ∑ j ∈ Icc 1 (k - 1), resA (Icc 1 k) (Icc 1 (k - 1)) a b j / (T - b j) ^ 2 ≤
      6 / (β - α) * |ratF (Icc 1 k) (Icc 1 (k - 1)) a b T| := by
  have hD : 0 < (β - α) / 3 := by linarith
  have ha : ∀ i ∈ Icc 1 k, T ≠ a i := fun i hi e => by
    have := h.dist_a hl1 hlk hαβ T hT1 hT2 i hi; rw [e, sub_self, abs_zero] at this; linarith
  have hb : ∀ j ∈ Icc 1 (k - 1), T ≠ b j := fun j hj e => by
    have := h.dist_b hl1 hlk hαβ T hT1 hT2 j hj; rw [e, sub_self, abs_zero] at this; linarith
  rw [ratF_deriv_id _ _ a b (Side.card (by omega)) h.inj T ha hb]
  calc ratF (Icc 1 k) (Icc 1 (k - 1)) a b T * (∑ i ∈ Icc 1 k, 1 / (T - a i) - ∑ j ∈ Icc 1 (k - 1), 1 / (T - b j))
      ≤ |ratF (Icc 1 k) (Icc 1 (k - 1)) a b T * (∑ i ∈ Icc 1 k, 1 / (T - a i) - ∑ j ∈ Icc 1 (k - 1), 1 / (T - b j))| :=
        le_abs_self _
    _ = |ratF (Icc 1 k) (Icc 1 (k - 1)) a b T| * |∑ i ∈ Icc 1 k, 1 / (T - a i) - ∑ j ∈ Icc 1 (k - 1), 1 / (T - b j)| :=
        abs_mul _ _
    _ ≤ |ratF (Icc 1 k) (Icc 1 (k - 1)) a b T| * (6 / (β - α)) :=
        mul_le_mul_of_nonneg_left (h.logDeriv hl1 hlk hαβ T hT1 hT2) (abs_nonneg _)
    _ = 6 / (β - α) * |ratF (Icc 1 k) (Icc 1 (k - 1)) a b T| := mul_comm _ _

theorem Side.resA_nonneg (h : Side k l a b α β) (hk : 1 ≤ k) (j : ℕ) (hj : j ∈ Icc 1 (k - 1)) :
    0 ≤ resA (Icc 1 k) (Icc 1 (k - 1)) a b j :=
  Formalism.FourierDecayAlt.P.MAx3.R.resA_nonneg k hk a b h.inter h.inc j hj

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_C6

section S_R_C7
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset

section
variable {k l : ℕ} {af bf ag bg : ℕ → ℝ} {α β : ℝ}

theorem ratF_ne (s t : Finset ℕ) (a b : ℕ → ℝ) (T : ℝ) (ha : ∀ i ∈ s, T ≠ a i) (hb : ∀ j ∈ t, T ≠ b j) :
    ratF s t a b T ≠ 0 := by
  unfold ratF
  exact div_ne_zero (prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 (ha i hi))
    (prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hb j hj))

theorem g_far (hk : 1 ≤ k) (hl1 : 1 ≤ l) (hlk : l ≤ k) (hαβ : α < β) (hg : Side k l ag bg α β) (T Z : ℝ)
    (hT1 : α + (β - α) / 3 ≤ T) (hT2 : T ≤ β - (β - α) / 3)
    (hZ : ∀ j ∈ Icc 1 (k - 1), 1 ≤ |Z - bg j|) :
    |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg Z| ≤ |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T| *
      (1 + 6 * |Z - T| * (1 + |Z - T|) / (β - α)) := by
  have hI : 0 < β - α := by linarith
  have hTb : ∀ j ∈ Icc 1 (k - 1), T ≠ bg j := fun j hj e => by
    have := hg.dist_b hl1 hlk hαβ T hT1 hT2 j hj; rw [e, sub_self, abs_zero] at this; linarith
  have hZb : ∀ j ∈ Icc 1 (k - 1), Z ≠ bg j := fun j hj e => by
    have := hZ j hj; rw [e, sub_self, abs_zero] at this; linarith
  have htwo := ratF_two _ _ ag bg (Side.card hk) hg.inj T Z hTb hZb
  set S := ∑ j ∈ Icc 1 (k - 1), resA (Icc 1 k) (Icc 1 (k - 1)) ag bg j / (T - bg j) ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun j hj => div_nonneg (hg.resA_nonneg hk j hj) (sq_nonneg _)
  have hSd := hg.deriv_bounds hl1 hlk hαβ T hT1 hT2
  set d := |Z - T| with hd
  have hsum : |∑ j ∈ Icc 1 (k - 1), resA (Icc 1 k) (Icc 1 (k - 1)) ag bg j / ((Z - bg j) * (T - bg j))| ≤
      (1 + d) * S := by
    rw [hS, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
    have hA := hg.resA_nonneg hk j hj
    have hz1 := hZ j hj
    have hTbj : T - bg j ≠ 0 := sub_ne_zero.2 (hTb j hj)
    have htri : |T - bg j| ≤ (1 + d) * |Z - bg j| := by
      have h1 : |T - bg j| ≤ |T - Z| + |Z - bg j| := abs_sub_le T Z (bg j)
      have hTZ : |T - Z| = d := by rw [hd, abs_sub_comm]
      rw [hTZ] at h1
      have hd0 : 0 ≤ d := by rw [hd]; exact abs_nonneg _
      nlinarith
    rw [abs_div, abs_of_nonneg hA, abs_mul, div_le_iff₀ (by positivity)]
    have hsq : (T - bg j) ^ 2 = |T - bg j| ^ 2 := (sq_abs _).symm
    rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by rw [hsq]; positivity), hsq]
    have hp : 0 < |T - bg j| := abs_pos.2 hTbj
    calc resA (Icc 1 k) (Icc 1 (k - 1)) ag bg j * |T - bg j| ^ 2
        = resA (Icc 1 k) (Icc 1 (k - 1)) ag bg j * |T - bg j| * |T - bg j| := by ring
      _ ≤ resA (Icc 1 k) (Icc 1 (k - 1)) ag bg j * ((1 + d) * |Z - bg j|) * |T - bg j| := by gcongr
      _ = (1 + d) * resA (Icc 1 k) (Icc 1 (k - 1)) ag bg j * (|Z - bg j| * |T - bg j|) := by ring
  have hdiff : |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg Z - ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T| ≤
      d * (1 + d) * (6 / (β - α) * |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T|) := by
    rw [htwo, abs_mul, ← hd]
    have h1 : |1 + ∑ j ∈ Icc 1 (k - 1), resA (Icc 1 k) (Icc 1 (k - 1)) ag bg j / ((Z - bg j) * (T - bg j))| ≤
        (1 + d) * (1 + S) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_one]
      nlinarith [abs_nonneg (Z - T)]
    calc d * |1 + ∑ j ∈ Icc 1 (k - 1), resA (Icc 1 k) (Icc 1 (k - 1)) ag bg j / ((Z - bg j) * (T - bg j))|
        ≤ d * ((1 + d) * (1 + S)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ d * ((1 + d) * (6 / (β - α) * |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T|)) := by
          gcongr
      _ = d * (1 + d) * (6 / (β - α) * |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T|) := by ring
  have := abs_sub_abs_le_abs_sub (ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg Z) (ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T)
  have e : |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T| * (1 + 6 * d * (1 + d) / (β - α)) =
      |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T| + d * (1 + d) * (6 / (β - α) * |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T|) := by
    field_simp
  rw [e]
  linarith

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_C7

section S_R_C8
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset

section
variable {k l : ℕ} {af bf ag bg : ℕ → ℝ} {α β : ℝ}

theorem term_bound (A Gz F G d e I : ℝ) (hA : 0 ≤ A) (hF : 0 < F) (hG : 0 < G) (hI : 0 < I) (hd2 : 2 ≤ d)
    (hdI : I ≤ 3 * d) (he : d / 2 ≤ e) (hGz : Gz ≤ G * (1 + 6 * d * (1 + d) / I)) (hGz0 : 0 ≤ Gz) :
    A * Gz / (F * G * d ^ 3 * e) ≤ 22 / (I * F) * (A / d ^ 2) := by
  have hd : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have h11 : 1 + 6 * d * (1 + d) / I ≤ 11 * d ^ 2 / I := by
    rw [show 1 + 6 * d * (1 + d) / I = (I + 6 * d * (1 + d)) / I by field_simp, div_le_div_iff_of_pos_right hI]
    nlinarith
  have hGz' : Gz ≤ G * (11 * d ^ 2 / I) := hGz.trans (mul_le_mul_of_nonneg_left h11 hG.le)
  rw [div_le_iff₀ (by positivity)]
  have : 22 / (I * F) * (A / d ^ 2) * (F * G * d ^ 3 * e) = 22 * A * G * d * e / I := by
    field_simp
  rw [this]
  have h1 : A * Gz ≤ A * (G * (11 * d ^ 2 / I)) := mul_le_mul_of_nonneg_left hGz' hA
  have h2 : A * (G * (11 * d ^ 2 / I)) = 11 * A * G * d * d / I := by ring
  have h3 : 11 * A * G * d * d / I ≤ 22 * A * G * d * e / I := by
    apply div_le_div_of_nonneg_right _ hI.le
    have : 0 ≤ 11 * A * G * d := by positivity
    nlinarith
  linarith

theorem core_SS (hk : 1 ≤ k) (hl1 : 1 ≤ l) (hlk : l ≤ k) (hI6 : 6 ≤ β - α) (hf : Side k l af bf α β)
    (hg : Side k l ag bg α β) (hsh : ∀ j, bg j = bf j + 1) (T : ℝ)
    (hT1 : α + (β - α) / 3 ≤ T) (hT2 : T ≤ β - (β - α) / 3) (V : Finset ℕ) (hV : V ⊆ Icc 1 (k - 1))
    (hsep : ∀ m ∈ V, ∀ j ∈ Icc 1 (k - 1), 1 ≤ |bf m - bg j|) :
    ∑ m ∈ V, resA (Icc 1 k) (Icc 1 (k - 1)) af bf m * |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg (bf m)| /
      (|ratF (Icc 1 k) (Icc 1 (k - 1)) af bf T| * |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T| * |T - bf m| ^ 3 *
        |T - bg m|) ≤ 132 / (β - α) ^ 2 := by
  have hαβ : α < β := by linarith
  have hI : 0 < β - α := by linarith
  have hfa : ∀ i ∈ Icc 1 k, T ≠ af i := fun i hi e => by
    have := hf.dist_a hl1 hlk hαβ T hT1 hT2 i hi; rw [e, sub_self, abs_zero] at this; linarith
  have hfb : ∀ j ∈ Icc 1 (k - 1), T ≠ bf j := fun j hj e => by
    have := hf.dist_b hl1 hlk hαβ T hT1 hT2 j hj; rw [e, sub_self, abs_zero] at this; linarith
  have hga : ∀ i ∈ Icc 1 k, T ≠ ag i := fun i hi e => by
    have := hg.dist_a hl1 hlk hαβ T hT1 hT2 i hi; rw [e, sub_self, abs_zero] at this; linarith
  have hgb : ∀ j ∈ Icc 1 (k - 1), T ≠ bg j := fun j hj e => by
    have := hg.dist_b hl1 hlk hαβ T hT1 hT2 j hj; rw [e, sub_self, abs_zero] at this; linarith
  set F := |ratF (Icc 1 k) (Icc 1 (k - 1)) af bf T| with hFdef
  set G := |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg T| with hGdef
  have hF : 0 < F := abs_pos.2 (ratF_ne _ _ _ _ T hfa hfb)
  have hG : 0 < G := abs_pos.2 (ratF_ne _ _ _ _ T hga hgb)
  have hterm : ∀ m ∈ V, resA (Icc 1 k) (Icc 1 (k - 1)) af bf m * |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg (bf m)| /
      (F * G * |T - bf m| ^ 3 * |T - bg m|) ≤
        22 / ((β - α) * F) * (resA (Icc 1 k) (Icc 1 (k - 1)) af bf m / (T - bf m) ^ 2) := by
    intro m hm
    have hmt := hV hm
    have hd := hf.dist_b hl1 hlk hαβ T hT1 hT2 m hmt
    have hfar := g_far hk hl1 hlk hαβ hg T (bf m) hT1 hT2 (hsep m hm)
    rw [abs_sub_comm (bf m) T] at hfar
    have he : |T - bf m| / 2 ≤ |T - bg m| := by
      rw [hsh m]
      have : |T - bf m| - 1 ≤ |T - (bf m + 1)| := by
        have := abs_sub_abs_le_abs_sub (T - bf m) (T - (bf m + 1))
        have e1 : T - bf m - (T - (bf m + 1)) = 1 := by ring
        rw [e1, abs_one] at this; linarith
      linarith
    have h := term_bound (resA (Icc 1 k) (Icc 1 (k - 1)) af bf m) |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg (bf m)| F G
      |T - bf m| |T - bg m| (β - α) (hf.resA_nonneg hk m hmt) hF hG hI (by linarith) (by linarith) he hfar (abs_nonneg _)
    rwa [sq_abs] at h
  calc ∑ m ∈ V, resA (Icc 1 k) (Icc 1 (k - 1)) af bf m * |ratF (Icc 1 k) (Icc 1 (k - 1)) ag bg (bf m)| /
        (F * G * |T - bf m| ^ 3 * |T - bg m|)
      ≤ ∑ m ∈ V, 22 / ((β - α) * F) * (resA (Icc 1 k) (Icc 1 (k - 1)) af bf m / (T - bf m) ^ 2) := sum_le_sum hterm
    _ = 22 / ((β - α) * F) * ∑ m ∈ V, resA (Icc 1 k) (Icc 1 (k - 1)) af bf m / (T - bf m) ^ 2 := by rw [mul_sum]
    _ ≤ 22 / ((β - α) * F) * ∑ m ∈ Icc 1 (k - 1), resA (Icc 1 k) (Icc 1 (k - 1)) af bf m / (T - bf m) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg hV fun j hj _ => div_nonneg (hf.resA_nonneg hk j hj) (sq_nonneg _)
    _ ≤ 22 / ((β - α) * F) * (6 / (β - α) * F) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := hf.deriv_bounds hl1 hlk hαβ T hT1 hT2
        linarith
    _ = 132 / (β - α) ^ 2 := by field_simp; ring

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_C8

section S_R_C9
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset

section
variable {k l : ℕ} {a b : ℕ → ℝ} {α β : ℝ}

theorem Side.ratio (h : Side k l a b α β) (hl1 : 1 ≤ l) (hlk : l ≤ k) (hαβ : α < β) (Z₁ Z₂ : ℝ)
    (h1 : Z₁ ∈ Set.Icc (α + (β - α) / 3) (β - (β - α) / 3)) (h2 : Z₂ ∈ Set.Icc (α + (β - α) / 3) (β - (β - α) / 3)) :
    |ratF (Icc 1 k) (Icc 1 (k - 1)) a b Z₁| ≤ Real.exp 2 * |ratF (Icc 1 k) (Icc 1 (k - 1)) a b Z₂| := by
  set M := Set.Icc (α + (β - α) / 3) (β - (β - α) / 3)
  have hI : 0 < β - α := by linarith
  have hne : ∀ x ∈ M, ratF (Icc 1 k) (Icc 1 (k - 1)) a b x ≠ 0 := fun x hx => by
    apply ratF_ne
    · intro i hi e
      have := h.dist_a hl1 hlk hαβ x hx.1 hx.2 i hi; rw [e, sub_self, abs_zero] at this; linarith
    · intro j hj e
      have := h.dist_b hl1 hlk hαβ x hx.1 hx.2 j hj; rw [e, sub_self, abs_zero] at this; linarith
  have hder : ∀ x ∈ M, HasDerivWithinAt (fun x => Real.log (ratF (Icc 1 k) (Icc 1 (k - 1)) a b x))
      (∑ i ∈ Icc 1 k, 1 / (x - a i) - ∑ j ∈ Icc 1 (k - 1), 1 / (x - b j)) M x := by
    intro x hx
    have ha : ∀ i ∈ Icc 1 k, x ≠ a i := fun i hi e => by
      have := h.dist_a hl1 hlk hαβ x hx.1 hx.2 i hi; rw [e, sub_self, abs_zero] at this; linarith
    have hb : ∀ j ∈ Icc 1 (k - 1), x ≠ b j := fun j hj e => by
      have := h.dist_b hl1 hlk hαβ x hx.1 hx.2 j hj; rw [e, sub_self, abs_zero] at this; linarith
    have hd := (hasDerivAt_ratioLin _ _ a b x ha hb).log (hne x hx)
    refine (hd.congr_deriv ?_).hasDerivWithinAt
    have := hne x hx
    unfold ratF at this
    exact mul_div_cancel_left₀ _ this
  have hbound : ∀ x ∈ M, ‖∑ i ∈ Icc 1 k, 1 / (x - a i) - ∑ j ∈ Icc 1 (k - 1), 1 / (x - b j)‖ ≤ 6 / (β - α) :=
    fun x hx => by rw [Real.norm_eq_abs]; exact h.logDeriv hl1 hlk hαβ x hx.1 hx.2
  have hmvt := (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound h2 h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hdist : |Z₁ - Z₂| ≤ (β - α) / 3 := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hlog : Real.log |ratF (Icc 1 k) (Icc 1 (k - 1)) a b Z₁| ≤ Real.log |ratF (Icc 1 k) (Icc 1 (k - 1)) a b Z₂| + 2 := by
    rw [Real.log_abs, Real.log_abs]
    have := le_abs_self (Real.log (ratF (Icc 1 k) (Icc 1 (k - 1)) a b Z₁) - Real.log (ratF (Icc 1 k) (Icc 1 (k - 1)) a b Z₂))
    have h6 : 6 / (β - α) * |Z₁ - Z₂| ≤ 2 := by
      calc 6 / (β - α) * |Z₁ - Z₂| ≤ 6 / (β - α) * ((β - α) / 3) := by gcongr
        _ = 2 := by field_simp; ring
    linarith
  have hp1 : 0 < |ratF (Icc 1 k) (Icc 1 (k - 1)) a b Z₁| := abs_pos.2 (hne Z₁ h1)
  have hp2 : 0 < |ratF (Icc 1 k) (Icc 1 (k - 1)) a b Z₂| := abs_pos.2 (hne Z₂ h2)
  rw [← Real.log_le_log_iff hp1 (by positivity), Real.log_mul (by positivity) hp2.ne', Real.log_exp]
  linarith

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_C9

section S_R_X1
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

section Real
variable {S : Type} [Fintype S] [DecidableEq S]

def xsR (x0R : ℝ → ℝ) (v : List (Letter ℂ S)) (e : Ix S) (Z : ℝ) : ℝ := x0R Z * phR v e Z

def qwR (q0R : ℝ → ℝ) (v : List (Letter ℂ S)) (Z : ℝ) : ℝ := q0R Z * psR v Z

def csR (x0R q0R : ℝ → ℝ) : List (Letter ℂ S) → Ix S → ℝ
  | [], _ => 1
  | b :: v, e => csR x0R q0R v e *
      (if e b.intersection_update_fsHerm_neg_one = 0 then qwR q0R v b.pt.re / xsR x0R v e (b.pt.re + 1) else xsR x0R v e b.pt.re)

theorem cs_real (x0 q0 : ℂ → ℂ) (x0R q0R : ℝ → ℝ) (hx : ∀ Z : ℝ, x0 (Z : ℂ) = ((x0R Z : ℝ) : ℂ))
    (hq : ∀ Z : ℝ, q0 (Z : ℂ) = ((q0R Z : ℝ) : ℂ)) :
    ∀ (v : List (Letter ℂ S)), (∀ a ∈ v, a.plus = true ∧ a.pt.im = 0) →
      ∀ e : Ix S, cs x0 q0 v e = ((csR x0R q0R v e : ℝ) : ℂ)
  | [], _, e => by simp [cs, csR]
  | b :: v, h, e => by
    have hb := h b List.mem_cons_self
    have hv : ∀ a ∈ v, a.plus = true ∧ a.pt.im = 0 := fun a ha => h a (List.mem_cons_of_mem _ ha)
    have ih := cs_real x0 q0 x0R q0R hx hq v hv e
    have hp := pt_eq hb.2
    simp only [cs, csR, hb.1, if_true, ih]
    rw [hp, ofReal_add_one, qw_real _ _ hv, xs_real _ _ hv, xs_real _ _ hv, hx, hx, hq]
    simp only [Complex.ofReal_re, xsR, qwR]
    split_ifs <;> push_cast <;> ring

end Real

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X1

section S_R_X2
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

section Real
variable {S : Type} [Fintype S] [DecidableEq S]

theorem phR_cons (b : Letter ℂ S) (v : List (Letter ℂ S)) (e : Ix S) (Z : ℝ) :
    phR (b :: v) e Z = (if e b.intersection_update_fsHerm_neg_one = 0 then (Z - b.pt.re) / (Z - b.pt.re - 1) else 1) * phR v e Z := by
  simp [phR]

theorem psR_cons (b : Letter ℂ S) (v : List (Letter ℂ S)) (Z : ℝ) :
    psR (b :: v) Z = (Z - b.pt.re + 1) / (Z - b.pt.re) * psR v Z := by
  simp [psR]

theorem phR_congr : ∀ (v : List (Letter ℂ S)) (e e' : Ix S), (∀ b ∈ v, e b.intersection_update_fsHerm_neg_one = e' b.intersection_update_fsHerm_neg_one) →
    ∀ Z, phR v e Z = phR v e' Z
  | [], _, _, _, _ => rfl
  | b :: v, e, e', h, Z => by
    rw [phR_cons, phR_cons, h b List.mem_cons_self,
      phR_congr v e e' (fun c hc => h c (List.mem_cons_of_mem _ hc)) Z]

theorem csR_congr (x0R q0R : ℝ → ℝ) : ∀ (v : List (Letter ℂ S)) (e e' : Ix S), (∀ b ∈ v, e b.intersection_update_fsHerm_neg_one = e' b.intersection_update_fsHerm_neg_one) →
    csR x0R q0R v e = csR x0R q0R v e'
  | [], _, _, _ => rfl
  | b :: v, e, e', h => by
    have hv : ∀ c ∈ v, e c.intersection_update_fsHerm_neg_one = e' c.intersection_update_fsHerm_neg_one := fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [csR, xsR, csR_congr x0R q0R v e e' hv, phR_congr v e e' hv, h b List.mem_cons_self]

theorem phR_ne (b : Letter ℂ S) : ∀ (v : List (Letter ℂ S)), (∀ c ∈ v, 2 < |b.pt.re - c.pt.re|) →
    ∀ (e : Ix S) (t : ℝ), |t| ≤ 1 → phR v e (b.pt.re + t) ≠ 0
  | [], _, _, _, _ => by simp [phR]
  | c :: v, h, e, t, ht => by
    rw [phR_cons]
    refine mul_ne_zero ?_ (phR_ne b v (fun d hd => h d (List.mem_cons_of_mem _ hd)) e t ht)
    have hc := h c List.mem_cons_self
    rw [abs_le] at ht
    split_ifs
    · apply div_ne_zero
      · intro e0
        have : b.pt.re - c.pt.re = -t := by linarith
        rw [this, abs_neg] at hc
        rcases abs_cases t with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [ht.1, ht.2]
      · intro e0
        have : b.pt.re - c.pt.re = 1 - t := by linarith
        rw [this] at hc
        rcases abs_cases (1 - t) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [ht.1, ht.2]
    · exact one_ne_zero

theorem csR_type (x0s x0t q0R : ℝ → ℝ) (μ : Letter ℂ S → ℝ) : ∀ (v : List (Letter ℂ S)) (e : Ix S),
    v.Pairwise (fun b c => 2 < |b.pt.re - c.pt.re|) →
    (∀ b ∈ v, (e b.intersection_update_fsHerm_neg_one = 0 → x0t (b.pt.re + 1) = x0s (b.pt.re + 1) * μ b ∧ x0s (b.pt.re + 1) ≠ 0) ∧
      (e b.intersection_update_fsHerm_neg_one ≠ 0 → x0t b.pt.re * μ b = x0s b.pt.re) ∧ μ b ≠ 0) →
    csR x0t q0R v e * (v.map μ).prod = csR x0s q0R v e
  | [], e, _, _ => by simp [csR]
  | b :: v, e, hp, h => by
    rw [List.pairwise_cons] at hp
    have hv : ∀ c ∈ v, (e c.intersection_update_fsHerm_neg_one = 0 → x0t (c.pt.re + 1) = x0s (c.pt.re + 1) * μ c ∧ x0s (c.pt.re + 1) ≠ 0) ∧
        (e c.intersection_update_fsHerm_neg_one ≠ 0 → x0t c.pt.re * μ c = x0s c.pt.re) ∧ μ c ≠ 0 := fun c hc => h c (List.mem_cons_of_mem _ hc)
    have ih := csR_type x0s x0t q0R μ v e hp.2 hv
    obtain ⟨hb1, hb2, hb3⟩ := h b List.mem_cons_self
    simp only [csR, List.map_cons, List.prod_cons]
    rw [show csR x0t q0R v e * (if e b.intersection_update_fsHerm_neg_one = 0 then qwR q0R v b.pt.re / xsR x0t v e (b.pt.re + 1)
        else xsR x0t v e b.pt.re) * (μ b * (List.map μ v).prod) =
        (csR x0t q0R v e * (List.map μ v).prod) * ((if e b.intersection_update_fsHerm_neg_one = 0 then qwR q0R v b.pt.re / xsR x0t v e (b.pt.re + 1)
        else xsR x0t v e b.pt.re) * μ b) by ring, ih]
    congr 1
    by_cases he : e b.intersection_update_fsHerm_neg_one = 0
    · simp only [he, if_true, xsR]
      obtain ⟨e1, e2⟩ := hb1 he
      have e3 : phR v e (b.pt.re + 1) ≠ 0 := phR_ne b v hp.1 e 1 (by norm_num)
      rw [e1]
      field_simp
    · simp only [he, if_false, xsR]
      rw [← hb2 he]; ring

end Real

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X2

section S_R_X3
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

section Real
variable {S : Type} [Fintype S] [DecidableEq S]

theorem csR_pos (x0R q0R : ℝ → ℝ) (L : ℝ) (hL : 2 ≤ L) : ∀ (v : List (Letter ℂ S)) (e : Ix S),
    v.Pairwise (fun b c => L ≤ b.pt.re - c.pt.re) →
    (∀ b ∈ v, 0 < x0R b.pt.re ∧ 0 < x0R (b.pt.re + 1) ∧ 0 < q0R b.pt.re) → 0 < csR x0R q0R v e
  | [], e, _, _ => by simp [csR]
  | b :: v, e, hp, h => by
    rw [List.pairwise_cons] at hp
    have ih := csR_pos x0R q0R L hL v e hp.2 (fun c hc => h c (List.mem_cons_of_mem _ hc))
    obtain ⟨h1, h2, h3⟩ := h b List.mem_cons_self
    have hph0 := (phR_bounds L hL v e b.pt.re fun c hc => hp.1 c hc).1
    have hph1 := (phR_bounds L hL v e (b.pt.re + 1) fun c hc => by have := hp.1 c hc; linarith).1
    have hps := (psR_bounds L hL v b.pt.re fun c hc => hp.1 c hc).1
    simp only [csR, xsR, qwR]
    apply mul_pos ih
    split_ifs
    · apply div_pos (mul_pos h3 (by linarith)) (mul_pos h2 (by linarith))
    · exact mul_pos h1 (by linarith)

theorem phR_flip (la : Letter ℂ S) (e e' : Ix S) (he : ∀ x, x ≠ la.intersection_update_fsHerm_neg_one → e x = e' x) (hea : e la.intersection_update_fsHerm_neg_one = 0)
    (he'a : e' la.intersection_update_fsHerm_neg_one ≠ 0) (Z : ℝ) : ∀ (v : List (Letter ℂ S)), (v.map Letter.intersection_update_fsHerm_neg_one).Nodup → la ∈ v →
    phR v e Z = phR v e' Z * ((Z - la.pt.re) / (Z - la.pt.re - 1))
  | [], _, h => absurd h List.not_mem_nil
  | b :: v, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [phR_cons, phR_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · have hv : ∀ c ∈ v, e c.intersection_update_fsHerm_neg_one = e' c.intersection_update_fsHerm_neg_one := fun c hc => he _ (fun e0 => hnd.1 (e0 ▸ List.mem_map_of_mem hc))
      rw [phR_congr v e e' hv, if_pos hea, if_neg he'a]; ring
    · have hb : b.intersection_update_fsHerm_neg_one ≠ la.intersection_update_fsHerm_neg_one := fun e0 => hnd.1 (e0 ▸ List.mem_map_of_mem h')
      rw [he _ hb, phR_flip la e e' he hea he'a Z v hnd.2 h']; ring

end Real

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X3

section S_R_X4
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

theorem phi_bounds (L d : ℝ) (hL : 2 ≤ L) (hd : L ≤ d) : 1 ≤ d / (d - 1) ∧ d / (d - 1) ≤ 1 + 2 / L := by
  have h1 : 0 < d - 1 := by linarith
  constructor
  · rw [le_div_iff₀ h1]; linarith
  · rw [div_le_iff₀ h1]
    have h2 : 2 / L * (d - 1) ≥ 1 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
    nlinarith

section Real
variable {S : Type} [Fintype S] [DecidableEq S]

theorem csR_flip (x0R q0R : ℝ → ℝ) (L : ℝ) (hL : 2 ≤ L) (la : Letter ℂ S) (e e' : Ix S)
    (he : ∀ x, x ≠ la.intersection_update_fsHerm_neg_one → e x = e' x) (hea : e la.intersection_update_fsHerm_neg_one = 0) (he'a : e' la.intersection_update_fsHerm_neg_one ≠ 0) :
    ∀ (v : List (Letter ℂ S)), (v.map Letter.intersection_update_fsHerm_neg_one).Nodup → la ∈ v →
    v.Pairwise (fun b c => L ≤ b.pt.re - c.pt.re) →
    (∀ b ∈ v, 0 < x0R b.pt.re ∧ 0 < x0R (b.pt.re + 1) ∧ 0 < q0R b.pt.re) →
    csR x0R q0R v e ≤ csR x0R q0R v e' * (q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1))) *
      ((1 + 2 / L) * (1 + 1 / L)) ^ v.length
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | b :: v, hnd, h, hp, hpos => by
    have hnd' := hnd
    rw [List.map_cons, List.nodup_cons] at hnd'
    have hp' := hp
    rw [List.pairwise_cons] at hp'
    have hposv : ∀ c ∈ v, 0 < x0R c.pt.re ∧ 0 < x0R (c.pt.re + 1) ∧ 0 < q0R c.pt.re :=
      fun c hc => hpos c (List.mem_cons_of_mem _ hc)
    have hK1 : 1 ≤ (1 + 2 / L) * (1 + 1 / L) := by
      have : 0 ≤ 2 / L := by positivity
      have : 0 ≤ 1 / L := by positivity
      nlinarith
    have hKpos : 0 < (1 + 2 / L) * (1 + 1 / L) := by linarith
    have hcs' := csR_pos x0R q0R L hL v e' hp'.2 hposv
    obtain ⟨hb1, hb2, hb3⟩ := hpos b List.mem_cons_self
    simp only [csR, List.length_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · have hv : ∀ c ∈ v, e c.intersection_update_fsHerm_neg_one = e' c.intersection_update_fsHerm_neg_one := fun c hc => he _ (fun e0 => hnd'.1 (e0 ▸ List.mem_map_of_mem hc))
      rw [csR_congr x0R q0R v e e' hv, if_pos hea, if_neg he'a]
      simp only [xsR, qwR]
      rw [phR_congr v e e' hv]
      have hph0 := (phR_bounds L hL v e' la.pt.re fun c hc => hp'.1 c hc)
      have hph1 := (phR_bounds L hL v e' (la.pt.re + 1) fun c hc => by have := hp'.1 c hc; linarith)
      have hps := (psR_bounds L hL v la.pt.re fun c hc => hp'.1 c hc)
      have hKn : (1 + 1 / L) ^ v.length ≤ ((1 + 2 / L) * (1 + 1 / L)) ^ (v.length + 1) := by
        calc (1 + 1 / L) ^ v.length ≤ ((1 + 2 / L) * (1 + 1 / L)) ^ v.length := by
              apply pow_le_pow_left₀ (by positivity)
              have : 0 ≤ 2 / L := by positivity
              have : 0 ≤ 1 / L := by positivity
              nlinarith
          _ ≤ ((1 + 2 / L) * (1 + 1 / L)) ^ (v.length + 1) := pow_le_pow_right₀ hK1 (Nat.le_succ _)
      have key : psR v la.pt.re / phR v e' (la.pt.re + 1) ≤
          phR v e' la.pt.re * ((1 + 2 / L) * (1 + 1 / L)) ^ (v.length + 1) := by
        calc psR v la.pt.re / phR v e' (la.pt.re + 1) ≤ psR v la.pt.re := div_le_self (by linarith [hps.1]) hph1.1
          _ ≤ ((1 + 2 / L) * (1 + 1 / L)) ^ (v.length + 1) := hps.2.trans hKn
          _ ≤ phR v e' la.pt.re * ((1 + 2 / L) * (1 + 1 / L)) ^ (v.length + 1) :=
              le_mul_of_one_le_left (by positivity) hph0.1
      have e1 : csR x0R q0R v e' * (q0R la.pt.re * psR v la.pt.re / (x0R (la.pt.re + 1) * phR v e' (la.pt.re + 1))) =
          csR x0R q0R v e' * (q0R la.pt.re / x0R (la.pt.re + 1)) * (psR v la.pt.re / phR v e' (la.pt.re + 1)) := by
        field_simp
      have e2 : csR x0R q0R v e' * (x0R la.pt.re * phR v e' la.pt.re) * (q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1))) *
          ((1 + 2 / L) * (1 + 1 / L)) ^ (v.length + 1) =
          csR x0R q0R v e' * (q0R la.pt.re / x0R (la.pt.re + 1)) *
            (phR v e' la.pt.re * ((1 + 2 / L) * (1 + 1 / L)) ^ (v.length + 1)) := by
        field_simp
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left key (by positivity)
    · have hb : b.intersection_update_fsHerm_neg_one ≠ la.intersection_update_fsHerm_neg_one := fun e0 => hnd'.1 (e0 ▸ List.mem_map_of_mem h')
      have ih := csR_flip x0R q0R L hL la e e' he hea he'a v hnd'.2 h' hp'.2 hposv
      have hba : L ≤ b.pt.re - la.pt.re := hp'.1 la h'
      have hφ0 := phi_bounds L (b.pt.re - la.pt.re) hL hba
      have hφ1 := phi_bounds L (b.pt.re + 1 - la.pt.re) hL (by linarith)
      have hflip0 := phR_flip la e e' he hea he'a b.pt.re v hnd'.2 h'
      have hflip1 := phR_flip la e e' he hea he'a (b.pt.re + 1) v hnd'.2 h'
      have hph0 := (phR_bounds L hL v e' b.pt.re fun c hc => hp'.1 c hc)
      have hph1 := (phR_bounds L hL v e' (b.pt.re + 1) fun c hc => by have := hp'.1 c hc; linarith)
      have hps := (psR_bounds L hL v b.pt.re fun c hc => hp'.1 c hc)
      rw [he _ hb]
      have hcse : 0 ≤ csR x0R q0R v e := (csR_pos x0R q0R L hL v e hp'.2 hposv).le
      have hF : (if e' b.intersection_update_fsHerm_neg_one = 0 then qwR q0R v b.pt.re / xsR x0R v e (b.pt.re + 1) else xsR x0R v e b.pt.re) ≤
          (if e' b.intersection_update_fsHerm_neg_one = 0 then qwR q0R v b.pt.re / xsR x0R v e' (b.pt.re + 1) else xsR x0R v e' b.pt.re) *
            ((1 + 2 / L) * (1 + 1 / L)) := by
        simp only [xsR, qwR]
        rw [hflip0, hflip1]
        split_ifs
        · have hA : 0 < q0R b.pt.re * psR v b.pt.re := mul_pos hb3 (by linarith [hps.1])
          have hB : 0 < x0R (b.pt.re + 1) * phR v e' (b.pt.re + 1) := mul_pos hb2 (by linarith [hph1.1])
          calc q0R b.pt.re * psR v b.pt.re / (x0R (b.pt.re + 1) * (phR v e' (b.pt.re + 1) *
                ((b.pt.re + 1 - la.pt.re) / (b.pt.re + 1 - la.pt.re - 1))))
              ≤ q0R b.pt.re * psR v b.pt.re / (x0R (b.pt.re + 1) * phR v e' (b.pt.re + 1)) := by
                rw [← mul_assoc]
                apply div_le_div_of_nonneg_left hA.le hB
                exact le_mul_of_one_le_right hB.le hφ1.1
            _ ≤ q0R b.pt.re * psR v b.pt.re / (x0R (b.pt.re + 1) * phR v e' (b.pt.re + 1)) *
                ((1 + 2 / L) * (1 + 1 / L)) := le_mul_of_one_le_right (by positivity) hK1
        · have hA : 0 < x0R b.pt.re * phR v e' b.pt.re := mul_pos hb1 (by linarith [hph0.1])
          have : (1 + 2 / L) ≤ (1 + 2 / L) * (1 + 1 / L) := by
            have : 0 ≤ 1 / L := by positivity
            have : 0 ≤ 2 / L := by positivity
            nlinarith
          calc x0R b.pt.re * (phR v e' b.pt.re * ((b.pt.re - la.pt.re) / (b.pt.re - la.pt.re - 1)))
              = x0R b.pt.re * phR v e' b.pt.re * ((b.pt.re - la.pt.re) / (b.pt.re - la.pt.re - 1)) := by ring
            _ ≤ x0R b.pt.re * phR v e' b.pt.re * ((1 + 2 / L) * (1 + 1 / L)) :=
                mul_le_mul_of_nonneg_left (hφ0.2.trans this) hA.le
      have hFnn : 0 ≤ (if e' b.intersection_update_fsHerm_neg_one = 0 then qwR q0R v b.pt.re / xsR x0R v e (b.pt.re + 1) else xsR x0R v e b.pt.re) := by
        simp only [xsR, qwR]
        rw [hflip0, hflip1]
        split_ifs
        · apply div_nonneg (mul_nonneg hb3.le (by linarith [hps.1]))
          exact mul_nonneg hb2.le (mul_nonneg (by linarith [hph1.1]) (by linarith [hφ1.1]))
        · exact mul_nonneg hb1.le (mul_nonneg (by linarith [hph0.1]) (by linarith [hφ0.1]))
      calc csR x0R q0R v e * (if e' b.intersection_update_fsHerm_neg_one = 0 then qwR q0R v b.pt.re / xsR x0R v e (b.pt.re + 1) else xsR x0R v e b.pt.re)
          ≤ (csR x0R q0R v e' * (q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1))) *
              ((1 + 2 / L) * (1 + 1 / L)) ^ v.length) *
            ((if e' b.intersection_update_fsHerm_neg_one = 0 then qwR q0R v b.pt.re / xsR x0R v e' (b.pt.re + 1) else xsR x0R v e' b.pt.re) *
              ((1 + 2 / L) * (1 + 1 / L))) := mul_le_mul ih hF hFnn (by
                have hla := hpos la (List.mem_cons_of_mem _ h')
                have : 0 < q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1)) :=
                  div_pos hla.2.2 (mul_pos hla.1 hla.2.1)
                positivity)
        _ = csR x0R q0R v e' * (if e' b.intersection_update_fsHerm_neg_one = 0 then qwR q0R v b.pt.re / xsR x0R v e' (b.pt.re + 1)
              else xsR x0R v e' b.pt.re) * (q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1))) *
              ((1 + 2 / L) * (1 + 1 / L)) ^ (v.length + 1) := by ring

end Real

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X4

section S_R_X5
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

section Ev
variable (P : M.Par)

def ev1 (x : (DQ P).Pr) (q : Qp P.r P.TT) : ℂ := evQ P (x.1 1) q

theorem evalOne_add (x y : (DQ P).Pr) (q) : ev1 P (x + y) q = ev1 P x q + ev1 P y q := rfl
theorem evalOne_sub (x y : (DQ P).Pr) (q) : ev1 P (x - y) q = ev1 P x q - ev1 P y q := rfl
theorem evalOne_zero (q) : ev1 P (0 : (DQ P).Pr) q = 0 := rfl
theorem evalOne_algebraMap_alt (z : ℂ) (q) : ev1 P (algebraMap ℂ (DQ P).Pr z) q = z := by
  show z * 1 = z
  ring
theorem evalOne_smul (z : ℂ) (x : (DQ P).Pr) (q) : ev1 P (z • x) q = z * ev1 P x q := by
  rw [Algebra.smul_def]
  rfl
theorem evalOne_algebraMap_mul (z : ℂ) (x : (DQ P).Pr) (q) : ev1 P (algebraMap ℂ (DQ P).Pr z * x) q = z * ev1 P x q := by
  rw [← Algebra.smul_def, evalOne_smul]
theorem evalOne_mul_algebraMap (z : ℂ) (x : (DQ P).Pr) (q) : ev1 P (x * algebraMap ℂ (DQ P).Pr z) q = z * ev1 P x q := by
  rw [← Algebra.commutes, evalOne_algebraMap_mul]
theorem evalOne_function_mul (f fb : SmQ P.r P.TT) (x : (DQ P).Pr) (q) :
    ev1 P ((DQ P).fnP f fb * x) q = evQ P f q * ev1 P x q := rfl
theorem evalOne_sum {ι : Type} (s : Finset ι) (x : ι → (DQ P).Pr) (q) :
    ev1 P (∑ i ∈ s, x i) q = ∑ i ∈ s, ev1 P (x i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, evalOne_add, ih]

end Ev

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X5

section S_R_X6
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

section Ent
variable (P : M.Par)

theorem kap_eq (f : M.Ty P → ℂ) : kap P (DQ P) f = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (f π) := rfl

theorem algA_apply (c : ℂ) (π π' : M.Ty P) :
    (algebraMap ℂ (A P (DQ P)) c) π π' = if π = π' then algebraMap ℂ (DQ P).Pr c else 0 := by
  rw [Matrix.algebraMap_eq_diagonal]
  simp [Matrix.diagonal_apply]

theorem evalOne_scalar_matrix (c : ℂ) (π π' : M.Ty P) (q) :
    ev1 P ((algebraMap ℂ (A P (DQ P)) c) π π') q = if π = π' then c else 0 := by
  rw [algA_apply]; split_ifs
  · exact evalOne_algebraMap_alt P c q
  · exact evalOne_zero P q

theorem evalOne_mul_scalar_matrix (X : A P (DQ P)) (c : ℂ) (π π' : M.Ty P) (q) :
    ev1 P ((X * algebraMap ℂ (A P (DQ P)) c) π π') q = c * ev1 P (X π π') q := by
  rw [Matrix.algebraMap_eq_diagonal, Matrix.mul_diagonal]
  exact evalOne_mul_algebraMap P c _ q

theorem evalOne_shift_piece (l' : ℕ) (π0 : M.Ty P) (π π' : M.Ty P) (q) :
    ev1 P ((zA P (DQ P) * zbiA P (DQ P) * (kap P (DQ P) (fun π => if π = π0 then 1 else 0) * SS P (DQ P) l')) π π') q =
      evQ P ((DQ P).x M.vz) q * evQ P ((DQ P).inv ((DQ P).x M.vzb)) q * (if π = π0 then 1 else 0) *
        (if M.Up P l' π' π then ((Real.sqrt (M.Nrm P l' π') : ℝ) : ℂ) else 0) := by
  have e1 : (zA P (DQ P) * zbiA P (DQ P) * (kap P (DQ P) (fun π => if π = π0 then 1 else 0) * SS P (DQ P) l')) π π' =
      (DQ P).zP * ((DQ P).zbiP * (algebraMap ℂ (DQ P).Pr (if π = π0 then 1 else 0) * SS P (DQ P) l' π π')) := by
    simp only [zA, zbiA, sc, kap_eq, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
      mul_assoc]
  rw [e1]
  show evQ P ((DQ P).x M.vz) q * (evQ P ((DQ P).inv ((DQ P).x M.vzb)) q *
    ev1 P (algebraMap ℂ (DQ P).Pr (if π = π0 then 1 else 0) * SS P (DQ P) l' π π') q) = _
  rw [evalOne_algebraMap_mul]
  simp only [SS, Matrix.of_apply]
  split_ifs <;> simp [evalOne_algebraMap_alt, evalOne_zero] <;> ring

end Ent

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X6

section S_R_X7
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

section AuxEnt
variable (P : M.Par) {S : Type} [Fintype S] [DecidableEq S]

def multS (v : List (Letter ℂ S)) (γ : ℂ) (e : Ix S) : ℂ := (v.map fun l => 1 + sg (e l.intersection_update_fsHerm_neg_one) / (l.pt - γ)).prod

def eUS (a : S) (e e' : Ix S) : ℂ := if e a = 0 ∧ e' a = 1 ∧ ∀ b, b ≠ a → e b = e' b then 1 else 0

def lsS : List (Letter ℂ S) → List (Letter ℂ S) → ℂ → Ix S → Ix S → ℂ
  | _, [], _, _, _ => 0
  | v, l :: w, Y, e, e' => (Y - l.pt)⁻¹ * (eUS l.intersection_update_fsHerm_neg_one e e' * multS v l.pt e') + lsS (v ++ [l]) w Y e e'

theorem io_mult_apply (X : A P (DQ P)) (v : List (Letter ℂ S)) (γ : ℂ) (e e' : Ix S) :
    (io X * mult v γ : SlopeTestRemainingChoices S (A P (DQ P))) e e' = if e = e' then X * algebraMap ℂ (A P (DQ P)) (multS v γ e) else 0 := by
  simp only [io, mult, multS, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]

theorem eU_mult_apply (a : S) (v : List (Letter ℂ S)) (γ : ℂ) (e e' : Ix S) :
    (eU a 0 1 * mult v γ : SlopeTestRemainingChoices S (A P (DQ P))) e e' = algebraMap ℂ (A P (DQ P)) (eUS a e e' * multS v γ e') := by
  simp only [eU, mult, multS, eUS, Matrix.mul_diagonal, Matrix.of_apply]
  split_ifs <;> simp

theorem letterSum_eq : ∀ (w v : List (Letter ℂ S)) (Y : ℂ),
    (letterSum v w Y : SlopeTestRemainingChoices S (A P (DQ P))) = Matrix.of fun e e' => algebraMap ℂ (A P (DQ P)) (lsS v w Y e e')
  | [], v, Y => by ext e e' : 2; simp [letterSum, lsS]
  | l :: w, v, Y => by
    ext e e' : 2
    rw [letterSum, Matrix.add_apply, Matrix.smul_apply, eU_mult_apply, letterSum_eq w (v ++ [l]) Y]
    simp only [Matrix.of_apply, lsS, Algebra.smul_def, map_add, map_mul]

end AuxEnt

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X7

section S_R_X8
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

theorem wordS_nodup : ∀ v : List (Bool × ℝ), ((wordS v).map Letter.intersection_update_fsHerm_neg_one).Nodup
  | [] => List.nodup_nil
  | x :: v => by
    simp only [wordS, List.map_cons, List.map_map, List.nodup_cons]
    constructor
    · intro h
      rw [List.mem_map] at h
      obtain ⟨a, _, ha⟩ := h
      exact (Fin.castSucc_lt_last a.intersection_update_fsHerm_neg_one).ne ha
    · have := (wordS_nodup v).map (Fin.castSucc_injective v.length)
      rw [List.map_map] at this
      exact this

theorem plusWord_slots_nodup (w : List ℝ) : ((wordP w).map Letter.intersection_update_fsHerm_neg_one).Nodup := by
  unfold wordP
  rw [List.map_map]
  have h : ((wordS (LE.plus w)).map Letter.intersection_update_fsHerm_neg_one).map (Fin.cast (by simp [LE.plus])) =
      (wordS (LE.plus w)).map (Letter.intersection_update_fsHerm_neg_one ∘ fun lt => (⟨lt.plus, Fin.cast (by simp [LE.plus]) lt.intersection_update_fsHerm_neg_one, lt.pt⟩ :
        Letter ℂ (Fin w.length))) := by rw [List.map_map]; rfl
  rw [← h]
  exact (wordS_nodup _).map (Fin.cast_injective _)

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X8

section S_R_X9
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

theorem xC_real (P : M.Par) (π : M.Ty P) (Y : ℝ) : M.xC P π (Y : ℂ) = ((I.xpoly P.k (M.rho P π) Y : ℝ) : ℂ) := by
  simp [M.xC, I.xpoly]

theorem ofWord_inv {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
    (L : R.LevelData A r) (st : Start A) : ∀ (v : List (Letter ℂ S)), (∀ l ∈ v, l.plus = true) →
    ∀ Y, Y ∈ st.inv → (∀ l ∈ v, Y - l.pt ≠ 0 ∧ Y - l.pt ≠ 1) → Y ∈ (ofWord L st v).inv
  | [], _, Y, hY, _ => hY
  | l :: v, hp, Y, hY, hl => by
    have ih := ofWord_inv L st v (fun m hm => hp m (List.mem_cons_of_mem _ hm)) Y hY
      (fun m hm => hl m (List.mem_cons_of_mem _ hm))
    simp only [ofWord, hp l List.mem_cons_self, if_true]
    exact ⟨ih, hl l List.mem_cons_self⟩

theorem eeA_split (P : M.Par) (Y : ℂ) :
    ∑ l ∈ Finset.Icc 1 (P.k - 1), (kap P (DQ P) fun π => (Y + (M.rho P π l : ℂ))⁻¹) * SS P (DQ P) l =
      ∑ j : Fin (P.k - 1) × M.Ty P, (Y - -((M.rho P j.2 ((j.1 : ℕ) + 1) : ℝ) : ℂ))⁻¹ •
        (kap P (DQ P) (fun π => if π = j.2 then 1 else 0) * SS P (DQ P) ((j.1 : ℕ) + 1)) := by
  rw [Fintype.sum_prod_type]
  have e1 : ∀ l' : Fin (P.k - 1), ∑ π0 : M.Ty P, (Y - -((M.rho P π0 ((l' : ℕ) + 1) : ℝ) : ℂ))⁻¹ •
      (kap P (DQ P) (fun π => if π = π0 then 1 else 0) * SS P (DQ P) ((l' : ℕ) + 1)) =
      (kap P (DQ P) fun π => (Y + (M.rho P π ((l' : ℕ) + 1) : ℂ))⁻¹) * SS P (DQ P) ((l' : ℕ) + 1) := by
    intro l'
    simp_rw [← smul_mul_assoc, ← Finset.sum_mul, ← map_smul, ← map_sum]
    congr 2
    funext π
    simp [Finset.sum_apply, Pi.smul_apply, Finset.sum_ite_eq', sub_neg_eq_add]
  simp_rw [e1]
  rw [Fin.sum_univ_eq_sum_range (fun i => (kap P (DQ P) fun π => (Y + (M.rho P π (i + 1) : ℂ))⁻¹) * SS P (DQ P) (i + 1))]
  have e2 : Finset.Icc 1 (P.k - 1) = Finset.Ico 1 (P.k - 1 + 1) := by ext i; simp
  rw [e2, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by congr 1) fun i _ => ?_
  rw [add_comm 1 i]

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X9

section S_R_X10
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd

noncomputable section

def gJ (P : M.Par) (j : Fin (P.k - 1) × M.Ty P) : ℂ := -((M.rho P j.2 ((j.1 : ℕ) + 1) : ℝ) : ℂ)

def ZJ (P : M.Par) (j : Fin (P.k - 1) × M.Ty P) : A P (DQ P) :=
  kap P (DQ P) (fun π => if π = j.2 then 1 else 0) * SS P (DQ P) ((j.1 : ℕ) + 1)

theorem ee_form (P : M.Par) (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (hOK : P.OK) (hl1 : 1 ≤ l) (hlk : l ≤ P.k)
    (hL : IsModelLevel P (DQ P) L) (w : List ℝ) (hcutW : M.CutWord P l (wordP w))
    (hpts : ∀ a ∈ wordP w, ∀ j, a.pt ≠ gJ P j) (Y : ℂ) (hinv : Y ∈ (ofWord L (startM P (DQ P) l) (wordP w)).inv)
    (hinv1 : Y + 1 ∈ (ofWord L (startM P (DQ P) l) (wordP w)).inv) (hne : ∀ j, Y ≠ gJ P j) :
    (frW P l L w).ee Y = Kw L (wordP w) +
      (∑ j, (Y - gJ P j)⁻¹ • (io (L.ζ * L.ζbi * ZJ P j) * mult (wordP w) (gJ P j))) - letterSum [] (wordP w) Y := by
  have hTT : 0 ≤ P.TT := (mul_pos hOK.T_pos hOK.T'_pos).le
  have hLaws : (DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT
  have hStar : IsStarLevel L := Formalism.FourierDecayAlt.P.level_star_holds P (DQ P) hLaws L hL
  have hStart : IsLevelStart L (startM P (DQ P) l) := Formalism.FourierDecayAlt.P.start_admissible P hOK (DQ P) hLaws l L hL
  have hAdm : admitted (startM P (DQ P) l) (wordP w) :=
    (Formalism.FourierDecayAlt.P.admissible_joint_alt P (DQ P) l _ (wordP w)).2
      (Formalism.FourierDecayAlt.P.cut_admissible Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
        Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.types_interlace Formalism.FourierDecayAlt.P.realPoints_statement
        P hOK l hl1 hlk _ (wordP w) hcutW)
  have hee : ∀ Y, (startM P (DQ P) l).ee Y = L.ζ * L.ζbi * ∑ j, (Y - gJ P j)⁻¹ • ZJ P j := by
    intro Y
    obtain ⟨_, _, _, _, _, _, hz, _, _, hzbi, _⟩ := hL
    rw [hz, hzbi]
    show eeA P (DQ P) Y = _
    unfold eeA
    rw [eeA_split]
    rfl
  exact Formalism.FourierDecayAlt.P.fr_residue_form Formalism.FourierDecayAlt.P.frame_of_admissible_word Formalism.FourierDecayAlt.P.ee_conjugation (A P (DQ P))
    (Fin w.length) P.r L (startM P (DQ P) l) (Fin (P.k - 1) × M.Ty P) (ZJ P) (gJ P) (wordP w) hStar hStart hAdm
    (plusWord_letters_plus w) hee hpts Y hinv hinv1 hne

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_X10

section S_R_Y1
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

theorem rho_chain (k : ℕ) (u u' ρ : ℕ → ℝ) (h : I.Interlaces k u u' ρ) :
    ∀ n i, 1 ≤ i → i + n ≤ k - 1 → ρ (i + n) + n ≤ ρ i := by
  intro n
  induction n with
  | zero => intro i _ _; simp
  | succ n ih =>
    intro i hi hin
    have h1 := ih i hi (by omega)
    have h2 := h (i + n) (by simp [mem_Icc]; omega)
    have h3 := h (i + n + 1) (by simp [mem_Icc]; omega)
    rw [show i + (n + 1) = i + n + 1 by ring]
    push_cast
    linarith [h2.2.2.1, h3.1]

theorem rho_le (k : ℕ) (u u' ρ : ℕ → ℝ) (h : I.Interlaces k u u' ρ) (i i' : ℕ) (hi : 1 ≤ i) (hii : i ≤ i')
    (hi' : i' ≤ k - 1) : ρ i' + ((i' - i : ℕ) : ℝ) ≤ ρ i := by
  have := rho_chain k u u' ρ h (i' - i) i hi (by omega)
  rwa [Nat.add_sub_cancel' hii] at this

theorem sides (k l : ℕ) (u u' ρ : ℕ → ℝ) (α β : ℝ) (hk : 1 ≤ k) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : I.Interlaces k u u' ρ) (hα : I.OnCut u u' l α) (hβ : I.OnCut u u' l β) :
    Side k l (fun i => -(1 / 2) - u i) (fun j => -ρ j - 1) α β ∧
      Side k l (fun i => -(1 / 2) - u' i) (fun j => -ρ j) α β := by

  have hM : α ≥ 2 - max (u l) (u' l) ∧ β ≤ -(min (u l) (u' l)) - 2 := by
    unfold I.OnCut at hα hβ
    constructor
    · rcases hα with ⟨_, h2⟩ | ⟨_, h2⟩
      · have := le_max_right (u l) (u' l); linarith
      · have := le_max_left (u l) (u' l); linarith
    · rcases hβ with ⟨h1, _⟩ | ⟨h1, _⟩
      · have := min_le_left (u l) (u' l); linarith
      · have := min_le_right (u l) (u' l); linarith

  have hleft : ∀ i, 1 ≤ i → i < l → max (u l) (u' l) + 1 ≤ u i ∧ max (u l) (u' l) + 1 ≤ u' i ∧
      max (u l) (u' l) + 1 / 2 ≤ ρ i := by
    intro i hi1 hil
    have hρ := rho_le k u u' ρ h i (l - 1) hi1 (by omega) (by omega)
    have hl1' := h (l - 1) (by simp [mem_Icc]; omega)
    have hi' := h i (by simp [mem_Icc]; omega)
    rw [show l - 1 + 1 = l by omega] at hl1'
    have hcast : (0 : ℝ) ≤ ((l - 1 - i : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨?_, ?_, ?_⟩ <;> rcases le_total (u l) (u' l) with hm | hm <;>
      simp only [max_eq_right hm, max_eq_left hm] <;> linarith [hl1'.2.2.1, hl1'.2.2.2, hi'.1, hi'.2.1]
  have hright : ∀ i, l < i → i ≤ k → u i ≤ min (u l) (u' l) - 1 ∧ u' i ≤ min (u l) (u' l) - 1 := by
    intro i hli hik
    have hρ := rho_le k u u' ρ h l (i - 1) hl1 (by omega) (by omega)
    have hl' := h l (by simp [mem_Icc]; omega)
    have hi' := h (i - 1) (by simp [mem_Icc]; omega)
    rw [show i - 1 + 1 = i by omega] at hi'
    have hcast : (0 : ℝ) ≤ ((i - 1 - l : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨?_, ?_⟩ <;> rcases le_total (u l) (u' l) with hm | hm <;>
      simp only [min_eq_left hm, min_eq_right hm] <;> linarith [hl'.1, hl'.2.1, hi'.2.2.1, hi'.2.2.2]
  have hrhoR : ∀ j, l ≤ j → j ≤ k - 1 → ρ j ≤ min (u l) (u' l) - 1 / 2 := by
    intro j hlj hjk
    have hρ := rho_le k u u' ρ h l j hl1 hlj hjk
    have hl' := h l (by simp [mem_Icc]; omega)
    have hcast : (0 : ℝ) ≤ ((j - l : ℕ) : ℝ) := Nat.cast_nonneg _
    rcases le_total (u l) (u' l) with hm | hm <;> simp only [min_eq_left hm, min_eq_right hm] <;>
      linarith [hl'.1, hl'.2.1]
  have hinc : ∀ i ∈ Icc 1 (k - 1), ∀ j ∈ Icc 1 (k - 1), i < j → ρ j < ρ i := by
    intro i hi j hj hij
    have := rho_le k u u' ρ h i j (mem_Icc.1 hi).1 hij.le (mem_Icc.1 hj).2
    have : (1 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j - i)
    linarith
  constructor
  · refine ⟨fun j hj => ?_, fun i hi j hj hij => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_, ?_, fun j h1 h2 => ?_,
      fun j h1 h2 => ?_⟩
    · have := h j hj; have h2 := h j hj
      constructor
      · show -(1 / 2) - u j ≤ -ρ j - 1; linarith [this.1]
      · show -ρ j - 1 ≤ -(1 / 2) - u (j + 1); linarith [this.2.2.1]
    · show -ρ i - 1 < -ρ j - 1; linarith [hinc i hi j hj hij]
    · have := (hleft i h1 h2).1; show -(1 / 2) - u i ≤ α; linarith [hM.1]
    · have := (hright i h1 h2).1; show β ≤ -(1 / 2) - u i; linarith [hM.2]
    · show -(1 / 2) - u l ≤ α ∨ β ≤ -(1 / 2) - u l
      rcases le_total (u l) (u' l) with hm | hm
      · right; have := min_eq_left hm; linarith [hM.2]
      · left; have := max_eq_left hm; linarith [hM.1]
    · have := (hleft j h1 h2).2.2; show -ρ j - 1 ≤ α; linarith [hM.1]
    · have := hrhoR j h1 h2; show β ≤ -ρ j - 1; linarith [hM.2]
  · refine ⟨fun j hj => ?_, fun i hi j hj hij => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_, ?_, fun j h1 h2 => ?_,
      fun j h1 h2 => ?_⟩
    · have := h j hj
      constructor
      · show -(1 / 2) - u' j ≤ -ρ j; linarith [this.2.1]
      · show -ρ j ≤ -(1 / 2) - u' (j + 1); linarith [this.2.2.2]
    · show -ρ i < -ρ j; linarith [hinc i hi j hj hij]
    · have := (hleft i h1 h2).2.1; show -(1 / 2) - u' i ≤ α; linarith [hM.1]
    · have := (hright i h1 h2).2; show β ≤ -(1 / 2) - u' i; linarith [hM.2]
    · show -(1 / 2) - u' l ≤ α ∨ β ≤ -(1 / 2) - u' l
      rcases le_total (u l) (u' l) with hm | hm
      · left; have := max_eq_right hm; linarith [hM.1]
      · right; have := min_eq_right hm; linarith [hM.2]
    · have := (hleft j h1 h2).2.2; show -ρ j ≤ α; linarith [hM.1]
    · have := hrhoR j h1 h2; show β ≤ -ρ j; linarith [hM.2]

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y1

section S_R_Y2
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

theorem Nrm_eq (P : M.Par) (π : M.Ty P) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    M.Nrm P l π = P.T * P.T' *
      resA (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P π j - 1) l *
      ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P π j)
        (-M.rho P π l - 1) := by
  unfold M.Nrm resA ratF I.qpoly
  simp only []
  rw [← mul_prod_erase (Icc 1 (P.k - 1)) (fun j => -M.rho P π l - 1 - -M.rho P π j) hl]
  have e1 : ∏ m ∈ (Icc 1 (P.k - 1)).erase l, ((-M.rho P π l - 1) - (-M.rho P π m - 1)) =
      ∏ m ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P π m - M.rho P π l) :=
    prod_congr rfl fun m _ => by ring
  have e2 : ∏ m ∈ (Icc 1 (P.k - 1)).erase l, ((-M.rho P π l - 1) - -M.rho P π m) =
      ∏ m ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P π m - M.rho P π l - 1) :=
    prod_congr rfl fun m _ => by ring
  have e3 : ∏ i ∈ Icc 1 P.k, ((-M.rho P π l - 1 + 1 / 2 + P.u i) * (-M.rho P π l - 1 + 1 / 2 + P.u' i)) =
      (∏ i ∈ Icc 1 P.k, ((-M.rho P π l - 1) - (-(1 / 2) - P.u i))) *
        ∏ i ∈ Icc 1 P.k, ((-M.rho P π l - 1) - (-(1 / 2) - P.u' i)) := by
    rw [← prod_mul_distrib]; exact prod_congr rfl fun i _ => by ring
  rw [e1, e2, e3, show (-M.rho P π l - 1) - -M.rho P π l = -1 by ring]
  ring

theorem xpoly_up (k : ℕ) (ρs ρt : ℕ → ℝ) (l : ℕ) (hl : l ∈ Icc 1 (k - 1))
    (hup : ∀ i ∈ Icc 1 (k - 1), ρt i = ρs i + if i = l then 1 else 0) (Y : ℝ) :
    I.xpoly k ρt Y * (Y + ρs l) = I.xpoly k ρs Y * (Y + ρs l + 1) := by
  unfold I.xpoly
  rw [← mul_prod_erase _ _ hl, ← mul_prod_erase _ _ hl, hup l hl, if_pos rfl]
  have : ∏ x ∈ (Icc 1 (k - 1)).erase l, (Y + ρt x) = ∏ x ∈ (Icc 1 (k - 1)).erase l, (Y + ρs x) :=
    prod_congr rfl fun x hx => by rw [hup x (mem_of_mem_erase hx), if_neg (ne_of_mem_erase hx)]; ring
  rw [this]; ring

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y2

section S_R_Y3
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

theorem core_term (P : M.Par) (lc : ℕ) (πs πt : M.Ty P) (m : ℕ) (hm : m ∈ Icc 1 (P.k - 1))
    (hup : ∀ i ∈ Icc 1 (P.k - 1), M.rho P πt i = M.rho P πs i + if i = m then 1 else 0) (Y : ℝ)
    (hT : P.T * P.T' ≠ 0) (hq : qp P Y ≠ 0) (h0 : Y + M.rho P πs m ≠ 0) (h1 : Y + M.rho P πs m + 1 ≠ 0)
    (hNf : ∏ i ∈ Icc 1 P.k, (Y - (-(1 / 2) - P.u i)) ≠ 0) (hNg : ∏ i ∈ Icc 1 P.k, (Y - (-(1 / 2) - P.u' i)) ≠ 0)
    (hDf : ∏ j ∈ Icc 1 (P.k - 1), (Y - (-M.rho P πs j - 1)) ≠ 0) (hDg : ∏ j ∈ Icc 1 (P.k - 1), (Y - -M.rho P πs j) ≠ 0)
    (hA : 0 ≤ resA (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P πs j - 1) m) :
    M.Nrm P m πs * sx P lc πt Y * sx P lc πs (Y + 1) / (qp P Y * (Y + M.rho P πs m + 1) ^ 4) ≤
      resA (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P πs j - 1) m *
        |ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P πs j) (-M.rho P πs m - 1)| /
        (|ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P πs j - 1) Y| *
          |ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P πs j) Y| *
          |Y - (-M.rho P πs m - 1)| ^ 3 * |Y - -M.rho P πs m|) := by
  set A := resA (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P πs j - 1) m
  set G := ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P πs j) (-M.rho P πs m - 1)
  set Nf := ∏ i ∈ Icc 1 P.k, (Y - (-(1 / 2) - P.u i))
  set Ng := ∏ i ∈ Icc 1 P.k, (Y - (-(1 / 2) - P.u' i))
  set Df := ∏ j ∈ Icc 1 (P.k - 1), (Y - (-M.rho P πs j - 1))
  set Dg := ∏ j ∈ Icc 1 (P.k - 1), (Y - -M.rho P πs j)
  have hf : ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P πs j - 1) Y = Nf / Df := rfl
  have hg : ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P πs j) Y = Ng / Dg := rfl
  have hxs1 : I.xpoly P.k (M.rho P πs) (Y + 1) = Df := prod_congr rfl fun j _ => by ring
  have hxs : I.xpoly P.k (M.rho P πs) Y = Dg := prod_congr rfl fun j _ => by ring
  have hqp : qp P Y = -(P.T * P.T') * (Nf * Ng) := by
    rw [qp_split]
    congr 1
    congr 1 <;> exact prod_congr rfl fun i _ => by ring
  have hup' := xpoly_up P.k (M.rho P πs) (M.rho P πt) m hm hup Y
  have hsx : sx P lc πt Y * sx P lc πs (Y + 1) = I.xpoly P.k (M.rho P πt) Y * Df := by
    unfold sx
    rw [hxs1]
    have : ((-1 : ℝ) ^ (P.k - lc)) * (-1) ^ (P.k - lc) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (I.xpoly P.k (M.rho P πt) Y * Df) * this
  have hN : M.Nrm P m πs = P.T * P.T' * A * G := Nrm_eq P πs m hm
  have key : M.Nrm P m πs * sx P lc πt Y * sx P lc πs (Y + 1) / (qp P Y * (Y + M.rho P πs m + 1) ^ 4) =
      -(A * G) / (Nf / Df * (Ng / Dg) * (Y - -M.rho P πs m) * (Y - (-M.rho P πs m - 1)) ^ 3) := by
    rw [mul_assoc (M.Nrm P m πs), hsx, hN, hqp]
    have e1 : Y - -M.rho P πs m = Y + M.rho P πs m := by ring
    have e2 : Y - (-M.rho P πs m - 1) = Y + M.rho P πs m + 1 := by ring
    rw [e1, e2]
    have hxt : I.xpoly P.k (M.rho P πt) Y = Dg * (Y + M.rho P πs m + 1) / (Y + M.rho P πs m) := by
      rw [eq_div_iff h0, ← hxs, hup']
    rw [hxt]
    have hT1 : P.T ≠ 0 := left_ne_zero_of_mul hT
    have hT2 : P.T' ≠ 0 := right_ne_zero_of_mul hT
    field_simp
  rw [key, ← hf, ← hg]
  calc -(A * G) / (ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P πs j - 1) Y *
        ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P πs j) Y *
        (Y - -M.rho P πs m) * (Y - (-M.rho P πs m - 1)) ^ 3)
      ≤ |-(A * G) / (ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P πs j - 1) Y *
        ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P πs j) Y *
        (Y - -M.rho P πs m) * (Y - (-M.rho P πs m - 1)) ^ 3)| := le_abs_self _
    _ = _ := by
        rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hA, abs_mul, abs_mul, abs_mul, abs_pow]
        ring

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y3

section S_R_Y4
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

theorem onBoxes_pairwise (S : LE.Sys) (hBF : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x) :
    ∀ w : List ℝ, S.OnBoxes w → w.Pairwise fun p p' => S.L ≤ p - p'
  | [], _ => List.Pairwise.nil
  | Y :: w, h => by
    obtain ⟨h1, h2⟩ := h
    refine List.Pairwise.cons (fun p hp => ?_) (onBoxes_pairwise S hBF w h2)
    obtain ⟨a, ha, hpa⟩ := onBoxes_mem S w h2 p hp
    exact hBF a w.length ha p hpa Y h1

theorem tl_relabel (w : List ℝ) :
    tl w = (wordP w).map fun lt => (⟨lt.plus, Fin.castSucc lt.intersection_update_fsHerm_neg_one, lt.pt⟩ : Letter ℂ (Fin (w.length + 1))) := by
  unfold tl wordP
  rw [List.map_map, List.map_map]
  rfl

theorem tl_pairwise (w : List ℝ) (L : ℝ) (h : w.Pairwise fun p p' => L ≤ p - p') :
    (tl w).Pairwise fun b c => L ≤ b.pt.re - c.pt.re := by
  have h2 : ((tl w).map Letter.pt).Pairwise fun z z' : ℂ => L ≤ z.re - z'.re := by
    rw [tl_pts, List.pairwise_map]
    exact h.imp fun hh => by simpa using hh
  rwa [List.pairwise_map] at h2

theorem tl_nodup (w : List ℝ) : ((tl w).map Letter.intersection_update_fsHerm_neg_one).Nodup := by
  rw [tl_relabel, List.map_map]
  have := (plusWord_slots_nodup w).map (Fin.castSucc_injective w.length)
  rw [List.map_map] at this
  exact this

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y4

section S_R_Y5
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

def sgR (i : Fin 2) : ℝ := if i = 0 then 1 else -1

section
variable {S : Type} [Fintype S] [DecidableEq S]

def multR (v : List (Letter ℂ S)) (ρm : ℝ) (e : Ix S) : ℝ := (v.map fun b => 1 + sgR (e b.intersection_update_fsHerm_neg_one) / (b.pt.re + ρm + 1)).prod

theorem multR_bounds (ρm Iw : ℝ) (hI : 6 ≤ Iw) : ∀ (v : List (Letter ℂ S)) (e : Ix S),
    (∀ b ∈ v, Iw / 3 ≤ |b.pt.re + ρm + 1|) → (v.length : ℝ) ≤ Iw →
    0 < multR v ρm e ∧ multR v ρm e ≤ Real.exp 3
  | [], e, _, _ => by simp [multR]
  | b :: v, e, h, hlen => by
    have hb := h b List.mem_cons_self
    have hlen' : (v.length : ℝ) ≤ Iw := by simp at hlen; linarith
    have hI0 : 0 < Iw := by linarith
    have hd : 0 < |b.pt.re + ρm + 1| := by linarith
    have hfac : |sgR (e b.intersection_update_fsHerm_neg_one) / (b.pt.re + ρm + 1)| ≤ 3 / Iw := by
      rw [abs_div]
      have : |sgR (e b.intersection_update_fsHerm_neg_one)| = 1 := by unfold sgR; split_ifs <;> simp
      rw [this, div_le_div_iff₀ hd hI0]; linarith
    have h3 : 3 / Iw ≤ 1 / 2 := by rw [div_le_div_iff₀ hI0 (by norm_num)]; linarith
    rw [abs_le] at hfac

    have key : ∀ (u : List (Letter ℂ S)), (∀ c ∈ u, Iw / 3 ≤ |c.pt.re + ρm + 1|) →
        0 < multR u ρm e ∧ multR u ρm e ≤ (1 + 3 / Iw) ^ u.length := by
      intro u
      induction u with
      | nil => intro _; simp [multR]
      | cons c u ih =>
        intro hu
        have hc := hu c List.mem_cons_self
        obtain ⟨i1, i2⟩ := ih fun d hd => hu d (List.mem_cons_of_mem _ hd)
        have hdc : 0 < |c.pt.re + ρm + 1| := by linarith
        have hfc : |sgR (e c.intersection_update_fsHerm_neg_one) / (c.pt.re + ρm + 1)| ≤ 3 / Iw := by
          rw [abs_div]
          have : |sgR (e c.intersection_update_fsHerm_neg_one)| = 1 := by unfold sgR; split_ifs <;> simp
          rw [this, div_le_div_iff₀ hdc hI0]; linarith
        rw [abs_le] at hfc
        simp only [multR, List.map_cons, List.prod_cons, List.length_cons] at i1 i2 ⊢
        constructor
        · exact mul_pos (by linarith [hfc.1]) i1
        · rw [pow_succ']
          exact mul_le_mul (by linarith [hfc.2]) i2 i1.le (by positivity)
    obtain ⟨k1, k2⟩ := key (b :: v) h
    refine ⟨k1, k2.trans ?_⟩
    exact pow_le_exp 3 _ Iw hI0 (by norm_num) hlen

theorem ss_weight (x0s x0t q0R : ℝ → ℝ) (ρm L Iw Y : ℝ) (hL2 : 2 < L) (hI : 6 ≤ Iw) (v : List (Letter ℂ S))
    (e1 e0 : Ix S) (hag : ∀ b ∈ v, e1 b.intersection_update_fsHerm_neg_one = e0 b.intersection_update_fsHerm_neg_one)
    (hpos : ∀ b ∈ v, 0 < x0s b.pt.re ∧ 0 < x0s (b.pt.re + 1) ∧ 0 < q0R b.pt.re)
    (hrel : ∀ Z, x0t Z * (Z + ρm) = x0s Z * (Z + ρm + 1))
    (hord : v.Pairwise fun b c => L ≤ b.pt.re - c.pt.re) (hfarY : ∀ b ∈ v, L ≤ Y - b.pt.re)
    (hlen : (v.length : ℝ) ≤ L) (hlenI : (v.length : ℝ) ≤ Iw) (hρfar : ∀ b ∈ v, Iw / 3 ≤ |b.pt.re + ρm + 1|)
    (hρ0 : ∀ b ∈ v, b.pt.re + ρm ≠ 0)
    (hY1 : 0 < x0s (Y + 1)) (hYt : 0 < x0t Y) (hqY : 0 < q0R Y) :
    csR x0t q0R v e1 * (x0t Y * phR v e1 Y) * multR v ρm e1 ^ 2 ≤
      csR x0s q0R v e0 * (q0R Y * psR v Y) / (x0s (Y + 1) * phR v e0 (Y + 1)) *
        (Real.exp 7 * x0t Y * x0s (Y + 1) / q0R Y) := by
  have hL : 2 ≤ L := hL2.le
  have hI0 : 0 < Iw := by linarith
  have hordsep : v.Pairwise fun b c => 2 < |b.pt.re - c.pt.re| :=
    hord.imp fun h => by rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨hm0, hm1⟩ := multR_bounds ρm Iw hI v e1 hρfar hlenI

  have htype : csR x0t q0R v e1 * multR v ρm e1 = csR x0s q0R v e1 := by
    apply csR_type x0s x0t q0R (fun b => 1 + sgR (e1 b.intersection_update_fsHerm_neg_one) / (b.pt.re + ρm + 1)) v e1 hordsep
    intro b hb
    have hd : b.pt.re + ρm + 1 ≠ 0 := fun h0 => by
      have := hρfar b hb; rw [h0, abs_zero] at this; linarith
    have hd0 := hρ0 b hb
    obtain ⟨p1, p2, p3⟩ := hpos b hb
    refine ⟨fun he => ⟨?_, p2.ne'⟩, fun he => ?_, ?_⟩
    · have hr := hrel (b.pt.re + 1)
      have hd2 : b.pt.re + 1 + ρm ≠ 0 := by rw [show b.pt.re + 1 + ρm = b.pt.re + ρm + 1 by ring]; exact hd
      simp only [he, sgR, if_true]
      field_simp
      linear_combination hr
    · have he1 : e1 b.intersection_update_fsHerm_neg_one = 1 := by
        rcases Fin.exists_fin_two.1 ⟨e1 b.intersection_update_fsHerm_neg_one, rfl⟩ with h | h
        · exact absurd h he
        · exact h
      have hr := hrel b.pt.re
      simp only [he1, sgR, show (1 : Fin 2) ≠ 0 by decide, if_false]
      field_simp
      linear_combination hr
    · have hfar := hρfar b hb
      have hsg : |sgR (e1 b.intersection_update_fsHerm_neg_one) / (b.pt.re + ρm + 1)| ≤ 1 / 2 := by
        rw [abs_div]
        have : |sgR (e1 b.intersection_update_fsHerm_neg_one)| = 1 := by unfold sgR; split_ifs <;> simp
        rw [this, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      intro h0
      rw [abs_le] at hsg
      linarith [hsg.1]
  have hcongr : csR x0s q0R v e1 = csR x0s q0R v e0 := csR_congr x0s q0R v e1 e0 hag
  have hcs : 0 < csR x0s q0R v e0 := csR_pos x0s q0R L hL v e0 hord hpos
  have hph1 := phR_bounds L hL v e1 Y hfarY
  have hph0 := phR_bounds L hL v e0 (Y + 1) fun b hb => by have := hfarY b hb; linarith
  have hps := psR_bounds L hL v Y hfarY
  have e2 : (1 + 2 / L) ^ v.length ≤ Real.exp 2 := pow_le_exp 2 _ L (by linarith) (by norm_num) hlen

  have hL' : csR x0t q0R v e1 * (x0t Y * phR v e1 Y) * multR v ρm e1 ^ 2 =
      csR x0s q0R v e0 * multR v ρm e1 * x0t Y * phR v e1 Y := by
    rw [← hcongr, ← htype]; ring
  rw [hL']
  have hR' : csR x0s q0R v e0 * (q0R Y * psR v Y) / (x0s (Y + 1) * phR v e0 (Y + 1)) *
      (Real.exp 7 * x0t Y * x0s (Y + 1) / q0R Y) =
      csR x0s q0R v e0 * x0t Y * (Real.exp 7 * psR v Y / phR v e0 (Y + 1)) := by
    field_simp
  rw [hR']
  have hp0 : 0 < phR v e0 (Y + 1) := by linarith [hph0.1]
  have key : multR v ρm e1 * phR v e1 Y ≤ Real.exp 7 * psR v Y / phR v e0 (Y + 1) := by
    rw [le_div_iff₀ hp0]
    have he7 : Real.exp 7 = Real.exp 3 * Real.exp 2 * Real.exp 2 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    calc multR v ρm e1 * phR v e1 Y * phR v e0 (Y + 1) ≤ Real.exp 3 * Real.exp 2 * Real.exp 2 := by
          apply mul_le_mul (mul_le_mul hm1 (hph1.2.trans e2) (by linarith [hph1.1]) (by positivity))
            (hph0.2.trans e2) hp0.le (by positivity)
      _ ≤ Real.exp 7 * psR v Y := by rw [he7]; exact le_mul_of_one_le_right (by positivity) hps.1
  calc csR x0s q0R v e0 * multR v ρm e1 * x0t Y * phR v e1 Y
      = csR x0s q0R v e0 * x0t Y * (multR v ρm e1 * phR v e1 Y) := by ring
    _ ≤ csR x0s q0R v e0 * x0t Y * (Real.exp 7 * psR v Y / phR v e0 (Y + 1)) :=
        mul_le_mul_of_nonneg_left key (by positivity)

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y5

section S_R_Y6
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

section
variable {S : Type} [Fintype S] [DecidableEq S]

theorem let_weight (x0R q0R : ℝ → ℝ) (L Y H : ℝ) (hL2 : 2 < L) (v : List (Letter ℂ S)) (la : Letter ℂ S)
    (e e' : Ix S) (he : ∀ x, x ≠ la.intersection_update_fsHerm_neg_one → e x = e' x) (hea : e la.intersection_update_fsHerm_neg_one = 0) (he'a : e' la.intersection_update_fsHerm_neg_one ≠ 0)
    (hnd : (v.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hla : la ∈ v)
    (hpos : ∀ b ∈ v, 0 < x0R b.pt.re ∧ 0 < x0R (b.pt.re + 1) ∧ 0 < q0R b.pt.re)
    (hord : v.Pairwise fun b c => L ≤ b.pt.re - c.pt.re) (hfarY : ∀ b ∈ v, L ≤ Y - b.pt.re)
    (hlen : (v.length : ℝ) ≤ L) (hY0 : 0 < x0R Y) (hY1 : 0 < x0R (Y + 1)) (hqY : 0 < q0R Y)
    (hH : q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1)) ≤ H * (q0R Y / (x0R Y * x0R (Y + 1)))) (hH0 : 0 ≤ H) :
    csR x0R q0R v e * (x0R Y * phR v e Y) ≤
      csR x0R q0R v e' * (q0R Y * psR v Y) / (x0R (Y + 1) * phR v e' (Y + 1)) * (Real.exp 8 * H) := by
  have hL : 2 ≤ L := hL2.le
  have hLpos : 0 < L := by linarith
  have hflip := csR_flip x0R q0R L hL la e e' he hea he'a v hnd hla hord hpos
  have hphf := phR_flip la e e' he hea he'a Y v hnd hla
  have hph1 := phR_bounds L hL v e' Y hfarY
  have hph2 := phR_bounds L hL v e' (Y + 1) fun b hb => by have := hfarY b hb; linarith
  have hps := psR_bounds L hL v Y hfarY
  have e2 : (1 + 2 / L) ^ v.length ≤ Real.exp 2 := pow_le_exp 2 _ L hLpos (by norm_num) hlen
  have e1 : (1 + 1 / L) ^ v.length ≤ Real.exp 1 := pow_le_exp 1 _ L hLpos (by norm_num) hlen
  have hK : ((1 + 2 / L) * (1 + 1 / L)) ^ v.length ≤ Real.exp 3 := by
    rw [mul_pow, show Real.exp 3 = Real.exp 2 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    exact mul_le_mul e2 e1 (by positivity) (by positivity)
  have hφ := phi_bounds L (Y - la.pt.re) hL (hfarY la hla)
  have hcs : 0 < csR x0R q0R v e' := csR_pos x0R q0R L hL v e' hord hpos
  have hHa : 0 < q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1)) := by
    obtain ⟨a1, a2, a3⟩ := hpos la hla; exact div_pos a3 (mul_pos a1 a2)
  have hp2 : 0 < phR v e' (Y + 1) := by linarith [hph2.1]
  have hp1 : 0 < phR v e' Y := by linarith [hph1.1]
  rw [hphf]

  have step1 : csR x0R q0R v e * (x0R Y * (phR v e' Y * ((Y - la.pt.re) / (Y - la.pt.re - 1)))) ≤
      csR x0R q0R v e' * (q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1))) * Real.exp 3 *
        (x0R Y * (phR v e' Y * (1 + 2 / L))) := by
    apply mul_le_mul _ _ (mul_nonneg hY0.le (mul_nonneg hp1.le (by linarith [hφ.1])))
      (mul_nonneg (mul_nonneg hcs.le hHa.le) (Real.exp_pos 3).le)
    · calc csR x0R q0R v e ≤ csR x0R q0R v e' * (q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1))) *
            ((1 + 2 / L) * (1 + 1 / L)) ^ v.length := hflip
        _ ≤ _ := mul_le_mul_of_nonneg_left hK (by positivity)
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφ.2 hp1.le) hY0.le
  refine step1.trans ?_
  have hq : q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1)) * (x0R Y * x0R (Y + 1)) ≤ H * q0R Y := by
    have := mul_le_mul_of_nonneg_right hH (by positivity : (0 : ℝ) ≤ x0R Y * x0R (Y + 1))
    rwa [show H * (q0R Y / (x0R Y * x0R (Y + 1))) * (x0R Y * x0R (Y + 1)) = H * q0R Y by field_simp] at this
  have h2L : 1 + 2 / L ≤ Real.exp 1 := by
    have : 2 / L ≤ 1 := by rw [div_le_one hLpos]; exact hL
    have := Real.add_one_le_exp 1; linarith

  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have he8 : Real.exp 8 = Real.exp 3 * Real.exp 1 * Real.exp 2 * Real.exp 2 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
  have hpe : phR v e' Y * phR v e' (Y + 1) ≤ Real.exp 2 * Real.exp 2 :=
    mul_le_mul (hph1.2.trans e2) (hph2.2.trans e2) hp2.le (by positivity)
  calc csR x0R q0R v e' * (q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1))) * Real.exp 3 *
        (x0R Y * (phR v e' Y * (1 + 2 / L))) * (x0R (Y + 1) * phR v e' (Y + 1))
      = csR x0R q0R v e' * Real.exp 3 * (1 + 2 / L) * (phR v e' Y * phR v e' (Y + 1)) *
          ((q0R la.pt.re / (x0R la.pt.re * x0R (la.pt.re + 1))) * (x0R Y * x0R (Y + 1))) := by ring
    _ ≤ csR x0R q0R v e' * Real.exp 3 * Real.exp 1 * (Real.exp 2 * Real.exp 2) * (H * q0R Y) := by
        gcongr
    _ ≤ csR x0R q0R v e' * (q0R Y * psR v Y) * (Real.exp 8 * H) := by
        rw [he8]
        have : q0R Y ≤ q0R Y * psR v Y := le_mul_of_one_le_right hqY.le hps.1
        have h0 : 0 ≤ csR x0R q0R v e' * (Real.exp 3 * Real.exp 1 * Real.exp 2 * Real.exp 2 * H) := by positivity
        nlinarith

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y6

section S_R_Y7
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Finset

theorem sparse_bound {ι α : Type} [Fintype ι] [DecidableEq ι] (T : Finset α) (Pr : α → ι → ι → Prop)
    [∀ m i i', Decidable (Pr m i i')]
    (hu1 : ∀ m i i₁ i₂, Pr m i i₁ → Pr m i i₂ → i₁ = i₂) (hu2 : ∀ m i₁ i₂ i', Pr m i₁ i' → Pr m i₂ i' → i₁ = i₂)
    (κ : α → ι → ι → ℂ) (t σ : ι → ℝ) (β : α → ι → ℝ) (ht : ∀ i, 0 ≤ t i) (hσ : ∀ i, 0 ≤ σ i)
    (hβ : ∀ m ∈ T, ∀ i i', Pr m i i' → t i * ‖κ m i i'‖ ^ 2 ≤ σ i' * β m i') (hβ0 : ∀ m i', 0 ≤ β m i')
    (C : ℝ) (hC : ∀ i', (T.card : ℝ) * ∑ m ∈ T, β m i' ≤ C) (v : ι → ℂ) :
    ∑ i, t i * ‖∑ m ∈ T, ∑ i', (if Pr m i i' then κ m i i' else 0) * v i'‖ ^ 2 ≤ C * ∑ i', σ i' * ‖v i'‖ ^ 2 := by

  have hone : ∀ m i, ‖∑ i', (if Pr m i i' then κ m i i' else 0) * v i'‖ ^ 2 =
      ∑ i', (if Pr m i i' then ‖κ m i i'‖ ^ 2 * ‖v i'‖ ^ 2 else 0) := by
    intro m i
    by_cases h : ∃ i', Pr m i i'
    · obtain ⟨i0, h0⟩ := h
      rw [sum_eq_single i0, sum_eq_single i0]
      · rw [if_pos h0, if_pos h0, norm_mul, mul_pow]
      · intro b _ hb; rw [if_neg (fun hb' => hb (hu1 m i b i0 hb' h0))]
      · simp
      · intro b _ hb; rw [if_neg (fun hb' => hb (hu1 m i b i0 hb' h0))]; simp
      · simp
    · push Not at h
      rw [sum_eq_zero fun i' _ => by rw [if_neg (h i')]; simp, sum_eq_zero fun i' _ => by rw [if_neg (h i')]]
      simp
  have hcs : ∀ i, ‖∑ m ∈ T, ∑ i', (if Pr m i i' then κ m i i' else 0) * v i'‖ ^ 2 ≤
      (T.card : ℝ) * ∑ m ∈ T, ∑ i', (if Pr m i i' then ‖κ m i i'‖ ^ 2 * ‖v i'‖ ^ 2 else 0) := by
    intro i
    calc ‖∑ m ∈ T, ∑ i', (if Pr m i i' then κ m i i' else 0) * v i'‖ ^ 2
        ≤ (∑ m ∈ T, ‖∑ i', (if Pr m i i' then κ m i i' else 0) * v i'‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (T.card : ℝ) * ∑ m ∈ T, ‖∑ i', (if Pr m i i' then κ m i i' else 0) * v i'‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = _ := by simp_rw [hone]
  calc ∑ i, t i * ‖∑ m ∈ T, ∑ i', (if Pr m i i' then κ m i i' else 0) * v i'‖ ^ 2
      ≤ ∑ i, t i * ((T.card : ℝ) * ∑ m ∈ T, ∑ i', (if Pr m i i' then ‖κ m i i'‖ ^ 2 * ‖v i'‖ ^ 2 else 0)) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcs i) (ht i)
    _ = (T.card : ℝ) * ∑ m ∈ T, ∑ i', ‖v i'‖ ^ 2 * ∑ i, (if Pr m i i' then t i * ‖κ m i i'‖ ^ 2 else 0) := by
        rw [mul_sum]
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun m _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun i' _ => ?_
        refine sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
    _ ≤ (T.card : ℝ) * ∑ m ∈ T, ∑ i', ‖v i'‖ ^ 2 * (σ i' * β m i') := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        refine sum_le_sum fun m hm => sum_le_sum fun i' _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        by_cases h : ∃ i, Pr m i i'
        · obtain ⟨i0, h0⟩ := h
          rw [sum_eq_single i0, if_pos h0]
          · exact hβ m hm i0 i' h0
          · intro b _ hb; rw [if_neg (fun hb' => hb (hu2 m b i0 i' hb' h0))]
          · simp
        · push Not at h
          rw [sum_eq_zero fun i _ => by rw [if_neg (h i)]]
          exact mul_nonneg (hσ i') (hβ0 m i')
    _ = ∑ i', σ i' * ‖v i'‖ ^ 2 * ((T.card : ℝ) * ∑ m ∈ T, β m i') := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun i' _ => ?_
        rw [mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun m _ => by ring
    _ ≤ ∑ i', σ i' * ‖v i'‖ ^ 2 * C := sum_le_sum fun i' _ =>
        mul_le_mul_of_nonneg_left (hC i') (mul_nonneg (hσ i') (sq_nonneg _))
    _ = C * ∑ i', σ i' * ‖v i'‖ ^ 2 := by rw [mul_sum]; exact sum_congr rfl fun i' _ => by ring

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y7

section S_R_Y8
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

def phase (P : M.Par) (q : Qp P.r P.TT) : ℂ := evQ P ((DQ P).x M.vz) q * evQ P ((DQ P).inv ((DQ P).x M.vzb)) q

def dSS (P : M.Par) (w : List ℝ) (Y₁ Y₂ : ℝ) (q : Qp P.r P.TT) (e e' : Ix (Fin w.length)) (π π' : M.Ty P) : ℂ :=
  if e = e' then ∑ j : Fin (P.k - 1) × M.Ty P, (((Y₁ : ℂ) - gJ P j)⁻¹ - ((Y₂ : ℂ) - gJ P j)⁻¹) *
      multS (wordP w) (gJ P j) e * (phase P q * (if π = j.2 then 1 else 0) *
        (if M.Up P ((j.1 : ℕ) + 1) π' π then ((Real.sqrt (M.Nrm P ((j.1 : ℕ) + 1) π') : ℝ) : ℂ) else 0)) else 0

def dL (P : M.Par) (w : List ℝ) (Y₁ Y₂ : ℝ) (e e' : Ix (Fin w.length)) (π π' : M.Ty P) : ℂ :=
  if π = π' then lsS [] (wordP w) (Y₁ : ℂ) e e' - lsS [] (wordP w) (Y₂ : ℂ) e e' else 0

def eeF (P : M.Par) (w : List ℝ) (L : R.LevelData (A P (DQ P)) P.r) (Y : ℂ) : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P)) :=
  Kw L (wordP w) + (∑ j, (Y - gJ P j)⁻¹ • (io (L.ζ * L.ζbi * ZJ P j) * mult (wordP w) (gJ P j))) -
    letterSum [] (wordP w) Y

theorem evalOne_frame_difference (P : M.Par) (w : List ℝ) (L : R.LevelData (A P (DQ P)) P.r) (hL : IsModelLevel P (DQ P) L)
    (Y₁ Y₂ : ℝ) (q : Qp P.r P.TT) (e e' : Ix (Fin w.length)) (π π' : M.Ty P) :
    ev1 P ((eeF P w L (Y₁ : ℂ) - eeF P w L (Y₂ : ℂ)) e e' π π') q =
      dSS P w Y₁ Y₂ q e e' π π' - dL P w Y₁ Y₂ e e' π π' := by
  obtain ⟨_, _, _, _, _, _, hz, _, _, hzbi, _⟩ := hL
  have hsplit : ∀ (X₁ X₂ K Z₁ Z₂ : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))), (K + X₁ - Z₁) - (K + X₂ - Z₂) = (X₁ - X₂) - (Z₁ - Z₂) :=
    fun _ _ _ _ _ => by abel
  unfold eeF
  rw [hsplit, ← sum_sub_distrib, letterSum_eq, letterSum_eq]
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.of_apply, ← sub_smul]
  rw [evalOne_sub, evalOne_sum]
  unfold dSS dL
  congr 1
  · by_cases he : e = e'
    · rw [if_pos he]
      refine sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Matrix.smul_apply, evalOne_smul, io_mult_apply, if_pos he, evalOne_mul_scalar_matrix, hz, hzbi,
        ZJ, evalOne_shift_piece]
      unfold phase
      ring
    · rw [if_neg he]
      refine sum_eq_zero fun j _ => ?_
      rw [Matrix.smul_apply, Matrix.smul_apply, evalOne_smul, io_mult_apply, if_neg he]
      simp [evalOne_zero]
  · rw [evalOne_sub, evalOne_scalar_matrix, evalOne_scalar_matrix]
    split_ifs <;> simp

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y8

section S_R_Y9
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

theorem lsS_sum {S : Type} [Fintype S] [DecidableEq S] : ∀ (w v : List (Letter ℂ S)) (Y : ℂ) (e e' : Ix S),
    lsS v w Y e e' = ∑ n : Fin w.length, (Y - (w.get n).pt)⁻¹ *
      (eUS (w.get n).intersection_update_fsHerm_neg_one e e' * multS (v ++ w.take n) (w.get n).pt e')
  | [], v, Y, e, e' => by simp [lsS]
  | l :: w, v, Y, e, e' => by
    rw [lsS, lsS_sum w (v ++ [l]) Y e e']
    show _ = ∑ n : Fin (w.length + 1), (Y - ((l :: w).get n).pt)⁻¹ *
      (eUS ((l :: w).get n).intersection_update_fsHerm_neg_one e e' * multS (v ++ (l :: w).take n) ((l :: w).get n).pt e')
    rw [Fin.sum_univ_succ]
    congr 1
    · simp
    · refine sum_congr rfl fun n _ => ?_
      simp [List.append_assoc]

theorem ixOf_inj (P : M.Par) : ∀ (N : ℕ) (i i' : Iota P N), ixOf P N i = ixOf P N i' → i = i'
  | 0, i, i', h => by
    have := congrArg Prod.snd h
    simp only [ixOf] at this
    exact this
  | N + 1, (b, i), (b', i'), h => by
    simp only [ixOf, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hl := congrFun h1 (Fin.last N)
    simp only [Fin.snoc_last] at hl
    have hb : b = b' := by cases b <;> cases b' <;> simp_all
    have hi : (ixOf P N i).1 = (ixOf P N i').1 := by
      funext x
      have := congrFun h1 x.castSucc
      simpa using this
    have := ixOf_inj P N i i' (Prod.ext hi h2)
    rw [hb, this]

theorem plusWord_get_point (w : List ℝ) (n : Fin (wordP w).length) : ∃ p ∈ w, ((wordP w).get n).pt = (p : ℂ) :=
  MAx2.mem_wordP (List.get_mem _ _)

theorem mult_real {S : Type} [Fintype S] [DecidableEq S] (ρm : ℝ) (e : Ix S) : ∀ (v : List (Letter ℂ S)),
    (∀ a ∈ v, a.pt.im = 0) → multS v (-((ρm + 1 : ℝ) : ℂ)) e = ((multR v ρm e : ℝ) : ℂ)
  | [], _ => by simp [multS, multR]
  | a :: v, hv => by
    have ih := mult_real ρm e v fun b hb => hv b (List.mem_cons_of_mem _ hb)
    unfold multS multR at ih ⊢
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]
    have hp := pt_eq (hv a List.mem_cons_self)
    set p := a.pt.re
    rw [hp]
    have : sg (e a.intersection_update_fsHerm_neg_one) = ((sgR (e a.intersection_update_fsHerm_neg_one) : ℝ) : ℂ) := by unfold sg sgR; split_ifs <;> simp
    rw [this]
    push_cast
    ring

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y9

section S_R_Y10
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

theorem up_relation_source_unique (P : M.Par) (m : ℕ) (π₁ π₂ π : M.Ty P) (h1 : M.Up P m π₁ π) (h2 : M.Up P m π₂ π) : π₁ = π₂ := by
  funext i; apply Fin.ext; have := h1 i; have := h2 i; omega

theorem up_tgt (P : M.Par) (m : ℕ) (π π₁ π₂ : M.Ty P) (h1 : M.Up P m π π₁) (h2 : M.Up P m π π₂) : π₁ = π₂ := by
  funext i; apply Fin.ext; have := h1 i; have := h2 i; omega

theorem dSS_sparse (P : M.Par) (w : List ℝ) (Y₁ Y₂ : ℝ) (q : Qp P.r P.TT) (e e' : Ix (Fin w.length))
    (π π' : M.Ty P) :
    dSS P w Y₁ Y₂ q e e' π π' = ∑ m : Fin (P.k - 1),
      if e = e' ∧ M.Up P ((m : ℕ) + 1) π' π then
        (((Y₁ : ℂ) - gJ P (m, π))⁻¹ - ((Y₂ : ℂ) - gJ P (m, π))⁻¹) * multS (wordP w) (gJ P (m, π)) e *
          (phase P q * ((Real.sqrt (M.Nrm P ((m : ℕ) + 1) π') : ℝ) : ℂ))
      else 0 := by
  unfold dSS
  by_cases he : e = e'
  · rw [if_pos he, Fintype.sum_prod_type]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_eq_single π]
    · by_cases hu : M.Up P ((m : ℕ) + 1) π' π
      · have h1 : (e = e' ∧ M.Up P ((m : ℕ) + 1) π' π) := ⟨he, hu⟩
        rw [if_pos h1]
        simp only [hu, if_true, mul_one]
      · have h1 : ¬ (e = e' ∧ M.Up P ((m : ℕ) + 1) π' π) := fun h => hu h.2
        rw [if_neg h1]
        simp only [hu, if_false, mul_zero]
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; simp
    · simp
  · rw [if_neg he]
    exact (sum_eq_zero fun m _ => if_neg fun h => he h.1).symm

theorem dL_sparse (P : M.Par) (w : List ℝ) (Y₁ Y₂ : ℝ) (e e' : Ix (Fin w.length)) (π π' : M.Ty P) :
    dL P w Y₁ Y₂ e e' π π' = ∑ n : Fin (wordP w).length,
      if π = π' ∧ (e ((wordP w).get n).intersection_update_fsHerm_neg_one = 0 ∧ e' ((wordP w).get n).intersection_update_fsHerm_neg_one = 1 ∧
          ∀ b, b ≠ ((wordP w).get n).intersection_update_fsHerm_neg_one → e b = e' b) then
        (((Y₁ : ℂ) - ((wordP w).get n).pt)⁻¹ - ((Y₂ : ℂ) - ((wordP w).get n).pt)⁻¹) *
          multS ((wordP w).take n) ((wordP w).get n).pt e'
      else 0 := by
  unfold dL
  rw [lsS_sum, lsS_sum, ← sum_sub_distrib]
  by_cases hp : π = π'
  · rw [if_pos hp]
    refine sum_congr rfl fun n _ => ?_
    unfold eUS
    by_cases hc : e ((wordP w).get n).intersection_update_fsHerm_neg_one = 0 ∧ e' ((wordP w).get n).intersection_update_fsHerm_neg_one = 1 ∧
        ∀ b, b ≠ ((wordP w).get n).intersection_update_fsHerm_neg_one → e b = e' b
    · rw [if_pos hc, if_pos ⟨hp, hc⟩]; simp; ring
    · rw [if_neg hc, if_neg fun h => hc h.2]; simp
  · rw [if_neg hp]
    exact (sum_eq_zero fun n _ => if_neg fun h => hp h.1).symm

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y10

section S_R_Y11
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

structure Ctx (P : M.Par) (l : ℕ) (α β Lb : ℝ) (Ntot : ℕ) (w : List ℝ) (Y s : ℝ) : Prop where
  hOK : P.OK
  hl1 : 1 ≤ l
  hlk : l ≤ P.k
  hcut : ∀ Z ∈ Set.Icc α β, I.OnCut P.u P.u' l Z
  hαβ : α < β
  hL2 : 2 < Lb
  hNL : (Ntot : ℝ) ≤ Lb
  hNpos : 1 ≤ Ntot
  hn : ((P.k + 2 * P.r + 1 : ℕ) : ℝ) * Lb ≤ β - α
  h6 : 6 * (Ntot : ℝ) * Lb ≤ β - α
  hlen : w.length < Ntot
  hYm : α + (β - α) / 3 ≤ Y ∧ Y ≤ β - (β - α) / 3
  hYsm : α + (β - α) / 3 ≤ Y + s ∧ Y + s ≤ β - (β - α) / 3
  hsL : |s| ≤ Lb
  hwm : ∀ p ∈ w, α + (β - α) / 3 ≤ p ∧ p ≤ β - (β - α) / 3
  hfar : ∀ p ∈ w, Lb ≤ Y - p ∧ Lb ≤ Y + s - p
  hord : w.Pairwise fun p p' => Lb ≤ p - p'

theorem ctx_of (P : M.Par) (l : ℕ) (L : R.LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ)
    (hH : Hyps P l L j lam α β Lb Ntot) (w : List ℝ) (hw : (sysQ P l L j lam α β Lb c Ntot).OnBoxes w)
    (hl : w.length < Ntot) (Y s : ℝ) (hY : Y ∈ ((sysQ P l L j lam α β Lb c Ntot).step w).J)
    (hYs : Y + s ∈ ((sysQ P l L j lam α β Lb c Ntot).step w).J) : Ctx P l α β Lb Ntot w Y s := by
  obtain ⟨⟨hOK, hl1, hlk, _, hu, hu', hαβ, hcut⟩, _, _, _, hrN, hNL, hL2, hn, h6⟩ := hH
  have hBF := Formalism.FourierDecayAlt.P.boxes_fit (sysQ P l L j lam α β Lb c Ntot) hL2 h6
  have hYb : Y ∈ (sysQ P l L j lam α β Lb c Ntot).box w.length := hY
  have hYsb : Y + s ∈ (sysQ P l L j lam α β Lb c Ntot).box w.length := hYs
  have hY' : α + (β - α) / 3 + 2 * (w.length : ℝ) * Lb ≤ Y ∧ Y ≤ α + (β - α) / 3 + 2 * (w.length : ℝ) * Lb + Lb := hY
  have hYs' : α + (β - α) / 3 + 2 * (w.length : ℝ) * Lb ≤ Y + s ∧
      Y + s ≤ α + (β - α) / 3 + 2 * (w.length : ℝ) * Lb + Lb := hYs
  refine ⟨hOK, hl1, hlk, hcut, hαβ, hL2, hNL, by omega, hn, h6, hl, hBF.1 w.length hl hYb, hBF.1 w.length hl hYsb,
    by rw [abs_le]; constructor <;> linarith [hY'.1, hY'.2, hYs'.1, hYs'.2], fun p hp => ?_, fun p hp => ?_,
    onBoxes_pairwise _ hBF.2.1 w hw⟩
  · obtain ⟨a, ha, hpa⟩ := onBoxes_mem _ w hw p hp
    exact hBF.1 a (by show a < Ntot; omega) hpa
  · obtain ⟨a, ha, hpa⟩ := onBoxes_mem _ w hw p hp
    exact ⟨hBF.2.1 a w.length ha p hpa Y hYb, hBF.2.1 a w.length ha p hpa (Y + s) hYsb⟩

section
variable {P : M.Par} {l : ℕ} {α β Lb : ℝ} {Ntot : ℕ} {w : List ℝ} {Y s : ℝ}

theorem Ctx.twelve_le_window (h : Ctx P l α β Lb Ntot w Y s) : 12 ≤ β - α := by
  have h1 : (1 : ℝ) ≤ Ntot := by exact_mod_cast h.hNpos
  nlinarith [h.h6, h.hL2]

theorem Ctx.sx_pos (h : Ctx P l α β Lb Ntot w Y s) (π : M.Ty P) (Z : ℝ) (hZ : Z ∈ Set.Icc α β) :
    0 < sx P l π Z ∧ 0 < sx P l π (Z + 1) := by
  have hπ := Formalism.FourierDecayAlt.P.types_interlace P h.hOK π
  have h0 := Formalism.FourierDecayAlt.P.interlacing_sign P.k P.u P.u' (M.rho P π) l Z h.hl1 h.hlk hπ (h.hcut Z hZ) 0 (by simp)
  have h1 := Formalism.FourierDecayAlt.P.interlacing_sign P.k P.u P.u' (M.rho P π) l Z h.hl1 h.hlk hπ (h.hcut Z hZ) 1 (by simp)
  rw [add_zero] at h0
  exact ⟨h0, h1⟩

theorem Ctx.qp_pos (h : Ctx P l α β Lb Ntot w Y s) (Z : ℝ) (hZ : Z ∈ Set.Icc α β) : 0 < qp P Z := by
  have hπ := Formalism.FourierDecayAlt.P.types_interlace P h.hOK (fun _ => 0)
  exact Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' _ l Z P.T P.T' h.hl1 h.hlk hπ (h.hcut Z hZ) h.hOK.T_pos h.hOK.T'_pos

theorem Ctx.mid_I (h : Ctx P l α β Lb Ntot w Y s) (Z : ℝ) (hZ : α + (β - α) / 3 ≤ Z ∧ Z ≤ β - (β - α) / 3) :
    Z ∈ Set.Icc α β := ⟨by linarith [hZ.1, h.hαβ], by linarith [hZ.2, h.hαβ]⟩

theorem Ctx.xpoly_ne (h : Ctx P l α β Lb Ntot w Y s) (π : M.Ty P) (Z : ℝ) (hZ : Z ∈ Set.Icc α β) :
    I.xpoly P.k (M.rho P π) Z ≠ 0 ∧ I.xpoly P.k (M.rho P π) (Z + 1) ≠ 0 := by
  obtain ⟨h0, h1⟩ := h.sx_pos π Z hZ
  unfold sx at h0 h1
  exact ⟨fun e => by rw [e, mul_zero] at h0; exact lt_irrefl _ h0, fun e => by rw [e, mul_zero] at h1; exact lt_irrefl _ h1⟩

theorem Ctx.ee_at (h : Ctx P l α β Lb Ntot w Y s) (L : R.LevelData (A P (DQ P)) P.r) (hL : IsModelLevel P (DQ P) L)
    (Z : ℝ) (hZm : α + (β - α) / 3 ≤ Z ∧ Z ≤ β - (β - α) / 3) (hZfar : ∀ p ∈ w, Lb ≤ Z - p) :
    (frW P l L w).ee (Z : ℂ) = eeF P w L (Z : ℂ) := by
  have hwI : ∀ p ∈ w, p ∈ Set.Icc α β := fun p hp => h.mid_I p (h.hwm p hp)
  have hcutW : M.CutWord P l (wordP w) := by
    refine ⟨plusWord_slots_nodup w, fun a ha => ?_, MAx2.pairwise_wordP ?_⟩
    · obtain ⟨p, hp, e⟩ := MAx2.mem_wordP ha
      rw [e]
      exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact h.hcut p (hwI p hp)⟩
    · exact h.hord.imp fun hh => by rw [abs_of_pos (by linarith [h.hL2])]; linarith [h.hL2]
  have hpts : ∀ a ∈ wordP w, ∀ jj, a.pt ≠ gJ P jj := by
    intro a ha jj e
    obtain ⟨p, hp, ep⟩ := MAx2.mem_wordP ha
    rw [ep, gJ] at e
    have e' : p = -M.rho P jj.2 ((jj.1 : ℕ) + 1) := by exact_mod_cast e
    have hne := (h.xpoly_ne jj.2 p (hwI p hp)).1
    apply hne
    apply Finset.prod_eq_zero (i := (jj.1 : ℕ) + 1) (by have := jj.1.isLt; simp only [mem_Icc]; omega)
    rw [e']; ring
  have hZI := h.mid_I Z hZm
  have hinv : ∀ Z' : ℝ, Z' ∈ Set.Icc α β ∨ Z' - 1 ∈ Set.Icc α β → (∀ p ∈ w, Lb ≤ Z' - p ∨ Lb + 1 ≤ Z' - p) →
      (Z' : ℂ) ∈ (ofWord L (startM P (DQ P) l) (wordP w)).inv := by
    intro Z' hZ' hfar'
    apply ofWord_inv L _ (wordP w) (plusWord_letters_plus w)
    · intro π
      rw [xC_real]
      rcases hZ' with hZ' | hZ'
      · exact_mod_cast (h.xpoly_ne π Z' hZ').1
      · have := (h.xpoly_ne π (Z' - 1) hZ').2
        rw [sub_add_cancel] at this
        exact_mod_cast this
    · intro a ha
      obtain ⟨p, hp, ep⟩ := MAx2.mem_wordP ha
      rw [ep]
      have hd : 2 < Z' - p := by rcases hfar' p hp with hh | hh <;> linarith [h.hL2]
      constructor
      · intro e; have : Z' - p = 0 := by exact_mod_cast e
        linarith
      · intro e; have : Z' - p = 1 := by exact_mod_cast e
        linarith
  have hne : ∀ jj, (Z : ℂ) ≠ gJ P jj := by
    intro jj e
    rw [gJ] at e
    have e' : Z = -M.rho P jj.2 ((jj.1 : ℕ) + 1) := by exact_mod_cast e
    have hne := (h.xpoly_ne jj.2 Z hZI).1
    apply hne
    apply Finset.prod_eq_zero (i := (jj.1 : ℕ) + 1) (by have := jj.1.isLt; simp only [mem_Icc]; omega)
    rw [e']; ring
  have h1 : (Z : ℂ) + 1 = ((Z + 1 : ℝ) : ℂ) := by push_cast; ring
  have hi0 := hinv Z (Or.inl hZI) fun p hp => Or.inl (hZfar p hp)
  have hZ1 : Z + 1 - 1 ∈ Set.Icc α β := by rw [add_sub_cancel_right]; exact hZI
  have hi1 := hinv (Z + 1) (Or.inr hZ1) fun p hp => Or.inr (by linarith [hZfar p hp])
  rw [← h1] at hi1
  exact ee_form P l L h.hOK h.hl1 h.hlk hL w hcutW hpts (Z : ℂ) hi0 hi1 hne

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y11

section S_R_Y12
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

theorem dw_true_real (P : M.Par) (l : ℕ) (w : List ℝ) (Y : ℝ) (q : Qp P.r P.TT) (i : Iota P w.length) :
    dwW P l (Y :: w) q (true, i) = Wq P q ^ (w.length + 1) *
      (csR (sx P l (ixOf P w.length i).2) (qp P) (tl w) (ixOf P (w.length + 1) (true, i)).1 *
        xsR (sx P l (ixOf P w.length i).2) (tl w) (ixOf P (w.length + 1) (true, i)).1 Y) := by
  rw [dw_true, cs_real _ _ _ _ (coordinate_real P l _) (qC_real P) _ (tl_real w), xs_real _ _ (tl_real w), coordinate_real]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

theorem dw_false_real (P : M.Par) (l : ℕ) (w : List ℝ) (Y : ℝ) (q : Qp P.r P.TT) (i : Iota P w.length) :
    dwW P l (Y :: w) q (false, i) = Wq P q ^ (w.length + 1) *
      (csR (sx P l (ixOf P w.length i).2) (qp P) (tl w) (ixOf P (w.length + 1) (false, i)).1 *
        (qwR (qp P) (tl w) Y / xsR (sx P l (ixOf P w.length i).2) (tl w) (ixOf P (w.length + 1) (false, i)).1 (Y + 1))) := by
  rw [dw_false, cs_real _ _ _ _ (coordinate_real P l _) (qC_real P) _ (tl_real w), ofReal_add_one, qw_real _ _ (tl_real w),
    xs_real _ _ (tl_real w), coordinate_real, qC_real]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  rfl

theorem ixOf_castSucc (P : M.Par) (N : ℕ) (b : Bool) (i : Iota P N) (x : Fin N) :
    (ixOf P (N + 1) (b, i)).1 x.castSucc = (ixOf P N i).1 x := by
  simp [ixOf]

theorem ixOf_last' (P : M.Par) (N : ℕ) (b : Bool) (i : Iota P N) :
    (ixOf P (N + 1) (b, i)).1 (Fin.last N) = if b then 1 else 0 := by
  simp [ixOf]

theorem tl_agree (P : M.Par) (w : List ℝ) (i : Iota P w.length) (b b' : Bool) :
    ∀ a ∈ tl w, (ixOf P (w.length + 1) (b, i)).1 a.intersection_update_fsHerm_neg_one = (ixOf P (w.length + 1) (b', i)).1 a.intersection_update_fsHerm_neg_one := by
  intro a ha
  rw [tl_relabel, List.mem_map] at ha
  obtain ⟨a0, _, rfl⟩ := ha
  simp only [ixOf_castSucc]

theorem mult_tl (P : M.Par) (w : List ℝ) (i : Iota P w.length) (b : Bool) (γ : ℂ) :
    multS (wordP w) γ (ixOf P w.length i).1 = multS (tl w) γ (ixOf P (w.length + 1) (b, i)).1 := by
  unfold multS
  rw [tl_relabel, List.map_map]
  congr 1
  refine List.map_congr_left fun a0 _ => ?_
  simp only [Function.comp, ixOf_castSucc]

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y12

section S_R_Y13
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

def summand (P : M.Par) (π : M.Ty P) (Y : ℝ) (m : ℕ) : ℝ :=
  resA (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P π j - 1) m *
    |ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P π j) (-M.rho P π m - 1)| /
    (|ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P π j - 1) Y| *
      |ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P π j) Y| *
      |Y - (-M.rho P π m - 1)| ^ 3 * |Y - -M.rho P π m|)

theorem norm_phase (P : M.Par) (hTT : 0 < P.TT) (q : Qp P.r P.TT) : ‖phase P q‖ = 1 := by
  have hz : q.1.2 ≠ 0 := by
    intro h0; have := q.2.2; rw [h0, Complex.normSq_zero] at this; linarith
  have hu := (Formalism.FourierDecayAlt.P.analytic_units_hold P.r P.TT hTT.le).1 M.vzb
  unfold phase
  have e1 : evQ P ((DQ P).x M.vz) q = q.1.2 := Formalism.FourierDecayAlt.P.MAx1.An.coordE_vz q.1
  have e2 : evQ P ((DQ P).inv ((DQ P).x M.vzb)) q = (starRingEnd ℂ q.1.2)⁻¹ := by
    show ((Ring.inverse (coordQ M.vzb) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = _
    rw [MAx2.Jet.ev_inverse P _ hu]
    exact congrArg (·⁻¹) (Formalism.FourierDecayAlt.P.MAx1.An.coordE_vzb q.1)
  rw [e1, e2, norm_mul, norm_inv, Complex.norm_conj]
  exact mul_inv_cancel₀ (norm_ne_zero_iff.2 hz)

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y13

section S_R_Y14
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

section
variable {P : M.Par} {l : ℕ} {α β Lb : ℝ} {Ntot : ℕ} {w : List ℝ} {Y s : ℝ}

theorem Ctx.sides (h : Ctx P l α β Lb Ntot w Y s) (π : M.Ty P) :
    Side P.k l (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P π j - 1) α β ∧
      Side P.k l (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P π j) α β :=
  Formalism.FourierDecayAlt.P.MAx3.R.sides P.k l P.u P.u' (M.rho P π) α β h.hOK.k_pos h.hl1 h.hlk (Formalism.FourierDecayAlt.P.types_interlace P h.hOK π)
    (h.hcut α ⟨le_rfl, h.hαβ.le⟩) (h.hcut β ⟨h.hαβ.le, le_rfl⟩)

theorem coef_bound (a s Lb : ℝ) (hs : |s| ≤ Lb) (ha : 2 * Lb ≤ |a|) (hL : 0 < Lb) :
    ‖((a : ℂ))⁻¹ - ((a + s : ℝ) : ℂ)⁻¹‖ ^ 2 ≤ 4 * Lb ^ 2 / a ^ 4 := by
  have ha0 : 0 < |a| := by linarith
  have has : |a| / 2 ≤ |a + s| := by
    have := abs_sub_abs_le_abs_sub a (-s)
    rw [sub_neg_eq_add, abs_neg] at this; linarith
  have has0 : 0 < |a + s| := by linarith
  have hne : a ≠ 0 := fun e => by rw [e, abs_zero] at ha0; exact lt_irrefl _ ha0
  have hne' : a + s ≠ 0 := fun e => by rw [e, abs_zero] at has0; exact lt_irrefl _ has0
  have e : ((a : ℂ))⁻¹ - ((a + s : ℝ) : ℂ)⁻¹ = ((s / (a * (a + s)) : ℝ) : ℂ) := by
    have hc : (a : ℂ) ≠ 0 := by exact_mod_cast hne
    have hc' : (a : ℂ) + s ≠ 0 := by exact_mod_cast hne'
    push_cast; field_simp; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : s ^ 2 ≤ Lb ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  have h2 : a ^ 2 ≤ 4 * (a + s) ^ 2 := by
    rw [← sq_abs a, ← sq_abs (a + s)]; nlinarith
  have : (a * (a + s)) ^ 2 = a ^ 2 * (a + s) ^ 2 := by ring
  rw [this]
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  nlinarith [mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 ha2) (by positivity) (by positivity)]

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y14

section S_R_Y15
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

section
variable {P : M.Par} {l : ℕ} {α β Lb : ℝ} {Ntot : ℕ} {w : List ℝ} {Y s : ℝ}

theorem Ctx.ss_entry (h : Ctx P l α β Lb Ntot w Y s) (q : Qp P.r P.TT) (i i' : Iota P w.length) (m : Fin (P.k - 1))
    (hE : (ixOf P w.length i).1 = (ixOf P w.length i').1)
    (hup : M.Up P ((m : ℕ) + 1) (ixOf P w.length i').2 (ixOf P w.length i).2) :
    dwW P l (Y :: w) q (true, i) *
      ‖(((Y : ℂ) - gJ P (m, (ixOf P w.length i).2))⁻¹ - (((Y + s : ℝ) : ℂ) - gJ P (m, (ixOf P w.length i).2))⁻¹) *
        multS (wordP w) (gJ P (m, (ixOf P w.length i).2)) (ixOf P w.length i).1 *
        (phase P q * ((Real.sqrt (M.Nrm P ((m : ℕ) + 1) (ixOf P w.length i').2) : ℝ) : ℂ))‖ ^ 2 ≤
      dwW P l (Y :: w) q (false, i') *
        (4 * Real.exp 7 * Lb ^ 2 * summand P (ixOf P w.length i').2 Y ((m : ℕ) + 1)) := by
  set πt := (ixOf P w.length i).2
  set πs := (ixOf P w.length i').2
  set mm := (m : ℕ) + 1 with hmmdef
  have hmm : mm ∈ Icc 1 (P.k - 1) := by have := m.isLt; simp only [mem_Icc]; omega
  have hTT : 0 < P.TT := mul_pos h.hOK.T_pos h.hOK.T'_pos
  have hI := h.twelve_le_window
  have hYI := h.mid_I Y h.hYm
  have hLpos : 0 < Lb := by linarith [h.hL2]

  have hrho := Formalism.FourierDecayAlt.P.rho_raise P mm πs πt hup
  set ρs := M.rho P πs
  have hρt : M.rho P πt mm = ρs mm + 1 := by rw [hrho mm hmm, if_pos rfl]
  have hgJ : gJ P (m, πt) = -((ρs mm + 1 : ℝ) : ℂ) := by
    show -((M.rho P πt mm : ℝ) : ℂ) = _
    rw [hρt]

  obtain ⟨hf, hg⟩ := h.sides πs
  have hdist := hf.dist_b h.hl1 h.hlk h.hαβ Y h.hYm.1 h.hYm.2 mm hmm
  have hdist' := hg.dist_b h.hl1 h.hlk h.hαβ Y h.hYm.1 h.hYm.2 mm hmm

  have hNrm : 0 ≤ M.Nrm P mm πs := ((Formalism.FourierDecayAlt.P.nrmFacts_statement P h.hOK mm hmm πs).1 πt hup).1.le

  have hnorm : ‖(((Y : ℂ) - gJ P (m, πt))⁻¹ - (((Y + s : ℝ) : ℂ) - gJ P (m, πt))⁻¹) *
        multS (wordP w) (gJ P (m, πt)) (ixOf P w.length i).1 *
        (phase P q * ((Real.sqrt (M.Nrm P mm πs) : ℝ) : ℂ))‖ ^ 2 =
      ‖(((Y + ρs mm + 1 : ℝ) : ℂ))⁻¹ - (((Y + ρs mm + 1 + s : ℝ) : ℂ))⁻¹‖ ^ 2 *
        multR (tl w) (ρs mm) (ixOf P (w.length + 1) (true, i)).1 ^ 2 * M.Nrm P mm πs := by
    rw [mult_tl P w i true, hgJ, mult_real (ρs mm) _ (tl w) (fun a ha => (tl_real w a ha).2)]
    have hA : ((Y : ℂ) - -((ρs mm + 1 : ℝ) : ℂ))⁻¹ - (((Y + s : ℝ) : ℂ) - -((ρs mm + 1 : ℝ) : ℂ))⁻¹ =
        (((Y + ρs mm + 1 : ℝ) : ℂ))⁻¹ - (((Y + ρs mm + 1 + s : ℝ) : ℂ))⁻¹ := by
      push_cast; ring_nf
    rw [hA, norm_mul, norm_mul, norm_mul, norm_phase P hTT q, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_mul, mul_pow, mul_pow, Real.sq_sqrt hNrm, sq_abs]
  rw [hnorm, dw_true_real, dw_false_real]

  have hwI : ∀ p ∈ w, p ∈ Set.Icc α β := fun p hp => h.mid_I p (h.hwm p hp)
  have hxs_ne := h.xpoly_ne πs Y hYI
  have hq0 := h.qp_pos Y hYI
  have hsxs := h.sx_pos πs Y hYI
  have hsxt := h.sx_pos πt Y hYI
  have hrel : ∀ Z, sx P l πt Z * (Z + ρs mm) = sx P l πs Z * (Z + ρs mm + 1) := by
    intro Z
    have := xpoly_up P.k ρs (M.rho P πt) mm hmm hrho Z
    unfold sx
    linear_combination ((-1 : ℝ) ^ (P.k - l)) * this
  have hlenN : ((tl w).length : ℝ) ≤ Lb := by
    rw [tl_length]
    have : (w.length : ℝ) + 1 ≤ Ntot := by exact_mod_cast h.hlen
    linarith [h.hNL]
  have h6L : 6 * Lb ≤ β - α := by
    have h1 : (1 : ℝ) ≤ Ntot := by exact_mod_cast h.hNpos
    nlinarith [h.h6]
  have hsw := ss_weight (sx P l πs) (sx P l πt) (qp P) (ρs mm) Lb (β - α) Y h.hL2 (by linarith) (tl w)
    (ixOf P (w.length + 1) (true, i)).1 (ixOf P (w.length + 1) (false, i')).1
    (by
      intro b hb
      rw [tl_relabel, List.mem_map] at hb
      obtain ⟨a0, _, rfl⟩ := hb
      simp only [ixOf_castSucc, hE])
    (fun b hb => by
      obtain ⟨p, hp, e⟩ := tl_mem w hb
      rw [e, Complex.ofReal_re]
      exact ⟨(h.sx_pos πs p (hwI p hp)).1, (h.sx_pos πs p (hwI p hp)).2, h.qp_pos p (hwI p hp)⟩)
    hrel (tl_pairwise w Lb h.hord)
    (fun b hb => by obtain ⟨p, hp, e⟩ := tl_mem w hb; rw [e, Complex.ofReal_re]; exact (h.hfar p hp).1)
    hlenN (by linarith)
    (fun b hb => by
      obtain ⟨p, hp, e⟩ := tl_mem w hb
      rw [e, Complex.ofReal_re]
      have := hf.dist_b h.hl1 h.hlk h.hαβ p (h.hwm p hp).1 (h.hwm p hp).2 mm hmm
      rwa [show p - (-ρs mm - 1) = p + ρs mm + 1 by ring] at this)
    (fun b hb => by
      obtain ⟨p, hp, e⟩ := tl_mem w hb
      rw [e, Complex.ofReal_re]
      intro e0
      apply (h.xpoly_ne πs p (hwI p hp)).1
      exact Finset.prod_eq_zero hmm e0)
    hsxs.2 hsxt.1 hq0
  have hc := coef_bound (Y + ρs mm + 1) s Lb h.hsL (by
      have := hf.dist_b h.hl1 h.hlk h.hαβ Y h.hYm.1 h.hYm.2 mm hmm
      rw [show Y - (-ρs mm - 1) = Y + ρs mm + 1 by ring] at this
      linarith) hLpos
  have hct := core_term P l πs πt mm hmm hrho Y (mul_pos h.hOK.T_pos h.hOK.T'_pos).ne' hq0.ne'
    (fun e0 => hxs_ne.1 (Finset.prod_eq_zero hmm e0))
    (fun e0 => hxs_ne.2 (Finset.prod_eq_zero hmm (by rw [← e0]; ring)))
    (by intro e0; rw [qp_split] at hq0
        have : ∏ i ∈ Icc 1 P.k, (Y + (1 / 2 + P.u i)) = 0 := by
          rw [← e0]; exact Finset.prod_congr rfl fun i _ => by ring
        rw [this] at hq0; simp at hq0)
    (by intro e0; rw [qp_split] at hq0
        have : ∏ i ∈ Icc 1 P.k, (Y + (1 / 2 + P.u' i)) = 0 := by
          rw [← e0]; exact Finset.prod_congr rfl fun i _ => by ring
        rw [this] at hq0; simp at hq0)
    (by intro e0; apply hxs_ne.2; rw [← e0]; exact Finset.prod_congr rfl fun j _ => by ring)
    (by intro e0; apply hxs_ne.1; rw [← e0]; exact Finset.prod_congr rfl fun j _ => by ring)
    (hf.resA_nonneg h.hOK.k_pos mm hmm)

  set W := Wq P q ^ (w.length + 1)
  have hW : 0 ≤ W := pow_nonneg (MAx3.Wq_pos P hTT.le q).le _
  set CT := csR (sx P l πt) (qp P) (tl w) (ixOf P (w.length + 1) (true, i)).1
  set XT := xsR (sx P l πt) (tl w) (ixOf P (w.length + 1) (true, i)).1 Y
  set m2 := multR (tl w) (ρs mm) (ixOf P (w.length + 1) (true, i)).1 ^ 2
  set c2 := ‖(((Y + ρs mm + 1 : ℝ) : ℂ))⁻¹ - (((Y + ρs mm + 1 + s : ℝ) : ℂ))⁻¹‖ ^ 2
  set σ0 := csR (sx P l πs) (qp P) (tl w) (ixOf P (w.length + 1) (false, i')).1 *
    (qwR (qp P) (tl w) Y / xsR (sx P l πs) (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1))
  set K := Real.exp 7 * sx P l πt Y * sx P l πs (Y + 1) / qp P Y
  have hsw' : CT * XT * m2 ≤ σ0 * K := by
    calc CT * XT * m2 ≤ _ := hsw
      _ = σ0 * K := by
        show csR (sx P l πs) (qp P) (tl w) (ixOf P (w.length + 1) (false, i')).1 * (qp P Y * psR (tl w) Y) /
          (sx P l πs (Y + 1) * phR (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1)) * K =
          csR (sx P l πs) (qp P) (tl w) (ixOf P (w.length + 1) (false, i')).1 * (qp P Y * psR (tl w) Y /
            (sx P l πs (Y + 1) * phR (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1))) * K
        rw [mul_div_assoc]
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos 7).le hsxt.1.le) hsxs.2.le) hq0.le
  have hc2 : 0 ≤ c2 := sq_nonneg _
  have hσ0 : 0 ≤ σ0 := by
    have hcs := csR_pos (sx P l πs) (qp P) Lb h.hL2.le (tl w) (ixOf P (w.length + 1) (false, i')).1
      (tl_pairwise w Lb h.hord) (fun b hb => by
        obtain ⟨p, hp, e⟩ := tl_mem w hb
        rw [e, Complex.ofReal_re]
        exact ⟨(h.sx_pos πs p (hwI p hp)).1, (h.sx_pos πs p (hwI p hp)).2, h.qp_pos p (hwI p hp)⟩)
    have hps := psR_bounds Lb h.hL2.le (tl w) Y (fun b hb => by
      obtain ⟨p, hp, e⟩ := tl_mem w hb; rw [e, Complex.ofReal_re]; exact (h.hfar p hp).1)
    have hph := phR_bounds Lb h.hL2.le (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1) (fun b hb => by
      obtain ⟨p, hp, e⟩ := tl_mem w hb; rw [e, Complex.ofReal_re]; linarith [(h.hfar p hp).1])
    exact mul_nonneg hcs.le (div_nonneg (mul_nonneg hq0.le (by linarith [hps.1]))
      (mul_nonneg hsxs.2.le (by linarith [hph.1])))
  have hNr := hNrm
  calc W * (CT * XT) * (c2 * m2 * M.Nrm P mm πs) = W * (CT * XT * m2) * (c2 * M.Nrm P mm πs) := by ring
    _ ≤ W * (σ0 * K) * (c2 * M.Nrm P mm πs) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsw' hW) (mul_nonneg hc2 hNr)
    _ ≤ W * (σ0 * K) * (4 * Lb ^ 2 / (Y + ρs mm + 1) ^ 4 * M.Nrm P mm πs) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hNr) (mul_nonneg hW (mul_nonneg hσ0 hK))
    _ = W * σ0 * (4 * Real.exp 7 * Lb ^ 2 * (M.Nrm P mm πs * sx P l πt Y * sx P l πs (Y + 1) /
          (qp P Y * (Y + ρs mm + 1) ^ 4))) := by
        simp only [K]; field_simp
    _ ≤ W * σ0 * (4 * Real.exp 7 * Lb ^ 2 * summand P πs Y mm) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hW hσ0)
        apply mul_le_mul_of_nonneg_left hct (by positivity)

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y15

section S_R_Y16
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

section
variable {P : M.Par} {l : ℕ} {α β Lb : ℝ} {Ntot : ℕ} {w : List ℝ} {Y s : ℝ}

theorem plusWord_pairwise (w : List ℝ) (L : ℝ) (h : w.Pairwise fun p p' => L ≤ p - p') :
    (wordP w).Pairwise fun b c => L ≤ b.pt.re - c.pt.re := by
  have h2 : ((wordP w).map Letter.pt).Pairwise fun z z' : ℂ => L ≤ z.re - z'.re := by
    rw [MAx2.plusWord_points, List.pairwise_map]
    exact h.imp fun hh => by simpa using hh
  rwa [List.pairwise_map] at h2

theorem Ctx.h_ratio (h : Ctx P l α β Lb Ntot w Y s) (π : M.Ty P) (p Z : ℝ)
    (hp : α + (β - α) / 3 ≤ p ∧ p ≤ β - (β - α) / 3) (hZ : α + (β - α) / 3 ≤ Z ∧ Z ≤ β - (β - α) / 3) :
    qp P p / (sx P l π p * sx P l π (p + 1)) ≤ Real.exp 4 * (qp P Z / (sx P l π Z * sx P l π (Z + 1))) := by
  obtain ⟨hf, hg⟩ := h.sides π
  have hT : 0 < P.T * P.T' := mul_pos h.hOK.T_pos h.hOK.T'_pos
  have hform : ∀ X : ℝ, X ∈ Set.Icc α β → qp P X / (sx P l π X * sx P l π (X + 1)) =
      P.T * P.T' * (|ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P π j - 1) X| *
        |ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P π j) X|) := by
    intro X hX
    have hpos : 0 < qp P X / (sx P l π X * sx P l π (X + 1)) := by
      obtain ⟨a, b⟩ := h.sx_pos π X hX
      exact div_pos (h.qp_pos X hX) (mul_pos a b)
    rw [← abs_of_pos hpos]
    simp only [sx, qp_split, ratF, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hT]
    have e1 : I.xpoly P.k (M.rho P π) (X + 1) = ∏ j ∈ Icc 1 (P.k - 1), (X - (-M.rho P π j - 1)) :=
      Finset.prod_congr rfl fun j _ => by ring
    have e2 : I.xpoly P.k (M.rho P π) X = ∏ j ∈ Icc 1 (P.k - 1), (X - -M.rho P π j) :=
      Finset.prod_congr rfl fun j _ => by ring
    have e3 : ∏ i ∈ Icc 1 P.k, (X + (1 / 2 + P.u i)) = ∏ i ∈ Icc 1 P.k, (X - (-(1 / 2) - P.u i)) :=
      Finset.prod_congr rfl fun i _ => by ring
    have e4 : ∏ i ∈ Icc 1 P.k, (X + (1 / 2 + P.u' i)) = ∏ i ∈ Icc 1 P.k, (X - (-(1 / 2) - P.u' i)) :=
      Finset.prod_congr rfl fun i _ => by ring
    rw [e1, e2, e3, e4]
    ring
  rw [hform p (h.mid_I p hp), hform Z (h.mid_I Z hZ)]
  have r1 := hf.ratio h.hl1 h.hlk h.hαβ p Z hp hZ
  have r2 := hg.ratio h.hl1 h.hlk h.hαβ p Z hp hZ
  have he4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  rw [he4]
  calc P.T * P.T' * (|ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i) (fun j => -M.rho P π j - 1) p| *
        |ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P π j) p|)
      ≤ P.T * P.T' * ((Real.exp 2 * |ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u i)
          (fun j => -M.rho P π j - 1) Z|) *
          (Real.exp 2 * |ratF (Icc 1 P.k) (Icc 1 (P.k - 1)) (fun i => -(1 / 2) - P.u' i) (fun j => -M.rho P π j) Z|)) := by
        gcongr
    _ = _ := by ring

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y16

section S_R_Y17
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

theorem multS_bound {S : Type} [Fintype S] [DecidableEq S] (L : ℝ) (hL : 0 < L) (p : ℂ) (hp : p.im = 0)
    (e : Ix S) : ∀ (u : List (Letter ℂ S)), (∀ b ∈ u, b.pt.im = 0 ∧ L ≤ b.pt.re - p.re) →
    ‖multS u p e‖ ≤ (1 + 1 / L) ^ u.length
  | [], _ => by simp [multS]
  | b :: u, h => by
    have ih := multS_bound L hL p hp e u fun c hc => h c (List.mem_cons_of_mem _ hc)
    obtain ⟨hb1, hb2⟩ := h b List.mem_cons_self
    unfold multS at ih ⊢
    rw [List.map_cons, List.prod_cons, norm_mul, List.length_cons, pow_succ']
    refine mul_le_mul ?_ ih (norm_nonneg _) (by positivity)
    have hd : b.pt - p = (((b.pt.re - p.re) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hb1, hp]
    rw [hd]
    have hpos : 0 < b.pt.re - p.re := by linarith
    calc ‖1 + sg (e b.intersection_update_fsHerm_neg_one) / (((b.pt.re - p.re) : ℝ) : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖sg (e b.intersection_update_fsHerm_neg_one) / (((b.pt.re - p.re) : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ 1 + 1 / L := by
          rw [norm_one, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
          have : ‖sg (e b.intersection_update_fsHerm_neg_one)‖ = 1 := by unfold sg; split_ifs <;> simp
          rw [this]
          have := one_div_le_one_div_of_le hL hb2
          linarith

theorem coef2 (Y s p Lb : ℝ) (hL : 0 < Lb) (hs : |s| ≤ Lb) (h1 : Lb ≤ Y - p) (h2 : Lb ≤ Y + s - p) :
    ‖(((Y : ℂ) - (p : ℂ))⁻¹ - (((Y + s : ℝ) : ℂ) - (p : ℂ))⁻¹)‖ ^ 2 ≤ 1 / Lb ^ 2 := by
  have hne1 : Y - p ≠ 0 := by intro e; linarith
  have hne2 : Y + s - p ≠ 0 := by intro e; linarith
  have e : ((Y : ℂ) - (p : ℂ))⁻¹ - (((Y + s : ℝ) : ℂ) - (p : ℂ))⁻¹ = ((s / ((Y - p) * (Y + s - p)) : ℝ) : ℂ) := by
    have hc1 : (Y : ℂ) - p ≠ 0 := by exact_mod_cast hne1
    have hc2 : (Y : ℂ) + s - p ≠ 0 := by exact_mod_cast hne2
    push_cast; field_simp; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have hs2 : s ^ 2 ≤ Lb ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  have hd : Lb ^ 2 * Lb ^ 2 ≤ ((Y - p) * (Y + s - p)) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_left₀ hL.le h1 2) (pow_le_pow_left₀ hL.le h2 2) (by positivity) (by positivity)
  nlinarith [sq_nonneg (Lb ^ 2)]

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y17

section S_R_Y18
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

section
variable {P : M.Par} {l : ℕ} {α β Lb : ℝ} {Ntot : ℕ} {w : List ℝ} {Y s : ℝ}

theorem Ctx.let_entry (h : Ctx P l α β Lb Ntot w Y s) (q : Qp P.r P.TT) (i i' : Iota P w.length)
    (n : Fin (wordP w).length) (hPi : (ixOf P w.length i).2 = (ixOf P w.length i').2)
    (h0 : (ixOf P w.length i).1 ((wordP w).get n).intersection_update_fsHerm_neg_one = 0) (h1 : (ixOf P w.length i').1 ((wordP w).get n).intersection_update_fsHerm_neg_one = 1)
    (hrest : ∀ b, b ≠ ((wordP w).get n).intersection_update_fsHerm_neg_one → (ixOf P w.length i).1 b = (ixOf P w.length i').1 b) :
    dwW P l (Y :: w) q (true, i) *
      ‖(((Y : ℂ) - ((wordP w).get n).pt)⁻¹ - (((Y + s : ℝ) : ℂ) - ((wordP w).get n).pt)⁻¹) *
        multS ((wordP w).take n) ((wordP w).get n).pt (ixOf P w.length i').1‖ ^ 2 ≤
      dwW P l (Y :: w) q (false, i') * (Real.exp 14 / Lb ^ 2) := by
  have hTT : 0 < P.TT := mul_pos h.hOK.T_pos h.hOK.T'_pos
  have hLpos : 0 < Lb := by linarith [h.hL2]
  have hYI := h.mid_I Y h.hYm
  have hwI : ∀ p ∈ w, p ∈ Set.Icc α β := fun p hp => h.mid_I p (h.hwm p hp)
  set π := (ixOf P w.length i).2 with hπdef
  obtain ⟨pn, hpnw, hpn⟩ := MAx2.mem_wordP (List.get_mem (wordP w) n)
  set sn := ((wordP w).get n).intersection_update_fsHerm_neg_one

  set la : Letter ℂ (Fin (w.length + 1)) := ⟨((wordP w).get n).plus, Fin.castSucc sn, ((wordP w).get n).pt⟩
  have hla : la ∈ tl w := by rw [tl_relabel]; exact List.mem_map_of_mem (List.get_mem _ _)
  have hlapt : la.pt.re = pn := by show ((wordP w).get n).pt.re = pn; rw [hpn, Complex.ofReal_re]
  set e := (ixOf P (w.length + 1) (true, i)).1
  set e' := (ixOf P (w.length + 1) (true, i')).1
  have he : ∀ x, x ≠ la.intersection_update_fsHerm_neg_one → e x = e' x := by
    intro x hx
    by_cases hl : x = Fin.last w.length
    · rw [hl]
      show (ixOf P (w.length + 1) (true, i)).1 (Fin.last w.length) = (ixOf P (w.length + 1) (true, i')).1 (Fin.last w.length)
      rw [ixOf_last', ixOf_last']
    · obtain ⟨y, rfl⟩ : ∃ y : Fin w.length, x = y.castSucc := ⟨x.castPred hl, (Fin.castSucc_castPred x hl).symm⟩
      show (ixOf P (w.length + 1) (true, i)).1 y.castSucc = (ixOf P (w.length + 1) (true, i')).1 y.castSucc
      rw [ixOf_castSucc, ixOf_castSucc]
      exact hrest y fun e0 => hx (by rw [e0])
  have hea : e la.intersection_update_fsHerm_neg_one = 0 := by show (ixOf P (w.length + 1) (true, i)).1 sn.castSucc = 0; rw [ixOf_castSucc]; exact h0
  have he'a : e' la.intersection_update_fsHerm_neg_one ≠ 0 := by
    show (ixOf P (w.length + 1) (true, i')).1 sn.castSucc ≠ 0; rw [ixOf_castSucc, h1]; decide
  have hpos : ∀ b ∈ tl w, 0 < sx P l π b.pt.re ∧ 0 < sx P l π (b.pt.re + 1) ∧ 0 < qp P b.pt.re := fun b hb => by
    obtain ⟨p, hp, ep⟩ := tl_mem w hb
    rw [ep, Complex.ofReal_re]
    exact ⟨(h.sx_pos π p (hwI p hp)).1, (h.sx_pos π p (hwI p hp)).2, h.qp_pos p (hwI p hp)⟩
  have hfarY : ∀ b ∈ tl w, Lb ≤ Y - b.pt.re := fun b hb => by
    obtain ⟨p, hp, ep⟩ := tl_mem w hb; rw [ep, Complex.ofReal_re]; exact (h.hfar p hp).1
  have hlenN : ((tl w).length : ℝ) ≤ Lb := by
    rw [tl_length]
    have : (w.length : ℝ) + 1 ≤ Ntot := by exact_mod_cast h.hlen
    linarith [h.hNL]
  have hH := h.h_ratio π pn Y (h.hwm pn hpnw) h.hYm
  rw [← hlapt] at hH
  have hsx := h.sx_pos π Y hYI
  have hlw := let_weight (sx P l π) (qp P) Lb Y (Real.exp 4) h.hL2 (tl w) la e e' he hea he'a (tl_nodup w) hla hpos
    (tl_pairwise w Lb h.hord) hfarY hlenN hsx.1 hsx.2 (h.qp_pos Y hYI) hH (Real.exp_pos 4).le

  have hcs : csR (sx P l π) (qp P) (tl w) e' = csR (sx P l π) (qp P) (tl w) (ixOf P (w.length + 1) (false, i')).1 :=
    csR_congr _ _ (tl w) _ _ (tl_agree P w i' true false)
  have hph : phR (tl w) e' (Y + 1) = phR (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1) :=
    phR_congr (tl w) _ _ (tl_agree P w i' true false) _
  rw [dw_true_real, dw_false_real, ← hPi]

  have hc : ‖(((Y : ℂ) - ((wordP w).get n).pt)⁻¹ - (((Y + s : ℝ) : ℂ) - ((wordP w).get n).pt)⁻¹)‖ ^ 2 ≤ 1 / Lb ^ 2 := by
    rw [hpn]; exact coef2 Y s pn Lb hLpos h.hsL (h.hfar pn hpnw).1 (h.hfar pn hpnw).2
  have hm : ‖multS ((wordP w).take n) ((wordP w).get n).pt (ixOf P w.length i').1‖ ^ 2 ≤ Real.exp 2 := by
    have hord := plusWord_pairwise w Lb h.hord
    have hb : ∀ b ∈ (wordP w).take n, b.pt.im = 0 ∧ Lb ≤ b.pt.re - ((wordP w).get n).pt.re := by
      intro b hb
      obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.1 hb
      have hk1 : k < n := lt_of_lt_of_le hk (min_le_left _ _)
      have hk2 : k < (wordP w).length := lt_of_lt_of_le hk (min_le_right _ _)
      constructor
      · obtain ⟨p, _, ep⟩ := MAx2.mem_wordP (List.getElem_mem (l := wordP w) hk2)
        rw [ep]; simp
      · have := List.pairwise_iff_getElem.1 hord k n hk2 n.isLt hk1
        simpa using this
    have := multS_bound Lb hLpos ((wordP w).get n).pt (by rw [hpn]; simp) (ixOf P w.length i').1
      ((wordP w).take n) hb
    have hlen : (((wordP w).take n).length : ℝ) ≤ Lb := by
      have h1 : (((wordP w).take n).length : ℝ) ≤ w.length := by
        have hwl : (wordP w).length = w.length := by
          have := congrArg List.length (MAx2.plusWord_points w); simpa using this
        have : ((wordP w).take n).length ≤ w.length := by
          rw [List.length_take]; exact (min_le_right _ _).trans hwl.le
        exact_mod_cast this
      have : (w.length : ℝ) + 1 ≤ Ntot := by exact_mod_cast h.hlen
      linarith [h.hNL]
    have e1 := pow_le_exp 1 _ Lb hLpos (by norm_num) hlen
    calc ‖multS ((wordP w).take n) ((wordP w).get n).pt (ixOf P w.length i').1‖ ^ 2
        ≤ ((1 + 1 / Lb) ^ ((wordP w).take n).length) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by positivity) e1 2
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [norm_mul, mul_pow]
  set W := Wq P q ^ (w.length + 1)
  have hW : 0 ≤ W := pow_nonneg (MAx3.Wq_pos P hTT.le q).le _
  have hlw' : csR (sx P l π) (qp P) (tl w) e * xsR (sx P l π) (tl w) e Y ≤
      csR (sx P l π) (qp P) (tl w) (ixOf P (w.length + 1) (false, i')).1 *
        (qwR (qp P) (tl w) Y / xsR (sx P l π) (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1)) *
        (Real.exp 8 * Real.exp 4) := by
    rw [← hcs]
    simp only [xsR, qwR]
    rw [← hph, ← mul_div_assoc]
    exact hlw
  have hσ0 : 0 ≤ csR (sx P l π) (qp P) (tl w) (ixOf P (w.length + 1) (false, i')).1 *
      (qwR (qp P) (tl w) Y / xsR (sx P l π) (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1)) := by
    have h1 := csR_pos (sx P l π) (qp P) Lb h.hL2.le (tl w) (ixOf P (w.length + 1) (false, i')).1
      (tl_pairwise w Lb h.hord) hpos
    have hps := psR_bounds Lb h.hL2.le (tl w) Y hfarY
    have hph2 := phR_bounds Lb h.hL2.le (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1)
      (fun b hb => by have := hfarY b hb; linarith)
    exact mul_nonneg h1.le (div_nonneg (mul_nonneg (h.qp_pos Y hYI).le (by linarith [hps.1]))
      (mul_nonneg hsx.2.le (by linarith [hph2.1])))
  have he12 : Real.exp 8 * Real.exp 4 * (1 / Lb ^ 2 * Real.exp 2) = Real.exp 14 / Lb ^ 2 := by
    have : Real.exp 14 = Real.exp 8 * Real.exp 4 * Real.exp 2 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [this]; field_simp
  calc W * (csR (sx P l π) (qp P) (tl w) e * xsR (sx P l π) (tl w) e Y) *
        (‖(((Y : ℂ) - ((wordP w).get n).pt)⁻¹ - (((Y + s : ℝ) : ℂ) - ((wordP w).get n).pt)⁻¹)‖ ^ 2 *
          ‖multS ((wordP w).take n) ((wordP w).get n).pt (ixOf P w.length i').1‖ ^ 2)
      ≤ W * (csR (sx P l π) (qp P) (tl w) (ixOf P (w.length + 1) (false, i')).1 *
          (qwR (qp P) (tl w) Y / xsR (sx P l π) (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1)) *
          (Real.exp 8 * Real.exp 4)) * (1 / Lb ^ 2 * Real.exp 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hlw' hW) (mul_le_mul hc hm (sq_nonneg _) (by positivity))
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        exact mul_nonneg hW (mul_nonneg hσ0 (by positivity))
    _ = W * (csR (sx P l π) (qp P) (tl w) (ixOf P (w.length + 1) (false, i')).1 *
          (qwR (qp P) (tl w) Y / xsR (sx P l π) (tl w) (ixOf P (w.length + 1) (false, i')).1 (Y + 1))) *
          (Real.exp 14 / Lb ^ 2) := by rw [← he12]; ring

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y18

section S_R_Y19
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

section
variable {P : M.Par} {l : ℕ} {α β Lb : ℝ} {Ntot : ℕ} {w : List ℝ} {Y s : ℝ}

theorem Ctx.weights_nonneg (h : Ctx P l α β Lb Ntot w Y s) (q : Qp P.r P.TT) (i : Iota P w.length) :
    0 ≤ dwW P l (Y :: w) q (true, i) ∧ 0 ≤ dwW P l (Y :: w) q (false, i) := by
  have hTT : 0 < P.TT := mul_pos h.hOK.T_pos h.hOK.T'_pos
  have hYI := h.mid_I Y h.hYm
  have hwI : ∀ p ∈ w, p ∈ Set.Icc α β := fun p hp => h.mid_I p (h.hwm p hp)
  set π := (ixOf P w.length i).2
  have hpos : ∀ b ∈ tl w, 0 < sx P l π b.pt.re ∧ 0 < sx P l π (b.pt.re + 1) ∧ 0 < qp P b.pt.re := fun b hb => by
    obtain ⟨p, hp, ep⟩ := tl_mem w hb
    rw [ep, Complex.ofReal_re]
    exact ⟨(h.sx_pos π p (hwI p hp)).1, (h.sx_pos π p (hwI p hp)).2, h.qp_pos p (hwI p hp)⟩
  have hfarY : ∀ b ∈ tl w, Lb ≤ Y - b.pt.re := fun b hb => by
    obtain ⟨p, hp, ep⟩ := tl_mem w hb; rw [ep, Complex.ofReal_re]; exact (h.hfar p hp).1
  have hW : 0 ≤ Wq P q ^ (w.length + 1) := pow_nonneg (MAx3.Wq_pos P hTT.le q).le _
  have hsx := h.sx_pos π Y hYI
  constructor
  · rw [dw_true_real]
    have h1 := csR_pos (sx P l π) (qp P) Lb h.hL2.le (tl w) (ixOf P (w.length + 1) (true, i)).1
      (tl_pairwise w Lb h.hord) hpos
    have hph := phR_bounds Lb h.hL2.le (tl w) (ixOf P (w.length + 1) (true, i)).1 Y hfarY
    exact mul_nonneg hW (mul_nonneg h1.le (mul_nonneg hsx.1.le (by linarith [hph.1])))
  · rw [dw_false_real]
    have h1 := csR_pos (sx P l π) (qp P) Lb h.hL2.le (tl w) (ixOf P (w.length + 1) (false, i)).1
      (tl_pairwise w Lb h.hord) hpos
    have hps := psR_bounds Lb h.hL2.le (tl w) Y hfarY
    have hph := phR_bounds Lb h.hL2.le (tl w) (ixOf P (w.length + 1) (false, i)).1 (Y + 1)
      (fun b hb => by have := hfarY b hb; linarith)
    exact mul_nonneg hW (mul_nonneg h1.le (div_nonneg (mul_nonneg (h.qp_pos Y hYI).le (by linarith [hps.1]))
      (mul_nonneg hsx.2.le (by linarith [hph.1]))))

theorem sep_of_up (P : M.Par) (hOK : P.OK) (πs πt : M.Ty P) (m : ℕ) (hm : m ∈ Icc 1 (P.k - 1))
    (hup : M.Up P m πs πt) : ∀ j ∈ Icc 1 (P.k - 1), 1 ≤ |(-M.rho P πs m - 1) - -M.rho P πs j| := by
  intro j hj
  have hrho := Formalism.FourierDecayAlt.P.rho_raise P m πs πt hup
  have hs := Formalism.FourierDecayAlt.P.types_interlace P hOK πs
  have ht := Formalism.FourierDecayAlt.P.types_interlace P hOK πt
  have hm' := mem_Icc.1 hm
  have hj' := mem_Icc.1 hj
  rcases lt_trichotomy j m with hlt | heq | hgt
  · have h1 := rho_le P.k P.u P.u' (M.rho P πt) ht j m hj'.1 hlt.le hm'.2
    rw [hrho j hj, if_neg (ne_of_lt hlt), hrho m hm, if_pos rfl] at h1
    have : (1 : ℝ) ≤ ((m - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m - j)
    rw [abs_of_pos (by linarith)]; linarith
  · subst heq
    rw [show -M.rho P πs j - 1 - -M.rho P πs j = -1 by ring]; simp
  · have h1 := rho_le P.k P.u P.u' (M.rho P πs) hs m j hm'.1 hgt.le hj'.2
    have : (1 : ℝ) ≤ ((j - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j - m)
    rw [abs_of_neg (by linarith)]; linarith

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y19

section S_R_Y20
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

section
variable {P : M.Par} {l : ℕ} {α β Lb : ℝ} {Ntot : ℕ} {w : List ℝ} {Y s : ℝ}

theorem Ctx.summand_nonneg (h : Ctx P l α β Lb Ntot w Y s) (π : M.Ty P) (m : ℕ) (hm : m ∈ Icc 1 (P.k - 1)) :
    0 ≤ summand P π Y m := by
  obtain ⟨hf, hg⟩ := h.sides π
  unfold summand
  exact div_nonneg (mul_nonneg (hf.resA_nonneg h.hOK.k_pos m hm) (abs_nonneg _)) (by positivity)

set_option maxHeartbeats 800000 in
theorem Ctx.ss_bound (h : Ctx P l α β Lb Ntot w Y s) (q : Qp P.r P.TT) (v : Iota P w.length → ℂ) :
    ∑ i, dwW P l (Y :: w) q (true, i) * ‖∑ i', dSS P w Y (Y + s) q (ixOf P w.length i).1 (ixOf P w.length i').1
      (ixOf P w.length i).2 (ixOf P w.length i').2 * v i'‖ ^ 2 ≤
      88 * Real.exp 7 * ∑ i', dwW P l (Y :: w) q (false, i') * ‖v i'‖ ^ 2 := by
  classical
  have hform : ∀ i, ∑ i', dSS P w Y (Y + s) q (ixOf P w.length i).1 (ixOf P w.length i').1
      (ixOf P w.length i).2 (ixOf P w.length i').2 * v i' =
      ∑ m ∈ (univ : Finset (Fin (P.k - 1))), ∑ i',
        (if (ixOf P w.length i).1 = (ixOf P w.length i').1 ∧
            M.Up P ((m : ℕ) + 1) (ixOf P w.length i').2 (ixOf P w.length i).2 then
          (((Y : ℂ) - gJ P (m, (ixOf P w.length i).2))⁻¹ - (((Y + s : ℝ) : ℂ) - gJ P (m, (ixOf P w.length i).2))⁻¹) *
            multS (wordP w) (gJ P (m, (ixOf P w.length i).2)) (ixOf P w.length i).1 *
            (phase P q * ((Real.sqrt (M.Nrm P ((m : ℕ) + 1) (ixOf P w.length i').2) : ℝ) : ℂ))
        else 0) * v i' := by
    intro i
    simp_rw [dSS_sparse, sum_mul]
    rw [sum_comm]
  simp_rw [hform]
  have hI := h.twelve_le_window
  obtain ⟨hk1, hkl⟩ := And.intro h.hOK.k_pos h.hlk
  refine sparse_bound (ι := Iota P w.length) (α := Fin (P.k - 1)) univ
    (fun (m : Fin (P.k - 1)) (i i' : Iota P w.length) => (ixOf P w.length i).1 = (ixOf P w.length i').1 ∧
      M.Up P ((m : ℕ) + 1) (ixOf P w.length i').2 (ixOf P w.length i).2)
    (fun m i i₁ i₂ h1 h2 => ixOf_inj P _ _ _ (Prod.ext (h1.1.symm.trans h2.1) (up_relation_source_unique P _ _ _ _ h1.2 h2.2)))
    (fun m i₁ i₂ i' h1 h2 => ixOf_inj P _ _ _ (Prod.ext (h1.1.trans h2.1.symm) (up_tgt P _ _ _ _ h1.2 h2.2)))
    _ _ _ (fun (m : Fin (P.k - 1)) (i' : Iota P w.length) => if ∃ πt, M.Up P ((m : ℕ) + 1) (ixOf P w.length i').2 πt then
        4 * Real.exp 7 * Lb ^ 2 * summand P (ixOf P w.length i').2 Y ((m : ℕ) + 1) else 0)
    (fun i => (h.weights_nonneg q i).1) (fun i => (h.weights_nonneg q i).2) ?_ ?_ (88 * Real.exp 7) ?_ v
  · intro m _ i i' hPr
    rw [if_pos ⟨_, hPr.2⟩]
    exact h.ss_entry q i i' m hPr.1 hPr.2
  · intro m i'
    split_ifs
    · have hm : (m : ℕ) + 1 ∈ Icc 1 (P.k - 1) := by have := m.isLt; simp only [mem_Icc]; omega
      have := h.summand_nonneg (ixOf P w.length i').2 _ hm
      positivity
    · exact le_refl _
  · intro i'
    set πs := (ixOf P w.length i').2
    obtain ⟨hf, hg⟩ := h.sides πs
    let emb : Fin (P.k - 1) ↪ ℕ := ⟨fun (m : Fin (P.k - 1)) => (m : ℕ) + 1, fun a b e => Fin.ext (by simpa using e)⟩
    set V : Finset ℕ := ((univ : Finset (Fin (P.k - 1))).filter
      fun (m : Fin (P.k - 1)) => ∃ πt, M.Up P ((m : ℕ) + 1) πs πt).map emb
    have hV : V ⊆ Icc 1 (P.k - 1) := by
      intro x hx
      simp only [V, mem_map, mem_filter] at hx
      obtain ⟨m, _, rfl⟩ := hx
      have := m.isLt; rw [mem_Icc]; show 1 ≤ (m : ℕ) + 1 ∧ (m : ℕ) + 1 ≤ P.k - 1; omega
    have hsep : ∀ m ∈ V, ∀ j ∈ Icc 1 (P.k - 1), 1 ≤ |(-M.rho P πs m - 1) - -M.rho P πs j| := by
      intro x hx
      simp only [V, mem_map, mem_filter] at hx
      obtain ⟨m, ⟨_, πt, hup⟩, rfl⟩ := hx
      exact sep_of_up P h.hOK πs πt _ (by have := m.isLt; rw [mem_Icc]; show 1 ≤ (m : ℕ) + 1 ∧ (m : ℕ) + 1 ≤ P.k - 1; omega) hup
    have hcore := core_SS hk1 h.hl1 hkl (by linarith) hf hg (fun j => by ring) Y h.hYm.1 h.hYm.2 V hV hsep
    have hsum : ∑ m : Fin (P.k - 1), (if ∃ πt, M.Up P ((m : ℕ) + 1) πs πt then
        4 * Real.exp 7 * Lb ^ 2 * summand P πs Y ((m : ℕ) + 1) else 0) =
        4 * Real.exp 7 * Lb ^ 2 * ∑ x ∈ V, summand P πs Y x := by
      rw [sum_map, mul_sum, sum_filter]
      rfl
    rw [hsum]
    have hcore' : ∑ x ∈ V, summand P πs Y x ≤ 132 / (β - α) ^ 2 := hcore
    have hcard : ((univ : Finset (Fin (P.k - 1))).card : ℝ) * Lb ≤ β - α := by
      rw [card_univ, Fintype.card_fin]
      have := h.hn
      have hL0 : 0 ≤ Lb := by linarith [h.hL2]
      have : ((P.k - 1 : ℕ) : ℝ) ≤ ((P.k + 2 * P.r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
      nlinarith
    have h6L : 6 * Lb ≤ β - α := by
      have h1 : (1 : ℝ) ≤ Ntot := by exact_mod_cast h.hNpos
      nlinarith [h.h6, h.hL2]
    have hI0 : 0 < β - α := by linarith
    have hsn : 0 ≤ ∑ x ∈ V, summand P πs Y x := sum_nonneg fun x hx => h.summand_nonneg πs x (hV hx)
    set C := ((univ : Finset (Fin (P.k - 1))).card : ℝ)
    have hC0 : 0 ≤ C := Nat.cast_nonneg _
    have hL0 : 0 ≤ Lb := by linarith [h.hL2]
    calc C * (4 * Real.exp 7 * Lb ^ 2 * ∑ x ∈ V, summand P πs Y x)
        ≤ C * (4 * Real.exp 7 * Lb ^ 2 * (132 / (β - α) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcore' (by positivity)) hC0
      _ = 528 * Real.exp 7 * ((C * Lb) * Lb) / (β - α) ^ 2 := by ring
      _ ≤ 528 * Real.exp 7 * ((β - α) * ((β - α) / 6)) / (β - α) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hcard (by linarith) hL0 hI0.le
      _ = 88 * Real.exp 7 := by field_simp; ring

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y20

section S_R_Y21
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

section
variable {P : M.Par} {l : ℕ} {α β Lb : ℝ} {Ntot : ℕ} {w : List ℝ} {Y s : ℝ}

set_option maxHeartbeats 800000 in
theorem Ctx.let_bound (h : Ctx P l α β Lb Ntot w Y s) (q : Qp P.r P.TT) (v : Iota P w.length → ℂ) :
    ∑ i, dwW P l (Y :: w) q (true, i) * ‖∑ i', dL P w Y (Y + s) (ixOf P w.length i).1 (ixOf P w.length i').1
      (ixOf P w.length i).2 (ixOf P w.length i').2 * v i'‖ ^ 2 ≤
      Real.exp 14 * ∑ i', dwW P l (Y :: w) q (false, i') * ‖v i'‖ ^ 2 := by
  classical
  have hform : ∀ i, ∑ i', dL P w Y (Y + s) (ixOf P w.length i).1 (ixOf P w.length i').1
      (ixOf P w.length i).2 (ixOf P w.length i').2 * v i' =
      ∑ n ∈ (univ : Finset (Fin (wordP w).length)), ∑ i',
        (if (ixOf P w.length i).2 = (ixOf P w.length i').2 ∧
            ((ixOf P w.length i).1 ((wordP w).get n).intersection_update_fsHerm_neg_one = 0 ∧ (ixOf P w.length i').1 ((wordP w).get n).intersection_update_fsHerm_neg_one = 1 ∧
              ∀ b, b ≠ ((wordP w).get n).intersection_update_fsHerm_neg_one → (ixOf P w.length i).1 b = (ixOf P w.length i').1 b) then
          (((Y : ℂ) - ((wordP w).get n).pt)⁻¹ - (((Y + s : ℝ) : ℂ) - ((wordP w).get n).pt)⁻¹) *
            multS ((wordP w).take n) ((wordP w).get n).pt (ixOf P w.length i').1
        else 0) * v i' := by
    intro i
    simp_rw [dL_sparse, sum_mul]
    rw [sum_comm]
  simp_rw [hform]
  have hLpos : 0 < Lb := by linarith [h.hL2]
  refine sparse_bound (ι := Iota P w.length) (α := Fin (wordP w).length) univ
    (fun (n : Fin (wordP w).length) (i i' : Iota P w.length) => (ixOf P w.length i).2 = (ixOf P w.length i').2 ∧
      ((ixOf P w.length i).1 ((wordP w).get n).intersection_update_fsHerm_neg_one = 0 ∧ (ixOf P w.length i').1 ((wordP w).get n).intersection_update_fsHerm_neg_one = 1 ∧
        ∀ b, b ≠ ((wordP w).get n).intersection_update_fsHerm_neg_one → (ixOf P w.length i).1 b = (ixOf P w.length i').1 b))
    (fun n i i₁ i₂ h1 h2 => ixOf_inj P _ _ _ (Prod.ext (by
        funext b
        by_cases hb : b = ((wordP w).get n).intersection_update_fsHerm_neg_one
        · rw [hb, h1.2.2.1, h2.2.2.1]
        · rw [← h1.2.2.2 b hb, ← h2.2.2.2 b hb]) (h1.1.symm.trans h2.1)))
    (fun n i₁ i₂ i' h1 h2 => ixOf_inj P _ _ _ (Prod.ext (by
        funext b
        by_cases hb : b = ((wordP w).get n).intersection_update_fsHerm_neg_one
        · rw [hb, h1.2.1, h2.2.1]
        · rw [h1.2.2.2 b hb, h2.2.2.2 b hb]) (h1.1.trans h2.1.symm)))
    _ _ _ (fun _ _ => Real.exp 14 / Lb ^ 2)
    (fun i => (h.weights_nonneg q i).1) (fun i => (h.weights_nonneg q i).2) ?_ (fun _ _ => by positivity)
    (Real.exp 14) ?_ v
  · intro n _ i i' hPr
    exact h.let_entry q i i' n hPr.1 hPr.2.1 hPr.2.2.1 hPr.2.2.2
  · intro i'
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hwl : ((wordP w).length : ℝ) ≤ Lb := by
      have hwl' : (wordP w).length = w.length := by
        have := congrArg List.length (MAx2.plusWord_points w); simpa using this
      rw [hwl']
      have : (w.length : ℝ) + 1 ≤ Ntot := by exact_mod_cast h.hlen
      linarith [h.hNL]
    have h0 : (0 : ℝ) ≤ (wordP w).length := Nat.cast_nonneg _
    have hsq : ((wordP w).length : ℝ) * (wordP w).length ≤ Lb ^ 2 := by nlinarith
    calc ((wordP w).length : ℝ) * ((wordP w).length * (Real.exp 14 / Lb ^ 2))
        = ((wordP w).length * (wordP w).length) * Real.exp 14 / Lb ^ 2 := by ring
      _ ≤ Lb ^ 2 * Real.exp 14 / Lb ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hsq (Real.exp_pos 14).le
      _ = Real.exp 14 := by field_simp

end

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y21

section S_R_Y22
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.R

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Finset

noncomputable section

theorem norm_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

set_option maxHeartbeats 800000 in
theorem residues : Formalism.FourierDecayAlt.MA.ResiduesQ := by
  refine ⟨Real.sqrt (176 * Real.exp 7 + 2 * Real.exp 14), Real.sqrt_nonneg _, ?_⟩
  intro P l L j lam α β Lb c Ntot hH w hw hl Y s hY hYs (ω : Qp P.r P.TT) (v : Iota P w.length → ℂ)
  rw [Real.sq_sqrt (by positivity)]
  have h := ctx_of P l L j lam α β Lb c Ntot hH w hw hl Y s hY hYs
  have hL : IsModelLevel P (DQ P) L := hH.1.2.2.2.1
  have hee1 := h.ee_at L hL Y h.hYm (fun p hp => (h.hfar p hp).1)
  have hee2 := h.ee_at L hL (Y + s) h.hYsm (fun p hp => (h.hfar p hp).2)
  have hdec : ∀ i i' : Iota P w.length,
      ptMat P ((frW P l L w).ee (Y : ℂ)) ω i i' - ptMat P ((frW P l L w).ee ((Y + s : ℝ) : ℂ)) ω i i' =
        dSS P w Y (Y + s) ω (ixOf P w.length i).1 (ixOf P w.length i').1 (ixOf P w.length i).2 (ixOf P w.length i').2 -
        dL P w Y (Y + s) (ixOf P w.length i).1 (ixOf P w.length i').1 (ixOf P w.length i).2 (ixOf P w.length i').2 := by
    intro i i'
    rw [hee1, hee2, ← evalOne_frame_difference P w L hL Y (Y + s) ω]
    rfl
  show ∑ i, dwW P l (Y :: w) ω (true, i) *
      ‖∑ i', (ptMat P ((frW P l L w).ee (Y : ℂ)) ω i i' - ptMat P ((frW P l L w).ee ((Y + s : ℝ) : ℂ)) ω i i') * v i'‖ ^ 2 ≤
    (176 * Real.exp 7 + 2 * Real.exp 14) * ∑ i, dwW P l (Y :: w) ω (false, i) * ‖v i‖ ^ 2
  simp_rw [hdec, sub_mul, sum_sub_distrib]
  have hS := h.ss_bound ω v
  have hLb := h.let_bound ω v
  calc ∑ i, dwW P l (Y :: w) ω (true, i) *
        ‖∑ i', dSS P w Y (Y + s) ω (ixOf P w.length i).1 (ixOf P w.length i').1 (ixOf P w.length i).2
            (ixOf P w.length i').2 * v i' -
          ∑ i', dL P w Y (Y + s) (ixOf P w.length i).1 (ixOf P w.length i').1 (ixOf P w.length i).2
            (ixOf P w.length i').2 * v i'‖ ^ 2
      ≤ ∑ i, dwW P l (Y :: w) ω (true, i) *
          (2 * ‖∑ i', dSS P w Y (Y + s) ω (ixOf P w.length i).1 (ixOf P w.length i').1 (ixOf P w.length i).2
            (ixOf P w.length i').2 * v i'‖ ^ 2 +
          2 * ‖∑ i', dL P w Y (Y + s) (ixOf P w.length i).1 (ixOf P w.length i').1 (ixOf P w.length i).2
            (ixOf P w.length i').2 * v i'‖ ^ 2) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_sub_sq_le _ _) (h.weights_nonneg ω i).1
    _ = 2 * ∑ i, dwW P l (Y :: w) ω (true, i) *
          ‖∑ i', dSS P w Y (Y + s) ω (ixOf P w.length i).1 (ixOf P w.length i').1 (ixOf P w.length i).2
            (ixOf P w.length i').2 * v i'‖ ^ 2 +
        2 * ∑ i, dwW P l (Y :: w) ω (true, i) *
          ‖∑ i', dL P w Y (Y + s) (ixOf P w.length i).1 (ixOf P w.length i').1 (ixOf P w.length i).2
            (ixOf P w.length i').2 * v i'‖ ^ 2 := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring
    _ ≤ 2 * (88 * Real.exp 7 * ∑ i', dwW P l (Y :: w) ω (false, i') * ‖v i'‖ ^ 2) +
        2 * (Real.exp 14 * ∑ i', dwW P l (Y :: w) ω (false, i') * ‖v i'‖ ^ 2) := by
        gcongr
    _ = (176 * Real.exp 7 + 2 * Real.exp 14) * ∑ i, dwW P l (Y :: w) ω (false, i) * ‖v i‖ ^ 2 := by ring

end

end Formalism.FourierDecayAlt.P.MAx3.R

end S_R_Y22

section S_NF_NF1

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.NF

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

def matC {A : Type} [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) : Subalgebra ℂ (Matrix (Fin 2) (Fin 2) A) where
  carrier := {M | ∀ i j, M i j ∈ Z}
  mul_mem' {a b} ha hb i j := by
    rw [Matrix.mul_apply]; exact Subalgebra.sum_mem _ fun k _ => mul_mem (ha i k) (hb k j)
  add_mem' {a b} ha hb i j := add_mem (ha i j) (hb i j)
  algebraMap_mem' z i j := by
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs
    · exact Z.algebraMap_mem z
    · exact Z.zero_mem

theorem m22C {A : Type} [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (a b c d : A) (ha : a ∈ Z) (hb : b ∈ Z)
    (hc : c ∈ Z) (hd : d ∈ Z) : !![a, b; c, d] ∈ matC Z := by
  intro i j; fin_cases i <;> fin_cases j <;> simpa

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

def FS : Set A := L.fns ∪ Set.range (algebraMap ℂ A)

theorem FS_comm : ∀ x ∈ FS L, ∀ y ∈ FS L, x * y = y * x := by
  rintro x (hx | ⟨a, rfl⟩) y (hy | ⟨b, rfl⟩)
  · exact fc L hx hy
  · exact (Algebra.commutes b x).symm
  · exact Algebra.commutes a y
  · rw [← map_mul, ← map_mul, mul_comm]

theorem memF {x : A} (hx : x ∈ L.fns) : x ∈ Subring.closure (FS L) := Subring.subset_closure (Or.inl hx)
theorem memS (a : ℂ) : algebraMap ℂ A a ∈ Subring.closure (FS L) := Subring.subset_closure (Or.inr ⟨a, rfl⟩)

theorem memDr : L.Dr ∈ Subring.closure (FS L) :=
  Subring.list_prod_mem _ fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_c L i)
theorem memDri : L.Dri ∈ Subring.closure (FS L) :=
  Subring.list_prod_mem _ fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_ci L i)
theorem memDrb : L.Drb ∈ Subring.closure (FS L) :=
  Subring.list_prod_mem _ fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_cb L i)
theorem memDrbi : L.Drbi ∈ Subring.closure (FS L) :=
  Subring.list_prod_mem _ fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_cbi L i)
theorem memD : L.D ∈ Subring.closure (FS L) := Subring.mul_mem _ (memDr L) (memF L (m_ζ L))
theorem memDi : L.Di ∈ Subring.closure (FS L) := Subring.mul_mem _ (memF L (m_ζi L)) (memDri L)
theorem memDb : L.Db ∈ Subring.closure (FS L) := Subring.mul_mem _ (memDrb L) (memF L (m_ζb L))
theorem memDbi : L.Dbi ∈ Subring.closure (FS L) := Subring.mul_mem _ (memF L (m_ζbi L)) (memDrbi L)

theorem comm_cl {z : A} (hz : ∀ x ∈ FS L, z * x = x * z) {y : A} (hy : y ∈ Subring.closure (FS L)) :
    z * y = y * z := by
  induction hy using Subring.closure_induction with
  | mem x hx => exact hz x hx
  | zero => simp
  | one => simp
  | add x y _ _ h1 h2 => rw [mul_add, add_mul, h1, h2]
  | neg x _ h => rw [mul_neg, neg_mul, h]
  | mul x y _ _ h1 h2 => rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem cl_comm {x y : A} (hx : x ∈ Subring.closure (FS L)) (hy : y ∈ Subring.closure (FS L)) : x * y = y * x :=
  comm_cl L (fun w hw => (comm_cl L (fun v hv => FS_comm L w hw v hv) hx).symm) hy

theorem D_Di : L.D * L.Di = 1 := by
  unfold LevelData.D LevelData.Di
  rw [mul_assoc, ← mul_assoc L.ζ, L.ζ_ζi, one_mul, Dr_Dri]
theorem Di_D : L.Di * L.D = 1 := by
  unfold LevelData.D LevelData.Di
  rw [mul_assoc, ← mul_assoc L.Dri, Dri_Dr, one_mul, L.ζi_ζ]
theorem Drb_Dbi : L.Drb * L.Dbi = L.ζbi := by
  unfold LevelData.Dbi
  rw [← mul_assoc, cl_comm L (memDrb L) (memF L (m_ζbi L)), mul_assoc, Drb_Drbi, mul_one]

def la (y : ℂ) : A := L.Di * L.Ahat y

def lb (y : ℂ) : A := L.Dbi * L.R0 y

theorem letters_mem (Z : Subalgebra ℂ A) (hp : ∀ m, L.p m ∈ Z) (hfn : ∀ y ∈ L.fns, y ∈ Z) (hn : L.nab ∈ Z)
    (y : ℂ) : L.Ahat y ∈ Z ∧ L.R0 y ∈ Z ∧ la L y ∈ Z ∧ lb L y ∈ Z := by
  have hT : L.Tprod y ∈ matC Z := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hx)
    exact m22C Z _ _ _ _ (add_mem (Z.algebraMap_mem _) (hp m)) (neg_mem (hfn _ (m_c L m)))
      (hfn _ (m_ci L m)) Z.zero_mem
  have hA : L.Ar y ∈ Z := hT 0 0
  have hB : L.Br y ∈ Z := hT 1 0
  have prodZ : ∀ f : Fin r → A, (∀ i, f i ∈ Z) → (List.ofFn f).prod ∈ Z := fun f hf =>
    Subalgebra.list_prod_mem _ fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact hf i
  have hDr : L.Dr ∈ Z := prodZ _ fun i => hfn _ (m_c L i)
  have hDri : L.Dri ∈ Z := prodZ _ fun i => hfn _ (m_ci L i)
  have hDrb : L.Drb ∈ Z := prodZ _ fun i => hfn _ (m_cb L i)
  have hDrbi : L.Drbi ∈ Z := prodZ _ fun i => hfn _ (m_cbi L i)
  have hAh : L.Ahat y ∈ Z := mul_mem hDr hA
  have hl0 : L.l0 y ∈ Z := sub_mem (neg_mem hn) (mul_mem (Z.algebraMap_mem _)
    (mul_mem (hfn _ (m_ζb L)) (hfn _ (m_GGi L))))
  have hR : L.R0 y ∈ Z := mul_mem (mul_mem hDrb (hfn _ (m_GG L))) (add_mem (mul_mem hl0 hA) hB)
  refine ⟨hAh, hR, mul_mem (mul_mem (hfn _ (m_ζi L)) hDri) hAh, mul_mem (mul_mem (hfn _ (m_ζbi L)) hDrbi) hR⟩

theorem commH (h : A) (hp : ∀ m, L.p m * h = h * L.p m) (hfn : ∀ y ∈ L.fns, y * h = h * y)
    (hn : L.nab * h = h * L.nab) (y : ℂ) :
    la L y * h = h * la L y ∧ lb L y * h = h * lb L y := by
  have mZ : ∀ x : A, x * h = h * x → x ∈ Subalgebra.centralizer ℂ ({h} : Set A) := fun x hx => by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]; exact hx.symm
  obtain ⟨-, -, h1, h2⟩ := letters_mem L (Subalgebra.centralizer ℂ ({h} : Set A)) (fun m => mZ _ (hp m))
    (fun x hx => mZ _ (hfn x hx)) (mZ _ hn) y
  rw [Subalgebra.mem_centralizer_iff] at h1 h2
  exact ⟨(h1 h rfl).symm, (h2 h rfl).symm⟩

end

end Formalism.FourierDecayAlt.P.MAx3.NF

end S_NF_NF1

section S_NF_NF2

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.NF

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

open scoped IsMulCommutative in
instance instCF : CommRing (Subring.closure (FS L)) :=
  have := Subring.isMulCommutative_closure (FS_comm L); inferInstance

theorem hat_Dbi (Y : ℂ) : L.Dbi * L.Ahat Y = L.Ahat Y * L.Dbi ∧ L.Dbi * L.R0 Y = L.R0 Y * L.Dbi := by
  have h := commA L L.Drbi L.Drb (Drbi_Drb L) (Drb_Drbi L)
    (fun m => (comm_prod L.cbi (L.p m) (fun i => L.p_cbi m i)))
    (fun y hy => cl_comm L (memF L hy) (memDrbi L))
    (comm_prod L.cbi L.nab (fun i => L.nab_cbi i)) Y
  have h2 : L.ζbi * L.Ahat Y = L.Ahat Y * L.ζbi ∧ L.ζbi * L.R0 Y = L.R0 Y * L.ζbi :=
    commA L L.ζbi L.ζb L.ζbi_ζb L.ζb_ζbi (fun m => (L.p_ζbi m)) (fun y hy => fc L hy (m_ζbi L))
      L.nab_ζbi Y
  unfold LevelData.Dbi
  constructor
  · rw [mul_assoc, h.1, ← mul_assoc, h2.1, mul_assoc]
  · rw [mul_assoc, h.2, ← mul_assoc, h2.2, mul_assoc]

theorem Ahat_D (Y : ℂ) : L.Ahat Y * L.D = L.D * L.Ahat (Y + 1) := by
  have h := (Formalism.FourierDecayAlt.P.shiftConjugation A r L Y).1
  rw [← h, ← mul_assoc, ← mul_assoc, D_Di, one_mul]

theorem raising_mul_D (Y : ℂ) : L.R0 Y * L.D =
    L.D * (L.R0 (Y + 1) + algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y + 1))) := by
  have h := (Formalism.FourierDecayAlt.P.shiftConjugation A r L Y).2.1
  rw [← h, ← mul_assoc, ← mul_assoc, D_Di, one_mul]

def sn (SS : A) : A := L.Drb * L.Dri * SS

section S
variable (SS : A) (hf : ∀ x ∈ L.fns, x * SS = SS * x) (hp : ∀ l, L.p l * SS = SS * L.p l)
  (hpb : ∀ l, L.pb l * SS = SS * L.pb l) (hn : L.nab * SS = SS * L.nab - L.ζb * L.GGi * SS)
  (hns : L.nabs * SS = SS * L.nabs - L.ζ * L.GGi * SS)
include hf hp hpb hn hns

theorem SS_cl {x : A} (hx : x ∈ Subring.closure (FS L)) : x * SS = SS * x := by
  refine (comm_cl L (z := SS) (fun y hy => ?_) hx).symm
  rcases hy with hy | ⟨a, rfl⟩
  · exact (hf y hy).symm
  · exact (Algebra.commutes a SS).symm

theorem SSn_cl {x : A} (hx : x ∈ Subring.closure (FS L)) :
    x * sn L SS = sn L SS * x := by
  unfold sn
  rw [← mul_assoc, ← mul_assoc, cl_comm L hx (memDrb L), mul_assoc L.Drb, cl_comm L hx (memDri L),
    mul_assoc, mul_assoc, SS_cl L SS hf hp hpb hn hns hx, ← mul_assoc, ← mul_assoc]

theorem ruleSSn (Y : ℂ) : L.Ahat Y * sn L SS = sn L SS * L.Ahat (Y - 1) ∧
    L.R0 Y * sn L SS = sn L SS * L.R0 (Y - 1) := by
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation A r L SS 0 hf hp hpb hn hns (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) Y
  exact ⟨h.1, h.2.1⟩

theorem S_eq : L.ζ * L.ζbi * SS = L.D * L.Dbi * sn L SS :=
  (Formalism.FourierDecayAlt.P.start_ee A r L SS).symm

omit hf hp hpb hn hns in
theorem sw {u v : A} (hu : u ∈ Subring.closure (FS L)) (hv : v ∈ Subring.closure (FS L)) (x : A) :
    u * (v * x) = v * (u * x) := by rw [← mul_assoc, cl_comm L hu hv, mul_assoc]

theorem shift_norm_commute_closure {u : A} (hu : u ∈ Subring.closure (FS L)) (x : A) :
    sn L SS * (u * x) = u * (sn L SS * x) := by
  rw [← mul_assoc, ← SSn_cl L SS hf hp hpb hn hns hu, mul_assoc]

omit hf hp hpb hn hns in
theorem hat_commute_D (y : ℂ) (x : A) : L.Ahat y * (L.D * x) = L.D * (L.Ahat (y + 1) * x) := by
  rw [← mul_assoc, Ahat_D, mul_assoc]

omit hf hp hpb hn hns in
theorem raising_commute_D (y : ℂ) (x : A) : L.R0 y * (L.D * x) = L.D * (L.R0 (y + 1) * x) +
    L.D * (algebraMap ℂ A L.TT * (L.Drb * (L.Di * (L.Ahat (y + 1) * x)))) := by
  rw [← mul_assoc, raising_mul_D]; simp only [mul_add, add_mul, mul_assoc]

omit hf hp hpb hn hns in
theorem D_inv_mul_D (x : A) : L.Di * (L.D * x) = x := by rw [← mul_assoc, Di_D, one_mul]

omit hf hp hpb hn hns in
theorem D_mul_D_inv (x : A) : L.D * (L.Di * x) = x := by rw [← mul_assoc, D_Di, one_mul]

omit hf hp hpb hn hns in
theorem hat_commute_D_bar_inv (y : ℂ) (x : A) : L.Ahat y * (L.Dbi * x) = L.Dbi * (L.Ahat y * x) := by
  rw [← mul_assoc, ← (hat_Dbi L y).1, mul_assoc]

omit hf hp hpb hn hns in
theorem raising_commute_D_bar_inv (y : ℂ) (x : A) : L.R0 y * (L.Dbi * x) = L.Dbi * (L.R0 y * x) := by
  rw [← mul_assoc, ← (hat_Dbi L y).2, mul_assoc]

theorem S_la (y : ℂ) : la L y * (L.ζ * L.ζbi * SS) = (L.ζ * L.ζbi * SS) * la L y := by
  rw [S_eq L SS hf hp hpb hn hns]
  have e1 := (ruleSSn L SS hf hp hpb hn hns (y + 1)).1
  rw [add_sub_cancel_right] at e1
  unfold la
  simp only [mul_assoc]
  rw [hat_commute_D, D_inv_mul_D, hat_commute_D_bar_inv, e1, shift_norm_commute_closure L SS hf hp hpb hn hns (memDi L), sw L (memDbi L) (memDi L), D_mul_D_inv]

theorem S_lb (y : ℂ) : lb L y * (L.ζ * L.ζbi * SS) = (L.ζ * L.ζbi * SS) * lb L y +
    (algebraMap ℂ A L.TT * (L.ζbi * (L.ζ * L.ζbi * SS))) * la L y := by
  rw [S_eq L SS hf hp hpb hn hns]
  have e1 := ruleSSn L SS hf hp hpb hn hns (y + 1)
  rw [add_sub_cancel_right] at e1
  have fid : ∀ x : A, L.Dbi * (L.D * (algebraMap ℂ A L.TT * (L.Drb * (L.Di * (L.Dbi * x))))) =
      algebraMap ℂ A L.TT * (L.ζbi * (L.D * (L.Dbi * (L.Di * x)))) := by
    intro x
    have hz : (⟨L.Drb, memDrb L⟩ : Subring.closure (FS L)) * ⟨L.Dbi, memDbi L⟩ = ⟨L.ζbi, memF L (m_ζbi L)⟩ :=
      Subtype.ext (Drb_Dbi L)
    have h := congrArg Subtype.val (show (⟨L.Dbi, memDbi L⟩ : Subring.closure (FS L)) * ⟨L.D, memD L⟩ *
        (⟨algebraMap ℂ A L.TT, memS L _⟩ * (⟨L.Drb, memDrb L⟩ * ⟨L.Di, memDi L⟩)) * ⟨L.Dbi, memDbi L⟩ =
        ⟨algebraMap ℂ A L.TT, memS L _⟩ * ⟨L.ζbi, memF L (m_ζbi L)⟩ * (⟨L.D, memD L⟩ * ⟨L.Dbi, memDbi L⟩) *
          ⟨L.Di, memDi L⟩ by
      rw [← hz]; ring)
    simp only [Subring.coe_mul] at h
    have h2 := congrArg (· * x) h
    simp only [mul_assoc] at h2
    exact h2
  unfold la lb
  simp only [mul_assoc]
  rw [raising_commute_D, mul_add, raising_commute_D_bar_inv, e1.2, hat_commute_D_bar_inv, e1.1, fid, shift_norm_commute_closure L SS hf hp hpb hn hns (memDbi L),
    shift_norm_commute_closure L SS hf hp hpb hn hns (memDi L), sw L (memDbi L) (memD L)]

end S

end

end Formalism.FourierDecayAlt.P.MAx3.NF

end S_NF_NF2

section S_NF_NF3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.NF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable (P : M.Par) (L : LevelData (A P (DQ P)) P.r)

def gensB : Set (A P (DQ P)) :=
  {L.ζbi} ∪ Set.range (kap P (DQ P)) ∪ (fun i => L.ζ * L.ζbi * SS P (DQ P) i) '' Set.Icc 1 (P.k - 1)

def BB : Subalgebra ℂ (A P (DQ P)) := Algebra.adjoin ℂ (gensB P L)

theorem kap_diag (f : M.Ty P → ℂ) : kap P (DQ P) f = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (f π) := rfl

theorem kap_comm_diag (f : M.Ty P → ℂ) (d : M.Ty P → (DQ P).Pr) :
    Matrix.diagonal d * kap P (DQ P) f = kap P (DQ P) f * Matrix.diagonal d := by
  rw [kap_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext π; exact (Algebra.commutes _ _).symm

section Model
variable {P L} (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L)
include hL

theorem fns_sc : ∀ x ∈ L.fns, ∃ w, x = sc P (DQ P) w := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  intro x hx
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | h)
  · exact ⟨(DQ P).cP l, by rw [hc]; rfl⟩
  · exact ⟨(DQ P).ciP l, by rw [hci]; rfl⟩
  · exact ⟨(DQ P).cbP l, by rw [hcb]; rfl⟩
  · exact ⟨(DQ P).cbiP l, by rw [hcbi]; rfl⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(DQ P).zP, by rw [hz]; rfl⟩
    · exact ⟨(DQ P).ziP, by rw [hzi]; rfl⟩
    · exact ⟨(DQ P).zbP, by rw [hzb]; rfl⟩
    · exact ⟨(DQ P).zbiP, by rw [hzbi]; rfl⟩
    · exact ⟨(DQ P).ggP P.TT, by rw [hg]; rfl⟩
    · exact ⟨(DQ P).ggiP P.TT, by rw [hgi]; rfl⟩

theorem kap_letters (f : M.Ty P → ℂ) (y : ℂ) :
    la L y * kap P (DQ P) f = kap P (DQ P) f * la L y ∧ lb L y * kap P (DQ P) f = kap P (DQ P) f * lb L y := by
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL'
  refine commH L _ (fun m => ?_) (fun x hx => ?_) ?_ y
  · rw [hp]; show sc P (DQ P) _ * _ = _; rw [G.sc_diag]; exact kap_comm_diag P f _
  · obtain ⟨w, rfl⟩ := fns_sc hL x hx; rw [G.sc_diag]; exact kap_comm_diag P f _
  · rw [hn]; exact kap_comm_diag P f _

omit hL in
theorem zbi_letters (y : ℂ) : la L y * L.ζbi = L.ζbi * la L y ∧ lb L y * L.ζbi = L.ζbi * lb L y :=
  commH L L.ζbi (fun m => L.p_ζbi m) (fun x hx => fc L hx (m_ζbi L)) L.nab_ζbi y

include hTT in
theorem SS_hyps (i : ℕ) (hi : i ∈ Set.Icc 1 (P.k - 1)) :
    (∀ x ∈ L.fns, x * SS P (DQ P) i = SS P (DQ P) i * x) ∧ (∀ m, L.p m * SS P (DQ P) i = SS P (DQ P) i * L.p m) ∧
    (∀ m, L.pb m * SS P (DQ P) i = SS P (DQ P) i * L.pb m) ∧
    L.nab * SS P (DQ P) i = SS P (DQ P) i * L.nab - L.ζb * L.GGi * SS P (DQ P) i ∧
    L.nabs * SS P (DQ P) i = SS P (DQ P) i * L.nabs - L.ζ * L.GGi * SS P (DQ P) i := by
  have : Fact ((DQ P).Laws P.TT) := ⟨Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT⟩
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL'
  have hsc : ∀ w, sc P (DQ P) w * SS P (DQ P) i = SS P (DQ P) i * sc P (DQ P) w := fun w =>
    (Formalism.FourierDecayAlt.P.MAx1.sSScalar P (DQ P) i w).symm.eq
  have hi' : i ∈ Finset.Icc 1 (P.k - 1) := by simpa using hi
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.MAx1.nabSS P (DQ P) i hi'
  refine ⟨fun x hx => ?_, fun m => ?_, fun m => ?_, ?_, ?_⟩
  · obtain ⟨w, rfl⟩ := fns_sc hL x hx; exact hsc w
  · rw [hp]; exact hsc _
  · rw [hpb]; exact hsc _
  · rw [hn, hzb, hgi]; exact h1
  · rw [hns, hz, hgi]; exact h2

include hTT in

theorem BB_la {β : A P (DQ P)} (hβ : β ∈ BB P L) (y : ℂ) : la L y * β = β * la L y := by
  have hle : BB P L ≤ Subalgebra.centralizer ℂ ({la L y} : Set (A P (DQ P))) := by
    refine Algebra.adjoin_le fun g hg => ?_
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    rcases hg with (hg | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [Set.mem_singleton_iff.1 hg]; exact (zbi_letters y).1
    · exact (kap_letters hL f y).1
    · obtain ⟨h1, h2, h3, h4, h5⟩ := SS_hyps hTT hL i hi
      exact S_la L _ h1 h2 h3 h4 h5 y
  have := hle hβ
  rw [Subalgebra.mem_centralizer_iff] at this
  exact this _ rfl

include hTT in

theorem BB_lb {β : A P (DQ P)} (hβ : β ∈ BB P L) :
    ∃ β' ∈ BB P L, ∀ y : ℂ, lb L y * β = β * lb L y + β' * la L y := by
  induction hβ using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with (hg | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [Set.mem_singleton_iff.1 hg]
      exact ⟨0, Subalgebra.zero_mem _, fun y => by rw [zero_mul, add_zero]; exact (zbi_letters y).2⟩
    · exact ⟨0, Subalgebra.zero_mem _, fun y => by rw [zero_mul, add_zero]; exact (kap_letters hL f y).2⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := SS_hyps hTT hL i hi
      refine ⟨algebraMap ℂ (A P (DQ P)) L.TT * (L.ζbi * (L.ζ * L.ζbi * SS P (DQ P) i)), ?_,
        fun y => S_lb L _ h1 h2 h3 h4 h5 y⟩
      refine mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Algebra.subset_adjoin ?_) (Algebra.subset_adjoin ?_))
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨i, hi, rfl⟩
  | algebraMap z =>
    exact ⟨0, Subalgebra.zero_mem _, fun y => by rw [zero_mul, add_zero]; exact (Algebra.commutes z _).symm⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨x', hx', ex⟩ := ihx
    obtain ⟨y', hy', ey⟩ := ihy
    exact ⟨x' + y', add_mem hx' hy', fun t => by rw [mul_add, ex, ey, add_mul, add_mul]; abel⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨x', hx', ex⟩ := ihx
    obtain ⟨y', hy', ey⟩ := ihy
    refine ⟨x * y' + x' * y, add_mem (mul_mem hx hy') (mul_mem hx' hy), fun t => ?_⟩
    rw [← mul_assoc, ex, add_mul, mul_assoc, ey, mul_assoc x', BB_la hTT hL hy t]
    simp only [mul_add, add_mul, mul_assoc]
    abel

end Model

end

end Formalism.FourierDecayAlt.P.MAx3.NF

end S_NF_NF3

section S_NF_NF4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.NF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r)

section Frame
variable {S : Type} [Fintype S] [DecidableEq S]

abbrev UB (S : Type) [Fintype S] [DecidableEq S] : Subalgebra ℂ (SlopeTestRemainingChoices S (A P (DQ P))) :=
  MAx2.Jet.matSub (BB P L) (Ix S)

theorem io_memB {x : A P (DQ P)} (h : x ∈ BB P L) : (io x : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB P L S :=
  MAx2.Jet.scalar_mem _ _ h

theorem eU_memB (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB P L S := fun x y => by
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem insert_two_mem_bounded (a : S) (x y z w : SlopeTestRemainingChoices S (A P (DQ P))) (hx : x ∈ UB P L S) (hy : y ∈ UB P L S)
    (hz : z ∈ UB P L S) (hw : w ∈ UB P L S) : ins a !![x, y; z, w] ∈ UB P L S :=
  Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
    mul_mem (eU_memB P L a i j) (MAx2.Jet.matrix_two_mem_sub (UB P L S) x y z w hx hy hz hw i j)

theorem kap_memB (f : M.Ty P → ℂ) : kap P (DQ P) f ∈ BB P L :=
  Algebra.subset_adjoin (Or.inl (Or.inr ⟨f, rfl⟩))

theorem zbi_memB : L.ζbi ∈ BB P L := Algebra.subset_adjoin (Or.inl (Or.inl rfl))

variable {P L} (hL : IsModelLevel P (DQ P) L)
include hL

theorem eeA_memB (Y : ℂ) : eeA P (DQ P) Y ∈ BB P L := by
  have hL' := hL
  obtain ⟨-, -, -, -, -, -, hz, -, -, hzbi, -⟩ := hL'
  unfold eeA
  rw [← hz, ← hzbi, Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun j hj => ?_
  have hc : L.ζ * L.ζbi * (kap P (DQ P) fun π => (Y + (M.rho P π j : ℂ))⁻¹) =
      (kap P (DQ P) fun π => (Y + (M.rho P π j : ℂ))⁻¹) * (L.ζ * L.ζbi) := by
    obtain ⟨w1, e1⟩ := fns_sc hL L.ζ (by simp [LevelData.fns])
    obtain ⟨w2, e2⟩ := fns_sc hL L.ζbi (by simp [LevelData.fns])
    rw [e1, e2, G.sc_mul, G.sc_diag]
    exact kap_comm_diag P _ _
  rw [← mul_assoc, hc, mul_assoc]
  refine mul_mem (kap_memB P L _) (Algebra.subset_adjoin (Or.inr ⟨j, ?_, by simp only [mul_assoc]⟩))
  simpa using hj

theorem frame_memB :
    ∀ w : List (Letter ℂ S), (∀ Y, (ofWord L (startM P (DQ P) l) w).ee Y ∈ UB P L S) ∧
      (∀ Y, (ofWord L (startM P (DQ P) l) w).x Y ∈ UB P L S) ∧ (∀ Y, (ofWord L (startM P (DQ P) l) w).xi Y ∈ UB P L S)
  | [] => by
    refine ⟨fun Y => io_memB P L (eeA_memB hL Y), fun Y => io_memB P L (kap_memB P L _),
      fun Y => io_memB P L (kap_memB P L _)⟩
  | lt :: w => by
    obtain ⟨he, hx, hxi⟩ := frame_memB w
    have htz : (tz L : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB P L S := io_memB P L (Subalgebra.smul_mem _ (zbi_memB P L) _)
    have hDD : ∀ Y Ya, (ofWord L (startM P (DQ P) l) w).DD Y Ya ∈ UB P L S := fun Y Ya =>
      Subalgebra.smul_mem _ (sub_mem (he Y) (he Ya)) _
    have h1 : (1 : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB P L S := Subalgebra.one_mem _
    have h0 : (0 : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB P L S := Subalgebra.zero_mem _
    simp only [ofWord]
    split_ifs
    · refine ⟨fun Y => ?_, fun Y => ?_, fun Y => ?_⟩
      · exact insert_two_mem_bounded P L _ _ _ _ _ (add_mem (sub_mem (he Y) (hDD Y _)) htz) (neg_mem (Subalgebra.smul_mem _ h1 _)) h0
          (mul_mem (mul_mem (hxi _) (he Y)) (hx _))
      · exact mul_mem (hx Y) (insert_two_mem_bounded P L _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
      · exact mul_mem (hxi Y) (insert_two_mem_bounded P L _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
    · refine ⟨fun Y => ?_, fun Y => ?_, fun Y => ?_⟩
      · exact insert_two_mem_bounded P L _ _ _ _ _ (he Y) h0 (neg_mem (Subalgebra.smul_mem _ (mul_mem (hxi _) (hxi _)) _))
          (add_mem (sub_mem (mul_mem (mul_mem (hxi _) (he Y)) (hx _)) (hDD Y _)) htz)
      · exact mul_mem (hx Y) (insert_two_mem_bounded P L _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
      · exact mul_mem (hxi Y) (insert_two_mem_bounded P L _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)

end Frame

open Classical in

def deB (β : A P (DQ P)) : A P (DQ P) :=
  if h : ∃ β' ∈ BB P L, ∀ y : ℂ, lb L y * β = β * lb L y + β' * la L y then Classical.choose h else 0

theorem deB_spec {P L} (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L) {β : A P (DQ P)} (hβ : β ∈ BB P L) :
    deB P L β ∈ BB P L ∧ ∀ y : ℂ, lb L y * β = β * lb L y + deB P L β * la L y := by
  have h := BB_lb hTT hL hβ
  unfold deB
  rw [dif_pos h]
  exact Classical.choose_spec h

def deM {S : Type} [Fintype S] [DecidableEq S] (B : SlopeTestRemainingChoices S (A P (DQ P))) : SlopeTestRemainingChoices S (A P (DQ P)) :=
  Matrix.of fun e e' => deB P L (B e e')

theorem io_mul_entry {S : Type} [Fintype S] [DecidableEq S] (x : A P (DQ P)) (B : SlopeTestRemainingChoices S (A P (DQ P))) (e e' : Ix S) :
    ((io x : SlopeTestRemainingChoices S (A P (DQ P))) * B) e e' = x * B e e' := by
  simp [io, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem mul_io_entry {S : Type} [Fintype S] [DecidableEq S] (x : A P (DQ P)) (B : SlopeTestRemainingChoices S (A P (DQ P))) (e e' : Ix S) :
    (B * (io x : SlopeTestRemainingChoices S (A P (DQ P)))) e e' = B e e' * x := by
  simp [io, Matrix.scalar_apply, Matrix.mul_diagonal]

section Rec
variable {P L} (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L)
include hTT hL

theorem deM_spec {S : Type} [Fintype S] [DecidableEq S] {B : SlopeTestRemainingChoices S (A P (DQ P))} (hB : B ∈ UB P L S) :
    deM P L B ∈ UB P L S ∧ ∀ y : ℂ, io (lb L y) * B = B * io (lb L y) + deM P L B * io (la L y) := by
  refine ⟨fun e e' => (deB_spec hTT hL (hB e e')).1, fun y => ?_⟩
  ext e e' : 1
  rw [io_mul_entry, Matrix.add_apply, mul_io_entry, mul_io_entry]
  exact (deB_spec hTT hL (hB e e')).2 y

theorem la_comm {S : Type} [Fintype S] [DecidableEq S] {B : SlopeTestRemainingChoices S (A P (DQ P))} (hB : B ∈ UB P L S) (y : ℂ) :
    io (la L y) * B = B * io (la L y) := by
  ext e e' : 1
  rw [io_mul_entry, mul_io_entry]
  exact BB_la hTT hL (hB e e') y

end Rec

def ext2 {N : ℕ} (c00 c01 c10 c11 : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) : SlopeTestRemainingChoices (Fin (N + 1)) (A P (DQ P)) :=
  Matrix.of fun x y => (if x (Fin.last N) = 0 then (if y (Fin.last N) = 0 then c00 else c01)
    else (if y (Fin.last N) = 0 then c10 else c11)) (Fin.init x) (Fin.init y)

theorem block_extend_mem {N : ℕ} {c00 c01 c10 c11 : SlopeTestRemainingChoices (Fin N) (A P (DQ P))} (h00 : c00 ∈ UB P L (Fin N))
    (h01 : c01 ∈ UB P L (Fin N)) (h10 : c10 ∈ UB P L (Fin N)) (h11 : c11 ∈ UB P L (Fin N)) :
    ext2 P c00 c01 c10 c11 ∈ UB P L (Fin (N + 1)) := fun x y => by
  simp only [ext2, Matrix.of_apply]
  split_ifs
  · exact h00 _ _
  · exact h01 _ _
  · exact h10 _ _
  · exact h11 _ _

theorem apply_block_extend {N : ℕ} (c00 c01 c10 c11 : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (V : Qp P.r P.TT → Iota P (N + 1) → ℂ)
    (q : Qp P.r P.TT) (bi : Iota P (N + 1)) :
    wordModuleApply P (ext2 P c00 c01 c10 c11) V q bi =
      wordModuleApply P (if bi.1 then c10 else c00) (fun q' i' => V q' (false, i')) q bi.2 +
        wordModuleApply P (if bi.1 then c11 else c01) (fun q' i' => V q' (true, i')) q bi.2 := by
  obtain ⟨b, i⟩ := bi
  simp only [wordModuleApply]
  rw [← (Fin.snocEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1
  · refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun π' _ => ?_
    cases b <;> simp [ext2, ixOf, iotaOf, Fin.snocEquiv, Fin.snoc_last, Fin.init_snoc]
  · refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun π' _ => ?_
    cases b <;> simp [ext2, ixOf, iotaOf, Fin.snocEquiv, Fin.snoc_last, Fin.init_snoc]

end

end Formalism.FourierDecayAlt.P.MAx3.NF

end S_NF_NF4

section S_NF_NF5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.NF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r)

def Bm : (w : List ℝ) → SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))
  | [] => 1
  | y :: w => ext2 P (Bm w) 0 (deM P L (Bm w) + (frW P l L w).ee (y : ℂ) * Bm w) (Bm w)

def monL (u : Qp P.r P.TT → M.Ty P → ℂ) (t : ℝ) : (w : List ℝ) → Qp P.r P.TT → Iota P w.length → ℂ
  | [] => u
  | y :: w => fun q bi =>
      wordModuleApply P (io (if bi.1 then lb L ((y : ℂ) + t) else la L ((y : ℂ) + t))) (monL u t w) q bi.2

theorem monL_mem (u : Qp P.r P.TT → M.Ty P → ℂ) (hu : ∀ π, (fun q => u q π) ∈ smSub P.r P.TT) (t : ℝ) :
    ∀ (w : List ℝ) (i : Iota P w.length), (fun q => monL P L u t w q i) ∈ smSub P.r P.TT
  | [], i => hu i
  | y :: w, bi => G.apply_matrix_smooth P _ _ _

theorem one_eq_io {S : Type} [Fintype S] [DecidableEq S] :
    (1 : SlopeTestRemainingChoices S (A P (DQ P))) = io (sc P (DQ P) ((DQ P).fnP 1 1)) := by
  rw [MAx1.multiplierPair_one]; unfold io sc; rw [map_one, map_one]

theorem apply_matrix_one {N : ℕ} (U : Qp P.r P.TT → Iota P N → ℂ) (hU : ∀ i, (fun q => U q i) ∈ smSub P.r P.TT)
    (q : Qp P.r P.TT) (i : Iota P N) : wordModuleApply P 1 U q i = U q i := by
  rw [one_eq_io]
  refine (G.apply_matrix_function P 1 1 U hU q i).trans ?_
  show (1 : ℂ) * U q i = U q i
  rw [one_mul]

section Model
variable {P l L} (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L)
include hTT hL

theorem Bm_mem : ∀ w : List ℝ, Bm P l L w ∈ UB P L (Fin w.length)
  | [] => Subalgebra.one_mem _
  | y :: w => by
    have ih := Bm_mem w
    exact block_extend_mem P L ih (Subalgebra.zero_mem _)
      (add_mem (deM_spec hTT hL ih).1 (mul_mem ((frame_memB l hL (wordP w)).1 _) ih)) ih

theorem Xw_eq (u : Qp P.r P.TT → M.Ty P → ℂ) (hu : ∀ π, (fun q => u q π) ∈ smSub P.r P.TT) :
    ∀ (w : List ℝ) (q : Qp P.r P.TT) (i : Iota P w.length),
      Xw P l L u w q i = wordModuleApply P (Bm P l L w) (monL P L u 0 w) q i
  | [], q, i => (apply_matrix_one (N := 0) P u (fun i => hu i) q i).symm
  | y :: w, q, bi => by
    have ih : Xw P l L u w = wordModuleApply P (Bm P l L w) (monL P L u 0 w) :=
      funext fun q => funext fun i => Xw_eq u hu w q i
    have hB := Bm_mem (l := l) hTT hL w
    show wordModuleApply P (if bi.1 then g2 P l L w y else g1 P L w y) (Xw P l L u w) q bi.2 =
      wordModuleApply P (ext2 P (Bm P l L w) 0 (deM P L (Bm P l L w) + (frW P l L w).ee (y : ℂ) * Bm P l L w)
        (Bm P l L w)) (monL P L u 0 (y :: w)) q bi
    rw [apply_block_extend, ih, ← G.apply_matrix_mul]
    have e0 : (fun q' i' => monL P L u 0 (y :: w) q' (false, i')) =
        wordModuleApply P (io (la L (y : ℂ))) (monL P L u 0 w) := by
      funext q' i'; show wordModuleApply P (io (if false then _ else _)) _ _ _ = _; simp
    have e1 : (fun q' i' => monL P L u 0 (y :: w) q' (true, i')) =
        wordModuleApply P (io (lb L (y : ℂ))) (monL P L u 0 w) := by
      funext q' i'; show wordModuleApply P (io (if true then _ else _)) _ _ _ = _; simp
    rw [e0, e1, ← G.apply_matrix_mul, ← G.apply_matrix_mul]
    rcases bi with ⟨b, i⟩
    cases b
    · simp only [Bool.false_eq_true, if_false, g1]
      rw [zero_mul, G.apply_matrix_zero, add_zero]
      show wordModuleApply P (io (la L (y : ℂ)) * Bm P l L w) _ q i = _
      rw [la_comm hTT hL hB]
    · simp only [if_true, g2]
      have hlb := (deM_spec hTT hL hB).2 (y : ℂ)
      have e : (io (L.Dbi * L.R0 (y : ℂ)) + (frW P l L w).ee (y : ℂ) * io (L.Di * L.Ahat (y : ℂ)) :
          SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))) * Bm P l L w =
          (deM P L (Bm P l L w) + (frW P l L w).ee (y : ℂ) * Bm P l L w) * io (la L (y : ℂ)) +
            Bm P l L w * io (lb L (y : ℂ)) := by
        show (io (lb L (y : ℂ)) + (frW P l L w).ee (y : ℂ) * io (la L (y : ℂ))) * Bm P l L w = _
        rw [add_mul, hlb, mul_assoc, la_comm hTT hL hB, add_mul, ← mul_assoc]
        abel
      rw [e, G.apply_matrix_add]

theorem Xw_pt (u : Qp P.r P.TT → M.Ty P → ℂ) (hu : ∀ π, (fun q => u q π) ∈ smSub P.r P.TT) (w : List ℝ)
    (hBB : BB P L ≤ G.BaseMatrixAlgebra P) (q : Qp P.r P.TT) (i : Iota P w.length) :
    Xw P l L u w q i = ∑ k, ptMat P (Bm P l L w) q i k * monL P L u 0 w q k := by
  rw [Xw_eq hTT hL u hu w q i]
  exact G.apply_matrix_pointwise P _ (fun e e' => hBB (Bm_mem (l := l) hTT hL w e e')) _ (monL_mem P L u hu 0 w) q i

theorem monL_conj (u : Qp P.r P.TT → M.Ty P → ℂ) (hu : ∀ π, (fun q => u q π) ∈ smSub P.r P.TT) (s : ℝ) :
    ∀ (w : List ℝ) (t : ℝ) (q : Qp P.r P.TT) (k : Iota P w.length),
      monL P L (fun q π => ((Gq P q ^ s : ℝ) : ℂ) * u q π) t w q k =
        ((Gq P q ^ s : ℝ) : ℂ) * monL P L u (t + s) w q k
  | [], t, q, k => rfl
  | y :: w, t, q, bi => by
    have ih : monL P L (fun q π => ((Gq P q ^ s : ℝ) : ℂ) * u q π) t w =
        wordModuleApply P (io (G.Gs P s)) (monL P L u (t + s) w) := by
      funext q' k'
      rw [monL_conj u hu s w t q' k', G.apply_matrix_gamma_power P s _ (monL_mem P L u hu (t + s) w) q' k']
    obtain ⟨b, i⟩ := bi
    obtain ⟨hDi, hDbi⟩ := G.D_comm hTT hL s
    have hc : ((y : ℂ) + t) + s = (y : ℂ) + ((t + s : ℝ) : ℂ) := by push_cast; ring
    show wordModuleApply P (io (if b then lb L ((y : ℂ) + t) else la L ((y : ℂ) + t))) _ q i =
      _ * wordModuleApply P (io (if b then lb L ((y : ℂ) + ((t + s : ℝ) : ℂ)) else la L ((y : ℂ) + ((t + s : ℝ) : ℂ)))) _ q i
    rw [ih, ← G.apply_matrix_mul, ← G.io_mul]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      have e : la L ((y : ℂ) + t) * G.Gs P s = G.Gs P s * la L ((y : ℂ) + ((t + s : ℝ) : ℂ)) := by
        unfold la
        rw [mul_assoc, (G.hat_Gs hTT hL s _).1, ← mul_assoc, hDi.eq, mul_assoc, hc]
      rw [e, G.io_mul, G.apply_matrix_gamma_power_left]
    · simp only [if_true]
      have e : lb L ((y : ℂ) + t) * G.Gs P s = G.Gs P s * lb L ((y : ℂ) + ((t + s : ℝ) : ℂ)) := by
        unfold lb
        rw [mul_assoc, (G.hat_Gs hTT hL s _).2, ← mul_assoc, hDbi.eq, mul_assoc, hc]
      rw [e, G.io_mul, G.apply_matrix_gamma_power_left]

end Model

end

end Formalism.FourierDecayAlt.P.MAx3.NF

end S_NF_NF5

section S_NF_NF6

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.NF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r)

theorem scalar_projection_apply {x : (DQ P).Pr} (hx : x ∈ G.pr0 P) (g : (DQ P).R) : x.1 g = x.1 1 * g := by
  obtain ⟨f, hf⟩ := hx
  rw [hf]
  simp [DAlg.mulOp]

theorem ent_mul {a : A P (DQ P)} (ha : a ∈ G.BaseMatrixAlgebra P) (b : A P (DQ P)) (π π'' : M.Ty P) (q : Qp P.r P.TT) :
    evQ P (((a * b) π π'').1 1) q = ∑ π', evQ P ((a π π').1 1) q * evQ P ((b π' π'').1 1) q := by
  rw [Matrix.mul_apply, G.pfst_sum, LinearMap.sum_apply]
  refine (MAx2.Jet.evQ_sum P _ _ q).trans (Finset.sum_congr rfl fun π' _ => ?_)
  show evQ P ((a π π').1 ((b π' π'').1 1)) q = _
  rw [scalar_projection_apply P (ha π π')]
  rfl

theorem ent_add (a b : A P (DQ P)) (π π' : M.Ty P) (q : Qp P.r P.TT) :
    evQ P (((a + b) π π').1 1) q = evQ P ((a π π').1 1) q + evQ P ((b π π').1 1) q := by
  rw [Matrix.add_apply, G.pfst_add, LinearMap.add_apply]
  rfl

def bddA : Subalgebra ℂ (A P (DQ P)) where
  carrier := {β | β ∈ G.BaseMatrixAlgebra P ∧ ∃ C : ℝ, ∀ π π' q, ‖evQ P ((β π π').1 1) q‖ ≤ C}
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    obtain ⟨Ca, hCa⟩ := ha.2
    obtain ⟨Cb, hCb⟩ := hb.2
    refine ⟨Fintype.card (M.Ty P) * (Ca * Cb), fun π π'' q => ?_⟩
    rw [ent_mul P ha.1]
    refine (norm_sum_le _ _).trans ?_
    have h : ∀ π' ∈ (Finset.univ : Finset (M.Ty P)),
        ‖evQ P ((a π π').1 1) q * evQ P ((b π' π'').1 1) q‖ ≤ Ca * Cb := by
      intro π' _
      rw [norm_mul]
      exact mul_le_mul (hCa _ _ _) (hCb _ _ _) (norm_nonneg _) ((norm_nonneg _).trans (hCa π π' q))
    refine (Finset.sum_le_sum h).trans ?_
    simp
  add_mem' {a b} ha hb := by
    refine ⟨add_mem ha.1 hb.1, ?_⟩
    obtain ⟨Ca, hCa⟩ := ha.2
    obtain ⟨Cb, hCb⟩ := hb.2
    refine ⟨Ca + Cb, fun π π' q => ?_⟩
    rw [ent_add]
    exact (norm_add_le _ _).trans (add_le_add (hCa _ _ _) (hCb _ _ _))
  algebraMap_mem' z := by
    refine ⟨Subalgebra.algebraMap_mem _ z, ‖z‖, fun π π' q => ?_⟩
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs
    · rw [G.pfst_alg]
      show ‖evQ P (z • (1 : SmQ P.r P.TT)) q‖ ≤ ‖z‖
      rw [G.evQ_smul, show evQ P (1 : SmQ P.r P.TT) q = 1 from rfl, norm_mul, norm_one, mul_one]
    · show ‖(0 : ℂ)‖ ≤ ‖z‖
      simp

theorem ev_coord_inv (hTT : 0 ≤ P.TT) (v : M.Var P.r) (q : Qp P.r P.TT) :
    evQ P (Ring.inverse (coordQ (TT := P.TT) v)) q = (coordE v q.1)⁻¹ :=
  MAx2.Jet.ev_inverse P _ ((Formalism.FourierDecayAlt.P.analytic_units_hold P.r P.TT hTT).1 v) q

theorem sc_entry (w : (DQ P).Pr) (π π' : M.Ty P) : (sc P (DQ P) w) π π' = if π = π' then w else 0 := by
  rw [G.sc_diag, Matrix.diagonal_apply]

theorem sc_bdd (f fb : SmQ P.r P.TT) (C : ℝ) (h : ∀ q, ‖evQ P f q‖ ≤ C) (hC : 0 ≤ C) :
    sc P (DQ P) ((DQ P).fnP f fb) ∈ bddA P := by
  refine ⟨G.scalar_mem_base P (G.function_mem_base P f fb), C, fun π π' q => ?_⟩
  rw [sc_entry]
  split_ifs
  · show ‖evQ P (f * 1) q‖ ≤ C
    rw [mul_one]; exact h q
  · show ‖(0 : ℂ)‖ ≤ C
    simpa using hC

variable {P L} in
theorem BB_le (hTT : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) : BB P L ≤ bddA P := by
  have hL' := hL
  obtain ⟨-, -, -, -, -, -, hz, -, -, hzbi, -⟩ := hL'
  have hzbiB : L.ζbi ∈ bddA P := by
    rw [hzbi]
    refine sc_bdd P _ _ (Real.sqrt P.TT)⁻¹ (fun q => ?_) (by positivity)
    show ‖evQ P (Ring.inverse (coordQ (TT := P.TT) M.vzb)) q‖ ≤ _
    rw [ev_coord_inv P hTT.le, coordE_vzb, norm_inv, Complex.norm_conj]
    have h1 : P.TT < Complex.normSq q.1.2 := q.2.2
    rw [Complex.normSq_eq_norm_sq] at h1
    have h2 : Real.sqrt P.TT < ‖q.1.2‖ := by
      rw [show ‖q.1.2‖ = Real.sqrt (‖q.1.2‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_lt_sqrt hTT.le h1
    exact inv_anti₀ (Real.sqrt_pos.2 hTT) h2.le
  have hzzB : L.ζ * L.ζbi ∈ bddA P := by
    rw [hz, hzbi]
    show sc P (DQ P) (DAlg.fnP (DQ P) _ _) * sc P (DQ P) (DAlg.fnP (DQ P) _ _) ∈ bddA P
    rw [G.sc_mul, MAx1.multiplierPair_mul]
    refine sc_bdd P (coordQ (TT := P.TT) M.vz * Ring.inverse (coordQ (TT := P.TT) M.vzb)) _ 1 (fun q => ?_) zero_le_one
    show ‖evQ P (coordQ (TT := P.TT) M.vz) q * evQ P (Ring.inverse (coordQ (TT := P.TT) M.vzb)) q‖ ≤ 1
    rw [ev_coord_inv P hTT.le]
    show ‖coordE M.vz q.1 * (coordE M.vzb q.1)⁻¹‖ ≤ 1
    rw [coordE_vz, coordE_vzb, norm_mul, norm_inv, Complex.norm_conj]
    by_cases h : ‖q.1.2‖ = 0
    · rw [h]; simp
    · rw [mul_inv_cancel₀ h]
  have hkap : ∀ f : M.Ty P → ℂ, kap P (DQ P) f ∈ bddA P := fun f => by
    refine ⟨G.kappa_mem_base P f, ∑ π, ‖f π‖, fun π π' q => ?_⟩
    rw [kap_diag, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rw [G.pfst_alg]
      show ‖evQ P (f π • (1 : SmQ P.r P.TT)) q‖ ≤ _
      rw [G.evQ_smul, show evQ P (1 : SmQ P.r P.TT) q = 1 from rfl, norm_mul, norm_one, mul_one]
      exact Finset.single_le_sum (f := fun π => ‖f π‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ π)
    · show ‖(0 : ℂ)‖ ≤ _
      rw [norm_zero]
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSS : ∀ i, SS P (DQ P) i ∈ bddA P := fun i => by
    refine ⟨G.shift_matrix_mem_base P i, ∑ π, ∑ π' : M.Ty P, |Real.sqrt (M.Nrm P i π)|, fun π π' q => ?_⟩
    simp only [SS, Matrix.of_apply]
    split_ifs
    · rw [G.pfst_alg]
      show ‖evQ P ((((Real.sqrt (M.Nrm P i π') : ℝ) : ℂ)) • (1 : SmQ P.r P.TT)) q‖ ≤ _
      rw [G.evQ_smul, show evQ P (1 : SmQ P.r P.TT) q = 1 from rfl, mul_one, Complex.norm_real, Real.norm_eq_abs]
      refine le_trans ?_ (Finset.single_le_sum (f := fun π => ∑ π' : M.Ty P, |Real.sqrt (M.Nrm P i π)|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ π'))
      exact le_trans (le_of_eq (by simp)) (Finset.single_le_sum (f := fun _ => |Real.sqrt (M.Nrm P i π')|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ π'))
    · show ‖(0 : ℂ)‖ ≤ _
      rw [norm_zero]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Algebra.adjoin_le fun g hg => ?_
  rcases hg with (hg | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩
  · rw [Set.mem_singleton_iff.1 hg]; exact hzbiB
  · exact hkap f
  · exact mul_mem hzzB (hSS i)

variable {P L} in
theorem bounded_sub_base_algebra (hTT : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) : BB P L ≤ G.BaseMatrixAlgebra P :=
  fun β hβ => (BB_le hTT hL hβ).1

end

end Formalism.FourierDecayAlt.P.MAx3.NF

end S_NF_NF6

section S_NF_NF7

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.NF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r)

theorem const_mem (c : ℂ) : (fun _ : Qp P.r P.TT => c) ∈ smSub P.r P.TT := by
  have h : (fun _ : Qp P.r P.TT => c) = algebraMap ℂ (Qp P.r P.TT → ℂ) c := by funext x; simp
  rw [h]; exact (smSub P.r P.TT).algebraMap_mem c

theorem ptMat_mul {N : ℕ} (b c : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (hb : b ∈ G.BlockMatrixAlgebra P (Fin N)) (hc : c ∈ G.BlockMatrixAlgebra P (Fin N))
    (q : Qp P.r P.TT) (i k : Iota P N) :
    ptMat P (b * c) q i k = ∑ j, ptMat P b q i j * ptMat P c q j k := by
  classical
  let U : Qp P.r P.TT → Iota P N → ℂ := fun _ i' => if i' = k then 1 else 0
  have hU : ∀ i', (fun q => U q i') ∈ smSub P.r P.TT := fun i' => const_mem P _
  have h1 := G.apply_matrix_pointwise P (b * c) (mul_mem hb hc) U hU q i
  rw [G.apply_matrix_mul, G.apply_matrix_pointwise P b hb _ (fun i' => G.apply_matrix_smooth P c U i') q i] at h1
  simp only [U, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [G.apply_matrix_pointwise P c hc U hU q j]
  simp [U]

open Classical in
theorem ptMat_one {N : ℕ} (q : Qp P.r P.TT) (i k : Iota P N) :
    ptMat P (1 : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) q i k = if i = k then 1 else 0 := by
  classical
  let U : Qp P.r P.TT → Iota P N → ℂ := fun _ i' => if i' = k then 1 else 0
  have hU : ∀ i', (fun q => U q i') ∈ smSub P.r P.TT := fun i' => const_mem P _
  have h1 := G.apply_matrix_pointwise P (1 : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (Subalgebra.one_mem _) U hU q i
  rw [apply_matrix_one P U hU q i] at h1
  simp only [U, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  exact h1.symm

theorem eq_iff_last {N : ℕ} (x y : Ix (Fin (N + 1))) :
    x = y ↔ Fin.init x = Fin.init y ∧ x (Fin.last N) = y (Fin.last N) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, h1, h2]

theorem fin2 (c : Fin 2) : c = 0 ∨ c = 1 := by fin_cases c <;> simp

theorem block_extend_one {N : ℕ} : ext2 P (1 : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) 0 0 1 = 1 := by
  ext x y : 1
  simp only [ext2, Matrix.of_apply, Matrix.one_apply, eq_iff_last x y]
  rcases fin2 (x (Fin.last N)) with hx | hx <;> rcases fin2 (y (Fin.last N)) with hy | hy <;>
    simp [hx, hy, Matrix.one_apply]

theorem splitPlaneIdentityExtension_mul {N : ℕ} (a b c d a' b' c' d' : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) :
    ext2 P a b c d * ext2 P a' b' c' d' =
      ext2 P (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  ext x z : 1
  have hs : ∀ (c : Fin 2) (e : Ix (Fin N)), (Fin.snocEquiv (fun _ => Fin 2)) (c, e) = Fin.snoc e c := fun c e => rfl
  rw [Matrix.mul_apply, ← (Fin.snocEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [hs, ext2, Matrix.of_apply, Fin.snoc_last, Fin.init_snoc, Matrix.add_apply, Matrix.mul_apply]
  rcases fin2 (x (Fin.last N)) with hx | hx <;> rcases fin2 (z (Fin.last N)) with hz | hz <;>
    simp [hx, hz, Matrix.mul_apply]

def Bi : (w : List ℝ) → SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))
  | [] => 1
  | y :: w => ext2 P (Bi w) 0
      (-(Bi w * (deM P L (Bm P l L w) + (frW P l L w).ee (y : ℂ) * Bm P l L w) * Bi w)) (Bi w)

theorem Bi_mul : ∀ w : List ℝ, Bi P l L w * Bm P l L w = 1
  | [] => one_mul 1
  | y :: w => by
    show ext2 P _ _ _ _ * ext2 P _ _ _ _ = 1
    rw [splitPlaneIdentityExtension_mul, Bi_mul w]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    rw [neg_mul, mul_assoc (Bi P l L w * _), Bi_mul w, mul_one, neg_add_cancel]
    exact block_extend_one P

variable {P l L} in
theorem Bi_mem (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L) : ∀ w : List ℝ, Bi P l L w ∈ UB P L (Fin w.length)
  | [] => Subalgebra.one_mem _
  | y :: w => by
    have ih := Bi_mem hTT hL w
    have hB := Bm_mem (l := l) hTT hL w
    exact block_extend_mem P L ih (Subalgebra.zero_mem _)
      (neg_mem (mul_mem (mul_mem ih (add_mem (deM_spec hTT hL hB).1 (mul_mem ((frame_memB l hL (wordP w)).1 _) hB)))
        ih)) ih

theorem op_sum_smul {ι : Type} (s : Finset ι) (T : (DQ P).Op) (F : ι → (DQ P).R) (a : ι → ℂ) (q : Qp P.r P.TT) :
    evQ P (T (∑ t ∈ s, a t • F t)) q = ∑ t ∈ s, a t * evQ P (T (F t)) q := by
  rw [map_sum]
  refine (MAx2.Jet.evQ_sum P _ _ q).trans (Finset.sum_congr rfl fun t _ => ?_)
  rw [map_smul]
  exact G.evQ_smul P _ _ q

theorem apply_matrix_linear {N : ℕ} {ι : Type} (s : Finset ι) (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (a : ι → ℂ)
    (V : ι → Qp P.r P.TT → Iota P N → ℂ) (hV : ∀ t i, (fun q => V t q i) ∈ smSub P.r P.TT)
    (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P b (fun q' i' => ∑ t ∈ s, a t * V t q' i') q i = ∑ t ∈ s, a t * wordModuleApply P b (V t) q i := by
  have hts : ∀ k, toSm P (fun q' => ∑ t ∈ s, a t * V t q' k) = ∑ t ∈ s, a t • toSm P (fun q' => V t q' k) := by
    intro k
    have hf : (fun q' => ∑ t ∈ s, a t * V t q' k) = ∑ t ∈ s, a t • (fun q' => V t q' k) := by
      funext q'; simp
    have hmem : (fun q' => ∑ t ∈ s, a t * V t q' k) ∈ smSub P.r P.TT := by
      rw [hf]; exact Subalgebra.sum_mem _ fun t _ => Subalgebra.smul_mem _ (hV t k) _
    rw [G.toSm_of_mem P hmem]
    apply Subtype.ext
    funext q'
    simp [G.toSm_of_mem P (hV _ k)]
  calc wordModuleApply P b (fun q' i' => ∑ t ∈ s, a t * V t q' i') q i
      = ∑ e', ∑ π', ∑ t ∈ s, a t * evQ P (((b (ixOf P N i).1 e') (ixOf P N i).2 π').1
          (toSm P fun q' => V t q' (iotaOf P N e' π'))) q := by
        rw [G.apply_matrix_def]
        refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun π' _ => ?_
        rw [hts]
        generalize ((b (ixOf P N i).1 e') (ixOf P N i).2 π').1 = T
        exact op_sum_smul P s T (fun t => toSm P (fun q' => V t q' (iotaOf P N e' π'))) a q
    _ = ∑ e', ∑ t ∈ s, ∑ π', a t * evQ P (((b (ixOf P N i).1 e') (ixOf P N i).2 π').1
          (toSm P fun q' => V t q' (iotaOf P N e' π'))) q := Finset.sum_congr rfl fun e' _ => Finset.sum_comm
    _ = ∑ t ∈ s, ∑ e', ∑ π', a t * evQ P (((b (ixOf P N i).1 e') (ixOf P N i).2 π').1
          (toSm P fun q' => V t q' (iotaOf P N e' π'))) q := Finset.sum_comm
    _ = ∑ t ∈ s, a t * wordModuleApply P b (V t) q i := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [G.apply_matrix_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [Finset.mul_sum]

theorem monL_congr (u : Qp P.r P.TT → M.Ty P → ℂ) (t : ℝ) {w1 w2 : List ℝ} (e : w1 = w2) {N : ℕ}
    (h1 : Iota P N = Iota P w1.length) (h2 : Iota P N = Iota P w2.length) (q : Qp P.r P.TT) (k : Iota P N) :
    monL P L u t w1 q (cast h1 k) = monL P L u t w2 q (cast h2 k) := by
  subst e; rfl

theorem cast_pair {n m : ℕ} (e : n = m) (h : Iota P (n + 1) = Iota P (m + 1)) (h' : Iota P n = Iota P m)
    (k : Iota P (n + 1)) : cast h k = (show Iota P (m + 1) from (k.1, cast h' k.2)) := by
  subst e; rfl

theorem apply_matrix_cast {n m : ℕ} (e : n = m) (x : A P (DQ P)) (V : Qp P.r P.TT → Iota P m → ℂ)
    (h : Iota P n = Iota P m) (q : Qp P.r P.TT) (k : Iota P n) :
    wordModuleApply P (io x : SlopeTestRemainingChoices (Fin n) (A P (DQ P))) (fun q k' => V q (cast h k')) q k =
      wordModuleApply P (io x : SlopeTestRemainingChoices (Fin m) (A P (DQ P))) V q (cast h k) := by
  subst e; rfl

theorem monL_map (u : Qp P.r P.TT → M.Ty P → ℂ) (t s : ℝ) :
    ∀ (w : List ℝ) (h : Iota P (w.map (· + s)).length = Iota P w.length) (q : Qp P.r P.TT)
      (k : Iota P (w.map (· + s)).length), monL P L u t (w.map (· + s)) q k = monL P L u (t + s) w q (cast h k)
  | [], h, q, k => rfl
  | y :: w, h, q, k => by
    have hl : (w.map (· + s)).length = w.length := List.length_map _
    have h' : Iota P (w.map (· + s)).length = Iota P w.length := congrArg (Iota P) hl
    have ih := monL_map u t s w h'
    rw [cast_pair P hl h h' k]
    show wordModuleApply P (io (if k.1 then lb L (((y + s : ℝ) : ℂ) + t) else la L (((y + s : ℝ) : ℂ) + t)))
        (monL P L u t (w.map (· + s))) q k.2 =
      wordModuleApply P (io (if k.1 then lb L ((y : ℂ) + ((t + s : ℝ) : ℂ)) else la L ((y : ℂ) + ((t + s : ℝ) : ℂ))))
        (monL P L u (t + s) w) q (cast h' k.2)
    have hc : ((y + s : ℝ) : ℂ) + t = (y : ℂ) + ((t + s : ℝ) : ℂ) := by push_cast; ring
    rw [hc, show monL P L u t (w.map (· + s)) = fun q k' => monL P L u (t + s) w q (cast h' k') from
      funext fun q => funext fun k' => ih q k']
    exact apply_matrix_cast P hl _ _ h' q k.2

end

end Formalism.FourierDecayAlt.P.MAx3.NF

end S_NF_NF7

section S_NF_NF8

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.NF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r)

theorem la_poly : ∃ α : ℕ → A P (DQ P), ∀ s : ℂ, la L s = ∑ k ∈ Finset.range (P.r + 1 + 1), s ^ k • α k := by
  obtain ⟨α, hα⟩ := G.polyIn_mono (G.polyIn_const_mul L.Di (G.Ahat_poly P L 0)) (Nat.le_succ P.r)
  exact ⟨α, fun s => by have := hα s; simp only [zero_add] at this; exact this⟩

theorem lb_poly : ∃ β : ℕ → A P (DQ P), ∀ s : ℂ, lb L s = ∑ k ∈ Finset.range (P.r + 1 + 1), s ^ k • β k := by
  obtain ⟨β, hβ⟩ := G.polyIn_const_mul L.Dbi (G.raising_operator_polynomial P L 0)
  exact ⟨β, fun s => by have := hβ s; simp only [zero_add] at this; exact this⟩

theorem apply_matrix_polynomial {N : ℕ} (d : ℕ) (s : ℂ) (γ : ℕ → A P (DQ P)) (V : Qp P.r P.TT → Iota P N → ℂ)
    (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P (io (∑ k ∈ Finset.range d, s ^ k • γ k)) V q i = ∑ k ∈ Finset.range d, s ^ k * wordModuleApply P (io (γ k)) V q i := by
  have h : (io (∑ k ∈ Finset.range d, s ^ k • γ k) : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) =
      ∑ k ∈ Finset.range d, s ^ k • (io (γ k) : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) := by
    unfold io; rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := G.io_smul P (S := Fin N) (s ^ k) (γ k)
    unfold io at this
    exact this
  rw [h, G.apply_matrix_sum]
  exact Finset.sum_congr rfl fun k _ => G.apply_matrix_smul P _ _ _ q i

theorem monPoly (u : Qp P.r P.TT → M.Ty P → ℂ) (hu : ∀ π, (fun q => u q π) ∈ smSub P.r P.TT) :
    ∀ N : ℕ, ∃ c : (Fin N → Fin (P.r + 1 + 1)) → Qp P.r P.TT → Iota P N → ℂ,
      (∀ κ i, (fun q => c κ q i) ∈ smSub P.r P.TT) ∧
      ∀ (y : Fin N → ℝ) (q : Qp P.r P.TT) (i : Iota P N),
        monL P L u 0 (List.ofFn y) q (cast (iota_len P N y) i) =
          ∑ κ : Fin N → Fin (P.r + 1 + 1), ((∏ a, (y a) ^ (κ a : ℕ) : ℝ) : ℂ) * c κ q i
  | 0 => by
    refine ⟨fun _ => u, fun _ i => hu i, fun y q i => ?_⟩
    have e : List.ofFn y = [] := List.ofFn_zero
    rw [monL_congr P L u 0 e (iota_len P 0 y) rfl q i]
    show u q i = _
    rw [Fintype.sum_unique]
    simp
  | N + 1 => by
    obtain ⟨c', hc'm, hc'⟩ := monPoly u hu N
    obtain ⟨α, hα⟩ := la_poly P L
    obtain ⟨β, hβ⟩ := lb_poly P L
    let γ : Bool → ℕ → A P (DQ P) := fun b k => if b then β k else α k
    refine ⟨fun κ q bi => wordModuleApply P (io (γ bi.1 (κ 0 : ℕ))) (c' (Fin.tail κ)) q bi.2,
      fun κ bi => G.apply_matrix_smooth P _ _ _, fun y q i => ?_⟩
    have e : List.ofFn y = y 0 :: List.ofFn (fun a => y a.succ) := List.ofFn_succ
    have hlen : N = (List.ofFn (fun a => y a.succ)).length := (List.length_ofFn).symm
    have h2 : Iota P (N + 1) = Iota P (y 0 :: List.ofFn (fun a => y a.succ)).length :=
      congrArg (Iota P) (congrArg (· + 1) hlen)
    have h' : Iota P N = Iota P (List.ofFn fun a => y a.succ).length := iota_len P N (fun a => y a.succ)
    rw [monL_congr P L u 0 e (iota_len P (N + 1) y) h2 q i, cast_pair P hlen h2 h' i]
    show wordModuleApply P (io (if i.1 then lb L ((y 0 : ℂ) + ((0 : ℝ) : ℂ)) else la L ((y 0 : ℂ) + ((0 : ℝ) : ℂ))))
      (monL P L u 0 (List.ofFn fun a => y a.succ)) q (cast h' i.2) = _
    rw [← apply_matrix_cast P hlen _ _ h' q i.2]
    rw [show (fun q k => monL P L u 0 (List.ofFn fun a => y a.succ) q (cast h' k)) =
        fun q k => ∑ κ' : Fin N → Fin (P.r + 1 + 1), ((∏ a, (y a.succ) ^ (κ' a : ℕ) : ℝ) : ℂ) * c' κ' q k from
      funext fun q => funext fun k => hc' (fun a => y a.succ) q k]
    rw [apply_matrix_linear P Finset.univ _ _ c' hc'm q i.2]
    rcases i with ⟨b, i1⟩
    dsimp only
    have hx : (if b then lb L ((y 0 : ℂ) + ((0 : ℝ) : ℂ)) else la L ((y 0 : ℂ) + ((0 : ℝ) : ℂ))) =
        ∑ k ∈ Finset.range (P.r + 1 + 1), ((y 0 : ℝ) : ℂ) ^ k • γ b k := by
      cases b
      · simp only [Bool.false_eq_true, if_false, γ, Complex.ofReal_zero, add_zero]; exact hα _
      · simp only [if_true, γ, Complex.ofReal_zero, add_zero]; exact hβ _
    rw [hx]
    simp only [apply_matrix_polynomial]
    simp only [Finset.sum_range]
    conv_rhs => rw [← (Fin.consEquiv (fun _ => Fin (P.r + 1 + 1))).sum_comp]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hc0 : (Fin.consEquiv (fun _ => Fin (P.r + 1 + 1))) (m, κ') = Fin.cons m κ' := rfl
    rw [hc0, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons]
    push_cast
    ring

theorem ptMat_bdd {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (hb : ∀ e e', b e e' ∈ bddA P) :
    ∃ C : ℝ, ∀ q i k, ‖ptMat P b q i k‖ ≤ C := by
  choose C hC using fun e e' => (show _ ∧ _ from hb e e').2
  refine ⟨∑ e, ∑ e', max (C e e') 0, fun q i k => ?_⟩
  show ‖evQ P (((b (ixOf P N i).1 (ixOf P N k).1) (ixOf P N i).2 (ixOf P N k).2).1 1) q‖ ≤ _
  refine (hC _ _ _ _ q).trans ((le_max_left _ (0 : ℝ)).trans ?_)
  refine le_trans ?_ (Finset.single_le_sum (f := fun e => ∑ e', max (C e e') 0)
    (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ (ixOf P N i).1))
  exact Finset.single_le_sum (f := fun e' => max (C (ixOf P N i).1 e') 0) (fun _ _ => le_max_right _ _)
    (Finset.mem_univ (ixOf P N k).1)

theorem cont_of_mem {f : Qp P.r P.TT → ℂ} (hf : f ∈ smSub P.r P.TT) : Continuous f :=
  MAx3.evQ_cont P ⟨f, hf⟩

theorem ptMat_cont {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (i k : Iota P N) :
    Continuous fun q => ptMat P b q i k := MAx3.evQ_cont P _

end

end Formalism.FourierDecayAlt.P.MAx3.NF

end S_NF_NF8

section S_NF_NF9

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.NF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

section Fac
variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} (hTT : 0 < P.TT) (hL : IsModelLevel P (DQ P) L)
include hTT hL

theorem Gs_mem (s : ℝ) (u : Qp P.r P.TT → M.Ty P → ℂ) (hu : ∀ π, (fun q => u q π) ∈ smSub P.r P.TT) (π : M.Ty P) :
    (fun q => ((Gq P q ^ s : ℝ) : ℂ) * u q π) ∈ smSub P.r P.TT := by
  have h : (fun q => ((Gq P q ^ s : ℝ) : ℂ) * u q π) = evQ P (G.Gpow P s * ⟨_, hu π⟩) := by
    funext q
    rw [MAx2.Jet.evQ_mul, G.ev_Gpow]
    rfl
  rw [h]; exact Subtype.property _

theorem factor_id (u : Qp P.r P.TT → M.Ty P → ℂ) (hu : ∀ π, (fun q => u q π) ∈ smSub P.r P.TT) (N : ℕ)
    (Y : Fin N → ℝ) (s : ℝ) (ω : Qp P.r P.TT) (i : Iota P N) :
    (((Gq P ω) ^ (-s) : ℝ) : ℂ) *
        Xw P l L (fun q π => ((Gq P q ^ s : ℝ) : ℂ) * u q π) (List.ofFn Y) ω (cast (iota_len P N Y) i) =
      ∑ k, ptMat P (Bm P l L (List.ofFn Y)) ω (cast (iota_len P N Y) i) (cast (iota_len P N Y) k) *
        monL P L u 0 (List.ofFn fun a => Y a + s) ω (cast (iota_len P N fun a => Y a + s) k) := by
  rw [Xw_pt hTT.le hL _ (Gs_mem hTT hL s u hu) (List.ofFn Y) (bounded_sub_base_algebra hTT hL) ω _, Finset.mul_sum]
  rw [← Fintype.sum_equiv (Equiv.cast (iota_len P N Y)) (fun k => _) _ (fun k => rfl)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [monL_conj hTT.le hL u hu s (List.ofFn Y) 0 ω, Equiv.cast_apply, zero_add]
  have e : List.ofFn (fun a => Y a + s) = (List.ofFn Y).map (· + s) := by rw [List.map_ofFn]; rfl
  have hm : Iota P N = Iota P ((List.ofFn Y).map (· + s)).length := by rw [List.length_map, List.length_ofFn]
  have hmh : Iota P ((List.ofFn Y).map (· + s)).length = Iota P (List.ofFn Y).length := by rw [List.length_map]
  rw [monL_congr P L u 0 e (iota_len P N fun a => Y a + s) hm ω k, monL_map P L u 0 s (List.ofFn Y) hmh ω (cast hm k),
    cast_cast, zero_add]
  rw [← mul_assoc, mul_comm _ (ptMat P _ ω _ _), mul_assoc, ← mul_assoc _ (((Gq P ω) ^ s : ℝ) : ℂ),
    G.rpow_neg_mul _ _ (Gq_pos P ω), one_mul]

theorem inv_prop (w : List ℝ) (N : ℕ) (h : Iota P N = Iota P w.length) (ω : Qp P.r P.TT) (v : Iota P N → ℂ)
    (i : Iota P N) :
    ∑ x, ptMat P (Bi P l L w) ω (cast h i) (cast h x) * ∑ k, ptMat P (Bm P l L w) ω (cast h x) (cast h k) * v k =
      v i := by
  classical
  have hB := Bm_mem (l := l) hTT.le hL w
  have hBi := Bi_mem (l := l) hTT.le hL w
  have hUS : ∀ b : Wd.SlopeTestRemainingChoices (Fin w.length) (A P (DQ P)), b ∈ UB P L (Fin w.length) → b ∈ G.BlockMatrixAlgebra P (Fin w.length) :=
    fun b hb e e' => bounded_sub_base_algebra hTT hL (hb e e')
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ k : Iota P N, ∑ x : Iota P N, ptMat P (Bi P l L w) ω (cast h i) (cast h x) *
      (ptMat P (Bm P l L w) ω (cast h x) (cast h k) * v k) = if i = k then v k else 0 := by
    intro k
    simp only [← mul_assoc, ← Finset.sum_mul]
    rw [show (∑ x : Iota P N, ptMat P (Bi P l L w) ω (cast h i) (cast h x) *
        ptMat P (Bm P l L w) ω (cast h x) (cast h k)) = ∑ x' : Iota P w.length,
          ptMat P (Bi P l L w) ω (cast h i) x' * ptMat P (Bm P l L w) ω x' (cast h k) from
      Fintype.sum_equiv (Equiv.cast h) _ _ (fun x => rfl)]
    rw [← ptMat_mul P _ _ (hUS _ hBi) (hUS _ hB), Bi_mul, ptMat_one]
    by_cases hik : i = k
    · subst hik; simp
    · rw [if_neg (fun h' => hik ((cast_inj h).1 h')), if_neg hik, zero_mul]
  simp only [key]
  simp

end Fac

end

end Formalism.FourierDecayAlt.P.MAx3.NF

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx3.NF

theorem factor_exists : Formalism.FourierDecayAlt.MA.FactorExistsQ := by
  intro P l L j lam α β Lb Ntot hH N hN
  have hOK : P.OK := hH.1.1
  have hL : IsModelLevel P (DQ P) L := hH.1.2.2.2.1
  have hTT : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hu : ∀ π, (fun q => ju P j q π) ∈ smSub P.r P.TT := fun π => (j π).2
  obtain ⟨c, hcm, hc⟩ := monPoly P L (ju P j) hu N
  refine ⟨(fun y q i => monL P L (ju P j) 0 (List.ofFn y) q (cast (iota_len P N y) i),
    fun Y q i k => ptMat P (Bm P l L (List.ofFn Y)) q (cast (iota_len P N Y) i) (cast (iota_len P N Y) k)),
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact MAx3.Wq_meas P
  · intro y i
    exact (cont_of_mem P (monL_mem P L (ju P j) hu 0 (List.ofFn y) _)).measurable
  · intro Y i k
    exact (ptMat_cont P _ _ _).measurable
  · intro Y hY s ω i
    exact factor_id hTT hL (ju P j) hu N Y s ω i
  · intro Y hY
    have hB := Bm_mem (l := l) hTT.le hL (List.ofFn Y)
    have hBi := Bi_mem (l := l) hTT.le hL (List.ofFn Y)
    obtain ⟨C1, hC1⟩ := ptMat_bdd P (Bm P l L (List.ofFn Y)) fun e e' => BB_le hTT hL (hB e e')
    obtain ⟨C2, hC2⟩ := ptMat_bdd P (Bi P l L (List.ofFn Y)) fun e e' => BB_le hTT hL (hBi e e')
    refine ⟨max C1 C2, fun ω i k => ptMat P (Bi P l L (List.ofFn Y)) ω (cast (iota_len P N Y) i) (cast (iota_len P N Y) k),
      fun ω i k => ⟨(hC1 _ _ _).trans (le_max_left _ _), (hC2 _ _ _).trans (le_max_right _ _)⟩,
      fun i k => (ptMat_cont P _ _ _).measurable, fun ω v i => ?_⟩
    exact inv_prop hTT hL (List.ofFn Y) N (iota_len P N Y) ω v i
  · exact ⟨c, fun y ω i => hc y ω i⟩

end Formalism.FourierDecayAlt.P

end S_NF_NF9

section S_H_H1

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

def FS : Set A := L.fns ∪ Set.range (algebraMap ℂ A)

theorem FS_comm : ∀ x ∈ FS L, ∀ y ∈ FS L, x * y = y * x := by
  rintro x (hx | ⟨a, rfl⟩) y (hy | ⟨b, rfl⟩)
  · exact fc L hx hy
  · exact (Algebra.commutes b x).symm
  · exact Algebra.commutes a y
  · rw [← map_mul, ← map_mul, mul_comm]

abbrev CF : Type := Subring.closure (FS L)

instance : CommRing (CF L) := Subring.closureCommRingOfComm (FS_comm L)

theorem memF {x : A} (hx : x ∈ L.fns) : x ∈ Subring.closure (FS L) := Subring.subset_closure (Or.inl hx)
theorem memS (a : ℂ) : algebraMap ℂ A a ∈ Subring.closure (FS L) := Subring.subset_closure (Or.inr ⟨a, rfl⟩)

theorem memDr : L.Dr ∈ Subring.closure (FS L) := by
  unfold LevelData.Dr
  exact Subring.list_prod_mem _ fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_c L i)
theorem memDri : L.Dri ∈ Subring.closure (FS L) := by
  unfold LevelData.Dri
  exact Subring.list_prod_mem _ fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_ci L i)
theorem memDrb : L.Drb ∈ Subring.closure (FS L) := by
  unfold LevelData.Drb
  exact Subring.list_prod_mem _ fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_cb L i)
theorem memDrbi : L.Drbi ∈ Subring.closure (FS L) := by
  unfold LevelData.Drbi
  exact Subring.list_prod_mem _ fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_cbi L i)

theorem cl_comm {x y : A} (hx : x ∈ Subring.closure (FS L)) (hy : y ∈ Subring.closure (FS L)) : x * y = y * x := by
  have := mul_comm (⟨x, hx⟩ : CF L) ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem comm_cl {z : A} (hz : ∀ x ∈ FS L, z * x = x * z) {y : A} (hy : y ∈ Subring.closure (FS L)) :
    z * y = y * z := by
  induction hy using Subring.closure_induction with
  | mem x hx => exact hz x hx
  | zero => simp
  | one => simp
  | add x y _ _ h1 h2 => rw [mul_add, add_mul, h1, h2]
  | neg x _ h => rw [mul_neg, neg_mul, h]
  | mul x y _ _ h1 h2 => rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem Dr_Dri' : L.Dr * L.Dri = 1 := Dr_Dri L
theorem Drb_Drbi' : L.Drb * L.Drbi = 1 := Drb_Drbi L

theorem hat_ζbi (Y : ℂ) : L.ζbi * L.Ahat Y = L.Ahat Y * L.ζbi ∧ L.ζbi * L.R0 Y = L.R0 Y * L.ζbi :=
  commA L L.ζbi L.ζb L.ζbi_ζb L.ζb_ζbi (fun m => (L.p_ζbi m)) (fun y hy => fc L hy (m_ζbi L))
    L.nab_ζbi Y

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H1

section S_H_H2

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem D_Di : L.D * L.Di = 1 := by
  unfold LevelData.D LevelData.Di
  rw [mul_assoc, ← mul_assoc L.ζ, L.ζ_ζi, one_mul, Dr_Dri]
theorem Di_D : L.Di * L.D = 1 := by
  unfold LevelData.D LevelData.Di
  rw [mul_assoc, ← mul_assoc L.Dri, Dri_Dr, one_mul, L.ζi_ζ]
theorem Db_Dbi : L.Db * L.Dbi = 1 := by
  unfold LevelData.Db LevelData.Dbi
  rw [mul_assoc, ← mul_assoc L.ζb, L.ζb_ζbi, one_mul, Drb_Drbi]
theorem Dbi_Db : L.Dbi * L.Db = 1 := by
  unfold LevelData.Db LevelData.Dbi
  rw [mul_assoc, ← mul_assoc L.Drbi, Drbi_Drb, one_mul, L.ζbi_ζb]

theorem memD : L.D ∈ Subring.closure (FS L) := Subring.mul_mem _ (memDr L) (memF L (m_ζ L))
theorem memDi : L.Di ∈ Subring.closure (FS L) := Subring.mul_mem _ (memF L (m_ζi L)) (memDri L)
theorem memDb : L.Db ∈ Subring.closure (FS L) := Subring.mul_mem _ (memDrb L) (memF L (m_ζb L))
theorem memDbi : L.Dbi ∈ Subring.closure (FS L) := Subring.mul_mem _ (memF L (m_ζbi L)) (memDrbi L)

theorem hat_Dbi (Y : ℂ) : L.Dbi * L.Ahat Y = L.Ahat Y * L.Dbi ∧ L.Dbi * L.R0 Y = L.R0 Y * L.Dbi := by
  have h := commA L L.Drbi L.Drb (Drbi_Drb L) (Drb_Drbi L)
    (fun m => (comm_prod L.cbi (L.p m) (fun i => L.p_cbi m i)))
    (fun y hy => cl_comm L (memF L hy) (memDrbi L))
    (comm_prod L.cbi L.nab (fun i => L.nab_cbi i)) Y
  have h2 := hat_ζbi L Y
  unfold LevelData.Dbi
  constructor
  · rw [mul_assoc, h.1, ← mul_assoc, h2.1, mul_assoc]
  · rw [mul_assoc, h.2, ← mul_assoc, h2.2, mul_assoc]

theorem hat_Db (Y : ℂ) : L.Db * L.Ahat Y = L.Ahat Y * L.Db ∧ L.Db * L.R0 Y = L.R0 Y * L.Db := by
  obtain ⟨h1, h2⟩ := hat_Dbi L Y
  constructor
  · have := congrArg (fun x => L.Db * x * L.Db) h1
    simp only [← mul_assoc, Db_Dbi, one_mul] at this
    rw [mul_assoc, mul_assoc, Dbi_Db, mul_one] at this
    exact this.symm
  · have := congrArg (fun x => L.Db * x * L.Db) h2
    simp only [← mul_assoc, Db_Dbi, one_mul] at this
    rw [mul_assoc, mul_assoc, Dbi_Db, mul_one] at this
    exact this.symm

theorem Ahat_Di (Y : ℂ) : L.Ahat Y * L.Di = L.Di * L.Ahat (Y - 1) := by
  have h := (Formalism.FourierDecayAlt.P.shiftConjugation A r L (Y - 1)).1
  rw [sub_add_cancel] at h
  rw [← h, mul_assoc, mul_assoc, D_Di, mul_one]

theorem raising_mul_D_inv (Y : ℂ) : L.R0 Y * L.Di =
    L.Di * (L.R0 (Y - 1) - algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y - 1))) := by
  have h := (Formalism.FourierDecayAlt.P.shiftConjugation A r L (Y - 1)).2.1
  rw [sub_add_cancel] at h
  have h2 : L.Di * L.R0 (Y - 1) = (L.R0 Y + algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat Y)) * L.Di := by
    rw [← h, mul_assoc, mul_assoc, D_Di, mul_one]
  rw [mul_sub, h2, add_mul]
  have e1 : L.Di * algebraMap ℂ A L.TT = algebraMap ℂ A L.TT * L.Di := (Algebra.commutes _ _).symm
  have e2 : L.Di * L.Drb = L.Drb * L.Di := cl_comm L (memDi L) (memDrb L)
  have hc : L.Di * (algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y - 1))) =
      algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat Y) * L.Di := by
    calc L.Di * (algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y - 1)))
        = algebraMap ℂ A L.TT * (L.Drb * (L.Di * (L.Di * L.Ahat (Y - 1)))) := by
          rw [← mul_assoc, e1, mul_assoc]; congr 1; simp only [← mul_assoc]; rw [e2]
      _ = algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat Y) * L.Di := by
          rw [← Ahat_Di]; simp only [mul_assoc]
  rw [hc]
  abel

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H2

section S_H_H3

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem Ahat_Dipow (i : ℕ) (Y : ℂ) : L.Ahat Y * L.Di ^ i = L.Di ^ i * L.Ahat (Y - i) := by
  induction i generalizing Y with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', ← mul_assoc, Ahat_Di, mul_assoc, ih, ← mul_assoc]
    congr 2; push_cast; ring

theorem comm_Dbipow_A (i : ℕ) (Y : ℂ) : L.Ahat Y * L.Dbi ^ i = L.Dbi ^ i * L.Ahat Y :=
  ((Commute.pow_right (hat_Dbi L Y).1.symm i).symm).eq.symm

theorem comm_Dbipow_R (i : ℕ) (Y : ℂ) : L.R0 Y * L.Dbi ^ i = L.Dbi ^ i * L.R0 Y :=
  ((Commute.pow_right (hat_Dbi L Y).2.symm i).symm).eq.symm

theorem memPow {x : A} (hx : x ∈ Subring.closure (FS L)) (i : ℕ) : x ^ i ∈ Subring.closure (FS L) :=
  Subring.pow_mem _ hx i

theorem raising_D_inv_pow (i : ℕ) (Y : ℂ) : ∃ cs : List (ℂ × ℂ), L.R0 Y * L.Di ^ i =
    L.Di ^ i * (L.R0 (Y - i) + (cs.map fun x => x.1 • (L.Drb * L.Di * L.Ahat x.2)).sum) := by
  induction i generalizing Y with
  | zero => exact ⟨[], by simp⟩
  | succ i ih =>
    obtain ⟨cs, hcs⟩ := ih (Y - 1)
    refine ⟨cs ++ [(-L.TT, Y - 1 - i)], ?_⟩
    have hDD : L.Drb * L.Di * L.Di ^ i = L.Di ^ i * (L.Drb * L.Di) :=
      cl_comm L (Subring.mul_mem _ (memDrb L) (memDi L)) (memPow L (memDi L) i)
    have e : (Y - 1 - (i : ℂ)) = Y - ((i + 1 : ℕ) : ℂ) := by push_cast; ring
    have hX : algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y - 1)) * L.Di ^ i =
        L.Di ^ i * (L.TT • (L.Drb * L.Di * L.Ahat (Y - 1 - i))) := by
      rw [mul_assoc, mul_assoc (L.Drb * L.Di), Ahat_Dipow, ← mul_assoc (L.Drb * L.Di), hDD,
        Algebra.smul_def, ← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes L.TT (L.Di ^ i)]
      simp only [mul_assoc]
    calc L.R0 Y * L.Di ^ (i + 1) = L.R0 Y * L.Di * L.Di ^ i := by rw [pow_succ', mul_assoc]
      _ = L.Di * (L.R0 (Y - 1) * L.Di ^ i - algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y - 1)) * L.Di ^ i) := by
          rw [raising_mul_D_inv, mul_assoc, sub_mul]
      _ = L.Di ^ (i + 1) * (L.R0 (Y - ((i + 1 : ℕ) : ℂ)) +
            ((cs ++ [(-L.TT, Y - 1 - i)]).map fun x => x.1 • (L.Drb * L.Di * L.Ahat x.2)).sum) := by
          rw [hcs, hX, ← mul_sub, ← mul_assoc, ← pow_succ', e, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, neg_smul, ← sub_eq_add_neg, add_sub_assoc, ← e]

def plusHats : Set A := Set.range L.Ahat ∪ Set.range L.R0

def tm (b : A) (i i' : ℕ) (H : List A) : A := b * (L.Di ^ i * L.Dbi ^ i') * H.prod

variable (S : Submonoid A)

def Term (n : ℕ) : Set A :=
  {x | ∃ b ∈ S, ∃ (i i' : ℕ) (H : List A), i + i' = n ∧ H.length = n ∧ (∀ h ∈ H, h ∈ plusHats L) ∧
    x = tm L b i i' H}

def NF (n : ℕ) : Submodule ℂ A := Submodule.span ℂ (Term L S n)

structure Hyp : Prop where
  comm_Di : ∀ b ∈ S, b * L.Di = L.Di * b
  comm_Dbi : ∀ b ∈ S, b * L.Dbi = L.Dbi * b
  ahat : ∀ b ∈ S, ∃ t : ℂ, ∀ Y, L.Ahat Y * b = b * L.Ahat (Y + t)
  r0 : ∀ b ∈ S, ∀ Y, ∃ (t : ℂ) (ts : List (ℂ × A × ℂ)), (∀ x ∈ ts, x.2.1 ∈ S) ∧
    L.R0 Y * b = b * L.R0 (Y + t) + (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum
  drb : L.Drb * L.Di ∈ S

variable {L S}

theorem term_mem {n : ℕ} {b : A} (hb : b ∈ S) {i i' : ℕ} {H : List A} (h1 : i + i' = n) (h2 : H.length = n)
    (h3 : ∀ h ∈ H, h ∈ plusHats L) : tm L b i i' H ∈ NF L S n :=
  Submodule.subset_span ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩

theorem sum_mem_NF {n : ℕ} {ι : Type} (ts : List ι) (f : ι → A) (h : ∀ x ∈ ts, f x ∈ NF L S n) :
    (ts.map f).sum ∈ NF L S n := by
  induction ts with
  | nil => simp
  | cons a ts ih =>
    rw [List.map_cons, List.sum_cons]
    exact Submodule.add_mem _ (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem a_term (hS : Hyp L S) (y : ℂ) {n : ℕ} {x : A} (hx : x ∈ Term L S n) :
    L.Di * L.Ahat y * x ∈ NF L S (n + 1) := by
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  obtain ⟨t, ht⟩ := hS.ahat b hb
  have ht' : ∀ z, L.Ahat y * (b * z) = b * (L.Ahat (y + t) * z) := fun z => by
    rw [← mul_assoc, ht, mul_assoc]
  have hb' : ∀ z, L.Di * (b * z) = b * (L.Di * z) := fun z => by
    rw [← mul_assoc, ← hS.comm_Di b hb, mul_assoc]
  have hA1 : ∀ z, L.Ahat (y + t) * (L.Di ^ i * z) = L.Di ^ i * (L.Ahat (y + t - i) * z) := fun z => by
    rw [← mul_assoc, Ahat_Dipow, mul_assoc]
  have hA2 : ∀ z, L.Ahat (y + t - i) * (L.Dbi ^ i' * z) = L.Dbi ^ i' * (L.Ahat (y + t - i) * z) := fun z => by
    rw [← mul_assoc, comm_Dbipow_A, mul_assoc]
  have e : L.Di * L.Ahat y * tm L b i i' H = tm L b (i + 1) i' (L.Ahat (y + t - i) :: H) := by
    unfold tm
    rw [List.prod_cons, pow_succ']
    simp only [mul_assoc]
    rw [ht', hb', hA1, hA2]
  rw [e]
  exact term_mem hb (by omega) (by simp [h2]) (by
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact Or.inl ⟨_, rfl⟩
    · exact h3 h hh)

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H3

section S_H_H4

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} {L : LevelData A r} {S : Submonoid A}

def Term2 (L : LevelData A r) (S : Submonoid A) (d ℓ : ℕ) : Set A :=
  {x | ∃ b ∈ S, ∃ (i i' : ℕ) (H : List A), i + i' = d ∧ H.length = ℓ ∧ (∀ h ∈ H, h ∈ plusHats L) ∧
    x = tm L b i i' H}

def NormalFormTwo (L : LevelData A r) (S : Submonoid A) (d ℓ : ℕ) : Submodule ℂ A := Submodule.span ℂ (Term2 L S d ℓ)

theorem mem2 {d ℓ : ℕ} {b : A} (hb : b ∈ S) {i i' : ℕ} {H : List A} (h1 : i + i' = d) (h2 : H.length = ℓ)
    (h3 : ∀ h ∈ H, h ∈ plusHats L) : tm L b i i' H ∈ NormalFormTwo L S d ℓ :=
  Submodule.subset_span ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩

theorem cons_hats {h : A} (hh : h ∈ plusHats L) {H : List A} (h3 : ∀ x ∈ H, x ∈ plusHats L) :
    ∀ x ∈ h :: H, x ∈ plusHats L := by
  intro x hx; rcases List.mem_cons.1 hx with rfl | hx; exacts [hh, h3 x hx]

theorem span_mul {T : Set A} {M : Submodule ℂ A} (z : A) (h : ∀ x ∈ T, z * x ∈ M) {x : A}
    (hx : x ∈ Submodule.span ℂ T) : z * x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add]; exact M.add_mem h1 h2
  | smul c x _ h1 => rw [mul_smul_comm]; exact M.smul_mem c h1

theorem Di_tm (hS : Hyp L S) {b : A} (hb : b ∈ S) (i i' : ℕ) (H : List A) :
    L.Di * tm L b i i' H = tm L b (i + 1) i' H := by
  unfold tm
  rw [← mul_assoc, ← mul_assoc, ← hS.comm_Di b hb, pow_succ']
  simp only [mul_assoc]

theorem Dbi_tm (hS : Hyp L S) {b : A} (hb : b ∈ S) (i i' : ℕ) (H : List A) :
    L.Dbi * tm L b i i' H = tm L b i (i' + 1) H := by
  unfold tm
  have hc : L.Dbi * L.Di ^ i = L.Di ^ i * L.Dbi :=
    cl_comm L (memDbi L) (memPow L (memDi L) i)
  rw [← mul_assoc, ← mul_assoc, ← hS.comm_Dbi b hb, pow_succ']
  simp only [mul_assoc]
  rw [← mul_assoc L.Dbi, hc, mul_assoc]

theorem Ahat_tm (hS : Hyp L S) (y : ℂ) {b : A} (hb : b ∈ S) (i i' : ℕ) (H : List A) :
    ∃ y', L.Ahat y * tm L b i i' H = tm L b i i' (L.Ahat y' :: H) := by
  obtain ⟨t, ht⟩ := hS.ahat b hb
  refine ⟨y + t - i, ?_⟩
  unfold tm
  rw [List.prod_cons]
  simp only [mul_assoc]
  rw [← mul_assoc (L.Ahat y), ht, mul_assoc, ← mul_assoc (L.Ahat (y + t)), Ahat_Dipow, mul_assoc,
    ← mul_assoc (L.Ahat (y + t - i)), comm_Dbipow_A, mul_assoc]

theorem normal_form_D_inv (hS : Hyp L S) {d ℓ : ℕ} {x : A} (hx : x ∈ NormalFormTwo L S d ℓ) : L.Di * x ∈ NormalFormTwo L S (d + 1) ℓ := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  rw [Di_tm hS hb]; exact mem2 hb (by omega) h2 h3

theorem normal_form_two_D_bar_inv (hS : Hyp L S) {d ℓ : ℕ} {x : A} (hx : x ∈ NormalFormTwo L S d ℓ) : L.Dbi * x ∈ NormalFormTwo L S (d + 1) ℓ := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  rw [Dbi_tm hS hb]; exact mem2 hb (by omega) h2 h3

theorem normal_form_two_hat (hS : Hyp L S) (y : ℂ) {d ℓ : ℕ} {x : A} (hx : x ∈ NormalFormTwo L S d ℓ) :
    L.Ahat y * x ∈ NormalFormTwo L S d (ℓ + 1) := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  obtain ⟨y', e⟩ := Ahat_tm hS y hb i i' H
  rw [e]; exact mem2 hb h1 (by simp [h2]) (cons_hats (Or.inl ⟨_, rfl⟩) h3)

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H4

section S_H_H5

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} {L : LevelData A r} {S : Submonoid A}

theorem bAPQ (b : A) (y' : ℂ) (i i' : ℕ) (H : List A) :
    b * L.Ahat y' * (L.Di ^ i * L.Dbi ^ i') * H.prod = tm L b i i' (L.Ahat (y' - i) :: H) := by
  unfold tm
  rw [List.prod_cons]
  simp only [mul_assoc]
  rw [← mul_assoc (L.Ahat y'), Ahat_Dipow, mul_assoc, ← mul_assoc (L.Ahat (y' - i)), comm_Dbipow_A, mul_assoc]

theorem drb_comm_P (i : ℕ) : L.Drb * L.Di * L.Di ^ i = L.Di ^ i * (L.Drb * L.Di) :=
  cl_comm L (Subring.mul_mem _ (memDrb L) (memDi L)) (memPow L (memDi L) i)
theorem drb_comm_Q (i : ℕ) : L.Drb * L.Di * L.Dbi ^ i = L.Dbi ^ i * (L.Drb * L.Di) :=
  cl_comm L (Subring.mul_mem _ (memDrb L) (memDi L)) (memPow L (memDbi L) i)

theorem bRPQ (b : A) (y : ℂ) (i i' : ℕ) (H : List A) : ∃ cs : List (ℂ × ℂ),
    b * L.R0 y * (L.Di ^ i * L.Dbi ^ i') * H.prod = tm L b i i' (L.R0 (y - i) :: H) +
      (cs.map fun x => x.1 • tm L (b * (L.Drb * L.Di)) i i' (L.Ahat x.2 :: H)).sum := by
  obtain ⟨cs, hcs⟩ := raising_D_inv_pow L i y
  refine ⟨cs, ?_⟩
  have e1 : b * L.R0 y * (L.Di ^ i * L.Dbi ^ i') * H.prod =
      b * L.Di ^ i * (L.R0 (y - i) + (cs.map fun x => x.1 • (L.Drb * L.Di * L.Ahat x.2)).sum) *
        L.Dbi ^ i' * H.prod := by
    rw [mul_assoc b (L.Di ^ i), ← hcs]; simp only [mul_assoc]
  rw [e1, mul_add, add_mul, add_mul]
  congr 1
  · unfold tm; rw [List.prod_cons]; simp only [mul_assoc]; rw [← mul_assoc (L.R0 _), comm_Dbipow_R, mul_assoc]
  · rw [← List.sum_map_mul_left, ← List.sum_map_mul_right, ← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
    congr 1
    have tA : ∀ z, L.Ahat x.2 * (L.Dbi ^ i' * z) = L.Dbi ^ i' * (L.Ahat x.2 * z) := fun z => by
      rw [← mul_assoc, comm_Dbipow_A, mul_assoc]
    have tP : ∀ z, L.Di ^ i * (L.Drb * (L.Di * z)) = L.Drb * (L.Di * (L.Di ^ i * z)) := fun z => by
      rw [← mul_assoc L.Drb, ← mul_assoc, ← drb_comm_P, mul_assoc, mul_assoc]
    unfold tm; rw [List.prod_cons]; simp only [mul_assoc]
    rw [tA, tP]

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H5

section S_H_H6

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} {L : LevelData A r} {S : Submonoid A}

theorem normal_form_two_raising (hS : Hyp L S) (y : ℂ) {d ℓ : ℕ} {x : A} (hx : x ∈ NormalFormTwo L S d ℓ) :
    L.R0 y * x ∈ NormalFormTwo L S d (ℓ + 1) := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  obtain ⟨t, ts, hts, e⟩ := hS.r0 b hb y
  obtain ⟨cs, hcs⟩ := bRPQ (L := L) b (y + t) i i' H
  have e2 : L.R0 y * tm L b i i' H = (b * L.R0 (y + t) * (L.Di ^ i * L.Dbi ^ i') * H.prod) +
      (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2 * (L.Di ^ i * L.Dbi ^ i') * H.prod)).sum := by
    unfold tm
    rw [← mul_assoc, ← mul_assoc, e, add_mul, add_mul, ← List.sum_map_mul_right, ← List.sum_map_mul_right]
    congr 1
    congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc]
  have hlen : (L.R0 (y + t - i) :: H).length = ℓ + 1 := by simp [h2]
  rw [e2, hcs]
  refine Submodule.add_mem _ (Submodule.add_mem _ (mem2 hb h1 hlen (cons_hats (Or.inr ⟨_, rfl⟩) h3))
    (sum_mem_normal_form_two _ _ fun x _ => Submodule.smul_mem _ _ (mem2 (S.mul_mem hb hS.drb) h1 (by simp [h2])
      (cons_hats (Or.inl ⟨_, rfl⟩) h3)))) (sum_mem_normal_form_two _ _ fun x hx => ?_)
  rw [bAPQ]
  exact Submodule.smul_mem _ _ (mem2 (hts x hx) h1 (by simp [h2]) (cons_hats (Or.inl ⟨_, rfl⟩) h3))
where
  sum_mem_normal_form_two {ι : Type} (ts : List ι) (f : ι → A) (h : ∀ x ∈ ts, f x ∈ NormalFormTwo L S d (ℓ + 1)) :
      (ts.map f).sum ∈ NormalFormTwo L S d (ℓ + 1) := by
    induction ts with
    | nil => simp
    | cons a ts ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem letterA (hS : Hyp L S) (y : ℂ) {n : ℕ} {x : A} (hx : x ∈ NormalFormTwo L S n n) :
    L.Di * L.Ahat y * x ∈ NormalFormTwo L S (n + 1) (n + 1) := by
  rw [mul_assoc]; exact normal_form_D_inv hS (normal_form_two_hat hS y hx)

theorem letterR (hS : Hyp L S) (y : ℂ) {n : ℕ} {x : A} (hx : x ∈ NormalFormTwo L S n n) :
    L.Dbi * L.R0 y * x ∈ NormalFormTwo L S (n + 1) (n + 1) := by
  rw [mul_assoc]; exact normal_form_two_D_bar_inv hS (normal_form_two_raising hS y hx)

theorem one_mem_normal_form_two (hS : Hyp L S) : (1 : A) ∈ NormalFormTwo L S 0 0 := by
  have : tm L 1 0 0 [] = 1 := by simp [tm]
  rw [← this]; exact mem2 S.one_mem rfl rfl (by simp)

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H6

section S_H_H7

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} {L : LevelData A r}

def RaisingCommutesModulo (L : LevelData A r) (M : Set A) (b : A) : Prop :=
  ∀ Y, ∃ (t : ℂ) (ts : List (ℂ × A × ℂ)), (∀ x ∈ ts, x.2.1 ∈ M) ∧
    L.R0 Y * b = b * L.R0 (Y + t) + (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum

theorem hyp_closure (T : Set A)
    (hDi : ∀ b ∈ T, b * L.Di = L.Di * b) (hDbi : ∀ b ∈ T, b * L.Dbi = L.Dbi * b)
    (hA : ∀ b ∈ T, ∃ t : ℂ, ∀ Y, L.Ahat Y * b = b * L.Ahat (Y + t))
    (hR : ∀ b ∈ T, RaisingCommutesModulo L (Submonoid.closure T) b)
    (hdrb : L.Drb * L.Di ∈ Submonoid.closure T) : Hyp L (Submonoid.closure T) := by

  have P1 : ∀ b ∈ Submonoid.closure T, (b * L.Di = L.Di * b) ∧ (b * L.Dbi = L.Dbi * b) ∧
      (∃ t : ℂ, ∀ Y, L.Ahat Y * b = b * L.Ahat (Y + t)) ∧ RaisingCommutesModulo L (Submonoid.closure T) b := by
    intro b hb
    induction hb using Submonoid.closure_induction with
    | mem x hx => exact ⟨hDi x hx, hDbi x hx, hA x hx, hR x hx⟩
    | one => exact ⟨by simp, by simp, ⟨0, fun Y => by simp⟩, fun Y => ⟨0, [], by simp, by simp⟩⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨x1, x2, ⟨tx, htx⟩, rx⟩ := ihx
      obtain ⟨y1, y2, ⟨ty, hty⟩, ry⟩ := ihy
      refine ⟨by rw [mul_assoc, y1, ← mul_assoc, x1, mul_assoc], by rw [mul_assoc, y2, ← mul_assoc, x2, mul_assoc],
        ⟨tx + ty, fun Y => by rw [← mul_assoc, htx, mul_assoc, hty, mul_assoc, add_assoc]⟩, fun Y => ?_⟩
      obtain ⟨t1, ts1, hts1, e1⟩ := rx Y
      obtain ⟨t2, ts2, hts2, e2⟩ := ry (Y + t1)
      refine ⟨t1 + t2, (ts1.map fun z => (z.1, z.2.1 * y, z.2.2 + ty)) ++ (ts2.map fun z => (z.1, x * z.2.1, z.2.2)),
        ?_, ?_⟩
      · intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hz
          exact Submonoid.mul_mem _ (hts1 z' hz') hy
        · obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hz
          exact Submonoid.mul_mem _ hx (hts2 z' hz')
      · have s1 : (ts1.map fun z => z.1 • (z.2.1 * L.Ahat z.2.2)).sum * y =
            ((ts1.map fun z => (z.1, z.2.1 * y, z.2.2 + ty)).map fun z => z.1 • (z.2.1 * L.Ahat z.2.2)).sum := by
          rw [← List.sum_map_mul_right, List.map_map]
          congr 1
          refine List.map_congr_left fun z _ => ?_
          simp only [Function.comp_apply, smul_mul_assoc, mul_assoc, hty]
        have s2 : x * (ts2.map fun z => z.1 • (z.2.1 * L.Ahat z.2.2)).sum =
            ((ts2.map fun z => (z.1, x * z.2.1, z.2.2)).map fun z => z.1 • (z.2.1 * L.Ahat z.2.2)).sum := by
          rw [← List.sum_map_mul_left, List.map_map]
          congr 1
          refine List.map_congr_left fun z _ => ?_
          simp only [Function.comp_apply, mul_smul_comm, mul_assoc]
        calc L.R0 Y * (x * y) = (L.R0 Y * x) * y := by rw [mul_assoc]
          _ = x * (L.R0 (Y + t1) * y) + (ts1.map fun z => z.1 • (z.2.1 * L.Ahat z.2.2)).sum * y := by
              rw [e1, add_mul, mul_assoc]
          _ = _ := by
              rw [e2, s1, mul_add, s2, List.map_append, List.sum_append, ← mul_assoc, add_assoc Y]
              abel
  exact ⟨fun b hb => (P1 b hb).1, fun b hb => (P1 b hb).2.1, fun b hb => (P1 b hb).2.2.1,
    fun b hb Y => (P1 b hb).2.2.2 Y, hdrb⟩

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H7

section S_H_H8

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx2.Jet

noncomputable section

variable (P : M.Par)

def DG : Subalgebra ℂ (A P (DQ P)) := (Matrix.diagonalAlgHom ℂ : (M.Ty P → (DQ P).Pr) →ₐ[ℂ] A P (DQ P)).range

def SC : Subring (A P (DQ P)) := (Matrix.scalar (M.Ty P) : (DQ P).Pr →+* A P (DQ P)).range

theorem diag_memDG (d : M.Ty P → (DQ P).Pr) : Matrix.diagonal d ∈ DG P := ⟨d, rfl⟩
theorem sc_memDG (w : (DQ P).Pr) : sc P (DQ P) w ∈ DG P := ⟨fun _ => w, rfl⟩
theorem sc_memSC (w : (DQ P).Pr) : sc P (DQ P) w ∈ SC P := ⟨w, rfl⟩

theorem kap_comm_DG (f : M.Ty P → ℂ) {x : A P (DQ P)} (hx : x ∈ DG P) : kap P (DQ P) f * x = x * kap P (DQ P) f := by
  obtain ⟨d, rfl⟩ := hx
  show Matrix.diagonal (fun π => algebraMap ℂ (DQ P).Pr (f π)) * Matrix.diagonal d =
    Matrix.diagonal d * Matrix.diagonal (fun π => algebraMap ℂ (DQ P).Pr (f π))
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext π; exact Algebra.commutes _ _

theorem SS_comm_SC (i : ℕ) {x : A P (DQ P)} (hx : x ∈ SC P) : SS P (DQ P) i * x = x * SS P (DQ P) i := by
  obtain ⟨w, rfl⟩ := hx
  ext π' π
  show (SS P (DQ P) i * Matrix.scalar (M.Ty P) w) π' π = (Matrix.scalar (M.Ty P) w * SS P (DQ P) i) π' π
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]
  split_ifs
  · exact Algebra.commutes (R := ℂ) _ _
  · simp

section Lev
variable {P} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hL

theorem levDG : (∀ l, L.p l ∈ DG P) ∧ (∀ l, L.c l ∈ DG P) ∧ (∀ l, L.ci l ∈ DG P) ∧ (∀ l, L.cb l ∈ DG P) ∧
    (∀ l, L.cbi l ∈ DG P) ∧ L.ζ ∈ DG P ∧ L.ζi ∈ DG P ∧ L.ζb ∈ DG P ∧ L.ζbi ∈ DG P ∧ L.GG ∈ DG P ∧
    L.GGi ∈ DG P ∧ L.nab ∈ DG P := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [hp]; exact sc_memDG P _) | (rw [hc]; exact sc_memDG P _) | (rw [hci]; exact sc_memDG P _)
    | (rw [hcb]; exact sc_memDG P _) | (rw [hcbi]; exact sc_memDG P _) | (rw [hz]; exact sc_memDG P _)
    | (rw [hzi]; exact sc_memDG P _) | (rw [hzb]; exact sc_memDG P _) | (rw [hzbi]; exact sc_memDG P _)
    | (rw [hg]; exact sc_memDG P _) | (rw [hgi]; exact sc_memDG P _) | (rw [hn]; exact diag_memDG P _)

theorem levSC : (∀ l, L.c l ∈ SC P) ∧ (∀ l, L.ci l ∈ SC P) ∧ (∀ l, L.cb l ∈ SC P) ∧ (∀ l, L.cbi l ∈ SC P) ∧
    L.ζ ∈ SC P ∧ L.ζi ∈ SC P ∧ L.ζb ∈ SC P ∧ L.ζbi ∈ SC P ∧ L.GG ∈ SC P ∧ L.GGi ∈ SC P := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [hc]; exact sc_memSC P _) | (rw [hci]; exact sc_memSC P _)
    | (rw [hcb]; exact sc_memSC P _) | (rw [hcbi]; exact sc_memSC P _) | (rw [hz]; exact sc_memSC P _)
    | (rw [hzi]; exact sc_memSC P _) | (rw [hzb]; exact sc_memSC P _) | (rw [hzbi]; exact sc_memSC P _)
    | (rw [hg]; exact sc_memSC P _) | (rw [hgi]; exact sc_memSC P _)

theorem DrSC : L.Dr ∈ SC P ∧ L.Drb ∈ SC P ∧ L.Dri ∈ SC P ∧ L.Drbi ∈ SC P := by
  obtain ⟨hc, hci, hcb, hcbi, -⟩ := levSC hL
  refine ⟨Subring.list_prod_mem _ fun x hx => ?_, Subring.list_prod_mem _ fun x hx => ?_,
    Subring.list_prod_mem _ fun x hx => ?_, Subring.list_prod_mem _ fun x hx => ?_⟩ <;>
  · obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
    first | exact hc l | exact hcb l | exact hci l | exact hcbi l

theorem DSC : L.D ∈ SC P ∧ L.Di ∈ SC P ∧ L.Db ∈ SC P ∧ L.Dbi ∈ SC P := by
  obtain ⟨-, -, -, -, hz, hzi, hzb, hzbi, -⟩ := levSC hL
  obtain ⟨d1, d2, d3, d4⟩ := DrSC hL
  exact ⟨Subring.mul_mem _ d1 hz, Subring.mul_mem _ hzi d3, Subring.mul_mem _ d2 hzb, Subring.mul_mem _ hzbi d4⟩

theorem hatDG (Y : ℂ) : L.Ahat Y ∈ DG P ∧ L.R0 Y ∈ DG P := by
  obtain ⟨hp, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn⟩ := levDG hL
  have hDr : L.Dr ∈ DG P := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hc l
  have hDrb : L.Drb ∈ DG P := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hcb l
  have hT : L.Tprod Y ∈ matSub (DG P) (Fin 2) := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hx)
    exact matrix_two_mem_sub _ _ _ _ _ (add_mem (Subalgebra.algebraMap_mem _ _) (hp l)) (neg_mem (hc l)) (hci l)
      (Subalgebra.zero_mem _)
  refine ⟨mul_mem hDr (hT 0 0), mul_mem (mul_mem hDrb hg) (add_mem (mul_mem (sub_mem (neg_mem hn)
    (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hzb hgi))) (hT 0 0)) (hT 1 0))⟩

end Lev

end

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H8

section S_H_H9

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

def e (x : A) (hx : x ∈ Subring.closure (FS L)) : CF L := ⟨x, hx⟩

theorem rev_prod {l : List A} (hl : ∀ x ∈ l, x ∈ Subring.closure (FS L)) : l.reverse.prod = l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.reverse_cons, List.prod_append, List.prod_singleton, List.prod_cons,
      ih fun x hx => hl x (by simp [hx])]
    exact (cl_comm L (hl a (by simp)) (Subring.list_prod_mem _ fun x hx => hl x (by simp [hx]))).symm

theorem hat_ζi (Y : ℂ) : L.Ahat Y * L.ζi = L.ζi * L.Ahat Y ∧
    L.R0 Y * L.ζi = L.ζi * L.R0 Y + L.ζi * L.Drb * L.GG * L.ζi * L.Ar Y := by
  have hfx : ∀ x ∈ L.fns, cj L.ζi L.ζ L.ζi_ζ L.ζ_ζi x = x := fun x hx => cj_fix _ _ _ _ (fc L hx (m_ζi L))
  have hnab : cj L.ζi L.ζ L.ζi_ζ L.ζ_ζi L.nab = L.nab + algebraMap ℂ A 0 * (L.ζb * L.GGi) - L.ζi := by
    rw [cj_of_eq _ _ _ _ (a := -L.ζi) (by rw [L.nab_ζi, neg_mul]; abel), map_neg, hfx _ (m_ζi L), map_zero,
      zero_mul, add_zero, sub_eq_add_neg]
  obtain ⟨a1, a2⟩ := keyA L (cj L.ζi L.ζ L.ζi_ζ L.ζ_ζi) 0 L.ζi (cj_alg _ _ _ _)
    (fun l => by rw [map_zero, add_zero]; exact cj_fix _ _ _ _ (L.p_ζi l))
    (fun l => hfx _ (m_c L l)) (fun l => hfx _ (m_ci L l)) (fun l => hfx _ (m_cb L l))
    (hfx _ (m_GG L)) (hfx _ (m_ζb L)) (hfx _ (m_GGi L)) hnab Y
  rw [add_zero, cj_apply] at a1 a2
  constructor
  · calc L.Ahat Y * L.ζi = L.ζi * (L.ζ * L.Ahat Y * L.ζi) := by
          rw [← mul_assoc, ← mul_assoc, L.ζi_ζ, one_mul]
      _ = L.ζi * L.Ahat Y := by rw [a1]
  · calc L.R0 Y * L.ζi = L.ζi * (L.ζ * L.R0 Y * L.ζi) := by
          rw [← mul_assoc, ← mul_assoc, L.ζi_ζ, one_mul]
      _ = _ := by rw [a2, mul_add]; simp only [mul_assoc]

theorem Ar_eq (Y : ℂ) : L.Ar Y = L.Dri * L.Ahat Y := by
  unfold LevelData.Ahat; rw [← mul_assoc, Dri_Dr, one_mul]

theorem memζ : L.ζ ∈ Subring.closure (FS L) := memF L (m_ζ L)
theorem memζi : L.ζi ∈ Subring.closure (FS L) := memF L (m_ζi L)
theorem memζb : L.ζb ∈ Subring.closure (FS L) := memF L (m_ζb L)
theorem memζbi : L.ζbi ∈ Subring.closure (FS L) := memF L (m_ζbi L)
theorem memGG : L.GG ∈ Subring.closure (FS L) := memF L (m_GG L)

theorem coef_ζi : L.ζi * L.Drb * L.GG * L.ζi * L.Dri =
    L.Db * L.Di - algebraMap ℂ A L.TT * (L.ζi * L.ζbi * (L.Db * L.Di)) := by
  have h1 : e L L.ζ (memζ L) * e L L.ζi (memζi L) = 1 := Subtype.ext L.ζ_ζi
  have h2 : e L L.ζb (memζb L) * e L L.ζbi (memζbi L) = 1 := Subtype.ext L.ζb_ζbi
  have hG : e L L.GG (memGG L) = e L L.ζ (memζ L) * e L L.ζb (memζb L) - e L _ (memS L L.TT) :=
    Subtype.ext L.GG_def
  have key : e L L.ζi (memζi L) * e L L.Drb (memDrb L) * e L L.GG (memGG L) * e L L.ζi (memζi L) *
      e L L.Dri (memDri L) = e L L.Drb (memDrb L) * e L L.ζb (memζb L) * (e L L.ζi (memζi L) * e L L.Dri (memDri L)) -
      e L _ (memS L L.TT) * (e L L.ζi (memζi L) * e L L.ζbi (memζbi L) * (e L L.Drb (memDrb L) * e L L.ζb (memζb L) *
        (e L L.ζi (memζi L) * e L L.Dri (memDri L)))) := by
    rw [hG]; linear_combination (e L L.ζi (memζi L) * e L L.Drb (memDrb L) * e L L.ζb (memζb L) * e L L.Dri (memDri L)) * h1 +
      (e L _ (memS L L.TT) * e L L.ζi (memζi L) * e L L.ζi (memζi L) * e L L.Drb (memDrb L) * e L L.Dri (memDri L)) * h2
  have := congrArg Subtype.val key
  simpa [e, LevelData.Db, LevelData.Di, mul_assoc] using this

theorem drb_eq : L.Drb * L.Di = L.Db * L.Di * L.ζbi := by
  have h2 : e L L.ζb (memζb L) * e L L.ζbi (memζbi L) = 1 := Subtype.ext L.ζb_ζbi
  have key : e L L.Drb (memDrb L) * (e L L.ζi (memζi L) * e L L.Dri (memDri L)) =
      e L L.Drb (memDrb L) * e L L.ζb (memζb L) * (e L L.ζi (memζi L) * e L L.Dri (memDri L)) * e L L.ζbi (memζbi L) := by
    linear_combination (-(e L L.Drb (memDrb L) * e L L.ζi (memζi L) * e L L.Dri (memDri L))) * h2
  have := congrArg Subtype.val key
  simpa [e, LevelData.Db, LevelData.Di, mul_assoc] using this

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H9

section S_H_H10

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem Ahat_D (Y : ℂ) : L.Ahat Y * L.D = L.D * L.Ahat (Y + 1) := by
  rw [← (Formalism.FourierDecayAlt.P.shiftConjugation A r L Y).1, ← mul_assoc, ← mul_assoc, D_Di, one_mul]

theorem raising_mul_D (Y : ℂ) : L.R0 Y * L.D = L.D * (L.R0 (Y + 1) + L.TT • (L.Drb * L.Di * L.Ahat (Y + 1))) := by
  rw [Algebra.smul_def, ← (Formalism.FourierDecayAlt.P.shiftConjugation A r L Y).2.1, ← mul_assoc, ← mul_assoc, D_Di, one_mul]

theorem raising_mul_D_inv_expanded (Y : ℂ) : L.R0 Y * L.Di = L.Di * L.R0 (Y - 1) - L.TT • (L.Di * (L.Drb * L.Di) * L.Ahat (Y - 1)) := by
  rw [raising_mul_D_inv, mul_sub, Algebra.smul_def, ← mul_assoc, ← mul_assoc, ← Algebra.commutes L.TT L.Di]
  simp only [mul_assoc]

theorem memDD : L.D * L.Dbi ∈ Subring.closure (FS L) := Subring.mul_mem _ (memD L) (memDbi L)
theorem memDbD : L.Db * L.Di ∈ Subring.closure (FS L) := Subring.mul_mem _ (memDb L) (memDi L)
theorem memDrbDi : L.Drb * L.Di ∈ Subring.closure (FS L) := Subring.mul_mem _ (memDrb L) (memDi L)

theorem gen_DD_A (Y : ℂ) : L.Ahat Y * (L.D * L.Dbi) = L.D * L.Dbi * L.Ahat (Y + 1) := by
  rw [← mul_assoc, Ahat_D, mul_assoc, ← (hat_Dbi L (Y + 1)).1, mul_assoc]

theorem gen_DD_R (Y : ℂ) : L.R0 Y * (L.D * L.Dbi) = L.D * L.Dbi * L.R0 (Y + 1) +
    L.TT • (L.D * L.Dbi * (L.Drb * L.Di) * L.Ahat (Y + 1)) := by
  have hf : L.D * (L.Drb * L.Di) * L.Dbi = L.D * L.Dbi * (L.Drb * L.Di) := by
    have := congrArg Subtype.val (show e L _ (memD L) * (e L _ (memDrb L) * e L _ (memDi L)) * e L _ (memDbi L) =
      e L _ (memD L) * e L _ (memDbi L) * (e L _ (memDrb L) * e L _ (memDi L)) by ring)
    simpa [e] using this
  calc L.R0 Y * (L.D * L.Dbi) = L.R0 Y * L.D * L.Dbi := (mul_assoc _ _ _).symm
    _ = L.D * (L.R0 (Y + 1) * L.Dbi) + L.TT • (L.D * (L.Drb * L.Di) * (L.Ahat (Y + 1) * L.Dbi)) := by
        rw [raising_mul_D, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]; simp only [mul_assoc]
    _ = _ := by
        rw [← (hat_Dbi L (Y + 1)).1, ← (hat_Dbi L (Y + 1)).2, ← mul_assoc (L.D * (L.Drb * L.Di)), hf]
        simp only [mul_assoc]

theorem gen_DbD_A (Y : ℂ) : L.Ahat Y * (L.Db * L.Di) = L.Db * L.Di * L.Ahat (Y + -1) := by
  rw [← mul_assoc, ← (hat_Db L Y).1, mul_assoc, Ahat_Di, ← mul_assoc, sub_eq_add_neg]

theorem gen_DbD_R (Y : ℂ) : L.R0 Y * (L.Db * L.Di) = L.Db * L.Di * L.R0 (Y + -1) +
    (-L.TT) • (L.Db * L.Di * (L.Drb * L.Di) * L.Ahat (Y + -1)) := by
  rw [← mul_assoc, ← (hat_Db L Y).2, mul_assoc, raising_mul_D_inv_expanded, ← sub_eq_add_neg, mul_sub, neg_smul, ← sub_eq_add_neg,
    mul_smul_comm]
  simp only [mul_assoc]

theorem gen_ζi_R (Y : ℂ) : L.R0 Y * L.ζi = L.ζi * L.R0 (Y + 0) +
    ([((1 : ℂ), L.Db * L.Di, Y), (-L.TT, L.ζi * L.ζbi * (L.Db * L.Di), Y)].map
      fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum := by
  rw [add_zero, (hat_ζi L Y).2, Ar_eq]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  have := coef_ζi L
  calc L.ζi * L.Drb * L.GG * L.ζi * (L.Dri * L.Ahat Y) = (L.ζi * L.Drb * L.GG * L.ζi * L.Dri) * L.Ahat Y := by
        simp only [mul_assoc]
    _ = _ := by
        rw [this, sub_mul, one_smul, neg_smul, ← sub_eq_add_neg, Algebra.smul_def, mul_assoc (algebraMap ℂ A L.TT)]

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H10

section S_H_H11

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r}

theorem SSs_comm_SC (i : ℕ) {x : A P (DQ P)} (hx : x ∈ SC P) :
    star (SS P (DQ P) i) * x = x * star (SS P (DQ P) i) := by
  have h := SS_comm_SC P i (x := star x) (by
    obtain ⟨w, rfl⟩ := hx
    refine ⟨star w, ?_⟩
    ext a b
    rw [Matrix.star_apply]
    simp only [RingHom.coe_coe, Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h])
  have := congrArg star h
  simpa [star_mul] using this.symm

theorem star_list_prod' (l : List (A P (DQ P))) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.prod_cons, star_mul, ih, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]

variable (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL

theorem fnsSC : ∀ x ∈ L.fns, x ∈ SC P := by
  obtain ⟨hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi⟩ := levSC hL
  intro x hx
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
  exacts [hc l, hci l, hcb l, hcbi l, hz, hzi, hzb, hzbi, hg, hgi]

theorem pSC (l : Fin P.r) : L.p l ∈ SC P ∧ L.pb l ∈ SC P := by
  obtain ⟨hp, hpb, -⟩ := hL
  exact ⟨by rw [hp]; exact sc_memSC P _, by rw [hpb]; exact sc_memSC P _⟩

include hLaw

theorem star_fields : star L.nab = L.nabs ∧ star L.nabs = L.nab ∧ star L.ζ = L.ζb ∧ star L.ζb = L.ζ ∧
    star L.GGi = L.GGi ∧ (∀ l, star (L.cb l) = L.c l) ∧ (∀ l, star (L.ci l) = L.cbi l) := by
  have : Fact ((DQ P).Laws P.TT) := ⟨hLaw⟩
  have hs := Formalism.FourierDecayAlt.P.MAx1.starGens P (DQ P)
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, -, hzb, -, -, hgi, hn, hns, -⟩ := hL
  refine ⟨by rw [hn, hns]; exact hs.2.2.2.2.2, by rw [hn, hns, ← hs.2.2.2.2.2, star_star],
    by rw [hz, hzb]; exact hs.2.1, by rw [hz, hzb, ← hs.2.1, star_star], by rw [hgi]; exact hs.2.2.2.2.1,
    fun l => by rw [hcb, hc, ← (hs.1 l).1, star_star], fun l => by rw [hci, hcbi]; exact (hs.1 l).2.1⟩

theorem star_Drb : star L.Drb = L.Dr := by
  obtain ⟨-, -, -, -, -, hcb, -⟩ := star_fields hL hLaw
  unfold LevelData.Drb LevelData.Dr
  rw [star_list_prod', List.map_ofFn]
  have : (star ∘ L.cb) = L.c := funext hcb
  rw [this, rev_prod L]
  intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_c L l)

theorem star_Dri : star L.Dri = L.Drbi := by
  obtain ⟨-, -, -, -, -, -, hci⟩ := star_fields hL hLaw
  unfold LevelData.Dri LevelData.Drbi
  rw [star_list_prod', List.map_ofFn]
  have : (star ∘ L.ci) = L.cbi := funext hci
  rw [this, rev_prod L]
  intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_cbi L l)

end

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H11

section S_H_H12

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem SS_rel (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    L.nab * SS P (DQ P) i = SS P (DQ P) i * L.nab - L.ζb * L.GGi * SS P (DQ P) i ∧
    L.nabs * SS P (DQ P) i = SS P (DQ P) i * L.nabs - L.ζ * L.GGi * SS P (DQ P) i := by
  have : Fact ((DQ P).Laws P.TT) := ⟨hLaw⟩
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, hgi, hn, hns, -⟩ := hL
  rw [hn, hns, hz, hzb, hgi]
  exact Formalism.FourierDecayAlt.P.MAx1.nabSS P (DQ P) i hi

theorem SSs_rel (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    L.nab * star (SS P (DQ P) i) = star (SS P (DQ P) i) * L.nab + L.ζb * L.GGi * star (SS P (DQ P) i) ∧
    L.nabs * star (SS P (DQ P) i) = star (SS P (DQ P) i) * L.nabs + L.ζ * L.GGi * star (SS P (DQ P) i) := by
  obtain ⟨h1, h2⟩ := SS_rel hL hLaw i hi
  obtain ⟨sn, sns, sz, szb, sgi, -, -⟩ := star_fields hL hLaw
  obtain ⟨-, -, -, -, hz, -, hzb, -, -, hgi⟩ := levSC hL
  have c1 : star (SS P (DQ P) i) * (L.GGi * L.ζb) = L.ζb * L.GGi * star (SS P (DQ P) i) := by
    rw [← mul_assoc, SSs_comm_SC i hgi, mul_assoc, SSs_comm_SC i hzb, ← mul_assoc,
      Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memF L (m_GGi L)) (memζb L)]
  have c2 : star (SS P (DQ P) i) * (L.GGi * L.ζ) = L.ζ * L.GGi * star (SS P (DQ P) i) := by
    rw [← mul_assoc, SSs_comm_SC i hgi, mul_assoc, SSs_comm_SC i hz, ← mul_assoc,
      Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memF L (m_GGi L)) (memζ L)]
  constructor
  · have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sns, sz, sgi] at this
    rw [← c1, ← mul_assoc]
    rw [this]; simp only [mul_assoc]; abel
  · have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sn, szb, sgi] at this
    rw [← c2, ← mul_assoc]
    rw [this]; simp only [mul_assoc]; abel

end

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H12

section S_H_H13

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.H

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem ruleSS_SS (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    L.Ahat Y * (L.Drb * L.Dri * SS P (DQ P) i) = (L.Drb * L.Dri * SS P (DQ P) i) * L.Ahat (Y - 1) ∧
    L.R0 Y * (L.Drb * L.Dri * SS P (DQ P) i) = (L.Drb * L.Dri * SS P (DQ P) i) * L.R0 (Y - 1) := by
  obtain ⟨h1, h2⟩ := SS_rel hL hLaw i hi
  have hf : ∀ x ∈ L.fns, x * SS P (DQ P) i = SS P (DQ P) i * x := fun x hx => (SS_comm_SC P i (fnsSC hL x hx)).symm
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r L (SS P (DQ P) i) 0 hf (fun l => (SS_comm_SC P i (pSC hL l).1).symm)
    (fun l => (SS_comm_SC P i (pSC hL l).2).symm) h1 h2 (fun x _ => by simp) (fun l => by simp) (fun l => by simp)
    (by simp) (by simp) Y
  exact ⟨h.1, h.2.1⟩

theorem starSSn_eq (i : ℕ) : star (L.Drb * L.Dri * SS P (DQ P) i) = star (SS P (DQ P) i) * (L.Dr * L.Drbi) := by
  rw [star_mul, star_mul, star_Drb hL hLaw, star_Dri hL hLaw,
    Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memDrbi L) (memDr L)]

theorem ruleSS_SSs (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    L.Ahat Y * star (L.Drb * L.Dri * SS P (DQ P) i) = star (L.Drb * L.Dri * SS P (DQ P) i) * L.Ahat (Y + 1) ∧
    L.R0 Y * star (L.Drb * L.Dri * SS P (DQ P) i) = star (L.Drb * L.Dri * SS P (DQ P) i) * L.R0 (Y + 1) := by
  obtain ⟨h1, h2⟩ := SSs_rel hL hLaw i hi
  have hf : ∀ x ∈ L.fns, x * star (SS P (DQ P) i) = star (SS P (DQ P) i) * x :=
    fun x hx => (SSs_comm_SC i (fnsSC hL x hx)).symm
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r L 0 (star (SS P (DQ P) i)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) hf (fun l => (SSs_comm_SC i (pSC hL l).1).symm)
    (fun l => (SSs_comm_SC i (pSC hL l).2).symm) h1 h2 Y
  rw [starSSn_eq hL hLaw]
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem hyp_model : Hyp L (Submonoid.closure (bddSet P L)) := by
  have gen : ∀ {x}, x ∈ bddSet P L → x ∈ Submonoid.closure (bddSet P L) := fun h => Submonoid.subset_closure h
  have mDD : L.D * L.Dbi ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have mDbD : L.Db * L.Di ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have mζi : L.ζi ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have mζbi : L.ζbi ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have hdrb : L.Drb * L.Di ∈ Submonoid.closure (bddSet P L) := by
    rw [drb_eq]; exact Submonoid.mul_mem _ (gen mDbD) (gen mζbi)
  obtain ⟨-, hDi, -, hDbi⟩ := DSC hL
  have DiDG : L.Di ∈ DG P := by obtain ⟨w, hw⟩ := hDi; rw [← hw]; exact sc_memDG P w
  have DbiDG : L.Dbi ∈ DG P := by obtain ⟨w, hw⟩ := hDbi; rw [← hw]; exact sc_memDG P w
  have ssc : ∀ i, L.Drb * L.Dri * SS P (DQ P) i * L.Di = L.Di * (L.Drb * L.Dri * SS P (DQ P) i) ∧
      L.Drb * L.Dri * SS P (DQ P) i * L.Dbi = L.Dbi * (L.Drb * L.Dri * SS P (DQ P) i) := by
    intro i
    have c1 : L.Drb * L.Dri * L.Di = L.Di * (L.Drb * L.Dri) :=
      Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Subring.mul_mem _ (memDrb L) (memDri L)) (memDi L)
    have c2 : L.Drb * L.Dri * L.Dbi = L.Dbi * (L.Drb * L.Dri) :=
      Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Subring.mul_mem _ (memDrb L) (memDri L)) (memDbi L)
    exact ⟨by rw [mul_assoc, SS_comm_SC P i hDi, ← mul_assoc, c1, mul_assoc],
      by rw [mul_assoc, SS_comm_SC P i hDbi, ← mul_assoc, c2, mul_assoc]⟩
  have sssc : ∀ i, star (L.Drb * L.Dri * SS P (DQ P) i) * L.Di = L.Di * star (L.Drb * L.Dri * SS P (DQ P) i) ∧
      star (L.Drb * L.Dri * SS P (DQ P) i) * L.Dbi = L.Dbi * star (L.Drb * L.Dri * SS P (DQ P) i) := by
    intro i
    have c1 : L.Dr * L.Drbi * L.Di = L.Di * (L.Dr * L.Drbi) :=
      Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Subring.mul_mem _ (memDr L) (memDrbi L)) (memDi L)
    have c2 : L.Dr * L.Drbi * L.Dbi = L.Dbi * (L.Dr * L.Drbi) :=
      Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Subring.mul_mem _ (memDr L) (memDrbi L)) (memDbi L)
    rw [starSSn_eq hL hLaw]
    exact ⟨by rw [mul_assoc, c1, ← mul_assoc, SSs_comm_SC i hDi, mul_assoc],
      by rw [mul_assoc, c2, ← mul_assoc, SSs_comm_SC i hDbi, mul_assoc]⟩
  refine hyp_closure (bddSet P L) ?_ ?_ ?_ ?_ hdrb
  · rintro b ((((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memζi L) (memDi L)
      · exact Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memζbi L) (memDi L)
      · exact Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memDD L) (memDi L)
      · exact Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memDbD L) (memDi L)
    · exact kap_comm_DG P f DiDG
    · exact (ssc i).1
    · exact (sssc i).1
  · rintro b ((((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memζi L) (memDbi L)
      · exact Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memζbi L) (memDbi L)
      · exact Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memDD L) (memDbi L)
      · exact Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (memDbD L) (memDbi L)
    · exact kap_comm_DG P f DbiDG
    · exact (ssc i).2
    · exact (sssc i).2
  · rintro b ((((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact ⟨0, fun Y => by rw [add_zero]; exact (hat_ζi L Y).1⟩
      · exact ⟨0, fun Y => by rw [add_zero]; exact (hat_ζbi L Y).1.symm⟩
      · exact ⟨1, gen_DD_A L⟩
      · exact ⟨-1, gen_DbD_A L⟩
    · exact ⟨0, fun Y => by rw [add_zero]; exact (kap_comm_DG P f (hatDG hL Y).1).symm⟩
    · exact ⟨-1, fun Y => by rw [← sub_eq_add_neg]; exact (ruleSS_SS hL hLaw i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) Y).1⟩
    · exact ⟨1, fun Y => (ruleSS_SSs hL hLaw i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) Y).1⟩
  · rintro b ((((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)) Y
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · refine ⟨0, _, ?_, gen_ζi_R L Y⟩
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact gen mDbD
        · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (gen mζi) (gen mζbi)) (gen mDbD)
      · exact ⟨0, [], by simp, by rw [add_zero]; simpa using (hat_ζbi L Y).2.symm⟩
      · refine ⟨1, [(L.TT, L.D * L.Dbi * (L.Drb * L.Di), Y + 1)], ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; exact Submonoid.mul_mem _ (gen mDD) hdrb
        · rw [gen_DD_R]; simp
      · refine ⟨-1, [(-L.TT, L.Db * L.Di * (L.Drb * L.Di), Y + -1)], ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; exact Submonoid.mul_mem _ (gen mDbD) hdrb
        · rw [gen_DbD_R]; simp
    · exact ⟨0, [], by simp, by rw [add_zero]; simpa using (kap_comm_DG P f (hatDG hL Y).2).symm⟩
    · exact ⟨-1, [], by simp, by rw [← sub_eq_add_neg]; simpa using (ruleSS_SS hL hLaw i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) Y).2⟩
    · exact ⟨1, [], by simp, by simpa using (ruleSS_SSs hL hLaw i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) Y).2⟩

end

end Formalism.FourierDecayAlt.P.MAx3.H

end S_H_H13

section S_I4_I1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

variable {P : M.Par}

abbrev BA (L : LevelData (A P (DQ P)) P.r) : Subalgebra ℂ (A P (DQ P)) := Algebra.adjoin ℂ (bddSet P L)

abbrev UB (L : LevelData (A P (DQ P)) P.r) (S : Type) [Fintype S] [DecidableEq S] : Subalgebra ℂ (SlopeTestRemainingChoices S (A P (DQ P))) :=
  MAx2.Jet.matSub (BA L) (Ix S)

abbrev SB (L : LevelData (A P (DQ P)) P.r) : Submonoid (A P (DQ P)) := Submonoid.closure (bddSet P L)

theorem tm_mul_left (L : LevelData (A P (DQ P)) P.r) (x b : A P (DQ P)) (i i' : ℕ) (H : List (A P (DQ P))) :
    x * tm L b i i' H = tm L (x * b) i i' H := by
  unfold tm; simp only [mul_assoc]

theorem base_mul_normal_form {L : LevelData (A P (DQ P)) P.r} {x : A P (DQ P)} (hx : x ∈ BA L) {d ℓ : ℕ}
    {y : A P (DQ P)} (hy : y ∈ NormalFormTwo L (SB L) d ℓ) : x * y ∈ NormalFormTwo L (SB L) d ℓ := by
  induction hx using Algebra.adjoin_induction generalizing y with
  | mem x hx =>
    refine span_mul _ (fun z hz => ?_) hy
    obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hz
    rw [tm_mul_left]
    exact mem2 (Submonoid.mul_mem _ (Submonoid.subset_closure hx) hb) h1 h2 h3
  | algebraMap c => rw [← Algebra.smul_def]; exact Submodule.smul_mem _ c hy
  | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ (h1 hy) (h2 hy)
  | mul x x' _ _ h1 h2 => rw [mul_assoc]; exact h1 (h2 hy)

section frame
variable {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem gen_BA {x : A P (DQ P)} (hx : x ∈ bddSet P L) : x ∈ BA L := Algebra.subset_adjoin hx

theorem kap_BA (f : M.Ty P → ℂ) : kap P (DQ P) f ∈ BA L := gen_BA hL hLaw (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))
theorem ζbi_BA : L.ζbi ∈ BA L := gen_BA hL hLaw (Or.inl (Or.inl (Or.inl (by simp))))

theorem ζζbi_eq : L.ζ * L.ζbi = L.D * L.Dbi * (L.Drb * L.Dri) := by
  have h1 : e L L.Dr (memDr L) * e L L.Dri (memDri L) = 1 := Subtype.ext (RuleGD.Dr_Dri L)
  have h2 : e L L.Drb (memDrb L) * e L L.Drbi (memDrbi L) = 1 := Subtype.ext (RuleGD.Drb_Drbi L)
  have key : e L L.ζ (memζ L) * e L L.ζbi (memζbi L) = e L L.Dr (memDr L) * e L L.ζ (memζ L) *
      (e L L.ζbi (memζbi L) * e L L.Drbi (memDrbi L)) * (e L L.Drb (memDrb L) * e L L.Dri (memDri L)) := by
    linear_combination (-(e L L.ζ (memζ L) * e L L.ζbi (memζbi L) * e L L.Drb (memDrb L) * e L L.Drbi (memDrbi L))) * h1 +
      (-(e L L.ζ (memζ L) * e L L.ζbi (memζbi L))) * h2
  have := congrArg Subtype.val key
  simpa [e, LevelData.D, LevelData.Dbi, mul_assoc] using this

theorem eeA_BA (Y : ℂ) : eeA P (DQ P) Y ∈ BA L := by
  obtain ⟨-, -, -, -, -, -, hz, -, -, hzbi, -⟩ := id hL
  have hDrDG : L.Drb * L.Dri ∈ DG P := by
    obtain ⟨-, d2, d3, -⟩ := DrSC hL
    obtain ⟨w, hw⟩ := Subring.mul_mem _ d2 d3
    rw [← hw]; exact sc_memDG P w
  show zA P (DQ P) * zbiA P (DQ P) * _ ∈ BA L
  rw [← hz, ← hzbi, Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun i hi => ?_
  have hgen : L.Drb * L.Dri * SS P (DQ P) i ∈ bddSet P L :=
    Or.inl (Or.inr ⟨i, Set.mem_Icc.2 (Finset.mem_Icc.1 hi), rfl⟩)
  have hDD : L.D * L.Dbi ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have e1 : L.ζ * L.ζbi * (kap P (DQ P) (fun π => (Y + (M.rho P π i : ℂ))⁻¹) * SS P (DQ P) i) =
      L.D * L.Dbi * (kap P (DQ P) (fun π => (Y + (M.rho P π i : ℂ))⁻¹) * (L.Drb * L.Dri * SS P (DQ P) i)) := by
    rw [ζζbi_eq hL hLaw, mul_assoc (L.D * L.Dbi), ← mul_assoc (L.Drb * L.Dri),
      ← kap_comm_DG P _ hDrDG]
    simp only [mul_assoc]
  rw [e1]
  exact mul_mem (gen_BA hL hLaw hDD) (mul_mem (kap_BA hL hLaw _) (gen_BA hL hLaw hgen))

theorem io_B {S : Type} [Fintype S] [DecidableEq S] {x : A P (DQ P)} (h : x ∈ BA L) : (io x : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB L S :=
  MAx2.Jet.scalar_mem _ _ h

theorem eU_B {S : Type} [Fintype S] [DecidableEq S] (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB L S :=
  fun x y => by
    simp only [eU, Matrix.of_apply]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _

theorem insert_matrix_mem_base {S : Type} [Fintype S] [DecidableEq S] (a : S) (x y z w : SlopeTestRemainingChoices S (A P (DQ P)))
    (hx : x ∈ UB L S) (hy : y ∈ UB L S) (hz : z ∈ UB L S) (hw : w ∈ UB L S) : ins a !![x, y; z, w] ∈ UB L S :=
  Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => mul_mem (eU_B hL hLaw a i j)
    (MAx2.Jet.matrix_two_mem_sub (UB L S) x y z w hx hy hz hw i j)

theorem frame_memB (l : ℕ) {S : Type} [Fintype S] [DecidableEq S] :
    ∀ w : List (Letter ℂ S), (∀ Y, (ofWord L (startM P (DQ P) l) w).ee Y ∈ UB L S) ∧
      (∀ Y, (ofWord L (startM P (DQ P) l) w).x Y ∈ UB L S) ∧ (∀ Y, (ofWord L (startM P (DQ P) l) w).xi Y ∈ UB L S)
  | [] => ⟨fun Y => io_B hL hLaw (eeA_BA hL hLaw Y), fun Y => io_B hL hLaw (kap_BA hL hLaw _),
      fun Y => io_B hL hLaw (kap_BA hL hLaw _)⟩
  | lt :: w => by
    obtain ⟨he, hx, hxi⟩ := frame_memB l w
    have htz : (tz L : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB L S := io_B hL hLaw (Subalgebra.smul_mem _ (ζbi_BA hL hLaw) _)
    have hDD : ∀ Y Ya, (ofWord L (startM P (DQ P) l) w).DD Y Ya ∈ UB L S := fun Y Ya =>
      Subalgebra.smul_mem _ (sub_mem (he Y) (he Ya)) _
    have h1 : (1 : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB L S := Subalgebra.one_mem _
    have h0 : (0 : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB L S := Subalgebra.zero_mem _
    simp only [ofWord]
    split_ifs
    · refine ⟨fun Y => ?_, fun Y => ?_, fun Y => ?_⟩
      · exact insert_matrix_mem_base hL hLaw _ _ _ _ _ (add_mem (sub_mem (he Y) (hDD Y _)) htz) (neg_mem (Subalgebra.smul_mem _ h1 _)) h0
          (mul_mem (mul_mem (hxi _) (he Y)) (hx _))
      · exact mul_mem (hx Y) (insert_matrix_mem_base hL hLaw _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
      · exact mul_mem (hxi Y) (insert_matrix_mem_base hL hLaw _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
    · refine ⟨fun Y => ?_, fun Y => ?_, fun Y => ?_⟩
      · exact insert_matrix_mem_base hL hLaw _ _ _ _ _ (he Y) h0 (neg_mem (Subalgebra.smul_mem _ (mul_mem (hxi _) (hxi _)) _))
          (add_mem (sub_mem (mul_mem (mul_mem (hxi _) (he Y)) (hx _)) (hDD Y _)) htz)
      · exact mul_mem (hx Y) (insert_matrix_mem_base hL hLaw _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)
      · exact mul_mem (hxi Y) (insert_matrix_mem_base hL hLaw _ _ _ _ _ (Subalgebra.smul_mem _ h1 _) h0 h0 h1)

end frame

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I1

section S_I4_I2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

variable (P : M.Par)

theorem actA_zero (f : M.Ty P → SmQ P.r P.TT) : actA P 0 f = 0 := by
  funext π; simp only [MAx2.R2.actA_eq, Matrix.zero_apply, map_zero, LinearMap.zero_apply, Finset.sum_const_zero]; rfl

theorem actA_sum {ι : Type} (s : Finset ι) (x : ι → A P (DQ P)) (f : M.Ty P → SmQ P.r P.TT) (π : M.Ty P) :
    actA P (∑ t ∈ s, x t) f π = ∑ t ∈ s, actA P (x t) f π := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [actA_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, MAx2.R2.act_add, ih]

theorem evQ_actA_sum {ι : Type} (s : Finset ι) (x : ι → A P (DQ P)) (f : M.Ty P → SmQ P.r P.TT) (π : M.Ty P)
    (q : Qp P.r P.TT) : evQ P (actA P (∑ t ∈ s, x t) f π) q = ∑ t ∈ s, evQ P (actA P (x t) f π) q := by
  rw [actA_sum, MAx2.Jet.evQ_sum]

theorem apply_matrix_vector {N : ℕ} (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (𝒳 : Ix (Fin N) → A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT)
    (X : Qp P.r P.TT → Iota P N → ℂ) (hX : ∀ q i, X q i = evQ P (actA P (𝒳 (ixOf P N i).1) j (ixOf P N i).2) q)
    (q : Qp P.r P.TT) (i : Iota P N) :
    wordModuleApply P b X q i = evQ P (actA P (∑ e', b (ixOf P N i).1 e' * 𝒳 e') j (ixOf P N i).2) q := by
  rw [G.apply_matrix_def, evQ_actA_sum]
  refine Finset.sum_congr rfl fun e' _ => ?_
  have hT : ∀ π', toSm P (fun q' => X q' (iotaOf P N e' π')) = actA P (𝒳 e') j π' := by
    intro π'
    have : (fun q' => X q' (iotaOf P N e' π')) = evQ P (actA P (𝒳 e') j π') := by
      funext q'; rw [hX, G.ixOf_iotaOf]
    rw [this, MAx2.Jet.toSm_ev]
  simp only [hT]
  rw [MAx2.R2.act_mul, MAx2.R2.actA_eq, MAx2.Jet.evQ_sum]
  rfl

section letters
variable {P} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem letter_entry {N : ℕ} (y₁ y₂ : ℂ) (E : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (b : Bool) (e e' : Ix (Fin N)) :
    (if b then io (L.Dbi * L.R0 y₂) + E * io (L.Di * L.Ahat y₁) else io (L.Di * L.Ahat y₁) :
      SlopeTestRemainingChoices (Fin N) (A P (DQ P))) e e' = if b then ((if e = e' then L.Dbi * L.R0 y₂ else 0) + E e e' * (L.Di * L.Ahat y₁))
      else (if e = e' then L.Di * L.Ahat y₁ else 0) := by
  cases b <;> simp [io, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.mul_diagonal]

theorem letter_vec_NF {N : ℕ} (y₁ y₂ : ℂ) (E : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (hE : E ∈ UB L (Fin N))
    (𝒳 : Ix (Fin N) → A P (DQ P)) (h𝒳 : ∀ e, 𝒳 e ∈ NormalFormTwo L (SB L) N N) (b : Bool) (e : Ix (Fin N)) :
    ∑ e', (if b then io (L.Dbi * L.R0 y₂) + E * io (L.Di * L.Ahat y₁) else io (L.Di * L.Ahat y₁) :
      SlopeTestRemainingChoices (Fin N) (A P (DQ P))) e e' * 𝒳 e' ∈ NormalFormTwo L (SB L) (N + 1) (N + 1) := by
  have hS := hyp_model hL hLaw
  refine Submodule.sum_mem _ fun e' _ => ?_
  rw [letter_entry hL hLaw]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    split_ifs
    · exact letterA hS y₁ (h𝒳 e')
    · rw [zero_mul]; exact Submodule.zero_mem _
  · simp only [if_true, add_mul]
    refine Submodule.add_mem _ ?_ ?_
    · split_ifs
      · exact letterR hS y₂ (h𝒳 e')
      · rw [zero_mul]; exact Submodule.zero_mem _
    · rw [mul_assoc]; exact base_mul_normal_form (hE e e') (letterA hS y₁ (h𝒳 e'))

theorem Xw_rep (l : ℕ) (j : M.Ty P → SmQ P.r P.TT) : ∀ w : List ℝ, ∃ 𝒳 : Ix (Fin w.length) → A P (DQ P),
    (∀ e, 𝒳 e ∈ NormalFormTwo L (SB L) w.length w.length) ∧
    ∀ q i, Xw P l L (ju P j) w q i = evQ P (actA P (𝒳 (ixOf P w.length i).1) j (ixOf P w.length i).2) q
  | [] => ⟨fun _ => 1, fun _ => one_mem_normal_form_two (hyp_model hL hLaw), fun q i => by
      show (j i : Qp P.r P.TT → ℂ) q = evQ P (actA P 1 j i) q
      rw [MAx3.one_act]; rfl⟩
  | Y :: w => by
    obtain ⟨𝒳, h1, h2⟩ := Xw_rep l j w
    have hE : (frW P l L w).ee (Y : ℂ) ∈ UB L (Fin w.length) := (frame_memB hL hLaw l (wordP w)).1 (Y : ℂ)
    refine ⟨fun e => ∑ e', (if (e (Fin.last w.length) = 1 : Bool) then io (L.Dbi * L.R0 (Y : ℂ)) +
        (frW P l L w).ee (Y : ℂ) * io (L.Di * L.Ahat (Y : ℂ)) else io (L.Di * L.Ahat (Y : ℂ)) :
        SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))) (Fin.init e) e' * 𝒳 e', fun e => ?_, fun q bi => ?_⟩
    · exact letter_vec_NF hL hLaw (Y : ℂ) (Y : ℂ) _ hE 𝒳 h1 _ (Fin.init e)
    · obtain ⟨b, i⟩ := bi
      show wordModuleApply P (if b then g2 P l L w Y else g1 P L w Y) (Xw P l L (ju P j) w) q i = _
      rw [apply_matrix_vector P _ 𝒳 j _ h2]
      cases b
      · simp [g1, ixOf]
      · simp [g2, ixOf]

end letters

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I2

section S_I4_I3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

def lvec {N : ℕ} (L : LevelData (A P (DQ P)) P.r) (y₁ y₂ : ℂ) (E : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (𝒳 : Ix (Fin N) → A P (DQ P))
    (e : Ix (Fin (N + 1))) : A P (DQ P) :=
  ∑ e', (if (e (Fin.last N) = 1 : Bool) then io (L.Dbi * L.R0 y₂) + E * io (L.Di * L.Ahat y₁)
    else io (L.Di * L.Ahat y₁) : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (Fin.init e) e' * 𝒳 e'

theorem lvec_NF {N : ℕ} (y₁ y₂ : ℂ) (E : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (hE : E ∈ UB L (Fin N))
    (𝒳 : Ix (Fin N) → A P (DQ P)) (h𝒳 : ∀ e, 𝒳 e ∈ NormalFormTwo L (SB L) N N) (e : Ix (Fin (N + 1))) :
    lvec L y₁ y₂ E 𝒳 e ∈ NormalFormTwo L (SB L) (N + 1) (N + 1) :=
  letter_vec_NF hL hLaw y₁ y₂ E hE 𝒳 h𝒳 _ (Fin.init e)

theorem letter_rep {N : ℕ} (y₁ y₂ : ℂ) (E : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (𝒳 : Ix (Fin N) → A P (DQ P))
    (j : M.Ty P → SmQ P.r P.TT) (X : Qp P.r P.TT → Iota P N → ℂ)
    (hX : ∀ q i, X q i = evQ P (actA P (𝒳 (ixOf P N i).1) j (ixOf P N i).2) q) (q : Qp P.r P.TT) (b : Bool)
    (i : Iota P N) :
    wordModuleApply P (if b then io (L.Dbi * L.R0 y₂) + E * io (L.Di * L.Ahat y₁) else io (L.Di * L.Ahat y₁)) X q i =
      evQ P (actA P (lvec L y₁ y₂ E 𝒳 (ixOf P (N + 1) (b, i)).1) j (ixOf P (N + 1) (b, i)).2) q := by
  rw [apply_matrix_vector P _ 𝒳 j X hX]
  cases b
  · simp [lvec, ixOf]
  · simp [lvec, ixOf]

theorem conj_rep (hTT : 0 ≤ P.TT) (l : ℕ) (j : M.Ty P → SmQ P.r P.TT) (w : List ℝ) (Y s : ℝ) :
    ∃ 𝒵 : Ix (Fin (w.length + 1)) → A P (DQ P), (∀ e, 𝒵 e ∈ NormalFormTwo L (SB L) (w.length + 1) (w.length + 1)) ∧
    ∀ q bi, LE.conjS (baseQ P) (gL P l L w Y) (Xw P l L (ju P j) w) s q bi =
      evQ P (actA P (𝒵 (ixOf P (w.length + 1) bi).1) j (ixOf P (w.length + 1) bi).2) q := by
  obtain ⟨𝒳, h1, h2⟩ := Xw_rep hL hLaw l j w
  have hE : (frW P l L w).ee (Y : ℂ) ∈ UB L (Fin w.length) := (frame_memB hL hLaw l (wordP w)).1 (Y : ℂ)
  refine ⟨lvec L ((Y : ℂ) + s) ((Y : ℂ) + s) ((frW P l L w).ee (Y : ℂ)) 𝒳,
    lvec_NF hL hLaw _ _ _ hE 𝒳 h1, fun q bi => ?_⟩
  obtain ⟨b, i⟩ := bi
  rw [G.conjS_gL P hTT hL w Y s _ (G.Xw_mem P l L j w) q b i]
  exact letter_rep hL hLaw _ _ _ 𝒳 j _ h2 q b i

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I3

section S_I4_I4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An
open scoped ComplexConjugate

noncomputable section

variable {P : M.Par}

def IsFn (x : A P (DQ P)) (g : Qp P.r P.TT → ℂ) : Prop :=
  ∃ F Fb : SmQ P.r P.TT, x = sc P (DQ P) ((DQ P).fnP F Fb) ∧ ∀ q, evQ P F q = g q

theorem isFn_mul {x y : A P (DQ P)} {g h : Qp P.r P.TT → ℂ} (hx : IsFn x g) (hy : IsFn y h) :
    IsFn (x * y) (fun q => g q * h q) := by
  obtain ⟨F, Fb, rfl, hF⟩ := hx
  obtain ⟨F2, KoszulImageInIdeal, rfl, hF2⟩ := hy
  refine ⟨F * F2, Fb * KoszulImageInIdeal, ?_, fun q => ?_⟩
  · rw [Formalism.FourierDecayAlt.P.MAx3.G.sc_mul P]; exact congrArg (sc P (DQ P)) (MAx1.multiplierPair_mul (DQ P) F Fb F2 KoszulImageInIdeal)
  · rw [MAx2.Jet.evQ_mul, hF, hF2]

theorem isFn_one : IsFn (1 : A P (DQ P)) (fun _ => 1) := by
  refine ⟨(1 : (DQ P).R), (1 : (DQ P).R), ?_, fun q => rfl⟩
  rw [MAx1.multiplierPair_one]
  show (1 : A P (DQ P)) = Matrix.scalar (M.Ty P) 1
  rw [map_one]

theorem isFn_pow {x : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (hx : IsFn x g) (n : ℕ) :
    IsFn (x ^ n) (fun q => g q ^ n) := by
  induction n with
  | zero => simpa using isFn_one
  | succ n ih => rw [pow_succ]; simpa [pow_succ] using isFn_mul ih hx

theorem isFn_prod {n : ℕ} (f : Fin n → A P (DQ P)) (g : Fin n → Qp P.r P.TT → ℂ) (h : ∀ i, IsFn (f i) (g i)) :
    IsFn (List.ofFn f).prod (fun q => ∏ i, g i q) := by
  induction n with
  | zero => simpa using isFn_one
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have := isFn_mul (h 0) (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))
    simpa [Fin.prod_univ_succ] using this

theorem coordE_vc (l : Fin P.r) (x : E P.r) : coordE (M.vc l : M.Var P.r) x = x.1 l := by
  simp [coordE, zE, M.vc]

theorem coordE_vcb (l : Fin P.r) (x : E P.r) : coordE (M.vcb l : M.Var P.r) x = conj (x.1 l) := by
  simp [coordE, zE, M.vcb]

variable (hTT : 0 ≤ P.TT)
include hTT

theorem unitQ (v : M.Var P.r) : IsUnit (coordQ (r := P.r) (TT := P.TT) v) :=
  isUnit_of_ne _ fun q => coordE_ne q.2 hTT v

theorem ev_invQ (v : M.Var P.r) (q : Qp P.r P.TT) :
    evQ P ((DQ P).inv ((DQ P).x v)) q = (coordE v q.1)⁻¹ :=
  MAx2.Jet.ev_inverse P _ (unitQ hTT v) q

variable {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hL

theorem fn_c (l : Fin P.r) : IsFn (L.c l) (fun q => q.1.1 l) := by
  rw [hL.2.2.1]; exact ⟨_, _, rfl, fun q => coordE_vc l q.1⟩
theorem fn_ci (l : Fin P.r) : IsFn (L.ci l) (fun q => (q.1.1 l)⁻¹) := by
  rw [hL.2.2.2.1]; exact ⟨_, _, rfl, fun q => by rw [ev_invQ hTT, coordE_vc]⟩
theorem fn_cb (l : Fin P.r) : IsFn (L.cb l) (fun q => conj (q.1.1 l)) := by
  rw [hL.2.2.2.2.1]; exact ⟨_, _, rfl, fun q => coordE_vcb l q.1⟩
theorem fn_cbi (l : Fin P.r) : IsFn (L.cbi l) (fun q => (conj (q.1.1 l))⁻¹) := by
  rw [hL.2.2.2.2.2.1]; exact ⟨_, _, rfl, fun q => by rw [ev_invQ hTT, coordE_vcb]⟩
theorem fn_ζ : IsFn L.ζ (fun q => q.1.2) := by
  rw [hL.2.2.2.2.2.2.1]; exact ⟨_, _, rfl, fun q => coordE_vz q.1⟩
theorem fn_ζi : IsFn L.ζi (fun q => (q.1.2)⁻¹) := by
  rw [hL.2.2.2.2.2.2.2.1]; exact ⟨_, _, rfl, fun q => by rw [ev_invQ hTT, coordE_vz]⟩
theorem fn_ζb : IsFn L.ζb (fun q => conj q.1.2) := by
  rw [hL.2.2.2.2.2.2.2.2.1]; exact ⟨_, _, rfl, fun q => coordE_vzb q.1⟩
theorem fn_ζbi : IsFn L.ζbi (fun q => (conj q.1.2)⁻¹) := by
  rw [hL.2.2.2.2.2.2.2.2.2.1]; exact ⟨_, _, rfl, fun q => by rw [ev_invQ hTT, coordE_vzb]⟩

theorem fn_Dr : IsFn L.Dr (fun q => ∏ l, q.1.1 l) := isFn_prod _ _ (fn_c hTT hL)
theorem fn_Dri : IsFn L.Dri (fun q => ∏ l, (q.1.1 l)⁻¹) := isFn_prod _ _ (fn_ci hTT hL)
theorem fn_Drb : IsFn L.Drb (fun q => ∏ l, conj (q.1.1 l)) := isFn_prod _ _ (fn_cb hTT hL)
theorem fn_Drbi : IsFn L.Drbi (fun q => ∏ l, (conj (q.1.1 l))⁻¹) := isFn_prod _ _ (fn_cbi hTT hL)

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I4

section S_I4_I5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An
open scoped ComplexConjugate

noncomputable section

variable {P : M.Par}

def PW (x : A P (DQ P)) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∃ Mx : Qp P.r P.TT → Matrix (M.Ty P) (M.Ty P) ℂ, (∀ q π π', ‖Mx q π π'‖ ≤ C) ∧
    ∀ (f : M.Ty P → SmQ P.r P.TT) q π, evQ P (actA P x f π) q = ∑ π', Mx q π π' * evQ P (f π') q

theorem PW_mul {x y : A P (DQ P)} {C₁ C₂ : ℝ} (hx : PW x C₁) (hy : PW y C₂) :
    PW (x * y) (Fintype.card (M.Ty P) * C₁ * C₂) := by
  obtain ⟨h1, M1, b1, e1⟩ := hx
  obtain ⟨h2, M2, b2, e2⟩ := hy
  refine ⟨by positivity, fun q π π'' => ∑ π', M1 q π π' * M2 q π' π'', fun q π π'' => ?_, fun f q π => ?_⟩
  · calc ‖∑ π', M1 q π π' * M2 q π' π''‖ ≤ ∑ π' : M.Ty P, ‖M1 q π π' * M2 q π' π''‖ := norm_sum_le _ _
      _ ≤ ∑ π' : M.Ty P, C₁ * C₂ := Finset.sum_le_sum fun π' _ => by
          rw [norm_mul]; exact mul_le_mul (b1 q π π') (b2 q π' π'') (norm_nonneg _) h1
      _ = _ := by simp [mul_assoc]
  · rw [MAx2.R2.act_mul, e1]
    simp only [e2, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun π'' _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun π' _ => by ring

theorem PW_mono {x : A P (DQ P)} {C C' : ℝ} (h : PW x C) (hC : C ≤ C') : PW x C' := by
  obtain ⟨h0, Mx, b, e⟩ := h
  exact ⟨h0.trans hC, Mx, fun q π π' => (b q π π').trans hC, e⟩

theorem PW_fn {x : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (hx : IsFn x g) {C : ℝ} (hC : 0 ≤ C) (hg : ∀ q, ‖g q‖ ≤ C) :
    PW x C := by
  obtain ⟨F, Fb, rfl, hF⟩ := hx
  classical
  refine ⟨hC, fun q π π' => if π = π' then g q else 0, fun q π π' => ?_, fun f q π => ?_⟩
  · dsimp only
    split_ifs
    · exact hg q
    · simpa using hC
  · rw [MAx2.R2.act_sc, Finset.sum_eq_single π (fun b _ hb => by dsimp only; rw [if_neg (Ne.symm hb), zero_mul])
      (by simp)]
    dsimp only
    rw [if_pos rfl, ← hF q]
    show evQ P (F * f π) q = _
    rw [MAx2.Jet.evQ_mul]

theorem PW_kap (g : M.Ty P → ℂ) : PW (kap P (DQ P) g) (∑ π, ‖g π‖) := by
  classical
  refine ⟨by positivity, fun _ π π' => if π = π' then g π else 0, fun q π π' => ?_, fun f q π => ?_⟩
  · dsimp only
    split_ifs
    · exact Finset.single_le_sum (f := fun π => ‖g π‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ π)
    · simpa using Finset.sum_nonneg (fun π _ => norm_nonneg (g π))
  · rw [MAx2.R2.act_kap, Finset.sum_eq_single π (fun b _ hb => by dsimp only; rw [if_neg (Ne.symm hb), zero_mul])
      (by simp)]
    dsimp only
    rw [if_pos rfl]
    rfl

theorem PW_scalars (x : A P (DQ P)) (c : M.Ty P → M.Ty P → ℂ) (hc : ∀ π π', x π π' = algebraMap ℂ (DQ P).Pr (c π π')) :
    PW x (∑ π, ∑ π', ‖c π π'‖) := by
  refine ⟨by positivity, fun _ => c, fun q π π' => ?_, fun f q π => ?_⟩
  · exact (Finset.single_le_sum (f := fun π' => ‖c π π'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ π')).trans
      (Finset.single_le_sum (f := fun π => ∑ π', ‖c π π'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ π))
  · rw [MAx2.R2.actA_eq, MAx2.Jet.evQ_sum]
    refine Finset.sum_congr rfl fun π' _ => ?_
    rw [hc]
    rfl

theorem PW_SS (i : ℕ) : ∃ C, PW (SS P (DQ P) i) C := by
  classical
  exact ⟨_, PW_scalars _ (fun π' π => if M.Up P i π π' then ((Real.sqrt (M.Nrm P i π) : ℝ) : ℂ) else 0)
    (fun π' π => by simp only [SS, Matrix.of_apply]; split_ifs <;> simp)⟩

theorem PW_starSS (i : ℕ) : ∃ C, PW (star (SS P (DQ P) i)) C := by
  classical
  exact ⟨_, PW_scalars _ (fun π π' => if M.Up P i π π' then ((Real.sqrt (M.Nrm P i π) : ℝ) : ℂ) else 0)
    (fun π π' => by
      rw [Matrix.star_apply]
      simp only [SS, Matrix.of_apply]
      split_ifs
      · rw [← algebraMap_star_comm]; simp
      · simp)⟩

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I5

section S_I4_I6

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An
open scoped ComplexConjugate

noncomputable section

variable {P : M.Par}

def Dabs (q : Qp P.r P.TT) : ℝ := (∏ l, ‖q.1.1 l‖) * ‖q.1.2‖

theorem c_ne (q : Qp P.r P.TT) (l : Fin P.r) : q.1.1 l ≠ 0 := q.2.1 l

theorem ζ_ne (hTT : 0 ≤ P.TT) (q : Qp P.r P.TT) : q.1.2 ≠ 0 := by
  intro h
  have h2 : P.TT < Complex.normSq q.1.2 := q.2.2
  rw [h, Complex.normSq_zero] at h2
  linarith

theorem Dabs_pos (hTT : 0 ≤ P.TT) (q : Qp P.r P.TT) : 0 < Dabs q :=
  mul_pos (Finset.prod_pos fun l _ => norm_pos_iff.2 (c_ne q l)) (norm_pos_iff.2 (ζ_ne hTT q))

theorem ζinv_le (hTT : 0 < P.TT) (q : Qp P.r P.TT) : ‖(q.1.2)⁻¹‖ ≤ (Real.sqrt P.TT)⁻¹ := by
  have h2 : P.TT < Complex.normSq q.1.2 := q.2.2
  rw [norm_inv]
  apply inv_anti₀ (Real.sqrt_pos.2 hTT)
  calc Real.sqrt P.TT ≤ Real.sqrt (‖q.1.2‖ ^ 2) :=
        Real.sqrt_le_sqrt (by rw [← Complex.normSq_eq_norm_sq]; exact h2.le)
    _ = ‖q.1.2‖ := Real.sqrt_sq (norm_nonneg _)

theorem PW_one : PW (1 : A P (DQ P)) 1 :=
  PW_fn isFn_one zero_le_one fun q => by simp

variable (hTTp : 0 < P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTTp hL

theorem fn_D : IsFn L.D (fun q => (∏ l, q.1.1 l) * q.1.2) := isFn_mul (fn_Dr hTTp.le hL) (fn_ζ hTTp.le hL)
theorem fn_Di : IsFn L.Di (fun q => (q.1.2)⁻¹ * ∏ l, (q.1.1 l)⁻¹) := isFn_mul (fn_ζi hTTp.le hL) (fn_Dri hTTp.le hL)
theorem fn_Db : IsFn L.Db (fun q => (∏ l, conj (q.1.1 l)) * conj q.1.2) := isFn_mul (fn_Drb hTTp.le hL) (fn_ζb hTTp.le hL)
theorem fn_Dbi : IsFn L.Dbi (fun q => (conj q.1.2)⁻¹ * ∏ l, (conj (q.1.1 l))⁻¹) :=
  isFn_mul (fn_ζbi hTTp.le hL) (fn_Drbi hTTp.le hL)

theorem norm_Di (q : Qp P.r P.TT) : ‖(q.1.2)⁻¹ * ∏ l, (q.1.1 l)⁻¹‖ * Dabs q = 1 := by
  unfold Dabs
  rw [norm_mul, norm_inv, norm_prod]
  simp only [norm_inv]
  rw [Finset.prod_inv_distrib]
  have h1 : ‖q.1.2‖ ≠ 0 := norm_ne_zero_iff.2 (ζ_ne hTTp.le q)
  have h2 : (∏ l, ‖q.1.1 l‖) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => norm_ne_zero_iff.2 (c_ne q l)
  field_simp

theorem norm_Dbi (q : Qp P.r P.TT) : ‖(conj q.1.2)⁻¹ * ∏ l, (conj (q.1.1 l))⁻¹‖ * Dabs q = 1 := by
  have : ‖(conj q.1.2)⁻¹ * ∏ l, (conj (q.1.1 l))⁻¹‖ = ‖(q.1.2)⁻¹ * ∏ l, (q.1.1 l)⁻¹‖ := by
    rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_conj, norm_prod, norm_prod]
    simp only [norm_inv, Complex.norm_conj]
  rw [this]; exact norm_Di hTTp hL q

theorem norm_D (q : Qp P.r P.TT) : ‖(∏ l, q.1.1 l) * q.1.2‖ = Dabs q := by
  unfold Dabs; rw [norm_mul, norm_prod]

theorem norm_Db (q : Qp P.r P.TT) : ‖(∏ l, conj (q.1.1 l)) * conj q.1.2‖ = Dabs q := by
  unfold Dabs; rw [norm_mul, norm_prod, Complex.norm_conj]; simp only [Complex.norm_conj]

theorem PW_DDbi : PW (L.D * L.Dbi) 1 :=
  PW_fn (isFn_mul (fn_D hTTp hL) (fn_Dbi hTTp hL)) zero_le_one fun q => by
    rw [norm_mul, norm_D hTTp hL, mul_comm, norm_Dbi hTTp hL]

theorem PW_DbDi : PW (L.Db * L.Di) 1 :=
  PW_fn (isFn_mul (fn_Db hTTp hL) (fn_Di hTTp hL)) zero_le_one fun q => by
    rw [norm_mul, norm_Db hTTp hL, mul_comm, norm_Di hTTp hL]

theorem PW_ζi : PW L.ζi (Real.sqrt P.TT)⁻¹ :=
  PW_fn (fn_ζi hTTp.le hL) (by positivity) fun q => ζinv_le hTTp q

theorem PW_ζbi : PW L.ζbi (Real.sqrt P.TT)⁻¹ :=
  PW_fn (fn_ζbi hTTp.le hL) (by positivity) fun q => by
    have := ζinv_le hTTp q; rwa [norm_inv, Complex.norm_conj, ← norm_inv]

theorem fn_DrbDri : IsFn (L.Drb * L.Dri) (fun q => (∏ l, conj (q.1.1 l)) * ∏ l, (q.1.1 l)⁻¹) :=
  isFn_mul (fn_Drb hTTp.le hL) (fn_Dri hTTp.le hL)

theorem PW_DrbDri : PW (L.Drb * L.Dri) 1 :=
  PW_fn (fn_DrbDri hTTp hL) zero_le_one fun q => by
    rw [norm_mul, norm_prod, norm_prod]
    simp only [Complex.norm_conj, norm_inv]
    rw [← Finset.prod_mul_distrib]
    exact le_of_eq (Finset.prod_eq_one fun l _ => mul_inv_cancel₀ (norm_ne_zero_iff.2 (c_ne q l)))

theorem PW_DrDrbi : PW (L.Dr * L.Drbi) 1 :=
  PW_fn (isFn_mul (fn_Dr hTTp.le hL) (fn_Drbi hTTp.le hL)) zero_le_one fun q => by
    rw [norm_mul, norm_prod, norm_prod]
    simp only [Complex.norm_conj, norm_inv]
    rw [← Finset.prod_mul_distrib]
    exact le_of_eq (Finset.prod_eq_one fun l _ => mul_inv_cancel₀ (norm_ne_zero_iff.2 (c_ne q l)))

include hLaw

theorem PW_gen {b : A P (DQ P)} (hb : b ∈ bddSet P L) : ∃ C, PW b C := by
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨_, PW_ζi hTTp hL⟩
    · exact ⟨_, PW_ζbi hTTp hL⟩
    · exact ⟨_, PW_DDbi hTTp hL⟩
    · exact ⟨_, PW_DbDi hTTp hL⟩
  · exact ⟨_, PW_kap f⟩
  · obtain ⟨C, hC⟩ := PW_SS (P := P) i
    exact ⟨_, PW_mul (PW_DrbDri hTTp hL) hC⟩
  · obtain ⟨C, hC⟩ := PW_starSS (P := P) i
    show ∃ C, PW (star (L.Drb * L.Dri * SS P (DQ P) i)) C
    rw [starSSn_eq hL hLaw]
    exact ⟨_, PW_mul hC (PW_DrDrbi hTTp hL)⟩

theorem PW_SB {b : A P (DQ P)} (hb : b ∈ SB L) : ∃ C, PW b C := by
  induction hb using Submonoid.closure_induction with
  | mem x hx => exact PW_gen hTTp hL hLaw hx
  | one => exact ⟨1, PW_one⟩
  | mul x y _ _ h1 h2 =>
    obtain ⟨C1, hC1⟩ := h1
    obtain ⟨C2, hC2⟩ := h2
    exact ⟨_, PW_mul hC1 hC2⟩

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I6

section S_I4_I7

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An
open scoped ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem actA_smul (c : ℂ) (x : A P (DQ P)) (f : M.Ty P → SmQ P.r P.TT) (π : M.Ty P) :
    actA P (c • x) f π = c • actA P x f π := by
  rw [MAx2.R2.actA_eq, MAx2.R2.actA_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  show ((c • x π π').1) (f π') = c • (x π π').1 (f π')
  rw [G.pfst_smul]; rfl

theorem evQ_smul' (c : ℂ) (f : SmQ P.r P.TT) (q : Qp P.r P.TT) : evQ P (c • f) q = c * evQ P f q := rfl

def NFB (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (d ℓ : ℕ) (x : A P (DQ P)) : Prop :=
  ∃ (C : ℝ) (T : List (List (A P (DQ P)) × M.Ty P)), 0 ≤ C ∧
    (∀ t ∈ T, t.1.length = ℓ ∧ ∀ h ∈ t.1, h ∈ plusHats L) ∧
    ∀ π q, ‖evQ P (actA P x j π) q‖ * Dabs q ^ d ≤ C * (T.map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖).sum

theorem sumT_nonneg (j : M.Ty P → SmQ P.r P.TT) (T : List (List (A P (DQ P)) × M.Ty P)) (q : Qp P.r P.TT) :
    0 ≤ (T.map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖).sum :=
  List.sum_nonneg fun x hx => by obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _

variable (hTTp : 0 < P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem fn_Dpow (i i' : ℕ) : ∃ v : Qp P.r P.TT → ℂ, IsFn (L.Di ^ i * L.Dbi ^ i') v ∧
    ∀ q, ‖v q‖ * Dabs q ^ (i + i') = 1 := by
  refine ⟨_, isFn_mul (isFn_pow (fn_Di hTTp hL) i) (isFn_pow (fn_Dbi hTTp hL) i'), fun q => ?_⟩
  rw [norm_mul, norm_pow, norm_pow, pow_add]
  calc ‖(q.1.2)⁻¹ * ∏ l, (q.1.1 l)⁻¹‖ ^ i * ‖(conj q.1.2)⁻¹ * ∏ l, (conj (q.1.1 l))⁻¹‖ ^ i' *
        (Dabs q ^ i * Dabs q ^ i') = (‖(q.1.2)⁻¹ * ∏ l, (q.1.1 l)⁻¹‖ * Dabs q) ^ i *
        (‖(conj q.1.2)⁻¹ * ∏ l, (conj (q.1.1 l))⁻¹‖ * Dabs q) ^ i' := by ring
    _ = 1 := by rw [norm_Di hTTp hL, norm_Dbi hTTp hL, one_pow, one_pow, one_mul]

theorem NFB_term (j : M.Ty P → SmQ P.r P.TT) {b : A P (DQ P)} (hb : b ∈ SB L) {i i' d ℓ : ℕ}
    {H : List (A P (DQ P))} (h1 : i + i' = d) (h2 : H.length = ℓ) (h3 : ∀ h ∈ H, h ∈ plusHats L) :
    NFB L j d ℓ (tm L b i i' H) := by
  obtain ⟨Cb, hCb0, Mb, hMb, hactb⟩ := PW_SB hTTp hL hLaw hb
  obtain ⟨v, ⟨F, Fb, hFeq, hF⟩, hv⟩ := fn_Dpow hTTp hL hLaw i i'
  refine ⟨Cb, (Finset.univ : Finset (M.Ty P)).toList.map fun π' => (H, π'), hCb0, fun t ht => ?_, fun π q => ?_⟩
  · obtain ⟨π', _, rfl⟩ := List.mem_map.1 ht; exact ⟨h2, h3⟩
  · have hD : ∀ π', evQ P (actA P (L.Di ^ i * L.Dbi ^ i') (actA P H.prod j) π') q =
        v q * evQ P (actA P H.prod j π') q := fun π' => by
      rw [hFeq, MAx2.R2.act_sc]
      show evQ P (F * actA P H.prod j π') q = _
      rw [MAx2.Jet.evQ_mul, hF]
    have e : evQ P (actA P (tm L b i i' H) j π) q =
        ∑ π', Mb q π π' * (v q * evQ P (actA P H.prod j π') q) := by
      unfold tm
      rw [MAx2.R2.act_mul, MAx2.R2.act_mul, hactb]
      simp only [hD]
    rw [e, List.map_map, ← h1]
    have hsum : (List.map ((fun t => ‖evQ P (actA P t.1.prod j t.2) q‖) ∘ fun π' => (H, π'))
        (Finset.univ : Finset (M.Ty P)).toList).sum = ∑ π', ‖evQ P (actA P H.prod j π') q‖ := by
      rw [Finset.sum_map_toList]; rfl
    rw [hsum, Finset.mul_sum]
    calc ‖∑ π', Mb q π π' * (v q * evQ P (actA P H.prod j π') q)‖ * Dabs q ^ (i + i')
        ≤ (∑ π', ‖Mb q π π' * (v q * evQ P (actA P H.prod j π') q)‖) * Dabs q ^ (i + i') :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg (Dabs_pos hTTp.le q).le _)
      _ = ∑ π', ‖Mb q π π'‖ * ‖evQ P (actA P H.prod j π') q‖ * (‖v q‖ * Dabs q ^ (i + i')) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun π' _ => ?_
          rw [norm_mul, norm_mul]; ring
      _ ≤ ∑ π', Cb * ‖evQ P (actA P H.prod j π') q‖ := Finset.sum_le_sum fun π' _ => by
          rw [hv, mul_one]; exact mul_le_mul_of_nonneg_right (hMb q π π') (norm_nonneg _)

theorem normal_form_two_bounded (j : M.Ty P → SmQ P.r P.TT) {d ℓ : ℕ} {x : A P (DQ P)} (hx : x ∈ NormalFormTwo L (SB L) d ℓ) :
    NFB L j d ℓ x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
    exact NFB_term hTTp hL hLaw j hb h1 h2 h3
  | zero =>
    refine ⟨0, [], le_rfl, by simp, fun π q => ?_⟩
    have : actA P (0 : A P (DQ P)) j π = 0 := by rw [actA_zero]; rfl
    rw [this, G.evQ_zero]; simp
  | add x y _ _ h1 h2 =>
    obtain ⟨C1, T1, hC1, hT1, b1⟩ := h1
    obtain ⟨C2, T2, hC2, hT2, b2⟩ := h2
    refine ⟨C1 + C2, T1 ++ T2, by positivity, fun t ht => ?_, fun π q => ?_⟩
    · rcases List.mem_append.1 ht with ht | ht; exacts [hT1 t ht, hT2 t ht]
    · rw [MAx2.R2.act_add, G.evQ_add, List.map_append, List.sum_append]
      have s1 := sumT_nonneg j T1 q
      have s2 := sumT_nonneg j T2 q
      have hDp := pow_nonneg (Dabs_pos hTTp.le q).le d
      calc ‖evQ P (actA P x j π) q + evQ P (actA P y j π) q‖ * Dabs q ^ d
          ≤ (‖evQ P (actA P x j π) q‖ + ‖evQ P (actA P y j π) q‖) * Dabs q ^ d :=
            mul_le_mul_of_nonneg_right (norm_add_le _ _) hDp
        _ ≤ C1 * (T1.map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖).sum +
            C2 * (T2.map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖).sum := by
            rw [add_mul]; exact add_le_add (b1 π q) (b2 π q)
        _ ≤ _ := by nlinarith
  | smul c x _ h =>
    obtain ⟨C, T, hC, hT, b⟩ := h
    refine ⟨‖c‖ * C, T, by positivity, hT, fun π q => ?_⟩
    rw [actA_smul, evQ_smul', norm_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b π q) (norm_nonneg c)

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I7

section S_I4_I8

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem Dabs_sq (hTT : 0 ≤ P.TT) (q : Qp P.r P.TT) : Dabs q ^ 2 = Gq P q * Wq P q := by
  have h : P.TT < Complex.normSq q.1.2 := q.2.2
  have hne : Complex.normSq q.1.2 - P.TT ≠ 0 := by linarith
  unfold Dabs Gq Wq
  rw [mul_pow, ← Finset.prod_pow]
  simp only [← Complex.normSq_eq_norm_sq]
  field_simp

theorem th_le (ε σ x : ℝ) (n : ℕ) (hε : 0 < ε) (hx : 0 < x) (hσ : (n : ℝ) ≤ σ) :
    LE.th ε σ x ≤ (ε⁻¹) ^ n * x ^ n := by
  unfold LE.th
  have hb0 : 0 < x / (x + ε) := div_pos hx (by linarith)
  have hb1 : x / (x + ε) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  calc (x / (x + ε)) ^ σ ≤ (x / (x + ε)) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hσ
    _ = x ^ n / (x + ε) ^ n := by rw [Real.rpow_natCast, div_pow]
    _ ≤ x ^ n / ε ^ n := div_le_div_of_nonneg_left (pow_nonneg hx.le n) (pow_pos hε n)
          (pow_le_pow_left₀ hε.le (by linarith) n)
    _ = (ε⁻¹) ^ n * x ^ n := by rw [inv_pow, div_eq_inv_mul]

theorem comp_le (hTT : 0 ≤ P.TT) (ε σ : ℝ) (n : ℕ) (hε : 0 < ε) (hσ : (n : ℝ) ≤ σ) (c : ℝ) (z : ℂ)
    (q : Qp P.r P.TT) :
    LE.th ε σ (Gq P q) * (Wq P q ^ n * c) * ‖z‖ ^ 2 ≤ |c| * (ε⁻¹) ^ n * (‖z‖ * Dabs q ^ n) ^ 2 := by
  have hG := Gq_pos P q
  have hth0 : 0 ≤ LE.th ε σ (Gq P q) := by unfold LE.th; positivity
  have hW : Wq P q ^ n * Gq P q ^ n = Dabs q ^ (2 * n) := by rw [pow_mul, Dabs_sq hTT, mul_pow, mul_comm]
  have hth := th_le ε σ (Gq P q) n hε hG hσ
  have hWn : 0 ≤ Wq P q ^ n := pow_nonneg (MAx3.Wq_pos P hTT q).le n
  have hc : 0 ≤ |c| := abs_nonneg c
  calc LE.th ε σ (Gq P q) * (Wq P q ^ n * c) * ‖z‖ ^ 2 ≤ LE.th ε σ (Gq P q) * (Wq P q ^ n * |c|) * ‖z‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hth0
        exact mul_le_mul_of_nonneg_left (le_abs_self c) hWn
    _ ≤ (ε⁻¹) ^ n * Gq P q ^ n * (Wq P q ^ n * |c|) * ‖z‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right hth (mul_nonneg hWn hc)
    _ = |c| * (ε⁻¹) ^ n * (‖z‖ ^ 2 * (Wq P q ^ n * Gq P q ^ n)) := by ring
    _ = _ := by rw [hW]; ring

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I8

section S_I4_I9

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem memLp_listsum {ι : Type} (T : List ι) (f : ι → Qp P.r P.TT → ℝ)
    (h : ∀ t ∈ T, MemLp (f t) 2 (mu0 P.r P.TT)) : MemLp (fun q => (T.map fun t => f t q).sum) 2 (mu0 P.r P.TT) := by
  induction T with
  | nil => simpa using (memLp_const (0 : ℝ))
  | cons a T ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun t ht => h t (by simp [ht]))

theorem gs_meas (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (w : List ℝ) (Y s : ℝ)
    (X : Qp P.r P.TT → Iota P w.length → ℂ) (k : Bool × Iota P w.length) :
    Measurable fun ω => LE.conjS (baseQ P) (gL P l L w Y) X s ω k := by
  show Measurable fun ω => (((Gq P ω) ^ (-s) : ℝ) : ℂ) * gL P l L w Y _ ω k
  refine Measurable.mul ?_ (MAx3.gL_cont P l L w Y _ k).measurable
  refine Complex.measurable_ofReal.comp ?_
  exact ((MAx3.Gq_cont P).rpow_const fun x => Or.inl (Gq_pos P x).ne').measurable

theorem th_meas (ε σ : ℝ) : Measurable fun ω : Qp P.r P.TT => LE.th ε σ (Gq P ω) := by
  unfold LE.th
  exact ((Gq_meas P).div ((Gq_meas P).add_const ε)).pow_const σ

variable {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  {lam : Fin (P.k + 2 * P.r + 1) → ℝ} {α β Lb : ℝ} {Ntot : ℕ}

theorem hat_product_square_integrable (hD : JDecay P L j (2 * Ntot + 2)) (H : List (A P (DQ P))) (hH : H.length ≤ 2 * Ntot + 2)
    (hH2 : ∀ h ∈ H, h ∈ plusHats L) (π : M.Ty P) :
    MemLp (fun q => ‖evQ P (actA P H.prod j π) q‖) 2 (mu0 P.r P.TT) := by
  have hint := hD H hH (fun a ha => by
    rcases hH2 a ha with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))) π
  refine (memLp_two_iff_integrable_sq ?_).2 hint
  exact (MAx3.evQ_cont P _).norm.aestronglyMeasurable

theorem gs_int (hH : Hyps P l L j lam α β Lb Ntot) (w : List ℝ) (hl : w.length < Ntot) (ε : ℝ) (hε : 0 < ε)
    (Y s : ℝ) : Integrable (fun ω => LE.th ε (4 * Ntot) (Gq P ω) *
      LE.sq (baseQ P) (dwW P l (Y :: w)) (LE.conjS (baseQ P) (gL P l L w Y) (Xw P l L (ju P j) w) s) ω)
      (mu0 P.r P.TT) := by
  have hOK := hH.1.1
  have hTTp : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hL := hH.1.2.2.2.1
  have hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTTp.le
  have hD := hH.2.1
  obtain ⟨𝒵, h𝒵, hrep⟩ := conj_rep hL hLaw hTTp.le l j w Y s
  choose C T hC hT hb using fun e => normal_form_two_bounded hTTp hL hLaw j (h𝒵 e)
  have hσ : ((w.length + 1 : ℕ) : ℝ) ≤ 4 * (Ntot : ℝ) := by
    have : w.length + 1 ≤ Ntot := by omega
    have h2 : ((w.length + 1 : ℕ) : ℝ) ≤ Ntot := by exact_mod_cast this
    nlinarith [(Nat.cast_nonneg Ntot : (0 : ℝ) ≤ Ntot)]
  let F : Ix (Fin (w.length + 1)) → Qp P.r P.TT → ℝ :=
    fun e q => ((T e).map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖).sum
  have hF2 : ∀ e, Integrable (fun q => F e q ^ 2) (mu0 P.r P.TT) := fun e =>
    (memLp_listsum (T e) _ fun t ht => hat_product_square_integrable hD t.1 (by rw [(hT e t ht).1]; omega) (hT e t ht).2 t.2).integrable_sq
  let n := w.length + 1
  let cc : Iota P n → ℝ := fun a => |(cs (M.x0 P l (ixOf P n a).2) (M.qC P) (wordP (Y :: w)) (ixOf P n a).1).re|
  refine Integrable.mono' (g := fun q => ∑ a : Iota P n, cc a * (ε⁻¹) ^ n * (C (ixOf P n a).1 * F (ixOf P n a).1 q) ^ 2)
    ?_ ?_ ?_
  · refine integrable_finset_sum _ fun a _ => ?_
    have := (hF2 (ixOf P n a).1).const_mul (cc a * (ε⁻¹) ^ n * C (ixOf P n a).1 ^ 2)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only []; ring
  · refine (Measurable.mul (th_meas ε _) ?_).aestronglyMeasurable
    exact Finset.measurable_sum _ fun a _ => (MAx3.dwW_meas P l (Y :: w) a).mul
      ((gs_meas l L w Y s _ a).norm.pow_const 2)
  · refine Filter.Eventually.of_forall fun q => ?_
    have hth0 : 0 ≤ LE.th ε (4 * Ntot) (Gq P q) := by unfold LE.th; have := Gq_pos P q; positivity
    rw [Real.norm_eq_abs]
    unfold LE.sq
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    have hz := hb (ixOf P n a).1 (ixOf P n a).2 q
    rw [← hrep q a] at hz
    have h1 := comp_le hTTp.le ε (4 * Ntot) n hε hσ
      (|(cs (M.x0 P l (ixOf P n a).2) (M.qC P) (wordP (Y :: w)) (ixOf P n a).1).re|)
      (LE.conjS (baseQ P) (gL P l L w Y) (Xw P l L (ju P j) w) s q a) q
    rw [abs_abs] at h1
    have hDp : 0 ≤ ‖LE.conjS (baseQ P) (gL P l L w Y) (Xw P l L (ju P j) w) s q a‖ * Dabs q ^ n :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (Dabs_pos hTTp.le q).le _)
    calc |LE.th ε (4 * Ntot) (Gq P q) * (dwW P l (Y :: w) q a *
          ‖LE.conjS (baseQ P) (gL P l L w Y) (Xw P l L (ju P j) w) s q a‖ ^ 2)|
        = LE.th ε (4 * Ntot) (Gq P q) * (Wq P q ^ n * cc a) *
          ‖LE.conjS (baseQ P) (gL P l L w Y) (Xw P l L (ju P j) w) s q a‖ ^ 2 := by
          rw [abs_mul, abs_of_nonneg hth0, abs_mul, abs_pow, abs_norm]
          simp only [dwW, cc, n, abs_mul, abs_pow, abs_of_pos (MAx3.Wq_pos P hTTp.le q), List.length_cons]
          ring
      _ ≤ cc a * (ε⁻¹) ^ n * (‖LE.conjS (baseQ P) (gL P l L w Y) (Xw P l L (ju P j) w) s q a‖ * Dabs q ^ n) ^ 2 := h1
      _ ≤ cc a * (ε⁻¹) ^ n * (C (ixOf P n a).1 * F (ixOf P n a).1 q) ^ 2 := by
          gcongr

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I9

section S_I4_I10

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {S : Type} [Fintype S] [DecidableEq S]

def Rep (L : LevelData (A P (DQ P)) P.r) (G : Set ℂ) (E : ℂ → SlopeTestRemainingChoices S (A P (DQ P))) : Prop :=
  ∃ ts : List ((ℂ → ℂ) × SlopeTestRemainingChoices S (A P (DQ P))), (∀ t ∈ ts, t.2 ∈ UB L S ∧ ∀ Y ∈ G, ContinuousAt t.1 Y) ∧
    ∀ Y, E Y = (ts.map fun t => t.1 Y • t.2).sum

theorem rep_const {G : Set ℂ} {X : SlopeTestRemainingChoices S (A P (DQ P))} (hX : X ∈ UB L S) : Rep L G (fun _ => X) :=
  ⟨[(fun _ => 1, X)], by simp [hX, continuousAt_const], fun Y => by simp⟩

theorem rep_add {G : Set ℂ} {E F : ℂ → SlopeTestRemainingChoices S (A P (DQ P))} (hE : Rep L G E) (hF : Rep L G F) :
    Rep L G (fun Y => E Y + F Y) := by
  obtain ⟨t1, h1, e1⟩ := hE
  obtain ⟨t2, h2, e2⟩ := hF
  refine ⟨t1 ++ t2, fun t ht => ?_, fun Y => by dsimp only; rw [e1, e2, List.map_append, List.sum_append]⟩
  rcases List.mem_append.1 ht with ht | ht; exacts [h1 t ht, h2 t ht]

theorem rep_smul {G : Set ℂ} {E : ℂ → SlopeTestRemainingChoices S (A P (DQ P))} (c : ℂ → ℂ) (hc : ∀ Y ∈ G, ContinuousAt c Y)
    (hE : Rep L G E) : Rep L G (fun Y => c Y • E Y) := by
  obtain ⟨ts, h, e⟩ := hE
  refine ⟨ts.map fun t => (fun Y => c Y * t.1 Y, t.2), fun t ht => ?_, fun Y => ?_⟩
  · obtain ⟨t, ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨(h t ht').1, fun Y hY => (hc Y hY).mul ((h t ht').2 Y hY)⟩
  · dsimp only
    rw [e, List.smul_sum, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp [mul_smul]

theorem rep_lmul {G : Set ℂ} {E : ℂ → SlopeTestRemainingChoices S (A P (DQ P))} (X : SlopeTestRemainingChoices S (A P (DQ P))) (hX : X ∈ UB L S)
    (hE : Rep L G E) : Rep L G (fun Y => X * E Y) := by
  obtain ⟨ts, h, e⟩ := hE
  refine ⟨ts.map fun t => (t.1, X * t.2), fun t ht => ?_, fun Y => ?_⟩
  · obtain ⟨t, ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨mul_mem hX (h t ht').1, (h t ht').2⟩
  · dsimp only
    rw [e, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp [mul_smul_comm]

theorem rep_rmul {G : Set ℂ} {E : ℂ → SlopeTestRemainingChoices S (A P (DQ P))} (X : SlopeTestRemainingChoices S (A P (DQ P))) (hX : X ∈ UB L S)
    (hE : Rep L G E) : Rep L G (fun Y => E Y * X) := by
  obtain ⟨ts, h, e⟩ := hE
  refine ⟨ts.map fun t => (t.1, t.2 * X), fun t ht => ?_, fun Y => ?_⟩
  · obtain ⟨t, ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨mul_mem (h t ht').1 hX, (h t ht').2⟩
  · dsimp only
    rw [e, List.map_map, ← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp [smul_mul_assoc]

theorem rep_neg {G : Set ℂ} {E : ℂ → SlopeTestRemainingChoices S (A P (DQ P))} (hE : Rep L G E) : Rep L G (fun Y => -E Y) := by
  have := rep_smul (fun _ => (-1 : ℂ)) (fun _ _ => continuousAt_const) hE
  simpa using this

theorem rep_ins {G : Set ℂ} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT) (a : S)
    (E : ℂ → Matrix (Fin 2) (Fin 2) (SlopeTestRemainingChoices S (A P (DQ P)))) (hE : ∀ i j, Rep L G (fun Y => E Y i j)) :
    Rep L G (fun Y => ins a (E Y)) := by
  unfold ins
  have h2 : ∀ i : Fin 2, Rep L G (fun Y => ∑ j, eU a i j * E Y i j) := fun i => by
    have e : (fun Y => ∑ j, eU a i j * E Y i j) = fun Y => eU a i 0 * E Y i 0 + eU a i 1 * E Y i 1 :=
      funext fun Y => Fin.sum_univ_two (fun j => eU a i j * E Y i j)
    rw [e]
    exact rep_add (rep_lmul _ (eU_B hL hLaw a i 0) (hE i 0)) (rep_lmul _ (eU_B hL hLaw a i 1) (hE i 1))
  have e : (fun Y => ∑ i, ∑ j, eU a i j * E Y i j) = fun Y => (∑ j, eU a 0 j * E Y 0 j) + ∑ j, eU a 1 j * E Y 1 j :=
    funext fun Y => Fin.sum_univ_two (fun i => ∑ j, eU a i j * E Y i j)
  rw [e]
  exact rep_add (h2 0) (h2 1)

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I10

section S_I4_I11

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {S : Type} [Fintype S] [DecidableEq S]

theorem rep_mono {G G' : Set ℂ} (h : G' ⊆ G) {E : ℂ → SlopeTestRemainingChoices S (A P (DQ P))} (hE : Rep L G E) : Rep L G' E := by
  obtain ⟨ts, h1, e⟩ := hE
  exact ⟨ts, fun t ht => ⟨(h1 t ht).1, fun Y hY => (h1 t ht).2 Y (h hY)⟩, e⟩

theorem rep_finsum {ι : Type} (s : Finset ι) {G : Set ℂ} (E : ι → ℂ → SlopeTestRemainingChoices S (A P (DQ P)))
    (h : ∀ i ∈ s, Rep L G (E i)) : Rep L G (fun Y => ∑ i ∈ s, E i Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp, fun Y => by simp⟩
  | insert a s ha ih =>
    have e : (fun Y => ∑ i ∈ insert a s, E i Y) = fun Y => E a Y + ∑ i ∈ s, E i Y :=
      funext fun Y => Finset.sum_insert ha
    rw [e]
    exact rep_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

def Gbase (P : M.Par) : Set ℂ := {Y | ∀ j ∈ Finset.Icc 1 (P.k - 1), ∀ π : M.Ty P, Y + (M.rho P π j : ℂ) ≠ 0}

def Gw (P : M.Par) (v : List (Letter ℂ S)) : Set ℂ := {Y | Y ∈ Gbase P ∧ ∀ a ∈ v, Y ≠ a.pt}

variable (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem KSS_BA (f : M.Ty P → ℂ) (j : ℕ) (hj : j ∈ Finset.Icc 1 (P.k - 1)) :
    L.ζ * L.ζbi * (kap P (DQ P) f * SS P (DQ P) j) ∈ BA L := by
  have hDrDG : L.Drb * L.Dri ∈ DG P := by
    obtain ⟨-, d2, d3, -⟩ := DrSC hL
    obtain ⟨w, hw⟩ := Subring.mul_mem _ d2 d3
    rw [← hw]; exact sc_memDG P w
  have hgen : L.Drb * L.Dri * SS P (DQ P) j ∈ bddSet P L :=
    Or.inl (Or.inr ⟨j, Set.mem_Icc.2 (Finset.mem_Icc.1 hj), rfl⟩)
  have hDD : L.D * L.Dbi ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have e1 : L.ζ * L.ζbi * (kap P (DQ P) f * SS P (DQ P) j) =
      L.D * L.Dbi * (kap P (DQ P) f * (L.Drb * L.Dri * SS P (DQ P) j)) := by
    rw [ζζbi_eq hL hLaw, mul_assoc (L.D * L.Dbi), ← mul_assoc (L.Drb * L.Dri), ← kap_comm_DG P _ hDrDG]
    simp only [mul_assoc]
  rw [e1]
  exact mul_mem (gen_BA hL hLaw hDD) (mul_mem (kap_BA hL hLaw _) (gen_BA hL hLaw hgen))

theorem eeA_rep : Rep L (Gbase P) (fun Y => (io (eeA P (DQ P) Y) : SlopeTestRemainingChoices S (A P (DQ P)))) := by
  obtain ⟨-, -, -, -, -, -, hz, -, -, hzbi, -⟩ := id hL
  have e : ∀ Y, eeA P (DQ P) Y = ∑ j ∈ Finset.Icc 1 (P.k - 1), ∑ π : M.Ty P,
      (Y + (M.rho P π j : ℂ))⁻¹ • (L.ζ * L.ζbi * (kap P (DQ P) (Pi.single π 1) * SS P (DQ P) j)) := by
    intro Y
    show zA P (DQ P) * zbiA P (DQ P) * _ = _
    rw [← hz, ← hzbi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hk : kap P (DQ P) (fun π => (Y + (M.rho P π j : ℂ))⁻¹) =
        ∑ π : M.Ty P, (Y + (M.rho P π j : ℂ))⁻¹ • kap P (DQ P) (Pi.single π 1) := by
      have hf : (fun π => (Y + (M.rho P π j : ℂ))⁻¹) = ∑ π : M.Ty P, (Y + (M.rho P π j : ℂ))⁻¹ • Pi.single π (1 : ℂ) := by
        funext π'
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hf, map_sum]
      exact Finset.sum_congr rfl fun π _ => map_smul _ _ _
    rw [hk, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
  have e2 : (fun Y => (io (eeA P (DQ P) Y) : SlopeTestRemainingChoices S (A P (DQ P)))) = fun Y => ∑ j ∈ Finset.Icc 1 (P.k - 1),
      ∑ π ∈ (Finset.univ : Finset (M.Ty P)), (Y + (M.rho P π j : ℂ))⁻¹ •
        (io (L.ζ * L.ζbi * (kap P (DQ P) (Pi.single π 1) * SS P (DQ P) j)) : SlopeTestRemainingChoices S (A P (DQ P))) := by
    funext Y
    rw [e]
    unfold io
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    have := G.io_smul P (S := S) (Y + (M.rho P π j : ℂ))⁻¹ (L.ζ * L.ζbi * (kap P (DQ P) (Pi.single π 1) * SS P (DQ P) j))
    unfold io at this
    exact this
  rw [e2]
  refine rep_finsum _ _ fun j hj => rep_finsum _ _ fun π _ => rep_smul _ (fun Y hY => ?_)
    (rep_const (io_B hL hLaw (KSS_BA hL hLaw _ j hj)))
  exact (continuousAt_id.add continuousAt_const).inv₀ (hY j hj π)

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I11

section S_I4_I12

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {S : Type} [Fintype S] [DecidableEq S]

theorem rep_sub {G : Set ℂ} {E F : ℂ → SlopeTestRemainingChoices S (A P (DQ P))} (hE : Rep L G E) (hF : Rep L G F) :
    Rep L G (fun Y => E Y - F Y) := by
  have := rep_add hE (rep_neg hF)
  simpa [sub_eq_add_neg] using this

variable (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem ee_rep (l : ℕ) : ∀ v : List (Letter ℂ S), (∀ a ∈ v, a.plus = true) →
    Rep L (Gw P v) (fun Y => (ofWord L (startM P (DQ P) l) v).ee Y)
  | [], _ => rep_mono (fun Y hY => hY.1) (eeA_rep hL hLaw)
  | a :: v, h => by
    have ih := rep_mono (fun Y (hY : Y ∈ Gw P (a :: v)) => (⟨hY.1, fun b hb => hY.2 b (List.mem_cons_of_mem _ hb)⟩ :
      Y ∈ Gw P v)) (ee_rep l v fun b hb => h b (List.mem_cons_of_mem _ hb))
    obtain ⟨he, hx, hxi⟩ := frame_memB hL hLaw l v
    have hpl : a.plus = true := h a List.mem_cons_self
    have hcont : ∀ Y ∈ Gw P (a :: v), ContinuousAt (fun Y : ℂ => (Y - a.pt)⁻¹) Y := fun Y hY =>
      (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 (hY.2 a List.mem_cons_self))
    have htz : (tz L : SlopeTestRemainingChoices S (A P (DQ P))) ∈ UB L S := io_B hL hLaw (Subalgebra.smul_mem _ (ζbi_BA hL hLaw) _)
    simp only [ofWord, hpl, if_true]
    show Rep L (Gw P (a :: v)) (fun Y => ins a.intersection_update_fsHerm_neg_one !![(ofWord L (startM P (DQ P) l) v).ee Y -
      (ofWord L (startM P (DQ P) l) v).DD Y a.pt + tz L, -((Y - a.pt)⁻¹ • 1); 0,
      (ofWord L (startM P (DQ P) l) v).xi a.pt * (ofWord L (startM P (DQ P) l) v).ee Y *
        (ofWord L (startM P (DQ P) l) v).x a.pt])
    refine rep_ins hL hLaw a.intersection_update_fsHerm_neg_one _ fun i j => ?_
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one, FrameData.DD]
      exact rep_add (rep_sub ih (rep_smul _ hcont (rep_sub ih (rep_const (he a.pt))))) (rep_const htz)
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      exact rep_neg (rep_smul _ hcont (rep_const (Subalgebra.one_mem _)))
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      exact rep_const (Subalgebra.zero_mem _)
    · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      exact rep_rmul _ (hx a.pt) (rep_lmul _ (hxi a.pt) ih)

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I12

section S_I4_I13

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An Polynomial

noncomputable section

variable {P : M.Par}

theorem PW_add {x y : A P (DQ P)} {C₁ C₂ : ℝ} (hx : PW x C₁) (hy : PW y C₂) : PW (x + y) (C₁ + C₂) := by
  obtain ⟨h1, M1, b1, e1⟩ := hx
  obtain ⟨h2, M2, b2, e2⟩ := hy
  refine ⟨by positivity, fun q => M1 q + M2 q, fun q π π' => ?_, fun f q π => ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (b1 q π π') (b2 q π π'))
  · rw [MAx2.R2.act_add, G.evQ_add, e1, e2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun π' _ => by simp [add_mul]

theorem PW_alg (c : ℂ) : PW (algebraMap ℂ (A P (DQ P)) c) ‖c‖ := by
  classical
  refine ⟨norm_nonneg _, fun _ π π' => if π = π' then c else 0, fun q π π' => ?_, fun f q π => ?_⟩
  · dsimp only; split_ifs <;> simp
  · rw [MAx2.R2.act_alg, Finset.sum_eq_single π (fun b _ hb => by dsimp only; rw [if_neg (Ne.symm hb), zero_mul])
      (by simp)]
    dsimp only
    rw [if_pos rfl]
    rfl

theorem PW_entry {x : A P (DQ P)} {C : ℝ} (hx : PW x C) (q : Qp P.r P.TT) (π π' : M.Ty P) :
    ‖evQ P ((x π π').1 1) q‖ ≤ C := by
  classical
  obtain ⟨h0, Mx, b, e⟩ := hx
  have key := e (fun π'' => if π'' = π' then 1 else 0) q π
  have hl : actA P x (fun π'' => if π'' = π' then 1 else 0) π = (x π π').1 1 := by
    rw [MAx2.R2.actA_eq, Finset.sum_eq_single π' (fun b _ hb => by rw [if_neg hb, map_zero]) (by simp), if_pos rfl]
    rfl
  rw [hl] at key
  rw [key, Finset.sum_eq_single π' (fun b _ hb => by rw [if_neg hb, G.evQ_zero, mul_zero]) (by simp), if_pos rfl]
  show ‖Mx q π π' * 1‖ ≤ C
  rw [mul_one]; exact b q π π'

theorem ptMat_add {N : ℕ} (b c : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (q : Qp P.r P.TT) (i i' : Iota P N) :
    ptMat P (b + c) q i i' = ptMat P b q i i' + ptMat P c q i i' := rfl

theorem ptMat_smul {N : ℕ} (z : ℂ) (b : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) (q : Qp P.r P.TT) (i i' : Iota P N) :
    ptMat P (z • b) q i i' = z * ptMat P b q i i' := by
  show evQ P (((z • b (ixOf P N i).1 (ixOf P N i').1) (ixOf P N i).2 (ixOf P N i').2).1 1) q = _
  rw [show ((z • b (ixOf P N i).1 (ixOf P N i').1) (ixOf P N i).2 (ixOf P N i').2) =
    z • ((b (ixOf P N i).1 (ixOf P N i').1) (ixOf P N i).2 (ixOf P N i').2) from rfl, G.pfst_smul]
  rfl

theorem ptMat_listsum {N : ℕ} (ts : List ((ℂ → ℂ) × SlopeTestRemainingChoices (Fin N) (A P (DQ P)))) (Y : ℂ) (q : Qp P.r P.TT)
    (i i' : Iota P N) :
    ptMat P ((ts.map fun t => t.1 Y • t.2).sum) q i i' = (ts.map fun t => t.1 Y * ptMat P t.2 q i i').sum := by
  induction ts with
  | nil => rfl
  | cons a ts ih => rw [List.map_cons, List.sum_cons, ptMat_add, ptMat_smul, ih, List.map_cons, List.sum_cons]

section PWBA
variable {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem PW_BA {x : A P (DQ P)} (hx : x ∈ BA L) : ∃ C, PW x C := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact PW_gen hTTp hL hLaw hx
  | algebraMap c => exact ⟨_, PW_alg c⟩
  | add x y _ _ h1 h2 => obtain ⟨C1, h1⟩ := h1; obtain ⟨C2, h2⟩ := h2; exact ⟨_, PW_add h1 h2⟩
  | mul x y _ _ h1 h2 => obtain ⟨C1, h1⟩ := h1; obtain ⟨C2, h2⟩ := h2; exact ⟨_, PW_mul h1 h2⟩

theorem ptMat_bound {N : ℕ} {E : SlopeTestRemainingChoices (Fin N) (A P (DQ P))} (hE : E ∈ UB L (Fin N)) :
    ∃ C, ∀ q i i', ‖ptMat P E q i i'‖ ≤ C := by
  have h : ∀ e e', ∃ C, PW (E e e') C := fun e e' => PW_BA hTTp hL hLaw (hE e e')
  choose C hC using h
  refine ⟨∑ e, ∑ e', C e e', fun q i i' => ?_⟩
  have h1 := PW_entry (hC (ixOf P N i).1 (ixOf P N i').1) q (ixOf P N i).2 (ixOf P N i').2
  refine h1.trans ?_
  exact (Finset.single_le_sum (f := fun e' => C (ixOf P N i).1 e') (fun e' _ => (hC _ e').1) (Finset.mem_univ _)).trans
    (Finset.single_le_sum (f := fun e => ∑ e', C e e') (fun e _ => Finset.sum_nonneg fun e' _ => (hC e e').1)
      (Finset.mem_univ _))

end PWBA

theorem lagrange (d : ℕ) (c : Fin (d + 1) → ℂ) (Y : ℂ) :
    ∑ k : Fin (d + 1), Y ^ (k : ℕ) * c k = ∑ m : Fin (d + 1), (∑ k : Fin (d + 1), ((m : ℕ) : ℂ) ^ (k : ℕ) * c k) *
      (Lagrange.basis Finset.univ (fun m : Fin (d + 1) => ((m : ℕ) : ℂ)) m).eval Y := by
  set f : ℂ[X] := ∑ k : Fin (d + 1), C (c k) * X ^ (k : ℕ)
  have hinj : Set.InjOn (fun m : Fin (d + 1) => ((m : ℕ) : ℂ)) (Finset.univ : Finset (Fin (d + 1))) := by
    intro a _ b _ h; simp only at h; exact Fin.ext (by exact_mod_cast h)
  have hdeg : f.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]; exact degree_sum_fin_lt c
  have hf := Lagrange.eq_interpolate hinj hdeg
  have hev : ∀ Z, f.eval Z = ∑ k : Fin (d + 1), Z ^ (k : ℕ) * c k := fun Z => by
    simp only [f, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have := congrArg (eval Y) hf
  rw [hev, Lagrange.interpolate_apply, eval_finset_sum] at this
  rw [this]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_mul, eval_C, hev]

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I13

section S_I4_I14

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable {P : M.Par}

theorem part_poly {N : ℕ} (x : ℂ → A P (DQ P)) (d : ℕ) (hx : G.PolyIn (fun s => x (0 + s)) d)
    (U : Qp P.r P.TT → Iota P N → ℂ) : ∃ α : Fin (d + 1) → Qp P.r P.TT → Iota P N → ℂ,
    ∀ Y q i, wordModuleApply P (io (x Y)) U q i = ∑ k : Fin (d + 1), Y ^ (k : ℕ) * α k q i := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨fun k q i => wordModuleApply P (io (a k)) U q i, fun Y q i => ?_⟩
  have e1 : x Y = ∑ k ∈ Finset.range (d + 1), Y ^ k • a k := by
    have := ha Y; simp only [zero_add] at this; exact this
  have e2 : (io (x Y) : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) = ∑ k ∈ Finset.range (d + 1), Y ^ k • io (a k) := by
    rw [e1]
    unfold io
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := G.io_smul P (S := Fin N) (Y ^ k) (a k)
    unfold io at this
    exact this
  rw [e2, G.apply_matrix_sum]
  simp only [G.apply_matrix_smul]
  rw [Finset.sum_range (fun k => Y ^ k * wordModuleApply P (io (a k)) U q i)]

theorem poly_bound (d : ℕ) (K : Set ℝ) (hK : IsCompact K) : ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (c : Fin (d + 1) → ℂ), ∀ Y ∈ K,
    ‖∑ k : Fin (d + 1), ((Y : ℝ) : ℂ) ^ (k : ℕ) * c k‖ ≤
      Λ * ∑ m : Fin (d + 1), ‖∑ k : Fin (d + 1), ((m : ℕ) : ℂ) ^ (k : ℕ) * c k‖ := by
  have hb : ∀ m : Fin (d + 1), ∃ B, ∀ Y ∈ K,
      ‖(Lagrange.basis Finset.univ (fun m : Fin (d + 1) => ((m : ℕ) : ℂ)) m).eval ((Y : ℝ) : ℂ)‖ ≤ B := by
    intro m
    have hc : Continuous fun Y : ℝ =>
        (Lagrange.basis Finset.univ (fun m : Fin (d + 1) => ((m : ℕ) : ℂ)) m).eval ((Y : ℝ) : ℂ) :=
      (Polynomial.continuous _).comp Complex.continuous_ofReal
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨B, hB⟩
  choose B hB using hb
  refine ⟨∑ m, |B m|, Finset.sum_nonneg fun m _ => abs_nonneg _, fun c Y hY => ?_⟩
  rw [lagrange d c]
  calc ‖∑ m : Fin (d + 1), (∑ k : Fin (d + 1), ((m : ℕ) : ℂ) ^ (k : ℕ) * c k) *
        (Lagrange.basis Finset.univ (fun m : Fin (d + 1) => ((m : ℕ) : ℂ)) m).eval ((Y : ℝ) : ℂ)‖
      ≤ ∑ m : Fin (d + 1), ‖∑ k : Fin (d + 1), ((m : ℕ) : ℂ) ^ (k : ℕ) * c k‖ * |B m| := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((hB m Y hY).trans (le_abs_self _)) (norm_nonneg _)
    _ ≤ ∑ m : Fin (d + 1), ‖∑ k : Fin (d + 1), ((m : ℕ) : ℂ) ^ (k : ℕ) * c k‖ * ∑ m', |B m'| :=
        Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun m' => |B m'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ m))
          (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I14

section S_I4_I15

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

section lists
variable {S : Type} [Fintype S] [DecidableEq S]

theorem phR_cont (v : List (Letter ℂ S)) (e : Ix S) (Y : ℝ) (h : ∀ a ∈ v, Y - a.pt.re - 1 ≠ 0) :
    ContinuousAt (fun Z => MAx3.R.phR v e Z) Y := by
  induction v with
  | nil => simpa [MAx3.R.phR] using continuousAt_const
  | cons a v ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ha := h a List.mem_cons_self
    simp only [MAx3.R.phR, List.map_cons, List.prod_cons] at ih' ⊢
    refine ContinuousAt.mul ?_ ih'
    split_ifs
    · exact (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const |>.sub continuousAt_const) ha
    · exact continuousAt_const

theorem psR_cont (v : List (Letter ℂ S)) (Y : ℝ) (h : ∀ a ∈ v, Y - a.pt.re ≠ 0) :
    ContinuousAt (fun Z => MAx3.R.psR v Z) Y := by
  induction v with
  | nil => simpa [MAx3.R.psR] using continuousAt_const
  | cons a v ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ha := h a List.mem_cons_self
    simp only [MAx3.R.psR, List.map_cons, List.prod_cons] at ih' ⊢
    exact ContinuousAt.mul (((continuousAt_id.sub continuousAt_const).add continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) ha) ih'

theorem phR_ne (v : List (Letter ℂ S)) (e : Ix S) (Y : ℝ) (h : ∀ a ∈ v, Y - a.pt.re ≠ 0 ∧ Y - a.pt.re - 1 ≠ 0) :
    MAx3.R.phR v e Y ≠ 0 := by
  induction v with
  | nil => simp [MAx3.R.phR]
  | cons a v ih =>
    simp only [MAx3.R.phR, List.map_cons, List.prod_cons] at ih ⊢
    refine mul_ne_zero ?_ (ih fun b hb => h b (List.mem_cons_of_mem _ hb))
    split_ifs
    · exact div_ne_zero (h a List.mem_cons_self).1 (h a List.mem_cons_self).2
    · exact one_ne_zero

end lists

variable {P : M.Par}

theorem ofReal_add_one' (Y : ℝ) : (Y : ℂ) + 1 = ((Y + 1 : ℝ) : ℂ) := by push_cast; ring

theorem sx_cont (l : ℕ) (π : M.Ty P) : Continuous (fun Z => MAx3.R.sx P l π Z) := by
  unfold MAx3.R.sx I.xpoly
  exact continuous_const.mul (continuous_finset_prod _ fun i _ => continuous_id.add continuous_const)

theorem qp_cont : Continuous (fun Z => MAx3.R.qp P Z) := by
  unfold MAx3.R.qp I.qpoly
  exact continuous_const.mul (continuous_finset_prod _ fun i _ =>
    ((continuous_id.add continuous_const).add continuous_const).mul
      ((continuous_id.add continuous_const).add continuous_const))

theorem kt_cont (l : ℕ) (w : List ℝ) (π : M.Ty P) (e : Ix (Fin (w.length + 1))) (Y : ℝ)
    (h : ∀ p ∈ w, Y - p - 1 ≠ 0) :
    ContinuousAt (fun Z : ℝ => (cs (M.x0 P l π) (M.qC P) (MAx3.R.tl w) e *
      xs (M.x0 P l π) (MAx3.R.tl w) e (Z : ℂ)).re) Y := by
  have e1 : (fun Z : ℝ => (cs (M.x0 P l π) (M.qC P) (MAx3.R.tl w) e * xs (M.x0 P l π) (MAx3.R.tl w) e (Z : ℂ)).re) =
      fun Z : ℝ => (cs (M.x0 P l π) (M.qC P) (MAx3.R.tl w) e *
        ((MAx3.R.sx P l π Z : ℝ) : ℂ) * ((MAx3.R.phR (MAx3.R.tl w) e Z : ℝ) : ℂ)).re := by
    funext Z
    rw [MAx3.R.xs_real _ _ (MAx3.R.tl_real w), MAx3.R.coordinate_real, mul_assoc]
  rw [e1]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine ContinuousAt.mul (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
    (sx_cont l π).continuousAt)) (Complex.continuous_ofReal.continuousAt.comp (phR_cont _ e Y fun a ha => ?_))
  obtain ⟨p, hp, hpe⟩ := MAx3.R.tl_mem w ha
  rw [hpe, Complex.ofReal_re]; exact h p hp

theorem kf_cont (l : ℕ) (w : List ℝ) (π : M.Ty P) (e : Ix (Fin (w.length + 1))) (Y : ℝ)
    (h : ∀ p ∈ w, Y - p ≠ 0 ∧ Y + 1 - p - 1 ≠ 0 ∧ Y + 1 - p ≠ 0) (hsx : MAx3.R.sx P l π (Y + 1) ≠ 0) :
    ContinuousAt (fun Z : ℝ => (cs (M.x0 P l π) (M.qC P) (MAx3.R.tl w) e *
      (qw (M.qC P) (MAx3.R.tl w) (Z : ℂ) / xs (M.x0 P l π) (MAx3.R.tl w) e ((Z : ℂ) + 1))).re) Y := by
  have e1 : (fun Z : ℝ => (cs (M.x0 P l π) (M.qC P) (MAx3.R.tl w) e *
      (qw (M.qC P) (MAx3.R.tl w) (Z : ℂ) / xs (M.x0 P l π) (MAx3.R.tl w) e ((Z : ℂ) + 1))).re) =
      fun Z : ℝ => (cs (M.x0 P l π) (M.qC P) (MAx3.R.tl w) e *
        (((MAx3.R.qp P Z * MAx3.R.psR (MAx3.R.tl w) Z : ℝ) : ℂ) /
          ((MAx3.R.sx P l π (Z + 1) * MAx3.R.phR (MAx3.R.tl w) e (Z + 1) : ℝ) : ℂ))).re := by
    funext Z
    rw [ofReal_add_one', MAx3.R.qw_real _ _ (MAx3.R.tl_real w), MAx3.R.xs_real _ _ (MAx3.R.tl_real w),
      MAx3.R.coordinate_real, MAx3.R.qC_real]
    push_cast; ring
  rw [e1]
  have hpts : ∀ a ∈ MAx3.R.tl w, ∃ p ∈ w, a.pt.re = p := fun a ha => by
    obtain ⟨p, hp, hpe⟩ := MAx3.R.tl_mem w ha
    exact ⟨p, hp, by rw [hpe, Complex.ofReal_re]⟩
  have hden : MAx3.R.sx P l π (Y + 1) * MAx3.R.phR (MAx3.R.tl w) e (Y + 1) ≠ 0 :=
    mul_ne_zero hsx (phR_ne _ e _ fun a ha => by
      obtain ⟨p, hp, hpe⟩ := hpts a ha; rw [hpe]; exact ⟨(h p hp).2.2, (h p hp).2.1⟩)
  refine Complex.continuous_re.continuousAt.comp (continuousAt_const.mul ?_)
  refine (Complex.continuous_ofReal.continuousAt.comp ?_).div (Complex.continuous_ofReal.continuousAt.comp ?_)
    (by exact_mod_cast hden)
  · exact (qp_cont).continuousAt.mul (psR_cont _ Y fun a ha => by
      obtain ⟨p, hp, hpe⟩ := hpts a ha; rw [hpe]; exact (h p hp).1)
  · have h1 : ContinuousAt (fun Z : ℝ => Z + 1) Y := continuousAt_id.add continuousAt_const
    exact ((sx_cont l π).continuousAt.comp (f := fun Z : ℝ => Z + 1) h1).mul
      ((phR_cont _ e (Y + 1) fun a ha => by
        obtain ⟨p, hp, hpe⟩ := hpts a ha; rw [hpe]; exact (h p hp).2.1).comp (f := fun Z : ℝ => Z + 1) h1)

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I15

section S_I4_I16

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory

noncomputable section

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  {lam : Fin (P.k + 2 * P.r + 1) → ℝ} {α β Lb : ℝ} {Ntot : ℕ}

theorem normal_form_square_integrable (hH : Hyps P l L j lam α β Lb Ntot) {n : ℕ} (hn : n ≤ 2 * Ntot + 2) {x : A P (DQ P)}
    (hx : x ∈ NormalFormTwo L (SB L) n n) : ∃ (C : ℝ) (F : Qp P.r P.TT → ℝ), 0 ≤ C ∧ MemLp F 2 (mu0 P.r P.TT) ∧
      (∀ q, 0 ≤ F q) ∧ ∀ π q, ‖evQ P (actA P x j π) q‖ * Dabs q ^ n ≤ C * F q := by
  have hOK := hH.1.1
  have hTTp : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hL := hH.1.2.2.2.1
  have hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTTp.le
  obtain ⟨C, T, hC, hT, hb⟩ := normal_form_two_bounded hTTp hL hLaw j hx
  exact ⟨C, _, hC, memLp_listsum T _ fun t ht => hat_product_square_integrable hH.2.1 t.1 (by rw [(hT t ht).1]; exact hn) (hT t ht).2 t.2,
    fun q => sumT_nonneg j T q, hb⟩

theorem piece_square_integrable (hH : Hyps P l L j lam α β Lb Ntot) (w : List ℝ) (hl : w.length < Ntot) (y : ℂ) (b : Bool)
    (i : Iota P w.length) : ∃ (C : ℝ) (F : Qp P.r P.TT → ℝ), 0 ≤ C ∧ MemLp F 2 (mu0 P.r P.TT) ∧ (∀ q, 0 ≤ F q) ∧
      ∀ q, ‖wordModuleApply P (io (if b then L.Dbi * L.R0 y else L.Di * L.Ahat y)) (Xw P l L (ju P j) w) q i‖ *
        Dabs q ^ (w.length + 1) ≤ C * F q := by
  have hOK := hH.1.1
  have hTTp : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hL := hH.1.2.2.2.1
  have hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTTp.le
  obtain ⟨𝒳, h1, h2⟩ := Xw_rep hL hLaw l j w
  have h0 : (0 : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P))) ∈ UB L (Fin w.length) := Subalgebra.zero_mem _
  have hrep := letter_rep hL hLaw y y 0 𝒳 j _ h2
  obtain ⟨C, F, hC, hF, hF0, hb⟩ := normal_form_square_integrable hH (by omega) (lvec_NF hL hLaw y y 0 h0 𝒳 h1 (ixOf P (w.length + 1) (b, i)).1)
  refine ⟨C, F, hC, hF, hF0, fun q => ?_⟩
  have e : wordModuleApply P (io (if b then L.Dbi * L.R0 y else L.Di * L.Ahat y)) (Xw P l L (ju P j) w) q i =
      evQ P (actA P (lvec L y y 0 𝒳 (ixOf P (w.length + 1) (b, i)).1) j (ixOf P (w.length + 1) (b, i)).2) q := by
    rw [← hrep q b i]
    cases b
    · rfl
    · simp
  rw [e]
  exact hb _ q

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I16

section S_I4_I17

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory

noncomputable section

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  {lam : Fin (P.k + 2 * P.r + 1) → ℝ} {α β Lb : ℝ} {Ntot : ℕ}

def Jbox (α β Lb : ℝ) (n : ℕ) : Set ℝ :=
  Set.Icc (α + (β - α) / 3 + 2 * (n : ℝ) * Lb) (α + (β - α) / 3 + 2 * (n : ℝ) * Lb + Lb)

theorem jbox_facts (c : LE.Cut) (hH : Hyps P l L j lam α β Lb Ntot) (w : List ℝ)
    (hw : (sysQ P l L j lam α β Lb c Ntot).OnBoxes w) (hl : w.length < Ntot) {Y : ℝ}
    (hY : Y ∈ Jbox α β Lb w.length) :
    (∀ p ∈ w, Lb ≤ Y - p) ∧ Y ∈ Set.Icc α β ∧ Y + 1 ∈ Set.Icc α β ∧ 2 < Lb := by
  obtain ⟨⟨hOK, hl1, hlk, _, hu, hu', hαβ, hcut⟩, _, _, _, hN, hNL, hL2, hn, h6⟩ := hH
  have hBF := Formalism.FourierDecayAlt.P.boxes_fit (sysQ P l L j lam α β Lb c Ntot) hL2 h6
  have hYb : Y ∈ (sysQ P l L j lam α β Lb c Ntot).box w.length := hY
  have hYm : α + (β - α) / 3 ≤ Y ∧ Y ≤ β - (β - α) / 3 := hBF.1 w.length hl hYb
  have hN1 : (1 : ℝ) ≤ Ntot := by exact_mod_cast (by omega : 1 ≤ Ntot)
  have hβα : 12 ≤ β - α := by nlinarith
  refine ⟨fun p hp => ?_, ⟨by linarith [hYm.1], by linarith [hYm.2]⟩, ⟨by linarith [hYm.1], by linarith [hYm.2]⟩, hL2⟩
  obtain ⟨a, ha, hpa⟩ := MAx3.R.onBoxes_mem _ w hw p hp
  exact hBF.2.1 a w.length ha p hpa Y hYb

theorem sx_pos (hH : Hyps P l L j lam α β Lb Ntot) (π : M.Ty P) {Z : ℝ} (hZ : Z ∈ Set.Icc α β) :
    0 < MAx3.R.sx P l π Z ∧ 0 < MAx3.R.sx P l π (Z + 1) := by
  obtain ⟨⟨hOK, hl1, hlk, _, hu, hu', hαβ, hcut⟩, _⟩ := hH
  have hπ := Formalism.FourierDecayAlt.P.types_interlace P hOK π
  have h0 := Formalism.FourierDecayAlt.P.interlacing_sign P.k P.u P.u' (M.rho P π) l Z hl1 hlk hπ (hcut Z hZ) 0 (by simp)
  have h1 := Formalism.FourierDecayAlt.P.interlacing_sign P.k P.u P.u' (M.rho P π) l Z hl1 hlk hπ (hcut Z hZ) 1 (by simp)
  rw [add_zero] at h0
  exact ⟨h0, h1⟩

theorem inGw (hH : Hyps P l L j lam α β Lb Ntot) (w : List ℝ) {Y : ℝ} (hYI : Y ∈ Set.Icc α β)
    (hfar : ∀ p ∈ w, Lb ≤ Y - p) (hL2 : 2 < Lb) : ((Y : ℝ) : ℂ) ∈ Gw P (wordP w) := by
  refine ⟨fun i hi π => ?_, fun a ha => ?_⟩
  · have h := (sx_pos hH π hYI).1
    unfold MAx3.R.sx I.xpoly at h
    have hne : (∏ t ∈ Finset.Icc 1 (P.k - 1), (Y + M.rho P π t)) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
    have := (Finset.prod_ne_zero_iff.1 hne) i hi
    exact_mod_cast this
  · obtain ⟨p, hp, e⟩ := MAx2.mem_wordP ha
    rw [e]
    intro h
    have : Y = p := by exact_mod_cast h
    have := hfar p hp
    linarith

theorem listsum_ptMat {N : ℕ} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
    (K : Set ℝ) (hK : IsCompact K) (G : Set ℂ) (hKG : ∀ Y ∈ K, ((Y : ℝ) : ℂ) ∈ G) :
    ∀ ts : List ((ℂ → ℂ) × SlopeTestRemainingChoices (Fin N) (A P (DQ P))), (∀ t ∈ ts, t.2 ∈ UB L (Fin N) ∧ ∀ Y ∈ G, ContinuousAt t.1 Y) →
      ∃ E, ∀ q i i', (∀ Y ∈ K, ‖(ts.map fun t => t.1 (Y : ℂ) * ptMat P t.2 q i i').sum‖ ≤ E) ∧
        ContinuousOn (fun Y : ℝ => (ts.map fun t => t.1 (Y : ℂ) * ptMat P t.2 q i i').sum) K
  | [], _ => ⟨0, fun q i i' => ⟨fun Y _ => by simp, by simpa using continuousOn_const⟩⟩
  | t :: ts, h => by
    obtain ⟨E, hE⟩ := listsum_ptMat hTTp hL hLaw K hK G hKG ts fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    obtain ⟨hUB, hc⟩ := h t List.mem_cons_self
    obtain ⟨C, hC⟩ := ptMat_bound hTTp hL hLaw hUB
    have hcK : ContinuousOn (fun Y : ℝ => t.1 (Y : ℂ)) K := fun Y hY =>
      ((hc _ (hKG Y hY)).comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hcK
    refine ⟨|R| * |C| + E, fun q i i' => ⟨fun Y hY => ?_, ?_⟩⟩
    · rw [List.map_cons, List.sum_cons]
      refine (norm_add_le _ _).trans (add_le_add ?_ ((hE q i i').1 Y hY))
      rw [norm_mul]
      exact mul_le_mul ((hR Y hY).trans (le_abs_self _)) ((hC q i i').trans (le_abs_self _)) (norm_nonneg _)
        (abs_nonneg _)
    · simp only [List.map_cons, List.sum_cons]
      exact (hcK.mul continuousOn_const).add (hE q i i').2

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I17

section S_I4_I18

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory

noncomputable section

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  {lam : Fin (P.k + 2 * P.r + 1) → ℝ} {α β Lb : ℝ} {Ntot : ℕ}

theorem part_poly2 (L : LevelData (A P (DQ P)) P.r) {N : ℕ} (b : Bool) (U : Qp P.r P.TT → Iota P N → ℂ) :
    ∃ α : Fin (P.r + 1 + 1) → Qp P.r P.TT → Iota P N → ℂ, ∀ Y q i,
      wordModuleApply P (io (if b then L.Dbi * L.R0 Y else L.Di * L.Ahat Y)) U q i =
        ∑ k : Fin (P.r + 1 + 1), Y ^ (k : ℕ) * α k q i := by
  refine part_poly (fun y => if b then L.Dbi * L.R0 y else L.Di * L.Ahat y) (P.r + 1) ?_ U
  cases b
  · simpa using G.polyIn_mono (G.polyIn_const_mul L.Di (G.Ahat_poly P L 0)) (Nat.le_succ P.r)
  · simpa using G.polyIn_const_mul L.Dbi (G.raising_operator_polynomial P L 0)

theorem memLp_finsum {ι : Type} (s : Finset ι) (f : ι → Qp P.r P.TT → ℝ) (h : ∀ i ∈ s, MemLp (f i) 2 (mu0 P.r P.TT)) :
    MemLp (fun q => ∑ i ∈ s, f i q) 2 (mu0 P.r P.TT) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (memLp_const (0 : ℝ))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem part_unif (hH : Hyps P l L j lam α β Lb Ntot) (w : List ℝ) (hl : w.length < Ntot) (b : Bool)
    (K : Set ℝ) (hK : IsCompact K) :
    ∃ B : Iota P w.length → Qp P.r P.TT → ℝ, (∀ i, MemLp (B i) 2 (mu0 P.r P.TT)) ∧ (∀ i q, 0 ≤ B i q) ∧
      ∀ Y ∈ K, ∀ q i, ‖wordModuleApply P (io (if b then L.Dbi * L.R0 ((Y : ℝ) : ℂ) else L.Di * L.Ahat ((Y : ℝ) : ℂ)))
        (Xw P l L (ju P j) w) q i‖ * Dabs q ^ (w.length + 1) ≤ B i q := by
  have hTT : 0 ≤ P.TT := (mul_pos hH.1.1.T_pos hH.1.1.T'_pos).le
  obtain ⟨αc, hα⟩ := part_poly2 L b (Xw P l L (ju P j) w)
  obtain ⟨Λ, hΛ0, hΛ⟩ := poly_bound (P.r + 1) K hK
  have hnode : ∀ (m : Fin (P.r + 1 + 1)) (i : Iota P w.length), ∃ (C : ℝ) (F : Qp P.r P.TT → ℝ), 0 ≤ C ∧
      MemLp F 2 (mu0 P.r P.TT) ∧ (∀ q, 0 ≤ F q) ∧
      ∀ q, ‖wordModuleApply P (io (if b then L.Dbi * L.R0 ((m : ℕ) : ℂ) else L.Di * L.Ahat ((m : ℕ) : ℂ)))
        (Xw P l L (ju P j) w) q i‖ * Dabs q ^ (w.length + 1) ≤ C * F q :=
    fun m i => piece_square_integrable hH w hl ((m : ℕ) : ℂ) b i
  choose C F hC hF hF0 hb using hnode
  refine ⟨fun i q => Λ * ∑ m, C m i * F m i q, fun i => ?_, fun i q => ?_, fun Y hY q i => ?_⟩
  · exact (memLp_finsum _ _ fun m _ => (hF m i).const_mul (C m i)).const_mul Λ
  · exact mul_nonneg hΛ0 (Finset.sum_nonneg fun m _ => mul_nonneg (hC m i) (hF0 m i q))
  · have hD := pow_nonneg (Dabs_pos hTT q).le (w.length + 1)
    rw [hα]
    calc ‖∑ k : Fin (P.r + 1 + 1), ((Y : ℝ) : ℂ) ^ (k : ℕ) * αc k q i‖ * Dabs q ^ (w.length + 1)
        ≤ (Λ * ∑ m : Fin (P.r + 1 + 1), ‖∑ k : Fin (P.r + 1 + 1), ((m : ℕ) : ℂ) ^ (k : ℕ) * αc k q i‖) *
            Dabs q ^ (w.length + 1) := mul_le_mul_of_nonneg_right (hΛ (fun k => αc k q i) Y hY) hD
      _ = Λ * ∑ m : Fin (P.r + 1 + 1), ‖wordModuleApply P (io (if b then L.Dbi * L.R0 ((m : ℕ) : ℂ)
            else L.Di * L.Ahat ((m : ℕ) : ℂ))) (Xw P l L (ju P j) w) q i‖ * Dabs q ^ (w.length + 1) := by
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hα]
      _ ≤ Λ * ∑ m, C m i * F m i q :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hb m i q) hΛ0

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I18

section S_I4_I19

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory

noncomputable section

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  {lam : Fin (P.k + 2 * P.r + 1) → ℝ} {α β Lb : ℝ} {Ntot : ℕ}

def kap' (P : M.Par) (l : ℕ) (w : List ℝ) (b : Bool) (i : Iota P w.length) (Y : ℝ) : ℝ :=
  if b then (cs (M.x0 P l (ixOf P w.length i).2) (M.qC P) (MAx3.R.tl w) (ixOf P (w.length + 1) (true, i)).1 *
      xs (M.x0 P l (ixOf P w.length i).2) (MAx3.R.tl w) (ixOf P (w.length + 1) (true, i)).1 (Y : ℂ)).re
  else (cs (M.x0 P l (ixOf P w.length i).2) (M.qC P) (MAx3.R.tl w) (ixOf P (w.length + 1) (false, i)).1 *
      (qw (M.qC P) (MAx3.R.tl w) (Y : ℂ) /
        xs (M.x0 P l (ixOf P w.length i).2) (MAx3.R.tl w) (ixOf P (w.length + 1) (false, i)).1 ((Y : ℂ) + 1))).re

theorem dw_eq (w : List ℝ) (Y : ℝ) (q : Qp P.r P.TT) (b : Bool) (i : Iota P w.length) :
    dwW P l (Y :: w) q (b, i) = Wq P q ^ (w.length + 1) * kap' P l w b i Y := by
  cases b
  · rw [MAx3.R.dw_false]; rfl
  · rw [MAx3.R.dw_true]; rfl

theorem kap'_cont (hH : Hyps P l L j lam α β Lb Ntot) (w : List ℝ) (b : Bool) (i : Iota P w.length) {Y : ℝ}
    (hfar : ∀ p ∈ w, Lb ≤ Y - p) (hYI : Y ∈ Set.Icc α β) (hL2 : 2 < Lb) :
    ContinuousAt (kap' P l w b i) Y := by
  cases b
  · exact kf_cont l w _ _ Y (fun p hp => by have := hfar p hp; exact ⟨by linarith, by linarith, by linarith⟩)
      (sx_pos hH _ hYI).2.ne'
  · exact kt_cont l w _ _ Y (fun p hp => by have := hfar p hp; linarith)

theorem gL_false (w : List ℝ) (Y : ℝ) (X : Qp P.r P.TT → Iota P w.length → ℂ) (q : Qp P.r P.TT) (i : Iota P w.length) :
    gL P l L w Y X q (false, i) = wordModuleApply P (io (if false then L.Dbi * L.R0 (Y : ℂ) else L.Di * L.Ahat (Y : ℂ))) X q i :=
  rfl

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I19

section S_I4_I21

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory

noncomputable section

variable {P : M.Par}

def BdF {N : ℕ} (BA BR : Iota P N → Qp P.r P.TT → ℝ) (E : ℝ) : Bool × Iota P N → Qp P.r P.TT → ℝ :=
  fun a q => if a.1 then BR a.2 q + |E| * ∑ i', BA i' q else BA a.2 q

theorem gx_true_bound {l : ℕ} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (w : List ℝ) (Y : ℝ)
    (X : Qp P.r P.TT → Iota P w.length → ℂ) (q : Qp P.r P.TT) (i : Iota P w.length)
    (BA BR : Iota P w.length → Qp P.r P.TT → ℝ) (E D : ℝ) (hD : 0 ≤ D)
    (hR : ‖wordModuleApply P (io (L.Dbi * L.R0 (Y : ℂ))) X q i‖ * D ≤ BR i q)
    (hA : ∀ i', ‖gL P l L w Y X q (false, i')‖ * D ≤ BA i' q)
    (hP : ∀ i', ‖ptMat P ((frW P l L w).ee (Y : ℂ)) q i i'‖ ≤ |E|) :
    ‖gL P l L w Y X q (true, i)‖ * D ≤ BdF BA BR E (true, i) q := by
  rw [G.gX_split P hL w Y X q i]
  have h1 : ‖wordModuleApply P (io (L.Dbi * L.R0 (Y : ℂ))) X q i +
      ∑ i', ptMat P ((frW P l L w).ee (Y : ℂ)) q i i' * gL P l L w Y X q (false, i')‖ ≤
      ‖wordModuleApply P (io (L.Dbi * L.R0 (Y : ℂ))) X q i‖ +
        ∑ i', ‖ptMat P ((frW P l L w).ee (Y : ℂ)) q i i'‖ * ‖gL P l L w Y X q (false, i')‖ := by
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i' _ => norm_mul _ _))
  have h2 : ∀ i', ‖ptMat P ((frW P l L w).ee (Y : ℂ)) q i i'‖ * ‖gL P l L w Y X q (false, i')‖ * D ≤
      |E| * BA i' q := fun i' => by
    rw [mul_assoc]
    exact mul_le_mul (hP i') (hA i') (mul_nonneg (norm_nonneg _) hD) (abs_nonneg _)
  calc _ ≤ (‖wordModuleApply P (io (L.Dbi * L.R0 (Y : ℂ))) X q i‖ +
        ∑ i', ‖ptMat P ((frW P l L w).ee (Y : ℂ)) q i i'‖ * ‖gL P l L w Y X q (false, i')‖) * D :=
        mul_le_mul_of_nonneg_right h1 hD
    _ = ‖wordModuleApply P (io (L.Dbi * L.R0 (Y : ℂ))) X q i‖ * D +
        ∑ i', ‖ptMat P ((frW P l L w).ee (Y : ℂ)) q i i'‖ * ‖gL P l L w Y X q (false, i')‖ * D := by
        rw [add_mul, Finset.sum_mul]
    _ ≤ BR i q + ∑ i', |E| * BA i' q := add_le_add hR (Finset.sum_le_sum fun i' _ => h2 i')
    _ = BdF BA BR E (true, i) q := by simp only [BdF, if_true, Finset.mul_sum]

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I21

section S_I4_I22

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory

noncomputable section

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r}

theorem dom_bound {w : List ℝ} {Y σ : ℝ} (hTT : 0 ≤ P.TT) (ε : ℝ) (hε : 0 < ε) (hσ : ((w.length + 1 : ℕ) : ℝ) ≤ σ)
    (K : Bool × Iota P w.length → ℝ) (Bd : Bool × Iota P w.length → Qp P.r P.TT → ℝ)
    (X : Qp P.r P.TT → Iota P w.length → ℂ) (hK : ∀ a, ‖kap' P l w a.1 a.2 Y‖ ≤ K a) {q : Qp P.r P.TT}
    (hg : ∀ a, ‖gL P l L w Y X q a‖ * Dabs q ^ (w.length + 1) ≤ Bd a q) :
    ‖LE.th ε σ (Gq P q) * LE.sq (baseQ P) (dwW P l (Y :: w)) (gL P l L w Y X) q‖ ≤
      ∑ a : Bool × Iota P w.length, |K a| * (ε⁻¹) ^ (w.length + 1) * (Bd a q) ^ 2 := by
  have hth0 : 0 ≤ LE.th ε σ (Gq P q) := by unfold LE.th; have := Gq_pos P q; positivity
  rw [Real.norm_eq_abs]
  unfold LE.sq
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have h1 := comp_le hTT ε σ (w.length + 1) hε hσ (|kap' P l w a.1 a.2 Y|) (gL P l L w Y X q a) q
  rw [abs_abs] at h1
  have hnn : 0 ≤ ‖gL P l L w Y X q a‖ * Dabs q ^ (w.length + 1) :=
    mul_nonneg (norm_nonneg _) (pow_nonneg (Dabs_pos hTT q).le _)
  have hKa : |kap' P l w a.1 a.2 Y| ≤ |K a| := (hK a).trans (le_abs_self _)
  have he : |LE.th ε σ (Gq P q) * (dwW P l (Y :: w) q a * ‖gL P l L w Y X q a‖ ^ 2)| =
      LE.th ε σ (Gq P q) * (Wq P q ^ (w.length + 1) * |kap' P l w a.1 a.2 Y|) * ‖gL P l L w Y X q a‖ ^ 2 := by
    rcases a with ⟨b, i⟩
    rw [abs_mul, abs_of_nonneg hth0, abs_mul, abs_pow, abs_norm, dw_eq, abs_mul, abs_pow,
      abs_of_pos (MAx3.Wq_pos P hTT q)]
    ring
  rw [he]
  refine h1.trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_right hKa (by positivity)) (pow_le_pow_left₀ hnn (hg a) 2)
    (sq_nonneg _) (by positivity)

theorem cont_dw (w : List ℝ) {K : Set ℝ} (hkc : ∀ a : Bool × Iota P w.length, ContinuousOn (kap' P l w a.1 a.2) K)
    (q : Qp P.r P.TT) (b : Bool) (i : Iota P w.length) : ContinuousOn (fun Y => dwW P l (Y :: w) q (b, i)) K := by
  have e : (fun Y => dwW P l (Y :: w) q (b, i)) = fun Y => Wq P q ^ (w.length + 1) * kap' P l w b i Y :=
    funext fun Y => dw_eq w Y q b i
  rw [e]
  exact continuousOn_const.mul (hkc (b, i))

theorem cont_gA (w : List ℝ) (X : Qp P.r P.TT → Iota P w.length → ℂ) (K : Set ℝ) (q : Qp P.r P.TT)
    (i : Iota P w.length) : ContinuousOn (fun Y : ℝ => gL P l L w Y X q (false, i)) K := by
  obtain ⟨αc, hα⟩ := part_poly2 L false X
  have e : (fun Y : ℝ => gL P l L w Y X q (false, i)) =
      fun Y : ℝ => ∑ k : Fin (P.r + 1 + 1), ((Y : ℝ) : ℂ) ^ (k : ℕ) * αc k q i :=
    funext fun Y => (gL_false w Y X q i).trans (hα _ q i)
  rw [e]
  exact (continuous_finset_sum _ fun k _ => (Complex.continuous_ofReal.pow _).mul continuous_const).continuousOn

theorem cont_gR (hL : IsModelLevel P (DQ P) L) (w : List ℝ) (X : Qp P.r P.TT → Iota P w.length → ℂ) (K : Set ℝ)
    (ts : List ((ℂ → ℂ) × SlopeTestRemainingChoices (Fin w.length) (A P (DQ P)))) (q : Qp P.r P.TT)
    (hEc : ∀ i i', ContinuousOn (fun Y : ℝ => (ts.map fun t => t.1 (Y : ℂ) * ptMat P t.2 q i i').sum) K)
    (hpt : ∀ (Y : ℝ) i i', ptMat P ((frW P l L w).ee (Y : ℂ)) q i i' =
      (ts.map fun t => t.1 (Y : ℂ) * ptMat P t.2 q i i').sum) (i : Iota P w.length) :
    ContinuousOn (fun Y : ℝ => gL P l L w Y X q (true, i)) K := by
  obtain ⟨αc, hα⟩ := part_poly2 L true X
  have e : (fun Y : ℝ => gL P l L w Y X q (true, i)) = fun Y : ℝ =>
      ∑ k : Fin (P.r + 1 + 1), ((Y : ℝ) : ℂ) ^ (k : ℕ) * αc k q i +
        ∑ i', (ts.map fun t => t.1 (Y : ℂ) * ptMat P t.2 q i i').sum * gL P l L w Y X q (false, i') := by
    funext Y
    rw [G.gX_split P hL w Y X q i]
    have h1 := hα (Y : ℂ) q i
    simp only [if_true] at h1
    rw [h1]
    congr 1
    exact Finset.sum_congr rfl fun i' _ => by rw [hpt]
  rw [e]
  refine ContinuousOn.add ?_ (continuousOn_finset_sum _ fun i' _ => (hEc i i').mul (cont_gA w X K q i'))
  exact (continuous_finset_sum _ fun k _ => (Complex.continuous_ofReal.pow _).mul continuous_const).continuousOn

theorem cont_integrand (hL : IsModelLevel P (DQ P) L) (w : List ℝ) (X : Qp P.r P.TT → Iota P w.length → ℂ)
    {K : Set ℝ} {ε σ : ℝ} (hkc : ∀ a : Bool × Iota P w.length, ContinuousOn (kap' P l w a.1 a.2) K)
    (ts : List ((ℂ → ℂ) × SlopeTestRemainingChoices (Fin w.length) (A P (DQ P)))) {q : Qp P.r P.TT}
    (hEc : ∀ i i', ContinuousOn (fun Y : ℝ => (ts.map fun t => t.1 (Y : ℂ) * ptMat P t.2 q i i').sum) K)
    (hpt : ∀ (Y : ℝ) i i', ptMat P ((frW P l L w).ee (Y : ℂ)) q i i' =
      (ts.map fun t => t.1 (Y : ℂ) * ptMat P t.2 q i i').sum) :
    ContinuousOn (fun Y : ℝ => LE.th ε σ (Gq P q) * LE.sq (baseQ P) (dwW P l (Y :: w)) (gL P l L w Y X) q) K := by
  have key : ∀ a : Bool × Iota P w.length,
      ContinuousOn (fun Y : ℝ => dwW P l (Y :: w) q a * ‖gL P l L w Y X q a‖ ^ 2) K := by
    intro a
    rcases a with ⟨b, i⟩
    have hg : ContinuousOn (fun Y : ℝ => gL P l L w Y X q (b, i)) K := by
      cases b
      · exact cont_gA w X K q i
      · exact cont_gR hL w X K ts q hEc hpt i
    exact (cont_dw w hkc q b i).mul (hg.norm.pow 2)
  unfold LE.sq
  exact continuousOn_const.mul (continuousOn_finsetSum (Finset.univ : Finset (Bool × Iota P w.length))
    (f := fun a Y => dwW P l (Y :: w) q a * ‖gL P l L w Y X q a‖ ^ 2) fun a _ => key a)

end

end Formalism.FourierDecayAlt.P.MAx3.I4

end S_I4_I22

section S_I4_I20

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx1.An MeasureTheory

theorem fourth_identity_dual : Formalism.FourierDecayAlt.MA.I4'Q := by
  intro P l L j lam α β Lb c Ntot hH w hw hl ε hε
  have hOK := hH.1.1
  have hTTp : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hTT := hTTp.le
  have hL := hH.1.2.2.2.1
  have hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT
  refine ⟨fun Y _ s => MAx3.I4.gs_int hH w hl ε hε Y s, ?_⟩
  have hJc : IsCompact (MAx3.I4.Jbox α β Lb w.length) := isCompact_Icc
  have hfacts : ∀ Y ∈ MAx3.I4.Jbox α β Lb w.length, (∀ p ∈ w, Lb ≤ Y - p) ∧ Y ∈ Set.Icc α β ∧
      Y + 1 ∈ Set.Icc α β ∧ 2 < Lb := fun Y hY => MAx3.I4.jbox_facts c hH w hw hl hY
  obtain ⟨BA, hBA, hBA0, hBAb⟩ := MAx3.I4.part_unif hH w hl false _ hJc
  obtain ⟨BR, hBR, hBR0, hBRb⟩ := MAx3.I4.part_unif hH w hl true _ hJc
  obtain ⟨ts, hts, hee⟩ := MAx3.I4.ee_rep hL hLaw l (wordP w) (MAx3.R.plusWord_letters_plus w)
  obtain ⟨E, hE⟩ := MAx3.I4.listsum_ptMat hTTp hL hLaw _ hJc (MAx3.I4.Gw P (wordP w))
    (fun Y hY => MAx3.I4.inGw hH w (hfacts Y hY).2.1 (hfacts Y hY).1 (hfacts Y hY).2.2.2) ts hts
  have hpt : ∀ (Y : ℝ) q i i', ptMat P ((frW P l L w).ee (Y : ℂ)) q i i' =
      (ts.map fun t => t.1 (Y : ℂ) * ptMat P t.2 q i i').sum := fun Y q i i' =>
    (congrArg (fun b => ptMat P b q i i') (hee (Y : ℂ))).trans (MAx3.I4.ptMat_listsum ts (Y : ℂ) q i i')
  have hgx : ∀ Y ∈ MAx3.I4.Jbox α β Lb w.length, ∀ q a,
      ‖gL P l L w Y (Xw P l L (ju P j) w) q a‖ * MAx3.I4.Dabs q ^ (w.length + 1) ≤ MAx3.I4.BdF BA BR E a q := by
    intro Y hY q a
    rcases a with ⟨_ | _, i⟩
    · exact hBAb Y hY q i
    · have hR := hBRb Y hY q i
      simp only [if_true] at hR
      exact MAx3.I4.gx_true_bound hL w Y _ q i BA BR E _ (pow_nonneg (MAx3.I4.Dabs_pos hTT q).le _) hR
        (fun i' => hBAb Y hY q i') (fun i' => by rw [hpt]; exact ((hE q i i').1 Y hY).trans (le_abs_self _))
  have hkc : ∀ a : Bool × Iota P w.length, ContinuousOn (MAx3.I4.kap' P l w a.1 a.2) (MAx3.I4.Jbox α β Lb w.length) :=
    fun a Y hY => (MAx3.I4.kap'_cont hH w a.1 a.2 (hfacts Y hY).1 (hfacts Y hY).2.1 (hfacts Y hY).2.2.2).continuousWithinAt
  choose K hK using fun a => hJc.exists_bound_of_continuousOn (hkc a)
  have hσ : ((w.length + 1 : ℕ) : ℝ) ≤ 4 * (Ntot : ℝ) := by
    have : w.length + 1 ≤ Ntot := by omega
    have h2 : ((w.length + 1 : ℕ) : ℝ) ≤ Ntot := by exact_mod_cast this
    nlinarith [(Nat.cast_nonneg Ntot : (0 : ℝ) ≤ Ntot)]
  show ContinuousOn (fun Y : ℝ => ∫ ω, LE.th ε (4 * Ntot) (Gq P ω) *
    LE.sq (baseQ P) (dwW P l (Y :: w)) (gL P l L w Y (Xw P l L (ju P j) w)) ω ∂(mu0 P.r P.TT))
    (MAx3.I4.Jbox α β Lb w.length)
  refine MeasureTheory.continuousOn_of_dominated
    (bound := fun q => ∑ a : Bool × Iota P w.length, |K a| * (ε⁻¹) ^ (w.length + 1) * (MAx3.I4.BdF BA BR E a q) ^ 2)
    ?_ ?_ ?_ ?_
  · intro Y hY
    exact ((MAx3.I4.th_meas ε _).mul (Finset.measurable_sum _ fun a _ => (MAx3.dwW_meas P l (Y :: w) a).mul
      ((MAx3.gL_cont P l L w Y _ a).measurable.norm.pow_const 2))).aestronglyMeasurable
  · intro Y hY
    refine Filter.Eventually.of_forall fun q => ?_
    exact MAx3.I4.dom_bound hTT ε hε hσ K (MAx3.I4.BdF BA BR E) _ (fun a => hK a Y hY) (fun a => hgx Y hY q a)
  · refine integrable_finset_sum _ fun a _ => ?_
    have hBd : MemLp (MAx3.I4.BdF BA BR E a) 2 (mu0 P.r P.TT) := by
      rcases a with ⟨_ | _, i⟩
      · exact hBA i
      · exact (hBR i).add ((MAx3.I4.memLp_finsum _ _ fun i' _ => hBA i').const_mul |E|)
    exact hBd.integrable_sq.const_mul _
  · refine Filter.Eventually.of_forall fun q => ?_
    exact MAx3.I4.cont_integrand hL w _ hkc ts (fun i i' => (hE q i i').2) (fun Y i i' => hpt Y q i i')

end Formalism.FourierDecayAlt.P

end S_I4_I20

section S_L_L1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.L

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet

noncomputable section

variable (P : M.Par)

theorem iter_exp (s : ℝ) : ∀ n : ℕ, iteratedDeriv n (fun u : ℝ => Real.exp (u * s)) = fun u => s ^ n * Real.exp (u * s)
  | 0 => by simp
  | n + 1 => by
    rw [iteratedDeriv_succ, iter_exp s n]
    funext u
    have hd := (((hasDerivAt_id' u).mul_const s).exp).const_mul (s ^ n)
    rw [hd.deriv]; ring

theorem ldq_rpow (s : ℝ) (q : ℕ) (x : ℝ) (hx : 0 < x) : LE.ld q (fun x : ℝ => x ^ s) x = s ^ q * x ^ s := by
  unfold LE.ld
  have h : (fun u : ℝ => (fun x : ℝ => x ^ s) (Real.exp u)) = fun u => Real.exp (u * s) :=
    funext fun u => (Real.exp_mul u s).symm
  rw [h, iter_exp, Real.rpow_def_of_pos hx]

theorem Phiq_rpow (s : ℝ) (q : ℕ) : Phi P (fun x : ℝ => x ^ s) q = ((s : ℂ) ^ q) • G.Gpow P s := by
  apply Subtype.ext; funext x
  show evQ P (Phi P _ q) x = evQ P (((s : ℂ) ^ q) • G.Gpow P s) x
  rw [ev_Phi P (G.smoothLog_rpow s), G.evQ_smul, G.ev_Gpow, ldq_rpow s q _ (Gq_pos P x)]
  push_cast; ring

theorem isJ_group {F : (ℝ → ℝ) → SmQ P.r P.TT} (hF : IsJ P F) :
    ∃ (K : ℕ) (a : ℕ → SmQ P.r P.TT), ∀ φ, LE.SmoothLog φ → F φ = ∑ k ∈ Finset.range (K + 1), Phi P φ k * a k := by
  obtain ⟨n, qs, c, h⟩ := hF
  refine ⟨Finset.univ.sup qs, fun k => ∑ t ∈ Finset.univ.filter (fun t => qs t = k), c t, fun φ hφ => ?_⟩
  rw [h φ hφ]
  have hmaps : ∀ t ∈ (Finset.univ : Finset (Fin n)), qs t ∈ Finset.range (Finset.univ.sup qs + 1) := fun t _ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := qs) (Finset.mem_univ t)))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_filter.1 ht).2]

theorem group_unique (K : ℕ) (a b : ℕ → SmQ P.r P.TT)
    (h : ∀ s : ℝ, ∑ k ∈ Finset.range (K + 1), Phi P (fun x : ℝ => x ^ s) k * a k =
      ∑ k ∈ Finset.range (K + 1), Phi P (fun x : ℝ => x ^ s) k * b k) :
    ∀ k ∈ Finset.range (K + 1), a k = b k := by
  intro k hk
  apply Subtype.ext; funext x

  let pa : Polynomial ℂ := ∑ k ∈ Finset.range (K + 1), Polynomial.C (evQ P (a k) x) * Polynomial.X ^ k
  let pb : Polynomial ℂ := ∑ k ∈ Finset.range (K + 1), Polynomial.C (evQ P (b k) x) * Polynomial.X ^ k
  have hev : ∀ s : ℝ, pa.eval (s : ℂ) = pb.eval (s : ℂ) := by
    intro s
    have hs := congrArg (fun f : SmQ P.r P.TT => evQ P f x) (h s)
    simp only [MAx2.Jet.evQ_sum, MAx2.Jet.evQ_mul, Phiq_rpow, G.evQ_smul, G.ev_Gpow] at hs
    have hG : ((Gq P x ^ s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos (Gq_pos P x) s).ne'
    simp only [pa, pb, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    have e1 : ∀ (c : ℕ → SmQ P.r P.TT), ∑ k ∈ Finset.range (K + 1), (s : ℂ) ^ k * ((Gq P x ^ s : ℝ) : ℂ) * evQ P (c k) x =
        ((Gq P x ^ s : ℝ) : ℂ) * ∑ k ∈ Finset.range (K + 1), evQ P (c k) x * (s : ℂ) ^ k := by
      intro c; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1, e1] at hs
    exact mul_left_cancel₀ hG hs
  have hpab : pa = pb := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℝ) : ℂ))
    · intro m n hmn; simpa using hmn
    · intro n; exact hev n
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff k) hpab
  simp only [pa, pb, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  rw [Finset.sum_ite_eq _ k, Finset.sum_ite_eq _ k, if_pos hk, if_pos hk] at hc
  exact hc

theorem isJ_unique {F F' : (ℝ → ℝ) → SmQ P.r P.TT} (hF : IsJ P F) (hF' : IsJ P F')
    (h : ∀ s : ℝ, F (fun x : ℝ => x ^ s) = F' (fun x : ℝ => x ^ s)) :
    ∀ φ, LE.SmoothLog φ → F φ = F' φ := by
  obtain ⟨K1, a, ha⟩ := isJ_group P hF
  obtain ⟨K2, b, hb⟩ := isJ_group P hF'

  set K := max K1 K2
  have pad : ∀ (K0 : ℕ) (c : ℕ → SmQ P.r P.TT), K0 ≤ K → ∀ φ, ∑ k ∈ Finset.range (K0 + 1), Phi P φ k * c k =
      ∑ k ∈ Finset.range (K + 1), Phi P φ k * (if k ≤ K0 then c k else 0) := by
    intro K0 c hK φ
    rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hK)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (K0 + 1) (K + 1)) (fun k hk => by
      rw [if_neg (by simp [Finset.mem_Ico] at hk; omega), mul_zero]), add_zero]
    exact Finset.sum_congr rfl fun k hk => by rw [if_pos (by simp at hk; omega)]
  have hu := group_unique P K (fun k => if k ≤ K1 then a k else 0) (fun k => if k ≤ K2 then b k else 0) (fun s => by
    rw [← pad K1 a (le_max_left _ _), ← pad K2 b (le_max_right _ _), ← ha _ (G.smoothLog_rpow s),
      ← hb _ (G.smoothLog_rpow s)]
    exact h s)
  intro φ hφ
  rw [ha φ hφ, hb φ hφ, pad K1 a (le_max_left _ _), pad K2 b (le_max_right _ _)]
  exact Finset.sum_congr rfl fun k hk => by rw [hu k hk]

end

end Formalism.FourierDecayAlt.P.MAx3.L

end S_L_L1

section S_PG_PG1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.PG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An

noncomputable section

variable (P : M.Par)

theorem isJ_cm (p : ℕ) (g : SmQ P.r P.TT) : MAx2.Jet.IsJ P (fun ψ => MAx2.Jet.Phi P ψ p * g) :=
  ⟨1, fun _ => p, fun _ => g, fun φ hφ => by simp⟩

theorem Gs_conj_entry (x : A P (DQ P)) (s : ℝ) (π π' : M.Ty P) :
    (G.Gs P (-s) * x * G.Gs P s) π π' =
      (DQ P).fnP (G.GpD P (-s)) (G.GpD P (-s)) * x π π' * (DQ P).fnP (G.GpD P s) (G.GpD P s) := by
  simp only [G.Gs, sc, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem multiplierPair_fst_apply (f g h : SmQ P.r P.TT) : ((DQ P).fnP f g).1 h = f * h := rfl

theorem act_leibniz (x : A P (DQ P)) (hx : x ∈ MAx2.Jet.TS P) (d : ℕ) (c : ℕ → A P (DQ P))
    (hconj : ∀ s : ℝ, G.Gs P (-s) * x * G.Gs P s = ∑ k ∈ Finset.range (d + 1), ((s : ℂ) ^ k) • c k)
    (f : M.Ty P → SmQ P.r P.TT) (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ) (π : M.Ty P) :
    actA P x (fun π' => MAx2.Jet.Phi P φ 0 * f π') π =
      ∑ p ∈ Finset.range (d + 1), MAx2.Jet.Phi P φ p * actA P (c p) f π := by
  refine L.isJ_unique P (F := fun ψ => actA P x (fun π' => MAx2.Jet.Phi P ψ 0 * f π') π)
    (F' := fun ψ => ∑ p ∈ Finset.range (d + 1), MAx2.Jet.Phi P ψ p * actA P (c p) f π) ?_ ?_ ?_ φ hφ
  · show MAx2.Jet.IsJ P (fun ψ => ∑ π', MAx2.R2.Phi P (x π π') (MAx2.Jet.Phi P ψ 0 * f π'))
    exact MAx2.Jet.isJ_sum P _ _ fun π' _ => (hx π π') _ (isJ_cm P 0 (f π'))
  · exact MAx2.Jet.isJ_sum P _ _ fun p _ => isJ_cm P p _
  · intro s
    have hGG : G.Gpow P s * G.Gpow P (-s) = 1 := G.Gpow_mul_neg P s

    have he : ∀ π', G.Gpow P (-s) * MAx2.R2.Phi P (x π π') (G.Gpow P s * f π') =
        ∑ k ∈ Finset.range (d + 1), ((s : ℂ) ^ k) • MAx2.R2.Phi P (c k π π') (f π') := by
      intro π'
      have h1 := congrArg (fun y : A P (DQ P) => MAx2.R2.Phi P (y π π') (f π')) (hconj s)
      simp only [Gs_conj_entry, map_mul, Module.End.mul_apply] at h1
      rw [Matrix.sum_apply] at h1
      simp only [map_sum, Matrix.smul_apply, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] at h1
      exact h1
    show ∑ π', MAx2.R2.Phi P (x π π') (G.Gpow P s * f π') = ∑ p ∈ Finset.range (d + 1),
      MAx2.Jet.Phi P (fun x : ℝ => x ^ s) p * ∑ π', MAx2.R2.Phi P (c p π π') (f π')
    have he2 : ∀ π', MAx2.R2.Phi P (x π π') (G.Gpow P s * f π') =
        G.Gpow P s * ∑ k ∈ Finset.range (d + 1), ((s : ℂ) ^ k) • MAx2.R2.Phi P (c k π π') (f π') := by
      intro π'; rw [← he, ← mul_assoc, hGG, one_mul]
    simp only [he2, L.Phiq_rpow]
    rw [← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

end

end Formalism.FourierDecayAlt.P.MAx3.PG

end S_PG_PG1

section S_PG_PG2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.PG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.G

noncomputable section

section Poly
variable {R : Type} [Ring R] [Algebra ℂ R]

theorem polyIn_mul {f g : ℂ → R} {d₁ d₂ : ℕ} (hf : PolyIn f d₁) (hg : PolyIn g d₂) :
    PolyIn (fun t => f t * g t) (d₁ + d₂) := by
  first | exact UpperTheory.Reformulated.B.Qk18.polyIn_mul .. | (apply UpperTheory.Reformulated.B.Qk18.polyIn_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk18.polyIn_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk18.polyIn_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk18.polyIn_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk18.polyIn_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk18.polyIn_mul R ‹_› ‹_› f g d₁ d₂ hf hg | exact @UpperTheory.Reformulated.B.Qk18.polyIn_mul R ‹_› ‹_› f g d₁ d₂ hf | exact @UpperTheory.Reformulated.B.Qk18.polyIn_mul R ‹_› ‹_› f g d₁ d₂ | exact @UpperTheory.Reformulated.B.Qk18.polyIn_mul R ‹_› ‹_› f g d₁ | exact @UpperTheory.Reformulated.B.Qk18.polyIn_mul R ‹_› ‹_› f g | exact @UpperTheory.Reformulated.B.Qk18.polyIn_mul R ‹_› ‹_› f | exact @UpperTheory.Reformulated.B.Qk18.polyIn_mul R ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qk18.polyIn_mul R ‹_› | exact @UpperTheory.Reformulated.B.Qk18.polyIn_mul R

theorem lagrange {M : Type} [AddCommGroup M] [Module ℂ M] (F : ℂ → M) (K : ℕ) (a : ℕ → M)
    (hF : ∀ t, F t = ∑ k ∈ Finset.range (K + 1), t ^ k • a k) :
    ∃ lam : ℕ → ℕ → ℂ, ∀ k ∈ Finset.range (K + 1), a k = ∑ m ∈ Finset.range (K + 1), lam k m • F m := by
  classical
  let v : Fin (K + 1) → ℂ := fun m => (m : ℂ)
  have hv : Function.Injective v := fun m n h => by
    have : ((m : ℕ) : ℂ) = ((n : ℕ) : ℂ) := h
    exact Fin.ext (by exact_mod_cast this)
  let V := Matrix.vandermonde v
  have hdet : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hv
  have hWV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.2 hdet)
  refine ⟨fun k m => if h : k < K + 1 ∧ m < K + 1 then V⁻¹ ⟨k, h.1⟩ ⟨m, h.2⟩ else 0, fun k hk => ?_⟩
  have hk' : k < K + 1 := Finset.mem_range.1 hk
  rw [← Fin.sum_univ_eq_sum_range (fun m => (if h : k < K + 1 ∧ m < K + 1 then V⁻¹ ⟨k, h.1⟩ ⟨m, h.2⟩ else 0) • F m)]
  simp only [Fin.is_lt, hk', and_self, dite_true]
  have e1 : ∀ m : Fin (K + 1), F m = ∑ k' : Fin (K + 1), V m k' • a k' := by
    intro m
    rw [hF, ← Fin.sum_univ_eq_sum_range (fun k => ((m : ℕ) : ℂ) ^ k • a k)]
    rfl
  simp only [e1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e2 : ∀ k' : Fin (K + 1), ∑ m : Fin (K + 1), (V⁻¹ ⟨k, hk'⟩ m * V m k') • a k' = (V⁻¹ * V) ⟨k, hk'⟩ k' • a k' := by
    intro k'; rw [← Finset.sum_smul, Matrix.mul_apply]
  simp only [e2, hWV, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Poly

theorem Gs_SC {P : M.Par} (s : ℝ) : Gs P s ∈ SC P := sc_memSC P _

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTT hL hLaw

theorem Gs_comm_cl (s : ℝ) {x : A P (DQ P)} (hx : x ∈ Subring.closure (FS L)) : Gs P s * x = x * Gs P s := by
  refine comm_cl L (fun y hy => ?_) hx
  rcases hy with hy | ⟨a, rfl⟩
  · exact (G.fns_comm hTT hL s y hy).symm
  · exact (Algebra.commutes a _).symm

theorem Gs_comm_SB (s : ℝ) {b : A P (DQ P)} (hb : b ∈ I4.SB L) : Gs P s * b = b * Gs P s := by
  induction hb using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with (((hx | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Gs_comm_cl hTT hL hLaw s (memζi L)
      · exact Gs_comm_cl hTT hL hLaw s (memζbi L)
      · exact Gs_comm_cl hTT hL hLaw s (memDD L)
      · exact Gs_comm_cl hTT hL hLaw s (memDbD L)
    · exact (kap_comm_DG P f (sc_memDG P _)).symm
    · dsimp only
      rw [← mul_assoc, Gs_comm_cl hTT hL hLaw s (Subring.mul_mem _ (memDrb L) (memDri L)), mul_assoc,
        (SS_comm_SC P i (Gs_SC s)).symm, mul_assoc]
      simp only [mul_assoc]
    · dsimp only
      rw [starSSn_eq hL hLaw, ← mul_assoc, (SSs_comm_SC i (Gs_SC s)).symm, mul_assoc,
        Gs_comm_cl hTT hL hLaw s (Subring.mul_mem _ (memDr L) (memDrbi L)), mul_assoc]
      simp only [mul_assoc]
  | one => simp
  | mul x y _ _ h1 h2 => rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem conj_word : ∀ H : List (A P (DQ P)), (∀ h ∈ H, h ∈ plusHats L) →
    ∃ Hf : ℂ → List (A P (DQ P)), (∀ t, (Hf t).length = H.length) ∧ (∀ t, ∀ h ∈ Hf t, h ∈ plusHats L) ∧
      (∀ s : ℝ, Gs P (-s) * H.prod * Gs P s = (Hf s).prod) ∧ PolyIn (fun t => (Hf t).prod) (H.length * (P.r + 1))
  | [], _ => ⟨fun _ => [], fun _ => rfl, fun _ h hh => absurd hh List.not_mem_nil,
      fun s => by simp [Gs_neg_mul], by simpa using polyIn_const (1 : A P (DQ P))⟩
  | h :: H, hH => by
    obtain ⟨Hf, h1, h2, h3, h4⟩ := conj_word H (fun x hx => hH x (List.mem_cons_of_mem _ hx))
    have hh : h ∈ plusHats L := hH h List.mem_cons_self
    have key : ∃ hf : ℂ → A P (DQ P), (∀ t, hf t ∈ plusHats L) ∧ (∀ s : ℝ, Gs P (-s) * h * Gs P s = hf s) ∧
        PolyIn hf (P.r + 1) := by
      rcases hh with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨fun t => L.Ahat (y + t), fun t => Or.inl ⟨_, rfl⟩, fun s => (G.conj_hat hTT hL s y).1,
          polyIn_mono (Ahat_poly P L y) (Nat.le_succ _)⟩
      · exact ⟨fun t => L.R0 (y + t), fun t => Or.inr ⟨_, rfl⟩, fun s => (G.conj_hat hTT hL s y).2,
          raising_operator_polynomial P L y⟩
    obtain ⟨hf, k1, k2, k3⟩ := key
    refine ⟨fun t => hf t :: Hf t, fun t => by simp [h1], fun t x hx => ?_, fun s => ?_, ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact k1 t
      · exact h2 t x hx
    · rw [List.prod_cons, List.prod_cons, ← k2 s, ← h3 s]
      have : Gs P s * Gs P (-s) = 1 := Gs_mul_neg P s
      calc Gs P (-s) * (h * H.prod) * Gs P s = Gs P (-s) * h * (Gs P s * Gs P (-s)) * H.prod * Gs P s := by
            rw [this, mul_one]; simp only [mul_assoc]
        _ = _ := by simp only [mul_assoc]
    · have := polyIn_mul k3 h4
      rw [List.length_cons, show (H.length + 1) * (P.r + 1) = P.r + 1 + H.length * (P.r + 1) by ring]
      exact this

end

end Formalism.FourierDecayAlt.P.MAx3.PG

end S_PG_PG2

section S_PG_PG3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.PG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.G

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r}

def CP (L : LevelData (A P (DQ P)) P.r) (d ℓ : ℕ) (x : A P (DQ P)) : Prop :=
  ∃ (K : ℕ) (c : ℕ → A P (DQ P)), (∀ k, c k ∈ NormalFormTwo L (I4.SB L) d ℓ) ∧
    ∀ s : ℝ, Gs P (-s) * x * Gs P s = ∑ k ∈ Finset.range (K + 1), ((s : ℂ) ^ k) • c k

theorem pad {M : Type} [AddCommMonoid M] [Module ℂ M] (K K' : ℕ) (hK : K ≤ K') (c : ℕ → M) (t : ℂ) :
    ∑ k ∈ Finset.range (K + 1), t ^ k • c k =
      ∑ k ∈ Finset.range (K' + 1), t ^ k • (if k ≤ K then c k else 0) := by
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hK)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (K + 1) (K' + 1)) (fun k hk => by
    rw [if_neg (by simp [Finset.mem_Ico] at hk; omega), smul_zero]), add_zero]
  exact Finset.sum_congr rfl fun k hk => by rw [if_pos (by simp at hk; omega)]

theorem CP_zero (d ℓ : ℕ) : CP L d ℓ 0 :=
  ⟨0, fun _ => 0, fun _ => Submodule.zero_mem _, fun s => by simp⟩

theorem CP_add {d ℓ : ℕ} {x y : A P (DQ P)} (hx : CP L d ℓ x) (hy : CP L d ℓ y) : CP L d ℓ (x + y) := by
  obtain ⟨K1, c1, h1, e1⟩ := hx
  obtain ⟨K2, c2, h2, e2⟩ := hy
  refine ⟨K1 + K2, fun k => (if k ≤ K1 then c1 k else 0) + (if k ≤ K2 then c2 k else 0), fun k => ?_, fun s => ?_⟩
  · refine Submodule.add_mem _ ?_ ?_
    · split_ifs; exacts [h1 k, Submodule.zero_mem _]
    · split_ifs; exacts [h2 k, Submodule.zero_mem _]
  · rw [mul_add, add_mul, e1, e2, pad K1 (K1 + K2) (by omega) c1, pad K2 (K1 + K2) (by omega) c2,
      ← Finset.sum_add_distrib]
    simp only [smul_add]

theorem CP_smul {d ℓ : ℕ} (a : ℂ) {x : A P (DQ P)} (hx : CP L d ℓ x) : CP L d ℓ (a • x) := by
  obtain ⟨K, c, h, e⟩ := hx
  refine ⟨K, fun k => a • c k, fun k => Submodule.smul_mem _ _ (h k), fun s => ?_⟩
  rw [mul_smul_comm, smul_mul_assoc, e s, Finset.smul_sum]
  simp only [smul_comm a]

variable (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTT hL hLaw

theorem CP_term {d ℓ : ℕ} {b : A P (DQ P)} (hb : b ∈ I4.SB L) {i i' : ℕ} {H : List (A P (DQ P))}
    (h1 : i + i' = d) (h2 : H.length = ℓ) (h3 : ∀ h ∈ H, h ∈ plusHats L) : CP L d ℓ (tm L b i i' H) := by
  obtain ⟨Hf, k1, k2, k3, k4⟩ := conj_word hTT hL hLaw H h3
  have hpoly := polyIn_const_mul (b * (L.Di ^ i * L.Dbi ^ i')) k4
  obtain ⟨a, ha⟩ := hpoly
  obtain ⟨lam, hlam⟩ := lagrange (fun t => b * (L.Di ^ i * L.Dbi ^ i') * (Hf t).prod) _ a ha
  have hF : ∀ t, b * (L.Di ^ i * L.Dbi ^ i') * (Hf t).prod ∈ NormalFormTwo L (I4.SB L) d ℓ := fun t =>
    mem2 hb h1 (by rw [k1, h2]) (k2 t)
  refine ⟨H.length * (P.r + 1), fun k => if k ∈ Finset.range (H.length * (P.r + 1) + 1) then a k else 0,
    fun k => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs with hk
    · rw [hlam k hk]
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hF _)
    · exact Submodule.zero_mem _
  · have hD : Gs P (-s) * (b * (L.Di ^ i * L.Dbi ^ i')) = b * (L.Di ^ i * L.Dbi ^ i') * Gs P (-s) := by
      rw [← mul_assoc, Gs_comm_SB hTT hL hLaw (-s) hb, mul_assoc, mul_assoc,
        Gs_comm_cl hTT hL hLaw (-s) (Subring.mul_mem _ (memPow L (memDi L) i) (memPow L (memDbi L) i'))]
    have e1 : Gs P (-s) * tm L b i i' H * Gs P s = b * (L.Di ^ i * L.Dbi ^ i') * (Gs P (-s) * H.prod * Gs P s) := by
      unfold tm
      rw [← mul_assoc (Gs P (-s)), hD]; simp only [mul_assoc]
    rw [e1, k3 s]
    have hs := ha (s : ℂ)
    dsimp only at hs ⊢
    rw [hs]
    exact Finset.sum_congr rfl fun k hk => by rw [if_pos hk]

theorem polynomial_control_of_normal_form {d ℓ : ℕ} {x : A P (DQ P)} (hx : x ∈ NormalFormTwo L (I4.SB L) d ℓ) : CP L d ℓ x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
    exact CP_term hTT hL hLaw hb h1 h2 h3
  | zero => exact CP_zero d ℓ
  | add x y _ _ h1 h2 => exact CP_add h1 h2
  | smul a x _ h => exact CP_smul a h

end

end Formalism.FourierDecayAlt.P.MAx3.PG

end S_PG_PG3

section S_PG_PG4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.PG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.G

noncomputable section

variable {P : M.Par}

def chi (c : LE.Cut) (ε : ℝ) : ℝ → ℝ := fun x => c.sc ε 1 x

theorem smoothLog_chi (c : LE.Cut) (ε : ℝ) : LE.SmoothLog (chi c ε) := by
  unfold LE.SmoothLog chi LE.Cut.sc
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => Real.exp u / ε) :=
    Real.contDiff_exp.div_const ε
  exact (c.smooth.comp h1).pow 1

theorem log_derivative_zero (φ : ℝ → ℝ) (x : ℝ) (hx : 0 < x) : LE.ld 0 φ x = φ x := by
  simp [LE.ld, Real.exp_log hx]

theorem chiJ_eq (j : M.Ty P → SmQ P.r P.TT) (c : LE.Cut) (ε : ℝ) :
    chiJ P j c ε = fun π => MAx2.Jet.Phi P (chi c ε) 0 * j π := by
  funext π
  have hm : (fun q : Qp P.r P.TT => (c.sc ε 1 (Gq P q) : ℂ) * (j π).1 q) ∈ smSub P.r P.TT := by
    have h := (MAx2.Jet.Phi P (chi c ε) 0 * j π).2
    have e : ((MAx2.Jet.Phi P (chi c ε) 0 * j π : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) =
        fun q => (c.sc ε 1 (Gq P q) : ℂ) * (j π).1 q := by
      funext q
      show evQ P (MAx2.Jet.Phi P (chi c ε) 0 * j π) q = _
      rw [MAx2.Jet.evQ_mul, MAx2.Jet.ev_Phi P (smoothLog_chi c ε), log_derivative_zero _ _ (Gq_pos P q)]
      rfl
    rw [← e]; exact h
  show toSm P _ = _
  rw [G.toSm_of_mem P hm]
  apply Subtype.ext
  funext q
  show (c.sc ε 1 (Gq P q) : ℂ) * (j π).1 q = evQ P (MAx2.Jet.Phi P (chi c ε) 0 * j π) q
  rw [MAx2.Jet.evQ_mul, MAx2.Jet.ev_Phi P (smoothLog_chi c ε), log_derivative_zero _ _ (Gq_pos P q)]
  rfl

variable {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL

theorem starSS_mem (i : ℕ) : star (SS P (DQ P) i) ∈ MAx2.Jet.TS P := fun π π' => by
  rw [Matrix.star_apply]
  simp only [SS, Matrix.of_apply]
  split_ifs
  · rw [← algebraMap_star_comm]; exact Subalgebra.algebraMap_mem _ _
  · rw [star_zero]; exact Subalgebra.zero_mem _

theorem hatsTS {h : A P (DQ P)} (hh : h ∈ plusHats L) : h ∈ MAx2.Jet.TS P := by
  obtain ⟨-, -, -, -, -, -, -, -, hzb, -, hg, hgi, hn, -⟩ := MAx2.Jet.lev_mem P hL
  obtain ⟨d1, d2, d3, d4⟩ := MAx2.Jet.Dr_mem P hL
  rcases hh with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact mul_mem d1 ((MAx2.Jet.Tprod_mem P hL y).1 0 0)
  · have hT := (MAx2.Jet.Tprod_mem P hL y).1
    exact mul_mem (mul_mem d2 hg) (add_mem (mul_mem (sub_mem (neg_mem hn)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hzb hgi))) (hT 0 0)) (hT 1 0))

include hLaw

theorem DTS : L.D ∈ MAx2.Jet.TS P ∧ L.Di ∈ MAx2.Jet.TS P ∧ L.Db ∈ MAx2.Jet.TS P ∧ L.Dbi ∈ MAx2.Jet.TS P := by
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, -⟩ := MAx2.Jet.lev_mem P hL
  obtain ⟨d1, d2, d3, d4⟩ := MAx2.Jet.Dr_mem P hL
  exact ⟨mul_mem d1 hz, mul_mem hzi d3, mul_mem d2 hzb, mul_mem hzbi d4⟩

theorem SB_TS {b : A P (DQ P)} (hb : b ∈ I4.SB L) : b ∈ MAx2.Jet.TS P := by
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, -⟩ := MAx2.Jet.lev_mem P hL
  obtain ⟨d1, d2, d3, d4⟩ := MAx2.Jet.Dr_mem P hL
  obtain ⟨D1, D2, D3, D4⟩ := DTS hL hLaw
  induction hb using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with (((hx | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hzi
      · exact hzbi
      · exact mul_mem D1 D4
      · exact mul_mem D3 D2
    · exact MAx2.Jet.kap_mem P f
    · exact mul_mem (mul_mem d2 d3) (MAx2.Jet.SS_mem P i)
    · dsimp only
      rw [starSSn_eq hL hLaw]
      exact mul_mem (starSS_mem hL i) (mul_mem d1 d4)
  | one => exact Subalgebra.one_mem _
  | mul x y _ _ h1 h2 => exact mul_mem h1 h2

theorem normal_form_two_jet {d ℓ : ℕ} {x : A P (DQ P)} (hx : x ∈ NormalFormTwo L (I4.SB L) d ℓ) : x ∈ MAx2.Jet.TS P := by
  obtain ⟨-, D2, -, D4⟩ := DTS hL hLaw
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
    exact mul_mem (mul_mem (SB_TS hL hLaw hb) (mul_mem (pow_mem D2 i) (pow_mem D4 i')))
      (Subalgebra.list_prod_mem _ fun h hh => hatsTS hL (h3 h hh))
  | zero => exact Subalgebra.zero_mem _
  | add x y _ _ h1 h2 => exact add_mem h1 h2
  | smul a x _ h => exact Subalgebra.smul_mem _ h a

end

end Formalism.FourierDecayAlt.P.MAx3.PG

end S_PG_PG4

section S_PG_PG5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.PG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.G

noncomputable section

theorem list_sq_le {α : Type} (T : List α) (f : α → ℝ) :
    (T.map f).sum ^ 2 ≤ T.length * (T.map fun t => f t ^ 2).sum := by
  have e1 : (T.map f).sum = ∑ i : Fin T.length, f (T.get i) := by
    rw [← List.sum_ofFn]; congr 1; apply List.ext_get <;> simp
  have e2 : (T.map fun t => f t ^ 2).sum = ∑ i : Fin T.length, f (T.get i) ^ 2 := by
    rw [← List.sum_ofFn]; congr 1; apply List.ext_get <;> simp
  rw [e1, e2]
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin T.length))) (f := fun i => f (T.get i))
  simpa using this

theorem list_sum_nonneg {α : Type} (T : List α) (f : α → ℝ) (hf : ∀ t, 0 ≤ f t) : 0 ≤ (T.map f).sum :=
  List.sum_nonneg fun x hx => by obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx; exact hf t

theorem flat_sum {α β : Type} (l : List α) (T : α → List β) (f : β → ℝ) :
    ((l.flatMap T).map f).sum = (l.map fun a => ((T a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem flat_le {α β : Type} (l : List α) (T : α → List β) (f : β → ℝ) (hf : ∀ t, 0 ≤ f t) (a : α) (ha : a ∈ l) :
    ((T a).map f).sum ≤ ((l.flatMap T).map f).sum := by
  rw [flat_sum]
  exact List.single_le_sum (fun x hx => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx; exact list_sum_nonneg _ _ hf) _ (List.mem_map_of_mem ha)

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem chi_expand (j : M.Ty P → SmQ P.r P.TT) (c : LE.Cut) (ε : ℝ) {N : ℕ} {x : A P (DQ P)}
    (hx : x ∈ NormalFormTwo L (I4.SB L) N N) : ∃ (K : ℕ) (cc : ℕ → A P (DQ P)), (∀ k, cc k ∈ NormalFormTwo L (I4.SB L) N N) ∧
      ∀ π q, evQ P (actA P x (chiJ P j c ε) π) q =
        ∑ p ∈ Finset.range (K + 1), ((LE.ld p (chi c ε) (Gq P q) : ℝ) : ℂ) * evQ P (actA P (cc p) j π) q := by
  obtain ⟨K, cc, hcc, hconj⟩ := polynomial_control_of_normal_form hTTp.le hL hLaw hx
  refine ⟨K, cc, hcc, fun π q => ?_⟩
  rw [chiJ_eq, act_leibniz P x (normal_form_two_jet hL hLaw hx) K cc hconj j (chi c ε) (smoothLog_chi c ε) π,
    MAx2.Jet.evQ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MAx2.Jet.evQ_mul, MAx2.Jet.ev_Phi P (smoothLog_chi c ε)]

theorem chi_bound (j : M.Ty P → SmQ P.r P.TT) (c : LE.Cut) (ε : ℝ) (hε : 0 < ε) {N : ℕ} {x : A P (DQ P)}
    (hx : x ∈ NormalFormTwo L (I4.SB L) N N) :
    ∃ (C : ℝ) (T : List (List (A P (DQ P)) × M.Ty P)), 0 ≤ C ∧ (∀ t ∈ T, t.1.length = N ∧ ∀ h ∈ t.1, h ∈ plusHats L) ∧
      ∀ π q, Wq P q ^ N * ‖evQ P (actA P x (chiJ P j c ε) π) q‖ ^ 2 ≤
        C * (T.map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖ ^ 2).sum := by
  obtain ⟨K, cc, hcc, hexp⟩ := chi_expand hTTp hL hLaw j c ε hx
  have hB : ∀ p, I4.NFB L j N N (cc p) := fun p => I4.normal_form_two_bounded hTTp hL hLaw j (hcc p)
  choose Cp Tp hCp hTp hbp using hB
  have hχ : ∀ p : ℕ, ∃ C : ℝ, ∀ ε x : ℝ, 0 < ε → 0 < x →
      |LE.ld p (c.sc ε 1) x| ≤ C ∧ (x < ε / 2 → LE.ld p (c.sc ε 1) x = 0) ∧
        (ε < x → LE.ld p (c.sc ε 1) x = if p = 0 then 1 else 0) :=
    fun p => Formalism.FourierDecayAlt.P.cutoff_bound c 1 p le_rfl
  choose Cχ hCχ using hχ
  set T := (List.range (K + 1)).flatMap Tp with hT
  set C := (2 / ε) ^ N * ((K + 1 : ℕ) : ℝ) * ∑ p ∈ Finset.range (K + 1), (|Cχ p| * Cp p) ^ 2 * (Tp p).length
  have hC : 0 ≤ C := by positivity
  refine ⟨C, T, hC, fun t ht => ?_, fun π q => ?_⟩
  · obtain ⟨p, _, ht⟩ := List.mem_flatMap.1 ht; exact hTp p t ht
  set S := (T.map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖ ^ 2).sum
  have hS : 0 ≤ S := list_sum_nonneg _ _ fun t => sq_nonneg _
  have hG := Gq_pos P q
  by_cases hq : Gq P q < ε / 2
  · have h0 : evQ P (actA P x (chiJ P j c ε) π) q = 0 := by
      rw [hexp]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [show LE.ld p (chi c ε) (Gq P q) = 0 from (hCχ p ε (Gq P q) hε hG).2.1 hq]
      simp
    rw [h0, norm_zero]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact mul_nonneg hC hS
  · push Not at hq
    set X := evQ P (actA P x (chiJ P j c ε) π) q
    set S1 : ℕ → ℝ := fun p => ((Tp p).map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖).sum
    set S2 : ℕ → ℝ := fun p => ((Tp p).map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖ ^ 2).sum
    have hDq := I4.Dabs_pos hTTp.le q

    have hX : ‖X‖ * I4.Dabs q ^ N ≤ ∑ p ∈ Finset.range (K + 1), |Cχ p| * Cp p * S1 p := by
      rw [show X = _ from hexp π q]
      calc ‖∑ p ∈ Finset.range (K + 1), ((LE.ld p (chi c ε) (Gq P q) : ℝ) : ℂ) * evQ P (actA P (cc p) j π) q‖ *
            I4.Dabs q ^ N ≤ (∑ p ∈ Finset.range (K + 1),
              ‖((LE.ld p (chi c ε) (Gq P q) : ℝ) : ℂ) * evQ P (actA P (cc p) j π) q‖) * I4.Dabs q ^ N :=
            mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hDq.le _)
        _ = ∑ p ∈ Finset.range (K + 1), |LE.ld p (chi c ε) (Gq P q)| *
              (‖evQ P (actA P (cc p) j π) q‖ * I4.Dabs q ^ N) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun p _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; ring
        _ ≤ ∑ p ∈ Finset.range (K + 1), |Cχ p| * Cp p * S1 p := Finset.sum_le_sum fun p _ => by
            have h1 := (hCχ p ε (Gq P q) hε hG).1
            have h2 := hbp p π q
            have h3 : |LE.ld p (chi c ε) (Gq P q)| ≤ |Cχ p| := h1.trans (le_abs_self _)
            calc |LE.ld p (chi c ε) (Gq P q)| * (‖evQ P (actA P (cc p) j π) q‖ * I4.Dabs q ^ N)
                ≤ |Cχ p| * (Cp p * S1 p) := mul_le_mul h3 h2 (by positivity) (abs_nonneg _)
              _ = _ := by ring
    have hW : Wq P q ^ N = (I4.Dabs q ^ N) ^ 2 / Gq P q ^ N := by
      rw [← pow_mul, mul_comm N 2, pow_mul, I4.Dabs_sq hTTp.le, mul_pow]
      field_simp
    have hGN : 1 / Gq P q ^ N ≤ (2 / ε) ^ N := by
      rw [one_div, ← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (by rw [inv_le_comm₀ hG (by positivity), inv_div]; linarith) N
    have hsq : (∑ p ∈ Finset.range (K + 1), |Cχ p| * Cp p * S1 p) ^ 2 ≤
        ((K + 1 : ℕ) : ℝ) * ∑ p ∈ Finset.range (K + 1), (|Cχ p| * Cp p) ^ 2 * (Tp p).length * S := by
      have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range (K + 1)) (f := fun p => |Cχ p| * Cp p * S1 p)
      rw [Finset.card_range] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) (by positivity))
      have h2 : S1 p ^ 2 ≤ (Tp p).length * S2 p := list_sq_le _ _
      have h3 : S2 p ≤ S := flat_le (List.range (K + 1)) Tp _ (fun t => sq_nonneg _) p
        (List.mem_range.2 (Finset.mem_range.1 hp))
      calc (|Cχ p| * Cp p * S1 p) ^ 2 = (|Cχ p| * Cp p) ^ 2 * S1 p ^ 2 := by ring
        _ ≤ (|Cχ p| * Cp p) ^ 2 * ((Tp p).length * S) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            exact h2.trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _))
        _ = _ := by ring
    have hXD : (‖X‖ * I4.Dabs q ^ N) ^ 2 ≤ (∑ p ∈ Finset.range (K + 1), |Cχ p| * Cp p * S1 p) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hX 2
    calc Wq P q ^ N * ‖X‖ ^ 2 = (‖X‖ * I4.Dabs q ^ N) ^ 2 * (1 / Gq P q ^ N) := by rw [hW]; field_simp
      _ ≤ (∑ p ∈ Finset.range (K + 1), |Cχ p| * Cp p * S1 p) ^ 2 * (2 / ε) ^ N :=
          mul_le_mul hXD hGN (by positivity) (by positivity)
      _ ≤ ((K + 1 : ℕ) : ℝ) * (∑ p ∈ Finset.range (K + 1), (|Cχ p| * Cp p) ^ 2 * (Tp p).length * S) * (2 / ε) ^ N :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = C * S := by
          simp only [C]
          rw [← Finset.sum_mul]; ring

end

end Formalism.FourierDecayAlt.P.MAx3.PG

end S_PG_PG5

section S_PG_PG6

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.PG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.G Formalism.FourierDecayAlt.Wd
  Formalism.FourierDecayAlt.Fr MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem isFn_congr {x : A P (DQ P)} {g g' : Qp P.r P.TT → ℂ} (h : I4.IsFn x g) (e : ∀ q, g q = g' q) :
    I4.IsFn x g' := by
  obtain ⟨F, Fb, rfl, hF⟩ := h
  exact ⟨F, Fb, rfl, fun q => (hF q).trans (e q)⟩

theorem act_isFn {x : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (h : I4.IsFn x g) (f : M.Ty P → SmQ P.r P.TT) (π q) :
    evQ P (actA P x f π) q = g q * evQ P (f π) q := by
  obtain ⟨F, Fb, rfl, hF⟩ := h
  rw [MAx2.R2.act_sc]
  show evQ P (F * f π) q = _
  rw [MAx2.Jet.evQ_mul, hF]

variable {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem fn_GGi : I4.IsFn L.GGi (fun q => ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ)⁻¹) := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
  refine ⟨_, _, rfl, fun q => ?_⟩
  show ((Ring.inverse (MAx1.An.ggQ P.r P.TT) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q =
    ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ)⁻¹
  rw [MAx2.Jet.ev_inverse P (MAx1.An.ggQ P.r P.TT) hLaw.unit_gg q]
  rw [MAx1.An.gg_apply q, MAx1.An.coordE_vz,
    MAx1.An.coordE_vzb, Complex.mul_conj]
  push_cast; ring

theorem weight_function_pair : I4.IsFn (L.ζ * L.ζb * L.GGi) (fun q => ((Wq P q : ℝ) : ℂ)) := by
  refine isFn_congr (I4.isFn_mul (I4.isFn_mul (I4.fn_ζ hTTp.le hL) (I4.fn_ζb hTTp.le hL)) (fn_GGi hTTp hL hLaw))
    fun q => ?_
  rw [Complex.mul_conj, Wq]
  push_cast
  rw [div_eq_mul_inv]

theorem d_g_sum {N : ℕ} (cs : Ix (Fin N) → M.Ty P → ℂ) (g : Ix (Fin N) → A P (DQ P)) (e : Ix (Fin N)) :
    ∑ e', ((wt L : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) ^ N * Matrix.diagonal (fun e => kap P (DQ P) (cs e))) e e' * g e' =
      (L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) (cs e) * g e := by
  have hw : (wt L : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) ^ N = Matrix.diagonal (fun _ => (L.ζ * L.ζb * L.GGi) ^ N) := by
    unfold wt io
    rw [← map_pow]; rfl
  rw [hw, Matrix.diagonal_mul_diagonal, Finset.sum_eq_single e (fun b _ hb => by
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul]) (by simp), Matrix.diagonal_apply_eq]

theorem act_dg {N : ℕ} (f : M.Ty P → SmQ P.r P.TT) (c : M.Ty P → ℂ) (g : A P (DQ P)) (π q) :
    evQ P (actA P ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) c * g) f π) q =
      ((Wq P q : ℝ) : ℂ) ^ N * c π * evQ P (actA P g f π) q := by
  rw [MAx2.R2.act_mul, MAx2.R2.act_mul, act_isFn (I4.isFn_pow (weight_function_pair hTTp hL hLaw) N), MAx2.R2.act_kap]
  rw [show evQ P (c π • actA P g f π) q = c π * evQ P (actA P g f π) q from rfl]
  ring

end

end Formalism.FourierDecayAlt.P.MAx3.PG

end S_PG_PG6

section S_PG_PG7

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.PG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.G MeasureTheory

noncomputable section

variable {P : M.Par}

theorem integrable_list_sum {α : Type} {μ : Measure (Qp P.r P.TT)} (T : List α) (f : α → Qp P.r P.TT → ℝ)
    (h : ∀ t ∈ T, Integrable (f t) μ) : Integrable (fun q => (T.map fun t => f t q).sum) μ := by
  induction T with
  | nil => simp
  | cons a T ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun t ht => h t (by simp [ht]))

theorem plus_sub_hat {L : LevelData (A P (DQ P)) P.r} {h : A P (DQ P)} (hh : h ∈ plusHats L) : h ∈ hatSet P L :=
  Or.inl (Or.inl hh)

variable {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem term_integrable (j : M.Ty P → SmQ P.r P.TT) (c : LE.Cut) (ε : ℝ) (hε : 0 < ε) {m N : ℕ}
    (hD : JDecay P L j m) (hNm : N ≤ m) {x : A P (DQ P)} (hx : x ∈ NormalFormTwo L (I4.SB L) N N) (c0 : ℝ) (π : M.Ty P) :
    Integrable (fun q => Wq P q ^ N * c0 * ‖evQ P (actA P x (chiJ P j c ε) π) q‖ ^ 2) (mu0 P.r P.TT) := by
  obtain ⟨C, T, hC, hT, hb⟩ := chi_bound hTTp hL hLaw j c ε hε hx
  have hg : Integrable (fun q => |c0| * C * (T.map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖ ^ 2).sum)
      (mu0 P.r P.TT) := by
    refine Integrable.const_mul (integrable_list_sum T _ fun t ht => ?_) _
    exact hD t.1 (by rw [(hT t ht).1]; exact hNm) (fun a ha => plus_sub_hat ((hT t ht).2 a ha)) t.2
  refine Integrable.mono' hg ?_ (Filter.Eventually.of_forall fun q => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    exact (((MAx3.Wq_meas P).pow_const N).mul_const c0).mul
      ((MAx3.evQ_cont P _).measurable.norm.pow_const 2)
  · have hW : 0 ≤ Wq P q ^ N := pow_nonneg (MAx3.Wq_pos P hTTp.le q).le N
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hW, abs_pow, abs_norm]
    calc Wq P q ^ N * |c0| * ‖evQ P (actA P x (chiJ P j c ε) π) q‖ ^ 2
        = |c0| * (Wq P q ^ N * ‖evQ P (actA P x (chiJ P j c ε) π) q‖ ^ 2) := by ring
      _ ≤ |c0| * (C * (T.map fun t => ‖evQ P (actA P t.1.prod j t.2) q‖ ^ 2).sum) :=
          mul_le_mul_of_nonneg_left (hb π q) (abs_nonneg _)
      _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.MAx3.PG

end S_PG_PG7

section S_PG_PG8

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.PG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.G Formalism.FourierDecayAlt.Wd
  Formalism.FourierDecayAlt.Fr MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem sum_iota_real {n : ℕ} (F : Ix (Fin n) → M.Ty P → ℝ) :
    ∑ i : Iota P n, F (ixOf P n i).1 (ixOf P n i).2 = ∑ e, ∑ π, F e π := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (iotaEquiv P n) _ _ fun i => rfl

theorem sum_cast {N : ℕ} (Y : Fin N → ℝ) (F : Iota P (List.ofFn Y).length → ℝ) :
    ∑ i : Iota P N, F (cast (iota_len P N Y) i) = ∑ i, F i :=
  Fintype.sum_equiv (Equiv.cast (iota_len P N Y)) _ _ fun _ => rfl

theorem ju_chiJ (j : M.Ty P → SmQ P.r P.TT) (c : LE.Cut) (ε : ℝ) :
    ju P (chiJ P j c ε) = LE.mulF (baseQ P) (c.sc ε 1) (ju P j) := by
  funext ω a
  show evQ P (chiJ P j c ε a) ω = _
  rw [chiJ_eq]
  show evQ P (MAx2.Jet.Phi P (chi c ε) 0 * j a) ω = _
  rw [MAx2.Jet.evQ_mul, MAx2.Jet.ev_Phi P (smoothLog_chi c ε), log_derivative_zero _ _ (Gq_pos P ω)]
  rfl

theorem inner_real_of_pointwise (f : Qp P.r P.TT → ℝ) (g h : SmQ P.r P.TT) (hgh : ∀ q, evQ P g q * conj (evQ P h q) = (f q : ℂ)) :
    ip0 g h = ((∫ q, f q ∂mu0 P.r P.TT : ℝ) : ℂ) := by
  unfold ip0
  rw [show ((∫ q, f q ∂mu0 P.r P.TT : ℝ) : ℂ) = ∫ q, ((f q : ℝ) : ℂ) ∂mu0 P.r P.TT from integral_ofReal.symm]
  exact integral_congr_ae (Filter.Eventually.of_forall fun q => hgh q)

variable {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem lhs_term {n : ℕ} (cs0 : Ix (Fin n) → M.Ty P → ℂ) (hcs : ∀ e π, (cs0 e π).im = 0)
    (g : Ix (Fin n) → A P (DQ P)) (f : M.Ty P → SmQ P.r P.TT) (e : Ix (Fin n)) (π : M.Ty P) :
    ip0 (actA P (∑ e', ((wt L : SlopeTestRemainingChoices (Fin n) (A P (DQ P))) ^ n *
        Matrix.diagonal (fun e => kap P (DQ P) (cs0 e))) e e' * g e') f π) (actA P (g e) f π) =
      ((∫ q, Wq P q ^ n * (cs0 e π).re * ‖evQ P (actA P (g e) f π) q‖ ^ 2 ∂mu0 P.r P.TT : ℝ) : ℂ) := by
  rw [d_g_sum hTTp hL hLaw cs0 g e]
  refine inner_real_of_pointwise _ _ _ fun q => ?_
  rw [act_dg hTTp hL hLaw, mul_assoc, Complex.mul_conj, ← Complex.ofReal_pow]
  have hc : cs0 e π = ((cs0 e π).re : ℂ) := Complex.ext (by simp) (by simp [hcs e π])
  rw [hc, Complex.normSq_eq_norm_sq]
  push_cast
  simp only [Complex.ofReal_re]

end

end Formalism.FourierDecayAlt.P.MAx3.PG

end S_PG_PG8

section S_PG_PG9

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory Formalism.FourierDecayAlt.P.MAx3.PG

theorem theorem_P_weight : Formalism.FourierDecayAlt.MA.ThmPGw := by
  intro P l L j lam α β Lb c Ntot hH N Y hN hB ε hε
  obtain ⟨⟨hOK, hl1, hlk, hML, hu, hu', hαβ, hcut⟩, hD, hA, hE, hN1, -⟩ := id hH
  have hTTp : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hLaw := analytic_laws P.r P.TT hTTp.le
  have hcw : M.CutWord P l (wordP (List.ofFn Y)) := MAx3.F.cutWord_of hH c (List.ofFn Y) hB (by simpa using hN)
  obtain ⟨L', hL', -, -, hFC⟩ := model_frame_analytic P hOK l hl1 hlk
  have hLL := MAx3.F.level_unique P (DQ P) L' L hL' hML
  subst hLL
  have hFCw := hFC (Fin (List.ofFn Y).length) (wordP (List.ofFn Y)) hcw
  have hS := sites_admissible P (DQ P) hLaw l
  have hFr : ∀ w' : List ℝ, M.CutWord P l (wordP w') → IsFrame L' (ofWord L' (startM P (DQ P) l) (wordP w')) :=
    fun w' h => (hFC _ _ h).1
  set cs0 : Ix (Fin (List.ofFn Y).length) → M.Ty P → ℂ := fun e π => cs (M.x0 P l π) (M.qC P) (wordP (List.ofFn Y)) e
    with hcs0
  have hcs : ∀ e π, (cs0 e π).im = 0 := fun e π => (hFCw.2.2.2 e π).2
  have hXw := MAx3.F.Xw_eq hML hS hFr (chiJ P j c ε) (List.ofFn Y) hcw
  obtain ⟨𝒳, h𝒳, hX𝒳⟩ := MAx3.I4.Xw_rep hML hLaw l (chiJ P j c ε) (List.ofFn Y)
  have hlen : (List.ofFn Y).length = N := List.length_ofFn

  have hcomp : ∀ (e : Ix (Fin (List.ofFn Y).length)) (π : M.Ty P) (q : Qp P.r P.TT),
      Xw P l L' (ju P (chiJ P j c ε)) (List.ofFn Y) q (iotaOf P _ e π) =
        evQ P (actA P (gRing P l L' Y e) (chiJ P j c ε) π) q := by
    intro e π q
    have := hXw (iotaOf P _ e π) q
    rw [MAx3.G.ixOf_iotaOf] at this
    exact this
  have hcomp' : ∀ (e : Ix (Fin (List.ofFn Y).length)) (π : M.Ty P) (q : Qp P.r P.TT),
      evQ P (actA P (𝒳 e) (chiJ P j c ε) π) q = evQ P (actA P (gRing P l L' Y e) (chiJ P j c ε) π) q := by
    intro e π q
    have := hX𝒳 q (iotaOf P _ e π)
    rw [MAx3.G.ixOf_iotaOf] at this
    rw [← this, hcomp]

  have hint : ∀ e π, Integrable (fun q => Wq P q ^ (List.ofFn Y).length * (cs0 e π).re *
      ‖evQ P (actA P (gRing P l L' Y e) (chiJ P j c ε) π) q‖ ^ 2) (mu0 P.r P.TT) := by
    intro e π
    have h := term_integrable hTTp hML hLaw j c ε hε hD (N := (List.ofFn Y).length) (by omega) (h𝒳 e) (cs0 e π).re π
    have e2 : ∀ q, Wq P q ^ (List.ofFn Y).length * (cs0 e π).re * ‖evQ P (actA P (𝒳 e) (chiJ P j c ε) π) q‖ ^ 2 =
        Wq P q ^ (List.ofFn Y).length * (cs0 e π).re *
          ‖evQ P (actA P (gRing P l L' Y e) (chiJ P j c ε) π) q‖ ^ 2 := fun q => by rw [hcomp' e π q]
    exact h.congr (Filter.Eventually.of_forall e2)

  have hLHS : formDF P l L' j c Y ε = ∑ e, ∑ π, ∫ q, Wq P q ^ (List.ofFn Y).length * (cs0 e π).re *
      ‖evQ P (actA P (gRing P l L' Y e) (chiJ P j c ε) π) q‖ ^ 2 ∂mu0 P.r P.TT := by
    unfold formDF
    have hd : dRing P l L' Y = (wt L' : SlopeTestRemainingChoices (Fin (List.ofFn Y).length) (A P (DQ P))) ^ (List.ofFn Y).length *
        Matrix.diagonal (fun e => kap P (DQ P) (cs0 e)) := by
      unfold dRing frW
      rw [hFCw.2.2.1]
    rw [hd, Complex.re_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold ipA
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [lhs_term hTTp hML hLaw cs0 hcs (gRing P l L' Y) (chiJ P j c ε) e π, Complex.ofReal_re]

  have hRHS : ∀ ω : Qp P.r P.TT, LE.sq (baseQ P) (((sysQ P l L' j lam α β Lb c Ntot).fam N).dw Y)
      (((sysQ P l L' j lam α β Lb c Ntot).fam N).gw Y
        (LE.mulF (baseQ P) (c.sc ε 1) ((sysQ P l L' j lam α β Lb c Ntot).fam N).u)) ω =
      ∑ e, ∑ π, Wq P ω ^ (List.ofFn Y).length * (cs0 e π).re *
        ‖evQ P (actA P (gRing P l L' Y e) (chiJ P j c ε) π) ω‖ ^ 2 := by
    intro ω
    unfold LE.sq
    show ∑ i : Iota P N, (Wq P ω ^ N * (cs (M.x0 P l (ixOf P _ (cast (iota_len P N Y) i)).2) (M.qC P)
        (wordP (List.ofFn Y)) (ixOf P _ (cast (iota_len P N Y) i)).1).re) *
        ‖Xw P l L' (LE.mulF (baseQ P) (c.sc ε 1) (ju P j)) (List.ofFn Y) ω (cast (iota_len P N Y) i)‖ ^ 2 = _
    rw [← ju_chiJ, sum_cast Y (fun i' => (Wq P ω ^ N * (cs (M.x0 P l (ixOf P _ i').2) (M.qC P)
        (wordP (List.ofFn Y)) (ixOf P _ i').1).re) * ‖Xw P l L' (ju P (chiJ P j c ε)) (List.ofFn Y) ω i'‖ ^ 2)]
    rw [← sum_iota_real (P := P) (fun e π => Wq P ω ^ (List.ofFn Y).length * (cs0 e π).re *
        ‖evQ P (actA P (gRing P l L' Y e) (chiJ P j c ε) π) ω‖ ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hW : Wq P ω ^ N = Wq P ω ^ (List.ofFn Y).length := by rw [hlen]
    rw [← hcomp, MAx3.G.iotaOf_ixOf, hW]
  calc formDF P l L' j c Y ε = _ := hLHS
    _ = ∫ ω, ∑ e, ∑ π, Wq P ω ^ (List.ofFn Y).length * (cs0 e π).re *
          ‖evQ P (actA P (gRing P l L' Y e) (chiJ P j c ε) π) ω‖ ^ 2 ∂mu0 P.r P.TT := by
        rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _ fun π _ => hint e π)]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [integral_finsetSum _ fun π _ => hint e π]
    _ = _ := (integral_congr_ae (Filter.Eventually.of_forall hRHS)).symm

end Formalism.FourierDecayAlt.P

end S_PG_PG9

section S_Z_Z1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.I4 Matrix

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {l : ℕ} (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT) (hS : SitesOK (K := ℂ) (startM P (DQ P) l).QQ (sites P (DQ P)))
  (hFr : ∀ w : List ℝ, M.CutWord P l (wordP w) → IsFrame L (ofWord L (startM P (DQ P) l) (wordP w)))
include hL hLaw hS hFr

theorem gRw_nil (e : Ix (Fin ([] : List ℝ).length)) : F.gRw P (DQ P) L l [] e = 1 := by
  have hu : ∀ e'', uw (sites P (DQ P)) (wordP []) e'' = 1 := fun e'' => by
    rw [F.uw_prod P (DQ P) l hS [] ⟨List.nodup_nil, fun a ha => absurd ha List.not_mem_nil, List.Pairwise.nil⟩]
    rfl
  unfold F.gRw
  simp only [hu, mul_one]
  refine (Finset.sum_eq_single_of_mem e (Finset.mem_univ e) ?_).trans (Matrix.one_apply_eq e)
  intro b _ hb
  exact absurd (funext fun k => Fin.elim0 k) hb

theorem gRw_NF : ∀ w : List ℝ, M.CutWord P l (wordP w) → ∀ e, F.gRw P (DQ P) L l w e ∈ NormalFormTwo L (SB L) w.length w.length
  | [], _, e => by rw [gRw_nil hL hLaw hS hFr e]; exact one_mem_normal_form_two (hyp_model hL hLaw)
  | Y :: w, hcw, E => by
    have hcw' := F.cut_tail Y w hcw
    have IH := gRw_NF w hcw'
    have hG := F.good_of_cut (Y :: w) hcw
    have hG' := F.good_of_cut w hcw'
    have hNL := Formalism.FourierDecayAlt.P.new_vector_letter_plus (A P (DQ P)) (Fin w.length) P.r L
      (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) ((hFr w hcw').ee_fn _)
    have hE : (ofWord L (startM P (DQ P) l) (wordP w)).ee ((Y : ℝ) : ℂ) ∈ UB L (Fin w.length) :=
      (frame_memB hL hLaw l (wordP w)).1 _
    have hsnoc : Fin.snoc (α := fun _ => Fin 2) (Fin.init E) (E (Fin.last _)) = E := Fin.snoc_init_self E
    rw [← hsnoc, ← F.key_alg hL hS Y w hG hG' (E (Fin.last _)) (Fin.init E)]
    have hcol : (F.abelian₂ L (ofWord L (startM P (DQ P) l) (wordP w)) ((Y : ℝ) : ℂ) *ᵥ
        ![io (L.Ar ((Y : ℝ) : ℂ)), io (L.Br ((Y : ℝ) : ℂ))]) = ![io (L.Di * L.Ahat ((Y : ℝ) : ℂ)),
        io (L.Dbi * L.R0 ((Y : ℝ) : ℂ)) + (ofWord L (startM P (DQ P) l) (wordP w)).ee ((Y : ℝ) : ℂ) *
          io (L.Di * L.Ahat ((Y : ℝ) : ℂ))] := hNL
    rw [hcol]
    have h01 : ∀ c : Fin 2, c ≠ 1 → c = 0 := by decide
    by_cases hc : E (Fin.last w.length) = 1
    · rw [hc]
      exact letter_vec_NF hL hLaw ((Y : ℝ) : ℂ) ((Y : ℝ) : ℂ) _ hE _ IH true (Fin.init E)
    · rw [h01 _ hc]
      exact letter_vec_NF hL hLaw ((Y : ℝ) : ℂ) ((Y : ℝ) : ℂ) _ hE _ IH false (Fin.init E)

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z1

section S_Z_Z2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.I4 Formalism.FourierDecayAlt.P.MAx1.An
open scoped ComplexConjugate

noncomputable section

variable {P : M.Par}

def IsFn2 (x : A P (DQ P)) (g gb : Qp P.r P.TT → ℂ) : Prop :=
  ∃ F Fb : SmQ P.r P.TT, x = sc P (DQ P) ((DQ P).fnP F Fb) ∧ (∀ q, evQ P F q = g q) ∧ ∀ q, evQ P Fb q = gb q

theorem isFn2_mul {x y : A P (DQ P)} {g gb h hb : Qp P.r P.TT → ℂ} (hx : IsFn2 x g gb) (hy : IsFn2 y h hb) :
    IsFn2 (x * y) (fun q => g q * h q) (fun q => gb q * hb q) := by
  obtain ⟨F, Fb, rfl, hF, hFb⟩ := hx
  obtain ⟨H, Hb, rfl, hH, hHb⟩ := hy
  refine ⟨F * H, Fb * Hb, ?_, fun q => ?_, fun q => ?_⟩
  · rw [Formalism.FourierDecayAlt.P.MAx3.G.sc_mul P]; exact congrArg (sc P (DQ P)) (MAx1.multiplierPair_mul (DQ P) F Fb H Hb)
  · rw [MAx2.Jet.evQ_mul, hF, hH]
  · rw [MAx2.Jet.evQ_mul, hFb, hHb]

theorem isFn2_congr {x : A P (DQ P)} {g gb g' gb' : Qp P.r P.TT → ℂ} (h : IsFn2 x g gb) (e1 : ∀ q, g q = g' q)
    (e2 : ∀ q, gb q = gb' q) : IsFn2 x g' gb' := by
  obtain ⟨F, Fb, rfl, hF, hFb⟩ := h
  exact ⟨F, Fb, rfl, fun q => (hF q).trans (e1 q), fun q => (hFb q).trans (e2 q)⟩

theorem isFn2_eq {x y : A P (DQ P)} {g gb : Qp P.r P.TT → ℂ} (hx : IsFn2 x g gb) (hy : IsFn2 y g gb) : x = y := by
  obtain ⟨F, Fb, rfl, hF, hFb⟩ := hx
  obtain ⟨H, Hb, rfl, hH, hHb⟩ := hy
  have e1 : F = H := Subtype.ext (funext fun q => (hF q).trans (hH q).symm)
  have e2 : Fb = Hb := Subtype.ext (funext fun q => (hFb q).trans (hHb q).symm)
  rw [e1, e2]

theorem isFn2_prod {n : ℕ} (f : Fin n → A P (DQ P)) (g gb : Fin n → Qp P.r P.TT → ℂ)
    (h : ∀ i, IsFn2 (f i) (g i) (gb i)) :
    IsFn2 (List.ofFn f).prod (fun q => ∏ i, g i q) (fun q => ∏ i, gb i q) := by
  induction n with
  | zero =>
    refine ⟨(1 : (DQ P).R), (1 : (DQ P).R), ?_, fun q => by simp; rfl, fun q => by simp; rfl⟩
    simp only [List.ofFn_zero, List.prod_nil]
    rw [MAx1.multiplierPair_one]
    show (1 : A P (DQ P)) = Matrix.scalar (M.Ty P) 1
    rw [map_one]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine isFn2_congr (isFn2_mul (h 0) (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => gb i.succ) fun i => h _))
      (fun q => by rw [Fin.prod_univ_succ]) (fun q => by rw [Fin.prod_univ_succ])

variable (hTT : 0 < P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTT hL hLaw

theorem inverse_coordinate_function (l : Fin P.r) : IsFn2 (L.ci l) (fun q => (q.1.1 l)⁻¹) (fun q => (conj (q.1.1 l))⁻¹) := by
  rw [hL.2.2.2.1]
  exact ⟨_, _, rfl, fun q => by rw [ev_invQ hTT.le, coordE_vc], fun q => by rw [ev_invQ hTT.le, coordE_vcb]⟩
theorem inverse_conj_coordinate_function (l : Fin P.r) : IsFn2 (L.cbi l) (fun q => (conj (q.1.1 l))⁻¹) (fun q => (q.1.1 l)⁻¹) := by
  rw [hL.2.2.2.2.2.1]
  exact ⟨_, _, rfl, fun q => by rw [ev_invQ hTT.le, coordE_vcb], fun q => by rw [ev_invQ hTT.le, coordE_vc]⟩
theorem zeta_function_pair : IsFn2 L.ζ (fun q => q.1.2) (fun q => conj q.1.2) := by
  rw [hL.2.2.2.2.2.2.1]; exact ⟨_, _, rfl, fun q => coordE_vz q.1, fun q => coordE_vzb q.1⟩
theorem conj_zeta_function_pair : IsFn2 L.ζb (fun q => conj q.1.2) (fun q => q.1.2) := by
  rw [hL.2.2.2.2.2.2.2.2.1]; exact ⟨_, _, rfl, fun q => coordE_vzb q.1, fun q => coordE_vz q.1⟩
theorem inverse_zeta_function_pair : IsFn2 L.ζi (fun q => (q.1.2)⁻¹) (fun q => (conj q.1.2)⁻¹) := by
  rw [hL.2.2.2.2.2.2.2.1]
  exact ⟨_, _, rfl, fun q => by rw [ev_invQ hTT.le, coordE_vz], fun q => by rw [ev_invQ hTT.le, coordE_vzb]⟩
theorem inverse_conj_zeta_function_pair : IsFn2 L.ζbi (fun q => (conj q.1.2)⁻¹) (fun q => (q.1.2)⁻¹) := by
  rw [hL.2.2.2.2.2.2.2.2.2.1]
  exact ⟨_, _, rfl, fun q => by rw [ev_invQ hTT.le, coordE_vzb], fun q => by rw [ev_invQ hTT.le, coordE_vz]⟩
theorem inverse_gamma_function_pair : IsFn2 L.GGi (fun q => ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ)⁻¹)
    (fun q => ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ)⁻¹) := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
  have hv : ∀ q, evQ P (Ring.inverse (MAx1.An.ggQ P.r P.TT)) q = ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ)⁻¹ := by
    intro q
    show ((Ring.inverse (MAx1.An.ggQ P.r P.TT) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = _
    rw [MAx2.Jet.ev_inverse P (MAx1.An.ggQ P.r P.TT) hLaw.unit_gg q]
    rw [MAx1.An.gg_apply q, MAx1.An.coordE_vz, MAx1.An.coordE_vzb, Complex.mul_conj]
    push_cast; ring
  exact ⟨_, _, rfl, hv, hv⟩

theorem WDD : L.ζ * L.ζb * L.GGi * (L.Di * L.Dbi) = G.Gs P (-1) := by
  have hW := isFn2_mul (isFn2_mul (zeta_function_pair hTT hL hLaw) (conj_zeta_function_pair hTT hL hLaw)) (inverse_gamma_function_pair hTT hL hLaw)
  have hDi := isFn2_mul (inverse_zeta_function_pair hTT hL hLaw) (isFn2_prod L.ci _ _ (inverse_coordinate_function hTT hL hLaw))
  have hDbi := isFn2_mul (inverse_conj_zeta_function_pair hTT hL hLaw) (isFn2_prod L.cbi _ _ (inverse_conj_coordinate_function hTT hL hLaw))
  have h := isFn2_mul hW (isFn2_mul hDi hDbi)
  have hG : IsFn2 (G.Gs P (-1)) (fun q => ((Gq P q ^ (-1 : ℝ) : ℝ) : ℂ)) (fun q => ((Gq P q ^ (-1 : ℝ) : ℝ) : ℂ)) :=
    ⟨_, _, rfl, fun q => G.ev_Gpow P (-1) q, fun q => G.ev_Gpow P (-1) q⟩
  have key : ∀ (a ab p pb n : ℂ), a ≠ 0 → ab ≠ 0 → p ≠ 0 → pb ≠ 0 → n ≠ 0 →
      a * ab * n⁻¹ * ((a⁻¹ * p⁻¹) * (ab⁻¹ * pb⁻¹)) = (p * pb * n)⁻¹ := by
    intro a ab p pb n ha hab hp hpb hn; field_simp
  have hGv : ∀ q : Qp P.r P.TT, ((Gq P q ^ (-1 : ℝ) : ℝ) : ℂ) =
      ((∏ l, q.1.1 l) * (∏ l, conj (q.1.1 l)) * ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ))⁻¹ := by
    intro q
    rw [Real.rpow_neg_one, Gq, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    congr 2
    exact Finset.prod_congr rfl fun l _ => (Complex.mul_conj (q.1.1 l)).symm
  have hne : ∀ q : Qp P.r P.TT, q.1.2 ≠ 0 ∧ conj q.1.2 ≠ 0 ∧ (∏ l, q.1.1 l) ≠ 0 ∧ (∏ l, conj (q.1.1 l)) ≠ 0 ∧
      ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ) ≠ 0 := by
    intro q
    have hz : q.1.2 ≠ 0 := I4.ζ_ne hTT.le q
    have hN : Complex.normSq q.1.2 - P.TT ≠ 0 := by
      have := Gq_pos P q; unfold Gq at this
      intro h0; rw [h0, mul_zero] at this; exact lt_irrefl _ this
    refine ⟨hz, (map_ne_zero _).2 hz, Finset.prod_ne_zero_iff.2 fun l _ => I4.c_ne q l,
      Finset.prod_ne_zero_iff.2 fun l _ => (map_ne_zero _).2 (I4.c_ne q l), by exact_mod_cast hN⟩
  refine isFn2_eq (isFn2_congr h (fun q => ?_) (fun q => ?_)) hG
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hne q
    rw [hGv, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
    exact key _ _ _ _ _ h1 h2 h3 h4 h5
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hne q
    rw [hGv, Finset.prod_inv_distrib, Finset.prod_inv_distrib, mul_comm (∏ l, q.1.1 l)]
    exact key _ _ _ _ _ h2 h1 h4 h3 h5

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z2

section S_Z_Z3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.I4 Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

section Abs
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem Dpow_conv (i i' : ℕ) : L.Di ^ i * L.Dbi ^ i' = (L.Db * L.Di) ^ i * L.Dbi ^ (i + i') := by
  have h := congrArg Subtype.val (show (e L _ (memDi L)) ^ i * (e L _ (memDbi L)) ^ i' =
      (e L _ (memDb L) * e L _ (memDi L)) ^ i * (e L _ (memDbi L)) ^ (i + i') by
    rw [mul_pow, pow_add, ← mul_assoc, mul_comm ((e L _ (memDb L)) ^ i), mul_assoc ((e L _ (memDi L)) ^ i),
      ← mul_pow (e L _ (memDb L)), show e L _ (memDb L) * e L _ (memDbi L) = 1 from Subtype.ext (Db_Dbi L), one_pow,
      mul_one])
  simpa [e] using h

theorem tm_conv (b : A) (i i' : ℕ) (H : List A) :
    tm L b i i' H = (b * (L.Db * L.Di) ^ i) * L.Dbi ^ (i + i') * H.prod := by
  unfold tm; rw [Dpow_conv]; simp only [mul_assoc]

end Abs

variable {P : M.Par}

def NFD (L : LevelData (A P (DQ P)) P.r) (N : ℕ) : Submodule ℂ (A P (DQ P)) :=
  Submodule.span ℂ {x | ∃ (b : A P (DQ P)) (H : List (A P (DQ P))), b ∈ SB L ∧ (∀ h ∈ H, h ∈ plusHats L) ∧
    H.length = N ∧ x = b * L.Dbi ^ N * H.prod}

variable {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem normal_form_two_le_degree (N : ℕ) : NormalFormTwo L (SB L) N N ≤ NFD L N := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩
  rw [tm_conv, h1]
  have hDD : L.Db * L.Di ∈ SB L := Submonoid.subset_closure (Or.inl (Or.inl (Or.inl (by simp))))
  exact Submodule.subset_span ⟨_, H, Submonoid.mul_mem _ hb (Submonoid.pow_mem _ hDD i), h3, h2, rfl⟩

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z3

section S_L_L2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.L

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet

noncomputable section

variable (P : M.Par)

def Fq (φ : ℝ → ℝ) (q : ℕ) : (DQ P).Pr := (DQ P).fnP (Phi P φ q) (Phi P φ q)

theorem psnd_mul (x y : (DQ P).Pr) : (x * y).2.unop = y.2.unop * x.2.unop := rfl
theorem psnd_add (x y : (DQ P).Pr) : (x + y).2.unop = x.2.unop + y.2.unop := rfl
theorem psnd_sum {ι : Type} (s : Finset ι) (x : ι → (DQ P).Pr) : (∑ t ∈ s, x t).2.unop = ∑ t ∈ s, (x t).2.unop := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, psnd_add, ih, Finset.sum_insert ha]
theorem psnd_smul (z : ℂ) (x : (DQ P).Pr) : (z • x).2.unop = (starRingEnd ℂ z) • x.2.unop := by
  rw [Algebra.smul_def, psnd_mul]
  show x.2.unop * (algebraMap ℂ (DQ P).Op (starRingEnd ℂ z)) = _
  rw [← Algebra.commutes, Algebra.smul_def]
theorem pfst_smul' (z : ℂ) (x : (DQ P).Pr) : (z • x).1 = z • x.1 := G.pfst_smul P z x
theorem multiplierPair_fst (f g : SmQ P.r P.TT) : ((DQ P).fnP f g).1 = (DQ P).mulOp f := rfl
theorem multiplierPair_snd (f g : SmQ P.r P.TT) : ((DQ P).fnP f g).2.unop = (DQ P).mulOp g := rfl
theorem mulOp_apply (f g : SmQ P.r P.TT) : (DQ P).mulOp f g = f * g := rfl

def asS (f : (DQ P).R) : SmQ P.r P.TT := f

theorem isJ_const_mul (p : ℕ) (f : SmQ P.r P.TT) : IsJ P (fun ψ => Phi P ψ p * f) :=
  ⟨1, fun _ => p, fun _ => f, fun φ hφ => by simp⟩

theorem Phi0_rpow (s : ℝ) : Phi P (fun x : ℝ => x ^ s) 0 = G.Gpow P s := rfl

theorem real_pow_conj (σ s : ℝ) (k : ℕ) : starRingEnd ℂ (((σ * s : ℝ) : ℂ) ^ k) = ((σ * s : ℝ) : ℂ) ^ k := by
  rw [map_pow, Complex.conj_ofReal]

theorem fst_leib (x : (DQ P).Pr) (c : ℕ → (DQ P).Pr) (d : ℕ) (σ : ℝ) (hx1 : x.1 ∈ okSub P)
    (hconj : ∀ s : ℝ, (DQ P).fnP (G.Gpow P (-s)) (G.Gpow P (-s)) * x * (DQ P).fnP (G.Gpow P s) (G.Gpow P s) =
      ∑ k ∈ Finset.range (d + 1), (((σ * s : ℝ) : ℂ) ^ k) • c k)
    (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ) (f : SmQ P.r P.TT) :
    x.1 (Phi P φ 0 * f) = ∑ p ∈ Finset.range (d + 1), Phi P φ p * (((σ : ℂ) ^ p) • asS P ((c p).1 f)) := by
  have hGG : ∀ s, G.Gpow P s * G.Gpow P (-s) = 1 := G.Gpow_mul_neg P
  refine isJ_unique P (F := fun ψ => x.1 (Phi P ψ 0 * f))
    (F' := fun ψ => ∑ p ∈ Finset.range (d + 1), Phi P ψ p * (((σ : ℂ) ^ p) • asS P ((c p).1 f)))
    (hx1 _ (isJ_const_mul P 0 f)) (isJ_sum P _ _ fun p _ => isJ_const_mul P p _) (fun s => ?_) φ hφ
  have h1 : G.Gpow P (-s) * asS P (x.1 (G.Gpow P s * f)) =
      ∑ k ∈ Finset.range (d + 1), (((σ * s : ℝ) : ℂ) ^ k) • asS P ((c k).1 f) := by
    have := congrArg (fun y : (DQ P).Pr => asS P (y.1 f)) (hconj s)
    simp only [asS, G.pfst_mul, multiplierPair_fst, G.pfst_sum, pfst_smul', G.op_mul_apply, G.op_sum_apply] at this
    exact this
  show asS P (x.1 (G.Gpow P s * f)) = _
  rw [show asS P (x.1 (G.Gpow P s * f)) = G.Gpow P s * (G.Gpow P (-s) * asS P (x.1 (G.Gpow P s * f))) by
    rw [← mul_assoc, hGG, one_mul], h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Phiq_rpow]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1; push_cast; ring

theorem snd_leib (x : (DQ P).Pr) (c : ℕ → (DQ P).Pr) (d : ℕ) (σ : ℝ) (hc2 : ∀ k, (c k).2.unop ∈ okSub P)
    (hconj : ∀ s : ℝ, (DQ P).fnP (G.Gpow P (-s)) (G.Gpow P (-s)) * x * (DQ P).fnP (G.Gpow P s) (G.Gpow P s) =
      ∑ k ∈ Finset.range (d + 1), (((σ * s : ℝ) : ℂ) ^ k) • c k)
    (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ) (f : SmQ P.r P.TT) :
    Phi P φ 0 * asS P (x.2.unop f) = ∑ p ∈ Finset.range (d + 1), ((σ : ℂ) ^ p) • (c p).2.unop (Phi P φ p * f) := by
  have hGG : ∀ s, G.Gpow P s * G.Gpow P (-s) = 1 := G.Gpow_mul_neg P
  refine isJ_unique P (F := fun ψ => Phi P ψ 0 * asS P (x.2.unop f))
    (F' := fun ψ => ∑ p ∈ Finset.range (d + 1), ((σ : ℂ) ^ p) • (c p).2.unop (Phi P ψ p * f))
    (isJ_const_mul P 0 _) (isJ_sum P _ _ fun p _ => isJ_smul P _ (hc2 p _ (isJ_const_mul P p f))) (fun s => ?_) φ hφ
  have h1 : G.Gpow P s * asS P (x.2.unop f) =
      ∑ k ∈ Finset.range (d + 1), (((σ * s : ℝ) : ℂ) ^ k) • asS P ((c k).2.unop (G.Gpow P s * f)) := by
    have := congrArg (fun y : (DQ P).Pr => asS P (y.2.unop (G.Gpow P s * f))) (hconj s)
    simp only [asS, psnd_mul, multiplierPair_snd, psnd_sum, psnd_smul, real_pow_conj, G.op_mul_apply, G.op_sum_apply,
      mulOp_apply, LinearMap.smul_apply] at this
    rw [← mul_assoc, mul_comm (G.Gpow P (-s)), hGG, one_mul] at this
    exact this
  show G.Gpow P s * asS P (x.2.unop f) = _
  rw [h1]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : (c p).2.unop ((((s : ℂ) ^ p) • G.Gpow P s) * f) = ((s : ℂ) ^ p) • (c p).2.unop (G.Gpow P s * f) := by
    rw [smul_mul_assoc]; exact ((c p).2.unop).map_smul _ _
  rw [Phiq_rpow, e, smul_smul]
  simp only [asS]
  congr 1; push_cast; ring

end

end Formalism.FourierDecayAlt.P.MAx3.L

end S_L_L2

section S_L_L3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.L

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet

noncomputable section

theorem polyIn_coeff_span {R : Type} [AddCommGroup R] [Module ℂ R] (f : ℂ → R) (d : ℕ) (a : ℕ → R)
    (ha : ∀ t, f t = ∑ k ∈ Finset.range (d + 1), t ^ k • a k) :
    ∀ k ∈ Finset.range (d + 1), a k ∈ Submodule.span ℂ (Set.range fun n : Fin (d + 1) => f n) := by
  intro k hk
  set V : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.vandermonde (fun n : Fin (d + 1) => ((n : ℕ) : ℂ))
  have hV : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    intro m n h; exact Fin.ext (by simpa using h)
  set W := V⁻¹
  have hWV : W * V = 1 := Matrix.nonsing_inv_mul V hV
  have hf : ∀ n : Fin (d + 1), f n = ∑ j : Fin (d + 1), V n j • a j := by
    intro n
    rw [ha, Finset.sum_range (fun j => ((n : ℕ) : ℂ) ^ j • a j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [V, Matrix.vandermonde_apply]
  set kk : Fin (d + 1) := ⟨k, Finset.mem_range.1 hk⟩ with hkk
  have key : a k = ∑ n : Fin (d + 1), W kk n • f n := by
    simp_rw [hf, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have : ∀ j : Fin (d + 1), (∑ n, W kk n * V n j) = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) kk j := by
      intro j; rw [← hWV, Matrix.mul_apply]
    simp_rw [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    try rfl
  rw [key]
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

variable (P : M.Par)

theorem pr_leibniz (x : (DQ P).Pr) (c : ℕ → (DQ P).Pr) (d : ℕ) (σ : ℝ)
    (hx1 : x.1 ∈ okSub P) (hc2 : ∀ k, (c k).2.unop ∈ okSub P)
    (hconj : ∀ s : ℝ, (DQ P).fnP (G.Gpow P (-s)) (G.Gpow P (-s)) * x * (DQ P).fnP (G.Gpow P s) (G.Gpow P s) =
      ∑ k ∈ Finset.range (d + 1), (((σ * s : ℝ) : ℂ) ^ k) • c k)
    (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ) :
    x * Fq P φ 0 = ∑ p ∈ Finset.range (d + 1), Fq P φ p * (((σ : ℂ) ^ p) • c p) := by
  refine Prod.ext ?_ (MulOpposite.unop_injective ?_)
  · apply LinearMap.ext; intro f
    refine (fst_leib P x c d σ hx1 hconj φ hφ (asS P f)).trans ?_
    rw [G.pfst_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun p _ => rfl
  · apply LinearMap.ext; intro f
    have := snd_leib P x c d σ hc2 hconj φ hφ (asS P f)
    have term : ∀ p, (Fq P φ p * (((σ : ℂ) ^ p) • c p)).2.unop f =
        ((σ : ℂ) ^ p) • (c p).2.unop (Phi P φ p * asS P f) := by
      intro p; rw [psnd_mul, psnd_smul, map_pow, Complex.conj_ofReal]; rfl
    refine this.trans ?_
    rw [psnd_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun p _ => (term p).symm

theorem mat_leibniz (X : ℂ → A P (DQ P)) (y : ℂ) (σ : ℝ) (d : ℕ) (a : ℕ → A P (DQ P))
    (hpoly : ∀ t, X (y + t) = ∑ k ∈ Finset.range (d + 1), t ^ k • a k)
    (hconj : ∀ s : ℝ, G.Gs P (-s) * X y * G.Gs P s = X (y + ((σ * s : ℝ) : ℂ)))
    (hmem1 : ∀ π π', (X y π π').1 ∈ okSub P) (hmem2 : ∀ k π π', (a k π π').2.unop ∈ okSub P)
    (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ) :
    X y * sc P (DQ P) (Fq P φ 0) = ∑ p ∈ Finset.range (d + 1), sc P (DQ P) (Fq P φ p) * (((σ : ℂ) ^ p) • a p) := by
  ext π π'
  have hx := pr_leibniz P (X y π π') (fun k => a k π π') d σ (hmem1 π π') (fun k => hmem2 k π π') (fun s => by
    have h := congrArg (fun M : A P (DQ P) => M π π') (hconj s)
    simp only [hpoly] at h
    simpa [G.Gs, sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sum_apply,
      Matrix.smul_apply, G.GpD, mul_assoc] using h) φ hφ
  simp only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.sum_apply, Matrix.diagonal_mul, Matrix.smul_apply]
  exact hx

end

end Formalism.FourierDecayAlt.P.MAx3.L

end S_L_L3

section S_L_L4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.L

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.G

noncomputable section

variable (P : M.Par)

def prSub2 : Subalgebra ℂ (DQ P).Pr where
  carrier := {a | a.2.unop ∈ okSub P}
  mul_mem' {a b} ha hb := by show b.2.unop * a.2.unop ∈ okSub P; exact mul_mem hb ha
  add_mem' {a b} ha hb := by show a.2.unop + b.2.unop ∈ okSub P; exact add_mem ha hb
  algebraMap_mem' z := Subalgebra.algebraMap_mem (okSub P) (starRingEnd ℂ z)

theorem generators_sub_jet : (DQ P).gens P.TT ⊆ prSub2 P := by
  intro a ha
  simp only [DAlg.gens, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with ((((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | h)
  · exact mulOp_mem P _
  · exact mulOp_mem P _
  · exact mulOp_mem P _
  · exact mulOp_mem P _
  · exact neg_mem (euler_mem P _)
  · exact neg_mem (euler_mem P _)
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact mulOp_mem P _
    · exact neg_mem (mul_mem (mulOp_mem P _) (euler_mem P _))
    · exact neg_mem (mul_mem (mulOp_mem P _) (euler_mem P _))

abbrev JetMatrixAlgebra : Subalgebra ℂ (A P (DQ P)) := matSub (prSub P ⊓ prSub2 P) (M.Ty P)

section Lev
variable {P} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hL

theorem level_mem_jet_algebra : (∀ l, L.p l ∈ JetMatrixAlgebra P) ∧ (∀ l, L.pb l ∈ JetMatrixAlgebra P) ∧ (∀ l, L.c l ∈ JetMatrixAlgebra P) ∧ (∀ l, L.ci l ∈ JetMatrixAlgebra P) ∧
    (∀ l, L.cb l ∈ JetMatrixAlgebra P) ∧ (∀ l, L.cbi l ∈ JetMatrixAlgebra P) ∧ L.ζ ∈ JetMatrixAlgebra P ∧ L.ζi ∈ JetMatrixAlgebra P ∧ L.ζb ∈ JetMatrixAlgebra P ∧ L.ζbi ∈ JetMatrixAlgebra P ∧
    L.GG ∈ JetMatrixAlgebra P ∧ L.GGi ∈ JetMatrixAlgebra P ∧ L.nab ∈ JetMatrixAlgebra P ∧ L.nabs ∈ JetMatrixAlgebra P := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  have gm2 : ∀ a ∈ (DQ P).gens P.TT, a ∈ prSub P ⊓ prSub2 P := fun a ha => ⟨gens_sub P ha, generators_sub_jet P ha⟩
  have gm : ∀ a ∈ (DQ P).gens P.TT, sc P (DQ P) a ∈ JetMatrixAlgebra P := fun a ha => scalar_mem _ _ (gm2 a ha)
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]; exact gm _ (by simp [DAlg.gens])
  · rw [hpb]; exact gm _ (by simp [DAlg.gens])
  · rw [hc]; exact gm _ (by simp [DAlg.gens])
  · rw [hci]; exact gm _ (by simp [DAlg.gens])
  · rw [hcb]; exact gm _ (by simp [DAlg.gens])
  · rw [hcbi]; exact gm _ (by simp [DAlg.gens])
  · rw [hz]; exact gm _ (by simp [DAlg.gens])
  · rw [hzi]; exact gm _ (by simp [DAlg.gens])
  · rw [hzb]; exact gm _ (by simp [DAlg.gens])
  · rw [hzbi]; exact gm _ (by simp [DAlg.gens])
  · rw [hg]; exact gm _ (by simp [DAlg.gens])
  · rw [hgi]; exact gm _ (by simp [DAlg.gens])
  · rw [hn]
    refine diag_mem _ _ fun π => add_mem (gm2 _ (by simp [DAlg.gens])) (Subalgebra.smul_mem _
      (mul_mem (gm2 _ (by simp [DAlg.gens])) (gm2 _ (by simp [DAlg.gens]))) _)
  · rw [hns]
    refine diag_mem _ _ fun π => add_mem (neg_mem (gm2 _ (by simp [DAlg.gens]))) (Subalgebra.smul_mem _
      (mul_mem (gm2 _ (by simp [DAlg.gens])) (gm2 _ (by simp [DAlg.gens]))) _)

theorem hats_mem_jet_algebra (Y : ℂ) : L.Ahat Y ∈ JetMatrixAlgebra P ∧ L.R0 Y ∈ JetMatrixAlgebra P ∧ L.Ahatv Y ∈ JetMatrixAlgebra P ∧ L.R0v Y ∈ JetMatrixAlgebra P := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns⟩ := level_mem_jet_algebra hL
  have hDr : L.Dr ∈ JetMatrixAlgebra P := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hc l
  have hDrb : L.Drb ∈ JetMatrixAlgebra P := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hcb l
  have hT : L.Tprod Y ∈ matSub (JetMatrixAlgebra P) (Fin 2) := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hx)
    exact matrix_two_mem_sub _ _ _ _ _ (add_mem (Subalgebra.algebraMap_mem _ _) (hp l)) (neg_mem (hc l)) (hci l)
      (Subalgebra.zero_mem _)
  have hTv : L.Tvprod Y ∈ matSub (JetMatrixAlgebra P) (Fin 2) := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hx)
    exact matrix_two_mem_sub _ _ _ _ _ (sub_mem (Subalgebra.algebraMap_mem _ _) (hpb l)) (neg_mem (hcb l)) (hcbi l)
      (Subalgebra.zero_mem _)
  refine ⟨mul_mem hDr (hT 0 0), mul_mem (mul_mem hDrb hg) (add_mem (mul_mem (sub_mem (neg_mem hn)
    (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hzb hgi))) (hT 0 0)) (hT 1 0)),
    mul_mem hDrb (hTv 0 0), mul_mem (mul_mem hDr hg) (add_mem (mul_mem (sub_mem (neg_mem hns)
    (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hz hgi))) (hTv 0 0)) (hTv 1 0))⟩

end Lev

end

end Formalism.FourierDecayAlt.P.MAx3.L

end S_L_L4

section S_L_L5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.L

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.G

noncomputable section

section Conj
variable {P : M.Par} (hTT : 0 ≤ P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hTT hL

theorem conj_hatv (s : ℝ) (Y : ℂ) :
    Gs P (-s) * L.Ahatv Y * Gs P s = L.Ahatv (Y - s) ∧ Gs P (-s) * L.R0v Y * Gs P s = L.R0v (Y - s) := by
  have hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL'
  have hpr : ∀ l, L.p l * Gs P s = Gs P s * L.p l + algebraMap ℂ (A P (DQ P)) (s : ℂ) * Gs P s := by
    intro l
    rw [hp]
    show sc P (DQ P) ((DQ P).pP l) * Gs P s = Gs P s * sc P (DQ P) ((DQ P).pP l) + _
    rw [Gs, alg_sc, sc_mul, sc_mul, sc_mul, sc_add, pP_Gpow hLaw]
  have hpbr : ∀ l, L.pb l * Gs P s = Gs P s * L.pb l + algebraMap ℂ (A P (DQ P)) (s : ℂ) * Gs P s := by
    intro l
    rw [hpb]
    show sc P (DQ P) ((DQ P).pbP l) * Gs P s = Gs P s * sc P (DQ P) ((DQ P).pbP l) + _
    rw [Gs, alg_sc, sc_mul, sc_mul, sc_mul, sc_add, pbP_Gpow hLaw]
  have hnr : L.nab * Gs P s = Gs P s * L.nab + algebraMap ℂ (A P (DQ P)) (s : ℂ) * (L.ζb * L.GGi * Gs P s) := by
    rw [hn, hzb, hgi]
    simp only [nabA, zbA, ggiA, Gs, sc_diag, alg_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    congr 1; funext π
    exact nab_Gpow hLaw s (M.aC P π)
  have hnsr : L.nabs * Gs P s = Gs P s * L.nabs - algebraMap ℂ (A P (DQ P)) (s : ℂ) * (L.ζ * L.GGi * Gs P s) := by
    rw [hns, hz, hgi]
    simp only [nabsA, zA, ggiA, Gs, sc_diag, alg_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]
    congr 1; funext π
    exact nabs_Gpow hLaw s (M.aC P π)
  have h := Formalism.FourierDecayAlt.P.gaugeConjugation (A P (DQ P)) P.r L (s : ℂ) (Gs P s) (Gs P (-s)) (Gs_mul_neg P s)
    (Gs_neg_mul P s) (fns_comm hTT hL s) hpr hpbr hnr hnsr Y
  exact ⟨h.2.2.1, h.2.2.2⟩

end Conj

section Poly
variable (P : M.Par) (L : LevelData (A P (DQ P)) P.r) (Y0 : ℂ)

theorem Tvl_affine (l : Fin P.r) : ∃ u v : Matrix (Fin 2) (Fin 2) (A P (DQ P)),
    ∀ s : ℂ, L.Tvl (Y0 + s) l = s • u + v := by
  refine ⟨!![1, 0; 0, 0], L.Tvl Y0 l, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tvl, map_add, Algebra.algebraMap_eq_smul_one] <;> abel

theorem Tvprod_poly : PolyIn (fun s : ℂ => L.Tvprod (Y0 + s)) P.r := by
  have h := polyIn_list_prod ((List.ofFn fun l : Fin P.r => fun s : ℂ => L.Tvl (Y0 + s) l).reverse)
    (fun g hg => by
      obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hg)
      exact Tvl_affine P L Y0 l)
  rw [List.length_reverse, List.length_ofFn] at h
  refine (congrArg (fun F => PolyIn F P.r) (funext fun s => ?_)).mp h
  simp only [LevelData.Tvprod, List.map_reverse, List.map_ofFn]
  rfl

theorem Ahatv_poly : PolyIn (fun s : ℂ => L.Ahatv (Y0 + s)) P.r :=
  polyIn_const_mul L.Drb (polyIn_entry (Tvprod_poly P L Y0) 0 0)

theorem raising_constant_affine : ∃ u v : A P (DQ P), ∀ s : ℂ, L.m0 (Y0 + s) = s • u + v := by
  refine ⟨-(L.ζ * L.GGi), L.m0 Y0, fun s => ?_⟩
  simp only [LevelData.m0, map_add, map_sub, Algebra.algebraMap_eq_smul_one, add_mul, sub_mul, smul_mul_assoc,
    one_mul, smul_neg, add_smul, sub_smul]
  abel

theorem raising_variant_polynomial : PolyIn (fun s : ℂ => L.R0v (Y0 + s)) (P.r + 1) := by
  obtain ⟨u, v, huv⟩ := raising_constant_affine P L Y0
  have h1 := polyIn_affine_mul u v (polyIn_entry (Tvprod_poly P L Y0) 0 0)
  have h2 := polyIn_mono (polyIn_entry (Tvprod_poly P L Y0) 1 0) (Nat.le_succ P.r)
  have h3 := polyIn_const_mul (L.Dr * L.GG) (polyIn_add h1 h2)
  refine (congrArg (fun F => PolyIn F (P.r + 1)) (funext fun s => ?_)).mp h3
  simp only [LevelData.R0v, LevelData.Avr, LevelData.Bvr, huv]

end Poly

theorem leib_gen (P : M.Par) (X : ℂ → A P (DQ P)) (y : ℂ) (σ : ℝ) (d : ℕ)
    (hpolyIn : PolyIn (fun t => X (y + t)) d)
    (hconj : ∀ s : ℝ, Gs P (-s) * X y * Gs P s = X (y + ((σ * s : ℝ) : ℂ)))
    (hmem : ∀ t, X t ∈ JetMatrixAlgebra P) (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ) :
    ∃ a : ℕ → A P (DQ P), (∀ k, a k ∈ Submodule.span ℂ (Set.range fun n : Fin (d + 1) => X (y + n))) ∧
      X y * sc P (DQ P) (Fq P φ 0) = ∑ p ∈ Finset.range (d + 1), sc P (DQ P) (Fq P φ p) * (((σ : ℂ) ^ p) • a p) := by
  obtain ⟨a, ha⟩ := hpolyIn
  set a' : ℕ → A P (DQ P) := fun k => if k < d + 1 then a k else 0
  have ha' : ∀ t, X (y + t) = ∑ k ∈ Finset.range (d + 1), t ^ k • a' k := fun t => by
    rw [show X (y + t) = (fun t => X (y + t)) t from rfl, ha t]
    exact Finset.sum_congr rfl fun k hk => by simp only [a']; rw [if_pos (Finset.mem_range.1 hk)]
  have hspan : ∀ k, a' k ∈ Submodule.span ℂ (Set.range fun n : Fin (d + 1) => X (y + n)) := by
    intro k
    by_cases hk : k < d + 1
    · have := polyIn_coeff_span (fun t => X (y + t)) d a' ha' k (Finset.mem_range.2 hk)
      simpa using this
    · have : a' k = 0 := by simp only [a']; rw [if_neg hk]
      rw [this]; exact Submodule.zero_mem _
  have hsub : Submodule.span ℂ (Set.range fun n : Fin (d + 1) => X (y + n)) ≤ Subalgebra.toSubmodule (JetMatrixAlgebra P) :=
    Submodule.span_le.2 (by rintro _ ⟨n, rfl⟩; exact hmem _)
  refine ⟨a', hspan, mat_leibniz P X y σ d a' ha' hconj (fun π π' => ((hmem y) π π').1) (fun k π π' => ?_) φ hφ⟩
  exact ((hsub (hspan k)) π π').2

end

end Formalism.FourierDecayAlt.P.MAx3.L

end S_L_L5

section S_AD_AD1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L

noncomputable section

def admitted (φ : ℝ → ℝ) : Prop :=
  LE.SmoothLog φ ∧ (∃ ε > 0, ∀ x, x ≤ ε → φ x = 0) ∧ ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C

theorem vanish_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (a : ℝ) (h0 : ∀ u, u ≤ a → f u = 0)
    (n : ℕ) : ∀ u, u ≤ a → iteratedDeriv n f u = 0 := by
  have hopen : ∀ u, u < a → iteratedDeriv n f u = 0 := by
    intro u hu
    have hev : f =ᶠ[nhds u] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hu] with v hv using h0 v (le_of_lt hv)
    have hz : ∀ m, iteratedDeriv m (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [iteratedDeriv_succ, ih]; funext v; exact deriv_const v (0 : ℝ)
    rw [hev.iteratedDeriv_eq n, hz]
  have hcont : Continuous (iteratedDeriv n f) := hf.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hclosed : IsClosed {u | iteratedDeriv n f u = 0} := isClosed_eq hcont continuous_const
  intro u hu
  have hsub : Set.Iio a ⊆ {u | iteratedDeriv n f u = 0} := fun v hv => hopen v hv
  have := hclosed.closure_subset_iff.2 hsub
  rw [closure_Iio' (Set.nonempty_Iio)] at this
  exact this hu

theorem ld_zero {φ : ℝ → ℝ} {x : ℝ} (hx : 0 < x) : LE.ld 0 φ x = φ x := by
  simp [LE.ld, Real.exp_log hx]

theorem ld_vanish {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) {ε : ℝ} (hε : 0 < ε) (h0 : ∀ x, x ≤ ε → φ x = 0) (p : ℕ)
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ ε) : LE.ld p φ x = 0 := by
  unfold LE.ld
  refine vanish_deriv hφ (Real.log ε) (fun u hu => h0 _ ?_) p _ (Real.log_le_log hx0 hx)
  calc Real.exp u ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 hu
    _ = ε := Real.exp_log hε

theorem ld_comp_exp (φ : ℝ → ℝ) (p : ℕ) : (fun u => LE.ld p φ (Real.exp u)) = iteratedDeriv p (fun u => φ (Real.exp u)) := by
  funext u; simp [LE.ld, Real.log_exp]

theorem ld_ld (φ : ℝ → ℝ) (p q : ℕ) (x : ℝ) : LE.ld q (LE.ld p φ) x = LE.ld (q + p) φ x := by
  unfold LE.ld
  rw [show (fun u => iteratedDeriv p (fun u => φ (Real.exp u)) (Real.log (Real.exp u))) =
      iteratedDeriv p (fun u => φ (Real.exp u)) from funext fun u => by rw [Real.log_exp]]
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, Function.iterate_add_apply]

def tr (ε : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ ε then 0 else ψ x

theorem tr_comp_exp {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) {ε : ℝ} (hε : 0 < ε) (h0 : ∀ x, x ≤ ε → φ x = 0) (p : ℕ) :
    (fun u => tr ε (LE.ld p φ) (Real.exp u)) = fun u => LE.ld p φ (Real.exp u) := by
  funext u
  unfold tr
  split_ifs with h
  · exact (ld_vanish hφ hε h0 p (Real.exp_pos u) h).symm
  · rfl

theorem admissible_log_derivative {φ : ℝ → ℝ} (hφ : admitted φ) (p : ℕ) :
    ∃ ψ, admitted ψ ∧ ∀ x, 0 < x → ψ x = LE.ld p φ x := by
  obtain ⟨hs, ⟨ε, hε, h0⟩, hb⟩ := hφ
  refine ⟨tr ε (LE.ld p φ), ⟨?_, ⟨ε, hε, fun x hx => by simp [tr, hx]⟩, fun q => ?_⟩, fun x hx => ?_⟩
  · unfold LE.SmoothLog
    rw [tr_comp_exp hs hε h0 p, ld_comp_exp]
    rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv p hs
  · obtain ⟨C, hC⟩ := hb (q + p)
    refine ⟨C, fun x hx => ?_⟩
    have e : LE.ld q (tr ε (LE.ld p φ)) x = LE.ld q (LE.ld p φ) x := by
      show iteratedDeriv q (fun u => tr ε (LE.ld p φ) (Real.exp u)) (Real.log x) =
        iteratedDeriv q (fun u => LE.ld p φ (Real.exp u)) (Real.log x)
      rw [tr_comp_exp hs hε h0 p]
    rw [e, ld_ld]; exact hC x hx
  · unfold tr
    split_ifs with h
    · exact (ld_vanish hs hε h0 p hx h).symm
    · rfl

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD1

section S_AD_AD2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L

noncomputable section

theorem smooth_top_at {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (n : ℕ) (x : ℝ) :
    ContDiffAt ℝ n f x := (hf.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt

theorem ld_mul {φ ψ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hψ : LE.SmoothLog ψ) (q : ℕ) (x : ℝ) :
    LE.ld q (fun x => φ x * ψ x) x =
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * LE.ld i φ x * LE.ld (q - i) ψ x := by
  unfold LE.ld
  have e : (fun u => (fun x => φ x * ψ x) (Real.exp u)) = (fun u => φ (Real.exp u)) * (fun u => ψ (Real.exp u)) := rfl
  rw [e, iteratedDeriv_mul (smooth_top_at hφ q _) (smooth_top_at hψ q _)]

theorem isAdmissibleSplittingCharPair_mul_twist {φ ψ : ℝ → ℝ} (hφ : admitted φ) (hψ : admitted ψ) : admitted (fun x => φ x * ψ x) := by
  obtain ⟨hs, ⟨ε, hε, h0⟩, hb⟩ := hφ
  obtain ⟨hs', -, hb'⟩ := hψ
  refine ⟨?_, ⟨ε, hε, fun x hx => by simp [h0 x hx]⟩, fun q => ?_⟩
  · unfold LE.SmoothLog; exact hs.mul hs'
  · choose C hC using hb
    choose C' hC' using hb'
    refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * C i * C' (q - i), fun x hx => ?_⟩
    rw [ld_mul hs hs']
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 := hC i x hx
    have h2 := hC' (q - i) x hx
    have hc0 : 0 ≤ C i := (abs_nonneg _).trans h1
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (abs_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) hc0)

theorem smoothLog_rpow' (t : ℝ) : LE.SmoothLog (fun x : ℝ => x ^ t) := G.smoothLog_rpow t

theorem admissible_mul_rpow {φ : ℝ → ℝ} (hφ : admitted φ) {t : ℝ} (ht : t ≤ 0) : admitted (fun x => φ x * x ^ t) := by
  obtain ⟨hs, ⟨ε, hε, h0⟩, hb⟩ := hφ
  have hsm : LE.SmoothLog (fun x => φ x * x ^ t) := by
    unfold LE.SmoothLog; exact hs.mul (smoothLog_rpow' t)
  have hvan : ∀ x, x ≤ ε → φ x * x ^ t = 0 := fun x hx => by rw [h0 x hx, zero_mul]
  refine ⟨hsm, ⟨ε, hε, hvan⟩, fun q => ?_⟩
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * C i * (|t| ^ (q - i) * ε ^ t), fun x hx => ?_⟩
  by_cases hxe : x ≤ ε
  · rw [ld_vanish hsm hε hvan q hx hxe, abs_zero]
    refine Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans (hC i 1 one_pos)))
      (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hε.le _))
  · push Not at hxe
    rw [ld_mul hs (smoothLog_rpow' t)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [ldq_rpow t (q - i) x hx, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow,
      abs_of_nonneg (Real.rpow_nonneg hx.le _)]
    have h1 := hC i x hx
    have hc0 : 0 ≤ C i := (abs_nonneg _).trans h1
    have h3 : x ^ t ≤ ε ^ t := Real.rpow_le_rpow_of_nonpos hε hxe.le ht
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left h3 (pow_nonneg (abs_nonneg _) _)) (mul_nonneg (pow_nonneg (abs_nonneg _) _)
        (Real.rpow_nonneg hx.le _)) (mul_nonneg (Nat.cast_nonneg _) hc0)

variable (P : M.Par)

theorem Phi0_eq {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) : Phi P φ 0 = toSm P (fun q => ((φ (Gq P q) : ℝ) : ℂ)) := by
  unfold Phi
  congr 1
  funext q
  rw [ld_zero (Gq_pos P q)]

theorem eval_cutoff_operator_zero {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : Qp P.r P.TT) : evQ P (Phi P φ 0) q = ((φ (Gq P q) : ℝ) : ℂ) := by
  rw [ev_Phi P hφ, ld_zero (Gq_pos P q)]

theorem Phi0_mul {φ ψ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hψ : LE.SmoothLog ψ) :
    Phi P (fun x => φ x * ψ x) 0 = Phi P φ 0 * Phi P ψ 0 := by
  have hs : LE.SmoothLog (fun x => φ x * ψ x) := by unfold LE.SmoothLog; exact hφ.mul hψ
  apply Subtype.ext; funext q
  show evQ P (Phi P (fun x => φ x * ψ x) 0) q = evQ P (Phi P φ 0 * Phi P ψ 0) q
  rw [MAx2.Jet.evQ_mul, eval_cutoff_operator_zero P hs, eval_cutoff_operator_zero P hφ, eval_cutoff_operator_zero P hψ]
  push_cast; ring

def Ph (φ : ℝ → ℝ) : A P (DQ P) := sc P (DQ P) (Fq P φ 0)

theorem Ph_mul {φ ψ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hψ : LE.SmoothLog ψ) :
    Ph P φ * Ph P ψ = Ph P (fun x => φ x * ψ x) := by
  unfold Ph Fq
  rw [G.sc_mul]
  congr 1
  refine (Formalism.FourierDecayAlt.P.MAx1.multiplierPair_mul (DQ P) (Phi P φ 0) (Phi P φ 0) (Phi P ψ 0) (Phi P ψ 0)).trans ?_
  congr 1 <;> exact (Phi0_mul P hφ hψ).symm

theorem Ph_Gs {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (t : ℝ) :
    Ph P φ * G.Gs P t = Ph P (fun x => φ x * x ^ t) := by
  have : G.Gs P t = Ph P (fun x : ℝ => x ^ t) := rfl
  rw [this, Ph_mul P hφ (smoothLog_rpow' t)]

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD2

section S_K_K1

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.K

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} {L : LevelData A r} {S : Submonoid A}

def Term3 (L : LevelData A r) (S : Submonoid A) (Hs : Set A) (d ℓ : ℕ) : Set A :=
  {x | ∃ b ∈ S, ∃ (i i' : ℕ) (H : List A), i + i' = d ∧ H.length = ℓ ∧ (∀ h ∈ H, h ∈ Hs) ∧ x = tm L b i i' H}

def NormalFormThree (L : LevelData A r) (S : Submonoid A) (Hs : Set A) (d ℓ : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ (Term3 L S Hs d ℓ)

variable {Hs : Set A}

theorem mem3 {d ℓ : ℕ} {b : A} (hb : b ∈ S) {i i' : ℕ} {H : List A} (h1 : i + i' = d) (h2 : H.length = ℓ)
    (h3 : ∀ h ∈ H, h ∈ Hs) : tm L b i i' H ∈ NormalFormThree L S Hs d ℓ :=
  Submodule.subset_span ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩

theorem cons3 {h : A} (hh : h ∈ Hs) {H : List A} (h3 : ∀ x ∈ H, x ∈ Hs) : ∀ x ∈ h :: H, x ∈ Hs := by
  intro x hx; rcases List.mem_cons.1 hx with rfl | hx; exacts [hh, h3 x hx]

theorem sum3 {d ℓ : ℕ} {ι : Type} (ts : List ι) (f : ι → A) (h : ∀ x ∈ ts, f x ∈ NormalFormThree L S Hs d ℓ) :
    (ts.map f).sum ∈ NormalFormThree L S Hs d ℓ := by
  induction ts with
  | nil => simp
  | cons a ts ih =>
    rw [List.map_cons, List.sum_cons]
    exact Submodule.add_mem _ (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem normal_form_three_D_inv (hS : Hyp L S) {d ℓ : ℕ} {x : A} (hx : x ∈ NormalFormThree L S Hs d ℓ) : L.Di * x ∈ NormalFormThree L S Hs (d + 1) ℓ := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  rw [Di_tm hS hb]; exact mem3 hb (by omega) h2 h3

theorem normal_form_three_D_bar_inv (hS : Hyp L S) {d ℓ : ℕ} {x : A} (hx : x ∈ NormalFormThree L S Hs d ℓ) : L.Dbi * x ∈ NormalFormThree L S Hs (d + 1) ℓ := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  rw [Dbi_tm hS hb]; exact mem3 hb (by omega) h2 h3

theorem normal_form_three_hat (hS : Hyp L S) (hP : plusHats L ⊆ Hs) (y : ℂ) {d ℓ : ℕ} {x : A} (hx : x ∈ NormalFormThree L S Hs d ℓ) :
    L.Ahat y * x ∈ NormalFormThree L S Hs d (ℓ + 1) := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  obtain ⟨y', e⟩ := Ahat_tm hS y hb i i' H
  rw [e]; exact mem3 hb h1 (by simp [h2]) (cons3 (hP (Or.inl ⟨_, rfl⟩)) h3)

theorem normal_form_three_raising (hS : Hyp L S) (hP : plusHats L ⊆ Hs) (y : ℂ) {d ℓ : ℕ} {x : A} (hx : x ∈ NormalFormThree L S Hs d ℓ) :
    L.R0 y * x ∈ NormalFormThree L S Hs d (ℓ + 1) := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  obtain ⟨t, ts, hts, e⟩ := hS.r0 b hb y
  obtain ⟨cs, hcs⟩ := bRPQ (L := L) b (y + t) i i' H
  have e2 : L.R0 y * tm L b i i' H = (b * L.R0 (y + t) * (L.Di ^ i * L.Dbi ^ i') * H.prod) +
      (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2 * (L.Di ^ i * L.Dbi ^ i') * H.prod)).sum := by
    unfold tm
    rw [← mul_assoc, ← mul_assoc, e, add_mul, add_mul, ← List.sum_map_mul_right, ← List.sum_map_mul_right]
    congr 1
    congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc]
  rw [e2, hcs]
  refine Submodule.add_mem _ (Submodule.add_mem _ (mem3 hb h1 (by simp [h2]) (cons3 (hP (Or.inr ⟨_, rfl⟩)) h3))
    (sum3 _ _ fun x _ => Submodule.smul_mem _ _ (mem3 (S.mul_mem hb hS.drb) h1 (by simp [h2])
      (cons3 (hP (Or.inl ⟨_, rfl⟩)) h3)))) (sum3 _ _ fun x hx => ?_)
  rw [bAPQ]
  exact Submodule.smul_mem _ _ (mem3 (hts x hx) h1 (by simp [h2]) (cons3 (hP (Or.inl ⟨_, rfl⟩)) h3))

theorem normal_form_three_monoid_mul {b : A} (hb : b ∈ S) {d ℓ : ℕ} {x : A} (hx : x ∈ NormalFormThree L S Hs d ℓ) : b * x ∈ NormalFormThree L S Hs d ℓ := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b', hb', i, i', H, h1, h2, h3, rfl⟩ := hx
  have : b * tm L b' i i' H = tm L (b * b') i i' H := by unfold tm; simp only [mul_assoc]
  rw [this]; exact mem3 (S.mul_mem hb hb') h1 h2 h3

theorem normal_form_three_span_mul {z : A} (hz : z ∈ Submodule.span ℂ (S : Set A)) {d ℓ : ℕ} {x : A}
    (hx : x ∈ NormalFormThree L S Hs d ℓ) : z * x ∈ NormalFormThree L S Hs d ℓ := by
  induction hz using Submodule.span_induction with
  | mem b hb => exact normal_form_three_monoid_mul hb hx
  | zero => simp
  | add a b _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c a _ h1 => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h1

end Formalism.FourierDecayAlt.P.MAx3.K

end S_K_K1

section S_K_K2

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.K

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem hatv_D_fns : (∀ Y, L.Ahatv Y * L.Di = L.Di * L.Ahatv Y) ∧ ∀ Y, L.R0v Y * L.Di = L.Di * L.R0v Y := by
  have h := fun Y => (Formalism.FourierDecayAlt.P.shiftConjugation A r L Y).2.2.2.2.2
  have hc : ∀ Y, ∀ x ∈ Set.range L.c ∪ Set.range L.ci ∪ {L.ζ, L.ζi}, x * L.Ahatv Y = L.Ahatv Y * x ∧
      x * L.R0v Y = L.R0v Y * x := h
  have hDri : ∀ Y, L.Dri * L.Ahatv Y = L.Ahatv Y * L.Dri ∧ L.Dri * L.R0v Y = L.R0v Y * L.Dri := fun Y =>
    ⟨(comm_prod L.ci (L.Ahatv Y) (fun i => ((hc Y (L.ci i) (Or.inl (Or.inr ⟨i, rfl⟩))).1).symm)).symm,
     (comm_prod L.ci (L.R0v Y) (fun i => ((hc Y (L.ci i) (Or.inl (Or.inr ⟨i, rfl⟩))).2).symm)).symm⟩
  refine ⟨fun Y => ?_, fun Y => ?_⟩
  · unfold LevelData.Di
    rw [← mul_assoc, ← (hc Y L.ζi (Or.inr (Or.inr rfl))).1, mul_assoc, ← (hDri Y).1, mul_assoc]
  · unfold LevelData.Di
    rw [← mul_assoc, ← (hc Y L.ζi (Or.inr (Or.inr rfl))).2, mul_assoc, ← (hDri Y).2, mul_assoc]

theorem Ahatv_Dbi (Y : ℂ) : L.Ahatv Y * L.Dbi = L.Dbi * L.Ahatv (Y + 1) := by
  have h := (Formalism.FourierDecayAlt.P.shiftConjugation A r L (Y + 1)).2.2.1
  rw [add_sub_cancel_right] at h
  rw [← h, mul_assoc, mul_assoc, Db_Dbi, mul_one]

theorem raising_variant_D_bar_inv (Y : ℂ) : L.R0v Y * L.Dbi = L.Dbi * (L.R0v (Y + 1) + L.TT • (L.Dr * L.Dbi * L.Ahatv (Y + 1))) := by
  have h := (Formalism.FourierDecayAlt.P.shiftConjugation A r L (Y + 1)).2.2.2.1
  rw [add_sub_cancel_right] at h
  have h2 : L.R0v Y = L.Dbi * L.R0v (Y + 1) * L.Db + algebraMap ℂ A L.TT * (L.Dr * L.Dbi * L.Ahatv Y) := by
    rw [h]; abel
  have hc : L.Dr * L.Dbi * L.Dbi = L.Dbi * (L.Dr * L.Dbi) :=
    cl_comm L (Subring.mul_mem _ (memDr L) (memDbi L)) (memDbi L)
  rw [h2, add_mul, mul_assoc (L.Dbi * L.R0v (Y + 1)), Db_Dbi, mul_one, mul_assoc (algebraMap ℂ A L.TT),
    mul_assoc (L.Dr * L.Dbi), Ahatv_Dbi, ← mul_assoc (L.Dr * L.Dbi), hc, mul_add, Algebra.smul_def,
    ← mul_assoc L.Dbi (algebraMap ℂ A L.TT), ← Algebra.commutes L.TT L.Dbi]
  simp only [mul_assoc]

theorem Ahatv_Dbipow (i : ℕ) (Y : ℂ) : L.Ahatv Y * L.Dbi ^ i = L.Dbi ^ i * L.Ahatv (Y + i) := by
  induction i generalizing Y with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', ← mul_assoc, Ahatv_Dbi, mul_assoc, ih, ← mul_assoc]
    congr 2; push_cast; ring

theorem Ahatv_Dipow (i : ℕ) (Y : ℂ) : L.Ahatv Y * L.Di ^ i = L.Di ^ i * L.Ahatv Y :=
  (Commute.pow_right ((hatv_D_fns L).1 Y) i).eq

theorem raising_variant_D_inv_pow (i : ℕ) (Y : ℂ) : L.R0v Y * L.Di ^ i = L.Di ^ i * L.R0v Y :=
  (Commute.pow_right ((hatv_D_fns L).2 Y) i).eq

theorem raising_variant_D_bar_inv_pow (i : ℕ) (Y : ℂ) : ∃ cs : List (ℂ × ℂ), L.R0v Y * L.Dbi ^ i =
    L.Dbi ^ i * (L.R0v (Y + i) + (cs.map fun x => x.1 • (L.Dr * L.Dbi * L.Ahatv x.2)).sum) := by
  induction i generalizing Y with
  | zero => exact ⟨[], by simp⟩
  | succ i ih =>
    obtain ⟨cs, hcs⟩ := ih (Y + 1)
    refine ⟨cs ++ [(L.TT, Y + 1 + i)], ?_⟩
    have hDD : L.Dr * L.Dbi * L.Dbi ^ i = L.Dbi ^ i * (L.Dr * L.Dbi) :=
      cl_comm L (Subring.mul_mem _ (memDr L) (memDbi L)) (memPow L (memDbi L) i)
    have e : (Y + 1 + (i : ℂ)) = Y + ((i + 1 : ℕ) : ℂ) := by push_cast; ring
    have hX : L.TT • (L.Dr * L.Dbi * L.Ahatv (Y + 1)) * L.Dbi ^ i =
        L.Dbi ^ i * (L.TT • (L.Dr * L.Dbi * L.Ahatv (Y + 1 + i))) := by
      rw [smul_mul_assoc, mul_smul_comm, mul_assoc, Ahatv_Dbipow, ← mul_assoc, hDD, mul_assoc]
    calc L.R0v Y * L.Dbi ^ (i + 1) = L.R0v Y * L.Dbi * L.Dbi ^ i := by rw [pow_succ', mul_assoc]
      _ = L.Dbi * (L.R0v (Y + 1) * L.Dbi ^ i + L.TT • (L.Dr * L.Dbi * L.Ahatv (Y + 1)) * L.Dbi ^ i) := by
          rw [raising_variant_D_bar_inv, mul_assoc, add_mul]
      _ = L.Dbi ^ (i + 1) * (L.R0v (Y + ((i + 1 : ℕ) : ℂ)) +
            ((cs ++ [(L.TT, Y + 1 + i)]).map fun x => x.1 • (L.Dr * L.Dbi * L.Ahatv x.2)).sum) := by
          rw [hcs, hX, ← mul_add, ← mul_assoc, ← pow_succ', e, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, add_assoc, ← e]

end Formalism.FourierDecayAlt.P.MAx3.K

end S_K_K2

section S_K_K3

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx3.K

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} {L : LevelData A r} {S : Submonoid A} {Hs : Set A}

def minusHats (L : LevelData A r) : Set A := Set.range L.Ahatv ∪ Set.range L.R0v

structure HypV (L : LevelData A r) (S : Submonoid A) : Prop where
  ahatv : ∀ b ∈ S, ∃ t : ℂ, ∀ Y, L.Ahatv Y * b = b * L.Ahatv (Y + t)
  r0v : ∀ b ∈ S, ∀ Y, ∃ (t : ℂ) (ts : List (ℂ × A × ℂ)), (∀ x ∈ ts, x.2.1 ∈ S) ∧
    L.R0v Y * b = b * L.R0v (Y + t) + (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum
  drv : L.Dr * L.Dbi ∈ S

theorem bVPQ (b : A) (y' : ℂ) (i i' : ℕ) (H : List A) :
    b * L.Ahatv y' * (L.Di ^ i * L.Dbi ^ i') * H.prod = tm L b i i' (L.Ahatv (y' + i') :: H) := by
  unfold tm
  rw [List.prod_cons]
  simp only [mul_assoc]
  rw [← mul_assoc (L.Ahatv y'), Ahatv_Dipow, mul_assoc, ← mul_assoc (L.Ahatv y'), Ahatv_Dbipow, mul_assoc]

theorem drv_comm_P (i : ℕ) : L.Dr * L.Dbi * L.Di ^ i = L.Di ^ i * (L.Dr * L.Dbi) :=
  cl_comm L (Subring.mul_mem _ (memDr L) (memDbi L)) (memPow L (memDi L) i)
theorem drv_comm_Q (i : ℕ) : L.Dr * L.Dbi * L.Dbi ^ i = L.Dbi ^ i * (L.Dr * L.Dbi) :=
  cl_comm L (Subring.mul_mem _ (memDr L) (memDbi L)) (memPow L (memDbi L) i)

theorem bRvPQ (b : A) (y : ℂ) (i i' : ℕ) (H : List A) : ∃ cs : List (ℂ × ℂ),
    b * L.R0v y * (L.Di ^ i * L.Dbi ^ i') * H.prod = tm L b i i' (L.R0v (y + i') :: H) +
      (cs.map fun x => x.1 • tm L (b * (L.Dr * L.Dbi)) i i' (L.Ahatv x.2 :: H)).sum := by
  obtain ⟨cs, hcs⟩ := raising_variant_D_bar_inv_pow L i' y
  refine ⟨cs, ?_⟩
  have e1 : b * L.R0v y * (L.Di ^ i * L.Dbi ^ i') * H.prod =
      b * L.Di ^ i * (L.Dbi ^ i' * (L.R0v (y + i') + (cs.map fun x => x.1 • (L.Dr * L.Dbi * L.Ahatv x.2)).sum)) *
        H.prod := by
    rw [← hcs, mul_assoc b (L.R0v y), ← mul_assoc (L.R0v y), raising_variant_D_inv_pow]; simp only [mul_assoc]
  rw [e1, mul_add, mul_add, add_mul]
  congr 1
  · unfold tm; rw [List.prod_cons]; simp only [mul_assoc]
  · rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc]
    congr 1
    have tQ : ∀ z, L.Dbi ^ i' * (L.Dr * (L.Dbi * z)) = L.Dr * (L.Dbi * (L.Dbi ^ i' * z)) := fun z => by
      rw [← mul_assoc L.Dr, ← mul_assoc, ← drv_comm_Q, mul_assoc, mul_assoc]
    have tP : ∀ z, L.Di ^ i * (L.Dr * (L.Dbi * z)) = L.Dr * (L.Dbi * (L.Di ^ i * z)) := fun z => by
      rw [← mul_assoc L.Dr, ← mul_assoc, ← drv_comm_P, mul_assoc, mul_assoc]
    unfold tm; rw [List.prod_cons]; simp only [mul_assoc]
    rw [tQ, tP]

theorem normal_form_three_hat_variant (hS : HypV L S) (hM : minusHats L ⊆ Hs) (y : ℂ) {d ℓ : ℕ} {x : A}
    (hx : x ∈ NormalFormThree L S Hs d ℓ) : L.Ahatv y * x ∈ NormalFormThree L S Hs d (ℓ + 1) := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  obtain ⟨t, ht⟩ := hS.ahatv b hb
  have e : L.Ahatv y * tm L b i i' H = b * L.Ahatv (y + t) * (L.Di ^ i * L.Dbi ^ i') * H.prod := by
    unfold tm; rw [← mul_assoc, ← mul_assoc, ht]
  rw [e, bVPQ]
  exact mem3 hb h1 (by simp [h2]) (cons3 (hM (Or.inl ⟨_, rfl⟩)) h3)

theorem normal_form_three_raising_variant (hS : HypV L S) (hM : minusHats L ⊆ Hs) (y : ℂ) {d ℓ : ℕ} {x : A}
    (hx : x ∈ NormalFormThree L S Hs d ℓ) : L.R0v y * x ∈ NormalFormThree L S Hs d (ℓ + 1) := by
  refine span_mul _ (fun x hx => ?_) hx
  obtain ⟨b, hb, i, i', H, h1, h2, h3, rfl⟩ := hx
  obtain ⟨t, ts, hts, e⟩ := hS.r0v b hb y
  obtain ⟨cs, hcs⟩ := bRvPQ (L := L) b (y + t) i i' H
  have e2 : L.R0v y * tm L b i i' H = (b * L.R0v (y + t) * (L.Di ^ i * L.Dbi ^ i') * H.prod) +
      (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2 * (L.Di ^ i * L.Dbi ^ i') * H.prod)).sum := by
    unfold tm
    rw [← mul_assoc, ← mul_assoc, e, add_mul, add_mul, ← List.sum_map_mul_right, ← List.sum_map_mul_right]
    congr 1
    congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc]
  rw [e2, hcs]
  refine Submodule.add_mem _ (Submodule.add_mem _ (mem3 hb h1 (by simp [h2]) (cons3 (hM (Or.inr ⟨_, rfl⟩)) h3))
    (sum3 _ _ fun x _ => Submodule.smul_mem _ _ (mem3 (S.mul_mem hb hS.drv) h1 (by simp [h2])
      (cons3 (hM (Or.inl ⟨_, rfl⟩)) h3)))) (sum3 _ _ fun x hx => ?_)
  rw [bVPQ]
  exact Submodule.smul_mem _ _ (mem3 (hts x hx) h1 (by simp [h2]) (cons3 (hM (Or.inl ⟨_, rfl⟩)) h3))

def RaisingVariantCommutesModulo (L : LevelData A r) (M : Set A) (b : A) : Prop :=
  ∀ Y, ∃ (t : ℂ) (ts : List (ℂ × A × ℂ)), (∀ x ∈ ts, x.2.1 ∈ M) ∧
    L.R0v Y * b = b * L.R0v (Y + t) + (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum

theorem hypV_closure (T : Set A)
    (hA : ∀ b ∈ T, ∃ t : ℂ, ∀ Y, L.Ahatv Y * b = b * L.Ahatv (Y + t))
    (hR : ∀ b ∈ T, RaisingVariantCommutesModulo L (Submonoid.closure T) b)
    (hdrv : L.Dr * L.Dbi ∈ Submonoid.closure T) : HypV L (Submonoid.closure T) := by
  have P1 : ∀ b ∈ Submonoid.closure T, (∃ t : ℂ, ∀ Y, L.Ahatv Y * b = b * L.Ahatv (Y + t)) ∧
      RaisingVariantCommutesModulo L (Submonoid.closure T) b := by
    intro b hb
    induction hb using Submonoid.closure_induction with
    | mem x hx => exact ⟨hA x hx, hR x hx⟩
    | one => exact ⟨⟨0, fun Y => by simp⟩, fun Y => ⟨0, [], by simp, by simp⟩⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨⟨tx, htx⟩, rx⟩ := ihx
      obtain ⟨⟨ty, hty⟩, ry⟩ := ihy
      refine ⟨⟨tx + ty, fun Y => by rw [← mul_assoc, htx, mul_assoc, hty, mul_assoc, add_assoc]⟩, fun Y => ?_⟩
      obtain ⟨t1, ts1, hts1, e1⟩ := rx Y
      obtain ⟨t2, ts2, hts2, e2⟩ := ry (Y + t1)
      refine ⟨t1 + t2, (ts1.map fun z => (z.1, z.2.1 * y, z.2.2 + ty)) ++ (ts2.map fun z => (z.1, x * z.2.1, z.2.2)),
        ?_, ?_⟩
      · intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hz
          exact Submonoid.mul_mem _ (hts1 z' hz') hy
        · obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hz
          exact Submonoid.mul_mem _ hx (hts2 z' hz')
      · have s1 : (ts1.map fun z => z.1 • (z.2.1 * L.Ahatv z.2.2)).sum * y =
            ((ts1.map fun z => (z.1, z.2.1 * y, z.2.2 + ty)).map fun z => z.1 • (z.2.1 * L.Ahatv z.2.2)).sum := by
          rw [← List.sum_map_mul_right, List.map_map]
          congr 1
          refine List.map_congr_left fun z _ => ?_
          simp only [Function.comp_apply, smul_mul_assoc, mul_assoc, hty]
        have s2 : x * (ts2.map fun z => z.1 • (z.2.1 * L.Ahatv z.2.2)).sum =
            ((ts2.map fun z => (z.1, x * z.2.1, z.2.2)).map fun z => z.1 • (z.2.1 * L.Ahatv z.2.2)).sum := by
          rw [← List.sum_map_mul_left, List.map_map]
          congr 1
          refine List.map_congr_left fun z _ => ?_
          simp only [Function.comp_apply, mul_smul_comm, mul_assoc]
        calc L.R0v Y * (x * y) = (L.R0v Y * x) * y := by rw [mul_assoc]
          _ = x * (L.R0v (Y + t1) * y) + (ts1.map fun z => z.1 • (z.2.1 * L.Ahatv z.2.2)).sum * y := by
              rw [e1, add_mul, mul_assoc]
          _ = _ := by
              rw [e2, s1, mul_add, s2, List.map_append, List.sum_append, ← mul_assoc, add_assoc Y]
              abel
  exact ⟨fun b hb => (P1 b hb).1, fun b hb Y => (P1 b hb).2 Y, hdrv⟩

end Formalism.FourierDecayAlt.P.MAx3.K

end S_K_K3

section S_K_K4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.K

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H

section Abs
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem Ahatv_Db (Y : ℂ) : L.Ahatv Y * L.Db = L.Db * L.Ahatv (Y - 1) := by
  rw [← (Formalism.FourierDecayAlt.P.shiftConjugation A r L Y).2.2.1, ← mul_assoc, ← mul_assoc, Db_Dbi, one_mul]

theorem raising_variant_mul_D_bar (Y : ℂ) : L.R0v Y * L.Db = L.Db * (L.R0v (Y - 1) - L.TT • (L.Dr * L.Dbi * L.Ahatv (Y - 1))) := by
  rw [Algebra.smul_def, ← (Formalism.FourierDecayAlt.P.shiftConjugation A r L Y).2.2.2.1, ← mul_assoc, ← mul_assoc, Db_Dbi, one_mul]

theorem raising_variant_commute_D (Y : ℂ) : L.R0v Y * L.D = L.D * L.R0v Y := by
  have h := (hatv_D_fns L).2 Y
  calc L.R0v Y * L.D = L.D * L.Di * (L.R0v Y * L.D) := by rw [D_Di, one_mul]
    _ = L.D * (L.R0v Y * L.Di) * L.D := by rw [h]; simp only [mul_assoc]
    _ = L.D * L.R0v Y := by rw [mul_assoc, mul_assoc, Di_D, mul_one]

theorem Ahatv_D (Y : ℂ) : L.Ahatv Y * L.D = L.D * L.Ahatv Y := by
  have h := (hatv_D_fns L).1 Y
  calc L.Ahatv Y * L.D = L.D * L.Di * (L.Ahatv Y * L.D) := by rw [D_Di, one_mul]
    _ = L.D * (L.Ahatv Y * L.Di) * L.D := by rw [h]; simp only [mul_assoc]
    _ = L.D * L.Ahatv Y := by rw [mul_assoc, mul_assoc, Di_D, mul_one]

theorem vgen_DD_A (Y : ℂ) : L.Ahatv Y * (L.D * L.Dbi) = L.D * L.Dbi * L.Ahatv (Y + 1) := by
  rw [← mul_assoc, Ahatv_D, mul_assoc, Ahatv_Dbi, mul_assoc]

theorem vgen_DD_R (Y : ℂ) : L.R0v Y * (L.D * L.Dbi) = L.D * L.Dbi * L.R0v (Y + 1) +
    L.TT • (L.D * L.Dbi * (L.Dr * L.Dbi) * L.Ahatv (Y + 1)) := by
  rw [← mul_assoc, raising_variant_commute_D, mul_assoc, raising_variant_D_bar_inv]
  simp only [mul_add, mul_smul_comm, mul_assoc]

theorem vgen_DbD_A (Y : ℂ) : L.Ahatv Y * (L.Db * L.Di) = L.Db * L.Di * L.Ahatv (Y + -1) := by
  rw [← mul_assoc, Ahatv_Db, mul_assoc, (hatv_D_fns L).1, ← mul_assoc, sub_eq_add_neg]

theorem vgen_DbD_R (Y : ℂ) : L.R0v Y * (L.Db * L.Di) = L.Db * L.Di * L.R0v (Y + -1) +
    (-L.TT) • (L.Db * L.Di * (L.Dr * L.Dbi) * L.Ahatv (Y + -1)) := by
  have c : L.Dr * L.Dbi * L.Di = L.Di * (L.Dr * L.Dbi) :=
    cl_comm L (Subring.mul_mem _ (memDr L) (memDbi L)) (memDi L)
  rw [← mul_assoc, raising_variant_mul_D_bar, mul_assoc, sub_mul, (hatv_D_fns L).2, smul_mul_assoc, mul_assoc (L.Dr * L.Dbi),
    (hatv_D_fns L).1, ← mul_assoc (L.Dr * L.Dbi), c, mul_sub, neg_smul, ← sub_eq_add_neg, ← sub_eq_add_neg]
  simp only [mul_smul_comm, mul_assoc]

theorem coef_ζbi : L.G * L.Dbi * L.Dbi = L.D * L.Dbi - algebraMap ℂ A L.TT * (L.ζi * L.ζbi * (L.D * L.Dbi)) := by
  have h1 : e L L.ζ (memζ L) * e L L.ζi (memζi L) = 1 := Subtype.ext L.ζ_ζi
  have h2 : e L L.ζb (memζb L) * e L L.ζbi (memζbi L) = 1 := Subtype.ext L.ζb_ζbi
  have h3 : e L L.Drb (memDrb L) * e L L.Drbi (memDrbi L) = 1 := Subtype.ext (Drb_Drbi L)
  have hG : e L L.GG (memGG L) = e L L.ζ (memζ L) * e L L.ζb (memζb L) - e L _ (memS L L.TT) :=
    Subtype.ext L.GG_def
  have key : e L L.Dr (memDr L) * e L L.Drb (memDrb L) * e L L.GG (memGG L) *
      (e L L.ζbi (memζbi L) * e L L.Drbi (memDrbi L)) * (e L L.ζbi (memζbi L) * e L L.Drbi (memDrbi L)) =
      e L L.Dr (memDr L) * e L L.ζ (memζ L) * (e L L.ζbi (memζbi L) * e L L.Drbi (memDrbi L)) -
      e L _ (memS L L.TT) * (e L L.ζi (memζi L) * e L L.ζbi (memζbi L) * (e L L.Dr (memDr L) * e L L.ζ (memζ L) *
        (e L L.ζbi (memζbi L) * e L L.Drbi (memDrbi L)))) := by
    rw [hG]
    linear_combination (e L L.Dr (memDr L) * e L L.ζ (memζ L) * e L L.ζbi (memζbi L) * e L L.Drbi (memDrbi L) *
        e L L.ζb (memζb L) * e L L.ζbi (memζbi L)) * h3 +
      (e L L.Dr (memDr L) * e L L.ζ (memζ L) * e L L.ζbi (memζbi L) * e L L.Drbi (memDrbi L)) * h2 -
      (e L _ (memS L L.TT) * e L L.Dr (memDr L) * e L L.ζbi (memζbi L) * e L L.ζbi (memζbi L) *
        e L L.Drbi (memDrbi L) * e L L.Drbi (memDrbi L) * e L L.Drb (memDrb L)) * 0 -
      (e L _ (memS L L.TT) * e L L.Dr (memDr L) * e L L.ζbi (memζbi L) * e L L.ζbi (memζbi L) *
        e L L.Drbi (memDrbi L)) * h3 +
      (e L _ (memS L L.TT) * e L L.ζbi (memζbi L) * e L L.Dr (memDr L) * e L L.ζbi (memζbi L) *
        e L L.Drbi (memDrbi L)) * h1
  have := congrArg Subtype.val key
  simpa [e, LevelData.G, LevelData.D, LevelData.Dbi, mul_assoc] using this

theorem drv_eq : L.Dr * L.Dbi = L.D * L.Dbi * L.ζi := by
  have h1 : e L L.ζ (memζ L) * e L L.ζi (memζi L) = 1 := Subtype.ext L.ζ_ζi
  have key : e L L.Dr (memDr L) * e L L.Dbi (memDbi L) =
      e L L.Dr (memDr L) * e L L.ζ (memζ L) * e L L.Dbi (memDbi L) * e L L.ζi (memζi L) := by
    linear_combination (-(e L L.Dr (memDr L) * e L L.Dbi (memDbi L))) * h1
  have := congrArg Subtype.val key
  simpa [e, LevelData.D, mul_assoc] using this

theorem vgen_ζbi_R (Y : ℂ) : L.R0v Y * L.ζbi = L.ζbi * L.R0v (Y + 0) +
    ([((-1 : ℂ), L.D * L.Dbi, Y), (L.TT, L.ζi * L.ζbi * (L.D * L.Dbi), Y)].map
      fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum := by
  have h := (Formalism.FourierDecayAlt.P.inverseCommutators A r L Y).2.2.2.1
  rw [add_zero, sub_eq_iff_eq_add'.mp h]
  congr 1
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [coef_ζbi, sub_mul, neg_sub, neg_one_smul, Algebra.smul_def, mul_assoc (algebraMap ℂ A L.TT)]
  abel

end Abs

end Formalism.FourierDecayAlt.P.MAx3.K

end S_K_K4

section S_K_K5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.K

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL

theorem hatvDG (Y : ℂ) : L.Ahatv Y ∈ DG P ∧ L.R0v Y ∈ DG P := by
  obtain ⟨hp, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn⟩ := levDG hL
  obtain ⟨-, hpb, -, -, -, -, -, -, -, -, -, -, -, hns, -⟩ := hL
  have hpb' : ∀ l, L.pb l ∈ DG P := fun l => by rw [hpb]; exact sc_memDG P _
  have hns' : L.nabs ∈ DG P := by rw [hns]; exact diag_memDG P _
  have hDr : L.Dr ∈ DG P := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hc l
  have hDrb : L.Drb ∈ DG P := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hcb l
  have hT : L.Tvprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (DG P) (Fin 2) := Subalgebra.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hx)
    exact Formalism.FourierDecayAlt.P.MAx2.Jet.matrix_two_mem_sub _ _ _ _ _ (sub_mem (Subalgebra.algebraMap_mem _ _) (hpb' l))
      (neg_mem (hcb l)) (hcbi l) (Subalgebra.zero_mem _)
  refine ⟨mul_mem hDrb (hT 0 0), mul_mem (mul_mem hDr hg) (add_mem (mul_mem (sub_mem (neg_mem hns')
    (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hz hgi))) (hT 0 0)) (hT 1 0))⟩

include hLaw

theorem ruleSSv_SS (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    L.Ahatv Y * (L.Drb * L.Dri * SS P (DQ P) i) = (L.Drb * L.Dri * SS P (DQ P) i) * L.Ahatv (Y - 1) ∧
    L.R0v Y * (L.Drb * L.Dri * SS P (DQ P) i) = (L.Drb * L.Dri * SS P (DQ P) i) * L.R0v (Y - 1) := by
  obtain ⟨h1, h2⟩ := SS_rel hL hLaw i hi
  have hf : ∀ x ∈ L.fns, x * SS P (DQ P) i = SS P (DQ P) i * x := fun x hx => (SS_comm_SC P i (fnsSC hL x hx)).symm
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r L (SS P (DQ P) i) 0 hf (fun l => (SS_comm_SC P i (pSC hL l).1).symm)
    (fun l => (SS_comm_SC P i (pSC hL l).2).symm) h1 h2 (fun x _ => by simp) (fun l => by simp) (fun l => by simp)
    (by simp) (by simp) Y
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem ruleSSv_SSs (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    L.Ahatv Y * star (L.Drb * L.Dri * SS P (DQ P) i) = star (L.Drb * L.Dri * SS P (DQ P) i) * L.Ahatv (Y + 1) ∧
    L.R0v Y * star (L.Drb * L.Dri * SS P (DQ P) i) = star (L.Drb * L.Dri * SS P (DQ P) i) * L.R0v (Y + 1) := by
  obtain ⟨h1, h2⟩ := SSs_rel hL hLaw i hi
  have hf : ∀ x ∈ L.fns, x * star (SS P (DQ P) i) = star (SS P (DQ P) i) * x :=
    fun x hx => (SSs_comm_SC i (fnsSC hL x hx)).symm
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r L 0 (star (SS P (DQ P) i)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) hf (fun l => (SSs_comm_SC i (pSC hL l).1).symm)
    (fun l => (SSs_comm_SC i (pSC hL l).2).symm) h1 h2 Y
  rw [starSSn_eq hL hLaw]
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem hypV_model : HypV L (Submonoid.closure (bddSet P L)) := by
  have gen : ∀ {x}, x ∈ bddSet P L → x ∈ Submonoid.closure (bddSet P L) := fun h => Submonoid.subset_closure h
  have mDD : L.D * L.Dbi ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have mDbD : L.Db * L.Di ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have mζi : L.ζi ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have mζbi : L.ζbi ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  have hdrv : L.Dr * L.Dbi ∈ Submonoid.closure (bddSet P L) := by
    rw [drv_eq]; exact Submonoid.mul_mem _ (gen mDD) (gen mζi)
  have hInv := fun Y => Formalism.FourierDecayAlt.P.inverseCommutators _ P.r L Y
  refine hypV_closure (bddSet P L) ?_ ?_ hdrv
  · rintro b ((((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact ⟨0, fun Y => by rw [add_zero]; exact (hInv Y).2.2.2.2.2.1.symm⟩
      · exact ⟨0, fun Y => by rw [add_zero]; exact (hInv Y).2.2.1.symm⟩
      · exact ⟨1, vgen_DD_A L⟩
      · exact ⟨-1, vgen_DbD_A L⟩
    · exact ⟨0, fun Y => by rw [add_zero]; exact (kap_comm_DG P f (hatvDG hL Y).1).symm⟩
    · exact ⟨-1, fun Y => by rw [← sub_eq_add_neg]; exact (ruleSSv_SS hL hLaw i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) Y).1⟩
    · exact ⟨1, fun Y => (ruleSSv_SSs hL hLaw i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) Y).1⟩
  · rintro b ((((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)) Y
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact ⟨0, [], by simp, by rw [add_zero]; simpa using (hInv Y).2.2.2.2.2.2.1.symm⟩
      · refine ⟨0, _, ?_, vgen_ζbi_R L Y⟩
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact gen mDD
        · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (gen mζi) (gen mζbi)) (gen mDD)
      · refine ⟨1, [(L.TT, L.D * L.Dbi * (L.Dr * L.Dbi), Y + 1)], ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; exact Submonoid.mul_mem _ (gen mDD) hdrv
        · rw [vgen_DD_R]; simp
      · refine ⟨-1, [(-L.TT, L.Db * L.Di * (L.Dr * L.Dbi), Y + -1)], ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; exact Submonoid.mul_mem _ (gen mDbD) hdrv
        · rw [vgen_DbD_R]; simp
    · exact ⟨0, [], by simp, by rw [add_zero]; simpa using (kap_comm_DG P f (hatvDG hL Y).2).symm⟩
    · exact ⟨-1, [], by simp, by rw [← sub_eq_add_neg]; simpa using
        (ruleSSv_SS hL hLaw i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) Y).2⟩
    · exact ⟨1, [], by simp, by simpa using (ruleSSv_SSs hL hLaw i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) Y).2⟩

end

end Formalism.FourierDecayAlt.P.MAx3.K

end S_K_K5

section S_Q_Q1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Q

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Matrix

noncomputable section

section Abs
variable {A : Type} [Ring A]

theorem transpose_mul_comm (M N : Matrix (Fin 2) (Fin 2) A) (h : ∀ i j k l, M i j * N k l = N k l * M i j) :
    (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext i j
  simp only [transpose_apply, mul_apply]
  exact Finset.sum_congr rfl fun k _ => h _ _ _ _

theorem transpose_list_prod : ∀ (l : List (Matrix (Fin 2) (Fin 2) A)),
    l.Pairwise (fun M N => ∀ i j k m, M i j * N k m = N k m * M i j) →
    (l.prod)ᵀ = (l.map transpose).reverse.prod
  | [], _ => by simp
  | M :: l, h => by
    rw [List.pairwise_cons] at h
    rw [List.prod_cons, transpose_mul_comm, transpose_list_prod l h.2, List.map_cons, List.reverse_cons,
      List.prod_append, List.prod_singleton]
    intro i j k m
    have key : ∀ N ∈ l, ∀ i j k m, M i j * N k m = N k m * M i j := h.1

    have hc : ∀ (L' : List (Matrix (Fin 2) (Fin 2) A)), (∀ N ∈ L', ∀ k m, M i j * N k m = N k m * M i j) →
        ∀ k m, M i j * L'.prod k m = L'.prod k m * M i j := by
      intro L' hL'
      induction L' with
      | nil => intro k m; simp only [List.prod_nil, one_apply]; split_ifs <;> simp
      | cons N L' ih =>
        intro k m
        rw [List.prod_cons, mul_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← mul_assoc, hL' N (by simp) k t, mul_assoc, ih (fun N' hN' => hL' N' (by simp [hN'])) t m, mul_assoc]
    exact hc l (fun N hN k m => key N hN i j k m) k m

end Abs

end

end Formalism.FourierDecayAlt.P.MAx3.Q

end S_Q_Q1

section S_Q_Q2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Q

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Matrix Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

section Abs
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem comm_Tvprod (z : A) (hpb : ∀ l, z * L.pb l = L.pb l * z) (hcb : ∀ l, z * L.cb l = L.cb l * z)
    (hcbi : ∀ l, z * L.cbi l = L.cbi l * z) (Y : ℂ) :
    z * L.Avr Y = L.Avr Y * z ∧ z * L.Bvr Y = L.Bvr Y * z := by
  have hS : ∀ l, L.Tvl Y l ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (Subalgebra.centralizer ℂ {z}) (Fin 2) := by
    intro l
    refine Formalism.FourierDecayAlt.P.MAx2.Jet.matrix_two_mem_sub _ _ _ _ _ ?_ ?_ ?_ (Subalgebra.zero_mem _)
    · refine sub_mem (Subalgebra.algebraMap_mem _ _) ?_
      rw [Subalgebra.mem_centralizer_iff]; intro w hw; rw [Set.mem_singleton_iff.1 hw]; exact hpb l
    · refine neg_mem ?_
      rw [Subalgebra.mem_centralizer_iff]; intro w hw; rw [Set.mem_singleton_iff.1 hw]; exact hcb l
    · rw [Subalgebra.mem_centralizer_iff]; intro w hw; rw [Set.mem_singleton_iff.1 hw]; exact hcbi l
  have hT : L.Tvprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (Subalgebra.centralizer ℂ {z}) (Fin 2) :=
    Subalgebra.list_prod_mem _ fun x hx => by
      obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hx); exact hS l
  have h1 := (Subalgebra.mem_centralizer_iff _).1 (hT 0 0) z rfl
  have h2 := (Subalgebra.mem_centralizer_iff _).1 (hT 1 0) z rfl
  exact ⟨h1, h2⟩

theorem Avr_Drb (Y : ℂ) : L.Avr Y * L.Drb = L.Drb * L.Avr (Y - 1) := by
  have hfx : ∀ x ∈ L.fns, cj L.Drb L.Drbi (Drb_Drbi L) (Drbi_Drb L) x = x :=
    fun x hx => cj_fix _ _ _ _ (fns_Drb L hx)
  obtain ⟨h1, -⟩ := keyV L (cj L.Drb L.Drbi (Drb_Drbi L) (Drbi_Drb L)) 1 (-(L.ζ * L.GGi)) (cj_alg _ _ _ _)
    (fun l => by rw [cj_of_eq _ _ _ _ (pb_Drb L l), map_one, map_one])
    (fun l => hfx _ (m_cb L l)) (fun l => hfx _ (m_cbi L l)) (fun l => hfx _ (m_c L l))
    (hfx _ (m_GG L)) (hfx _ (m_ζ L)) (hfx _ (m_GGi L))
    (by rw [cj_fix _ _ _ _ (comm_Drb L (fun l => L.nabs_cb l)), map_one, one_mul, sub_neg_eq_add, sub_add_cancel]) Y
  rw [cj_apply] at h1
  unfold LevelData.Ahatv at h1
  calc L.Avr Y * L.Drb = L.Drbi * (L.Drb * L.Avr Y) * L.Drb := by rw [← mul_assoc, Drbi_Drb, one_mul]
    _ = L.Drb * L.Avr (Y - 1) := by rw [← h1]

end Abs

end

end Formalism.FourierDecayAlt.P.MAx3.Q

end S_Q_Q2

section S_Q_Q3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Q

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Matrix Formalism.FourierDecayAlt.P.MAx3.H
open Formalism.FourierDecayAlt.P.MAx2.Jet (matSub matrix_two_mem_sub)

noncomputable section

section Abs
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

def siteC (l : Fin r) : Subalgebra ℂ A := Subalgebra.centralizer ℂ {L.pb l, L.cb l, L.cbi l}

theorem mem_siteC {l : Fin r} {z : A} (h1 : L.pb l * z = z * L.pb l) (h2 : L.cb l * z = z * L.cb l)
    (h3 : L.cbi l * z = z * L.cbi l) : z ∈ siteC L l := by
  rw [siteC, Subalgebra.mem_centralizer_iff]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl <;> assumption

theorem cmem (S : Subalgebra ℂ A) {x : A} (hx : x ∈ S) (y : ℂ) (l : Fin r) (hp : L.pb l ∈ S) (hc : L.cb l ∈ S)
    (hci : L.cbi l ∈ S) : L.Tvl y l ∈ matSub S (Fin 2) :=
  matrix_two_mem_sub _ _ _ _ _ (sub_mem (Subalgebra.algebraMap_mem _ _) hp) (neg_mem hc) hci (Subalgebra.zero_mem _)

theorem site_entries (l m : Fin r) (hlm : l ≠ m) (y y' : ℂ) (i j k n : Fin 2) :
    (L.Tvl y l) i j * (L.Tvl y' m) k n = (L.Tvl y' m) k n * (L.Tvl y l) i j := by
  have hm : L.Tvl y' m ∈ matSub (siteC L l) (Fin 2) := by
    refine matrix_two_mem_sub _ _ _ _ _ (sub_mem (Subalgebra.algebraMap_mem _ _) ?_) (neg_mem ?_) ?_ (Subalgebra.zero_mem _)
    · exact mem_siteC L (L.pb_pb l m) (by rw [L.pb_cb m l, if_neg (Ne.symm hlm), add_zero])
        (by rw [L.pb_cbi m l, if_neg (Ne.symm hlm), sub_zero])
    · refine mem_siteC L ?_ (fc L (m_cb L l) (m_cb L m)) (fc L (m_cbi L l) (m_cb L m))
      rw [L.pb_cb, if_neg hlm, add_zero]
    · refine mem_siteC L ?_ (fc L (m_cb L l) (m_cbi L m)) (fc L (m_cbi L l) (m_cbi L m))
      rw [L.pb_cbi, if_neg hlm, sub_zero]
  have hz := hm k n
  rw [siteC, Subalgebra.mem_centralizer_iff] at hz
  have hl : L.Tvl y l ∈ matSub (Subalgebra.centralizer ℂ {(L.Tvl y' m) k n}) (Fin 2) := by
    refine matrix_two_mem_sub _ _ _ _ _ (sub_mem (Subalgebra.algebraMap_mem _ _) ?_) (neg_mem ?_) ?_ (Subalgebra.zero_mem _) <;>
    · rw [Subalgebra.mem_centralizer_iff]; intro w hw; rw [Set.mem_singleton_iff.1 hw]
      first | exact (hz _ (by simp)).symm
  have := (Subalgebra.mem_centralizer_iff _).1 (hl i j) _ rfl
  exact this.symm

theorem Tvprod_transpose (y : ℂ) : (L.Tvprod y)ᵀ = (List.ofFn fun l => (L.Tvl y l)ᵀ).prod := by
  unfold LevelData.Tvprod
  rw [transpose_list_prod, List.map_reverse, List.reverse_reverse, List.map_ofFn]
  · rfl
  · rw [List.pairwise_reverse, List.pairwise_ofFn]
    intro l m hlm i j k n
    exact site_entries L m l hlm.ne' y y i j k n

end Abs

end

end Formalism.FourierDecayAlt.P.MAx3.Q

end S_Q_Q3

section S_Q_Q4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Q

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Matrix Formalism.FourierDecayAlt.P.MAx3.H
open Formalism.FourierDecayAlt.P.MAx2.Jet (matSub matrix_two_mem_sub)

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem star_all : (∀ l, star (L.p l) = -L.pb l) ∧ (∀ l, star (L.c l) = L.cb l) ∧ (∀ l, star (L.ci l) = L.cbi l) ∧
    (∀ l, star (L.cb l) = L.c l) ∧ (∀ l, star (L.cbi l) = L.ci l) ∧ star L.ζ = L.ζb ∧ star L.ζb = L.ζ ∧
    star L.GG = L.GG ∧ star L.GGi = L.GGi ∧ star L.nab = L.nabs ∧ star L.nabs = L.nab := by
  have : Fact ((DQ P).Laws P.TT) := ⟨hLaw⟩
  have hs := Formalism.FourierDecayAlt.P.MAx1.starGens P (DQ P)
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, hn, hns, -⟩ := hL
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp, hpb]; exact (hs.1 l).2.2
  · rw [hc, hcb]; exact (hs.1 l).1
  · rw [hci, hcbi]; exact (hs.1 l).2.1
  · rw [hc, hcb, ← (hs.1 l).1, star_star]
  · rw [hci, hcbi, ← (hs.1 l).2.1, star_star]
  · rw [hz, hzb]; exact hs.2.1
  · rw [hz, hzb, ← hs.2.1, star_star]
  · rw [hg]; exact hs.2.2.2.1
  · rw [hgi]; exact hs.2.2.2.2.1
  · rw [hn, hns]; exact hs.2.2.2.2.2
  · rw [hn, hns, ← hs.2.2.2.2.2, star_star]

theorem star_alg (z : ℂ) : star (algebraMap ℂ (A P (DQ P)) z) = algebraMap ℂ (A P (DQ P)) (starRingEnd ℂ z) := by
  rw [← algebraMap_star_comm]; rfl

theorem star_Tl (y : ℂ) (l : Fin P.r) : (L.Tl y l)ᴴ = (L.Tvl (starRingEnd ℂ y) l)ᵀ := by
  obtain ⟨hp, hc, hci, -⟩ := star_all hL hLaw
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, LevelData.Tvl, conjTranspose_apply, star_add, star_neg, hp, hc, hci, star_alg hL hLaw, sub_eq_add_neg]

theorem star_Tprod (y : ℂ) : (L.Tprod y)ᴴ = (L.Tvprod (starRingEnd ℂ y))ᵀ := by
  rw [Tvprod_transpose]
  unfold LevelData.Tprod
  rw [conjTranspose_list_prod, List.map_reverse, List.reverse_reverse, List.map_ofFn]
  congr 1
  exact congrArg List.ofFn (funext fun l => star_Tl hL hLaw y l)

theorem star_Ar (y : ℂ) : star (L.Ar y) = L.Avr (starRingEnd ℂ y) := by
  have h := congrArg (fun M => M 0 0) (star_Tprod hL hLaw y)
  simpa [conjTranspose_apply, LevelData.Ar, LevelData.Avr] using h

theorem star_Br (y : ℂ) : star (L.Br y) = L.Bvr (starRingEnd ℂ y) := by
  have h := congrArg (fun M => M 0 1) (star_Tprod hL hLaw y)
  simpa [conjTranspose_apply, LevelData.Br, LevelData.Bvr] using h

theorem star_Dr : star L.Dr = L.Drb := by
  obtain ⟨-, hc, -⟩ := star_all hL hLaw
  unfold LevelData.Dr LevelData.Drb
  rw [star_list_prod', List.map_ofFn]
  have : (star ∘ L.c) = L.cb := funext hc
  rw [this, rev_prod L]
  intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF L (m_cb L l)

theorem star_Ahat (y : ℂ) : star (L.Ahat y) = L.Ahatv (starRingEnd ℂ y - 1) := by
  unfold LevelData.Ahat LevelData.Ahatv
  rw [star_mul, star_Ar hL hLaw, star_Dr hL hLaw, Avr_Drb]

end

end Formalism.FourierDecayAlt.P.MAx3.Q

end S_Q_Q4

section S_Q_Q5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Q

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Matrix Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

section Abs
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem raising_constant_commute_sites (Y : ℂ) : (∀ l, L.m0 Y * L.pb l = L.pb l * L.m0 Y) ∧ (∀ l, L.m0 Y * L.cb l = L.cb l * L.m0 Y) ∧
    (∀ l, L.m0 Y * L.cbi l = L.cbi l * L.m0 Y) := by
  have hz : ∀ l, L.ζ * L.GGi * L.pb l = L.pb l * (L.ζ * L.GGi) := fun l => by
    rw [mul_assoc, ← L.pb_GGi, ← mul_assoc, ← L.pb_ζ, mul_assoc]
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_⟩
  · unfold LevelData.m0
    rw [sub_mul, mul_sub, neg_mul, mul_neg, ← L.pb_nabs, mul_assoc, hz, ← mul_assoc, ← mul_assoc,
      Algebra.commutes]
    simp only [mul_assoc]
  · unfold LevelData.m0
    have h1 : L.ζ * L.GGi * L.cb l = L.cb l * (L.ζ * L.GGi) :=
      cl_comm L (Subring.mul_mem _ (memζ L) (memF L (m_GGi L))) (memF L (m_cb L l))
    rw [sub_mul, mul_sub, neg_mul, mul_neg, L.nabs_cb, mul_assoc, h1, ← mul_assoc, ← mul_assoc, Algebra.commutes]
    simp only [mul_assoc]
  · unfold LevelData.m0
    have h1 : L.ζ * L.GGi * L.cbi l = L.cbi l * (L.ζ * L.GGi) :=
      cl_comm L (Subring.mul_mem _ (memζ L) (memF L (m_GGi L))) (memF L (m_cbi L l))
    rw [sub_mul, mul_sub, neg_mul, mul_neg, L.nabs_cbi, mul_assoc, h1, ← mul_assoc, ← mul_assoc, Algebra.commutes]
    simp only [mul_assoc]

theorem raising_constant_gamma_shift (Y : ℂ) : L.m0 (Y + 1) * L.GG = L.GG * L.m0 Y := by
  unfold LevelData.m0
  have hζ : L.ζ * L.GGi * L.GG = L.ζ := by rw [mul_assoc, L.GGi_GG, mul_one]
  have hζ' : L.GG * (L.ζ * L.GGi) = L.ζ := by
    rw [← mul_assoc, fc L (m_GG L) (m_ζ L), mul_assoc, L.GG_GGi, mul_one]
  have e : algebraMap ℂ A (Y + 1 - 1 / 2) = algebraMap ℂ A (Y - 1 / 2) + 1 := by
    rw [← map_one (algebraMap ℂ A), ← map_add]; congr 1; ring
  rw [sub_mul, neg_mul, L.nabs_GG, mul_assoc (algebraMap ℂ A _), hζ, mul_sub, mul_neg, ← mul_assoc L.GG,
    ← Algebra.commutes, mul_assoc, hζ', e, add_mul, one_mul]
  abel

end Abs

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem star_lowering_constant (y : ℂ) : star (L.l0 y) = L.m0 (starRingEnd ℂ y + 1) := by
  obtain ⟨-, -, -, -, -, hz, hzb, -, hgi, hn, -⟩ := star_all hL hLaw
  unfold LevelData.l0 LevelData.m0
  rw [star_sub, star_neg, hn, star_mul, star_mul, hzb, hgi, star_alg hL hLaw]
  have hc : L.GGi * L.ζ = L.ζ * L.GGi := fc L (m_GGi L) (m_ζ L)
  rw [hc, ← Algebra.commutes]
  congr 3
  simp only [map_add, map_div₀, map_one, map_ofNat]
  ring

theorem star_raising (y : ℂ) : star (L.R0 y) = L.R0v (starRingEnd ℂ y) := by
  obtain ⟨-, -, -, -, -, -, -, hg, -, -, -⟩ := star_all hL hLaw
  set Y := starRingEnd ℂ y
  unfold LevelData.R0 LevelData.R0v
  rw [star_mul, star_mul, star_add, star_mul, star_Ar hL hLaw, star_Br hL hLaw, star_lowering_constant hL hLaw, hg,
    star_Drb hL hLaw]

  have ha : L.Avr Y * L.m0 (Y + 1) = L.m0 (Y + 1) * L.Avr Y := by
    obtain ⟨h1, h2, h3⟩ := raising_constant_commute_sites L (Y + 1)
    exact ((comm_Tvprod L (L.m0 (Y + 1)) h1 h2 h3 Y).1).symm
  have hGA : L.GG * L.Avr Y = L.Avr Y * L.GG ∧ L.GG * L.Bvr Y = L.Bvr Y * L.GG :=
    comm_Tvprod L L.GG (fun l => (L.pb_GG l).symm) (fun l => fc L (m_GG L) (m_cb L l)) (fun l => fc L (m_GG L) (m_cbi L l)) Y
  have hDA : L.Dr * L.Avr Y = L.Avr Y * L.Dr ∧ L.Dr * L.Bvr Y = L.Bvr Y * L.Dr :=
    comm_Tvprod L L.Dr (fun l => (comm_prod L.c (L.pb l) (fun m => L.pb_c l m)).symm)
      (fun l => cl_comm L (memDr L) (memF L (m_cb L l))) (fun l => cl_comm L (memDr L) (memF L (m_cbi L l))) Y
  have hDm : L.Dr * L.m0 Y = L.m0 Y * L.Dr := by
    unfold LevelData.m0
    have h1 : L.nabs * L.Dr = L.Dr * L.nabs := comm_Dr L (fun l => L.nabs_c l)
    have h2 : L.Dr * (L.ζ * L.GGi) = L.ζ * L.GGi * L.Dr :=
      cl_comm L (memDr L) (Subring.mul_mem _ (memζ L) (memF L (m_GGi L)))
    rw [mul_sub, sub_mul, mul_neg, neg_mul, h1, ← mul_assoc, ← Algebra.commutes, mul_assoc, h2]
    simp only [mul_assoc]
  have hD1 : L.Dr * (L.m0 Y * L.Avr Y + L.Bvr Y) = (L.m0 Y * L.Avr Y + L.Bvr Y) * L.Dr := by
    rw [mul_add, add_mul, ← mul_assoc, hDm, mul_assoc, hDA.1, hDA.2, mul_assoc]
  have hDG : L.Dr * L.GG = L.GG * L.Dr := cl_comm L (memDr L) (memGG L)
  calc (L.Avr Y * L.m0 (Y + 1) + L.Bvr Y) * (L.GG * L.Dr)
      = (L.m0 (Y + 1) * (L.Avr Y * L.GG) + L.Bvr Y * L.GG) * L.Dr := by
        rw [ha]; simp only [add_mul, mul_assoc]
    _ = (L.m0 (Y + 1) * L.GG * L.Avr Y + L.GG * L.Bvr Y) * L.Dr := by
        rw [← hGA.1, ← hGA.2, mul_assoc]
    _ = L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y) * L.Dr := by
        rw [raising_constant_gamma_shift]; simp only [mul_add, mul_assoc]
    _ = L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y) := by
        rw [mul_assoc, ← hD1, ← mul_assoc, ← hDG]

end

end Formalism.FourierDecayAlt.P.MAx3.Q

end S_Q_Q5

section S_AD_AD3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L

noncomputable section

variable (P : M.Par) (L : LevelData (A P (DQ P)) P.r)

def Gen (k : ℕ) : Set (A P (DQ P)) :=
  {x | ∃ (φ : ℝ → ℝ) (b : A P (DQ P)) (v : List (A P (DQ P))), admitted φ ∧ b ∈ Submonoid.closure (bddSet P L) ∧
    (∀ h ∈ v, h ∈ hatSet P L) ∧ v.length ≤ k ∧ x = Ph P φ * b * v.prod}

def Z (k : ℕ) : Submodule ℂ (A P (DQ P)) := Submodule.span ℂ (Gen P L k)

def HB : Submodule ℂ (A P (DQ P)) :=
  Submodule.span ℂ {x | ∃ b h, b ∈ Submonoid.closure (bddSet P L) ∧ h ∈ hatSet P L ∧ x = b * h}

theorem Z_mono {k k' : ℕ} (h : k ≤ k') : Z P L k ≤ Z P L k' :=
  Submodule.span_mono fun x ⟨φ, b, v, h1, h2, h3, h4, e⟩ => ⟨φ, b, v, h1, h2, h3, h4.trans h, e⟩

variable {P L}

theorem mem_hatSet {X : A P (DQ P)} : X ∈ hatSet P L ↔
    (∃ y, X = L.Ahat y) ∨ (∃ y, X = L.R0 y) ∨ (∃ y, X = L.Ahatv y) ∨ (∃ y, X = L.R0v y) := by
  unfold hatSet
  simp only [Set.mem_union, Set.mem_range]
  constructor
  · rintro (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
    exacts [Or.inl ⟨y, rfl⟩, Or.inr (Or.inl ⟨y, rfl⟩), Or.inr (Or.inr (Or.inl ⟨y, rfl⟩)),
      Or.inr (Or.inr (Or.inr ⟨y, rfl⟩))]
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩)
    exacts [Or.inl (Or.inl (Or.inl ⟨y, rfl⟩)), Or.inl (Or.inl (Or.inr ⟨y, rfl⟩)), Or.inl (Or.inr ⟨y, rfl⟩),
      Or.inr ⟨y, rfl⟩]

variable (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem star_hat {X : A P (DQ P)} (hX : X ∈ hatSet P L) : star X ∈ hatSet P L := by
  rcases mem_hatSet.1 hX with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rw [Q.star_Ahat hL hLaw]; exact mem_hatSet.2 (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))
  · rw [Q.star_raising hL hLaw]; exact mem_hatSet.2 (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
  · have e : L.Ahatv y = star (L.Ahat (starRingEnd ℂ y + 1)) := by
      rw [Q.star_Ahat hL hLaw]; congr 1; simp
    rw [e, star_star]; exact mem_hatSet.2 (Or.inl ⟨_, rfl⟩)
  · have e : L.R0v y = star (L.R0 (starRingEnd ℂ y)) := by
      rw [Q.star_raising hL hLaw]; congr 1; simp
    rw [e, star_star]; exact mem_hatSet.2 (Or.inr (Or.inl ⟨_, rfl⟩))

theorem hat_mul_b {h b : A P (DQ P)} (hh : h ∈ hatSet P L) (hb : b ∈ Submonoid.closure (bddSet P L)) :
    h * b ∈ HB P L := by
  have hS := H.hyp_model hL hLaw
  have hV := K.hypV_model hL hLaw
  have gen : ∀ b' h', b' ∈ Submonoid.closure (bddSet P L) → h' ∈ hatSet P L → b' * h' ∈ HB P L :=
    fun b' h' h1 h2 => Submodule.subset_span ⟨b', h', h1, h2, rfl⟩
  have sumA : ∀ (ts : List (ℂ × A P (DQ P) × ℂ)), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum ∈ HB P L := by
    intro ts hts
    induction ts with
    | nil => simp
    | cons a ts ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (gen _ _ (hts a (by simp))
        (mem_hatSet.2 (Or.inl ⟨_, rfl⟩)))) (ih fun x hx => hts x (by simp [hx]))
  have sumV : ∀ (ts : List (ℂ × A P (DQ P) × ℂ)), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum ∈ HB P L := by
    intro ts hts
    induction ts with
    | nil => simp
    | cons a ts ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (gen _ _ (hts a (by simp))
        (mem_hatSet.2 (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))) (ih fun x hx => hts x (by simp [hx]))
  rcases mem_hatSet.1 hh with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨t, ht⟩ := hS.ahat b hb
    rw [ht]; exact gen _ _ hb (mem_hatSet.2 (Or.inl ⟨_, rfl⟩))
  · obtain ⟨t, ts, hts, e⟩ := hS.r0 b hb y
    rw [e]; exact Submodule.add_mem _ (gen _ _ hb (mem_hatSet.2 (Or.inr (Or.inl ⟨_, rfl⟩)))) (sumA ts hts)
  · obtain ⟨t, ht⟩ := hV.ahatv b hb
    rw [ht]; exact gen _ _ hb (mem_hatSet.2 (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
  · obtain ⟨t, ts, hts, e⟩ := hV.r0v b hb y
    rw [e]; exact Submodule.add_mem _ (gen _ _ hb (mem_hatSet.2 (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))))) (sumV ts hts)

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD3

section S_AD_AD4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r}

theorem Phi_ld {φ ψ : ℝ → ℝ} (p : ℕ) (h : ∀ x, 0 < x → ψ x = LE.ld p φ x) : Phi P ψ 0 = Phi P φ p := by
  unfold Phi
  congr 1
  funext q
  rw [ld_zero (Gq_pos P q), h _ (Gq_pos P q)]

theorem Fq_ld {φ ψ : ℝ → ℝ} (p : ℕ) (h : ∀ x, 0 < x → ψ x = LE.ld p φ x) : Fq P ψ 0 = Fq P φ p := by
  unfold Fq; rw [Phi_ld p h]

variable (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTT hL hLaw

theorem leib_hat {X : A P (DQ P)} (hX : X ∈ hatSet P L) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) :
    ∃ (d : ℕ) (σ : ℝ) (a : ℕ → A P (DQ P)), (∀ k, a k ∈ Submodule.span ℂ (hatSet P L)) ∧
      X * Ph P φ = ∑ p ∈ Finset.range (d + 1), sc P (DQ P) (Fq P φ p) * (((σ : ℂ) ^ p) • a p) := by
  have hspan : ∀ (F : ℂ → A P (DQ P)) (y : ℂ) (d : ℕ), (∀ t, F t ∈ hatSet P L) →
      Submodule.span ℂ (Set.range fun n : Fin (d + 1) => F (y + n)) ≤ Submodule.span ℂ (hatSet P L) :=
    fun F y d hF => Submodule.span_le.2 (by rintro _ ⟨n, rfl⟩; exact Submodule.subset_span (hF _))
  rcases mem_hatSet.1 hX with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨a, ha, e⟩ := leib_gen P L.Ahat y 1 P.r (G.Ahat_poly P L y)
      (fun s => by rw [(G.conj_hat hTT hL s y).1]; congr 1; push_cast; ring)
      (fun t => (hats_mem_jet_algebra hL t).1) φ hφ
    exact ⟨P.r, 1, a, fun k => hspan L.Ahat y P.r (fun t => mem_hatSet.2 (Or.inl ⟨t, rfl⟩)) (ha k), e⟩
  · obtain ⟨a, ha, e⟩ := leib_gen P L.R0 y 1 (P.r + 1) (G.raising_operator_polynomial P L y)
      (fun s => by rw [(G.conj_hat hTT hL s y).2]; congr 1; push_cast; ring)
      (fun t => (hats_mem_jet_algebra hL t).2.1) φ hφ
    exact ⟨P.r + 1, 1, a, fun k => hspan L.R0 y (P.r + 1) (fun t => mem_hatSet.2 (Or.inr (Or.inl ⟨t, rfl⟩))) (ha k), e⟩
  · obtain ⟨a, ha, e⟩ := leib_gen P L.Ahatv y (-1) P.r (Ahatv_poly P L y)
      (fun s => by rw [(conj_hatv hTT hL s y).1]; congr 1; push_cast; ring)
      (fun t => (hats_mem_jet_algebra hL t).2.2.1) φ hφ
    exact ⟨P.r, -1, a, fun k => hspan L.Ahatv y P.r
      (fun t => mem_hatSet.2 (Or.inr (Or.inr (Or.inl ⟨t, rfl⟩)))) (ha k), e⟩
  · obtain ⟨a, ha, e⟩ := leib_gen P L.R0v y (-1) (P.r + 1) (raising_variant_polynomial P L y)
      (fun s => by rw [(conj_hatv hTT hL s y).2]; congr 1; push_cast; ring)
      (fun t => (hats_mem_jet_algebra hL t).2.2.2) φ hφ
    exact ⟨P.r + 1, -1, a, fun k => hspan L.R0v y (P.r + 1)
      (fun t => mem_hatSet.2 (Or.inr (Or.inr (Or.inr ⟨t, rfl⟩)))) (ha k), e⟩

theorem span_hat_mul_b {a b : A P (DQ P)} (ha : a ∈ Submodule.span ℂ (hatSet P L))
    (hb : b ∈ Submonoid.closure (bddSet P L)) : a * b ∈ HB P L := by
  induction ha using Submodule.span_induction with
  | mem h hh => exact hat_mul_b hL hLaw hh hb
  | zero => simp
  | add x y _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h1 => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h1

theorem Ph_HB_mem {ψ : ℝ → ℝ} (hψ : admitted ψ) {x : A P (DQ P)} (hx : x ∈ HB P L) {v : List (A P (DQ P))}
    (hv : ∀ h ∈ v, h ∈ hatSet P L) {k : ℕ} (hk : v.length ≤ k) : Ph P ψ * x * v.prod ∈ Z P L (k + 1) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, h, hb, hh, rfl⟩ := hy
    refine Submodule.subset_span ⟨ψ, b, h :: v, hψ, hb, fun h' hh' => ?_, by simp [hk], by simp [mul_assoc]⟩
    rcases List.mem_cons.1 hh' with rfl | hh'
    exacts [hh, hv h' hh']
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add, add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h1 => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c h1

theorem hatPast {X : A P (DQ P)} (hX : X ∈ hatSet P L) {k : ℕ} {z : A P (DQ P)} (hz : z ∈ Z P L k) :
    X * z ∈ Z P L (k + 1) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, b, v, hφ, hb, hv, hlen, rfl⟩ := hx
    obtain ⟨d, σ, a, ha, e⟩ := leib_hat hTT hL hLaw hX hφ.1
    rw [← mul_assoc, ← mul_assoc, e, Finset.sum_mul, Finset.sum_mul]
    refine Submodule.sum_mem _ fun p _ => ?_
    obtain ⟨ψ, hψ, hψe⟩ := admissible_log_derivative hφ p
    rw [← Fq_ld p hψe]
    have : sc P (DQ P) (Fq P ψ 0) = Ph P ψ := rfl
    rw [this, mul_assoc (Ph P ψ)]
    exact Ph_HB_mem hTT hL hLaw hψ (span_hat_mul_b hTT hL hLaw (Submodule.smul_mem _ _ (ha p)) hb) hv hlen
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h1 => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD4

section S_AD_AD5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L MeasureTheory
open ComplexConjugate

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}

theorem act_Ph {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (y : A P (DQ P)) :
    actA P (Ph P φ * y) j = fun π => toSm P (fun q => ((φ (Gq P q) : ℝ) : ℂ)) * actA P y j π := by
  funext π
  rw [F.actA_mul]
  show actA P (sc P (DQ P) (Fq P φ 0)) (actA P y j) π = _
  rw [MAx2.R2.act_sc]
  show Phi P φ 0 * actA P y j π = _
  rw [Phi0_eq P hφ]

theorem jadj_bridge {m : ℕ} (hA : JAdj P L j m) {φ : ℝ → ℝ} (hφ : admitted φ) {b : A P (DQ P)}
    (hb : b ∈ Submonoid.closure (bddSet P L)) {X : A P (DQ P)} (hX : X ∈ hatSet P L) {v w : List (A P (DQ P))}
    (hvw : v.length + w.length + 1 ≤ m) (hv : ∀ a ∈ v, a ∈ hatSet P L) (hw : ∀ a ∈ w, a ∈ hatSet P L) :
    ipA P (actA P (X * (Ph P φ * b * v.prod)) j) (actA P w.prod j) =
      ipA P (actA P (Ph P φ * b * v.prod) j) (actA P (star X * w.prod) j) := by
  obtain ⟨hs, ⟨ε, hε, h0⟩, hbd⟩ := hφ
  rw [F.actA_mul, mul_assoc, act_Ph hs]
  exact hA φ ε hε hs h0 hbd b hb X hX v w hvw (fun a ha => by
    rcases List.mem_append.1 ha with ha | ha; exacts [hv a ha, hw a ha])

theorem star_word_mem (hTT : 0 ≤ P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT) :
    ∀ (W : List (A P (DQ P))), (∀ h ∈ W, h ∈ hatSet P L) → ∀ {k : ℕ} {z : A P (DQ P)}, z ∈ Z P L k →
      star W.prod * z ∈ Z P L (k + W.length)
  | [], _, k, z, hz => by simpa using hz
  | X :: W, hW, k, z, hz => by
    rw [List.prod_cons, star_mul, mul_assoc]
    have h1 := hatPast hTT hL hLaw (star_hat hL hLaw (hW X (by simp))) hz
    have h2 := star_word_mem hTT hL hLaw W (fun h hh => hW h (by simp [hh])) h1
    simpa [Nat.add_assoc, Nat.add_comm 1] using h2

theorem ev_gen {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) {b : A P (DQ P)} {C : ℝ} (hb : I4.PW b C) :
    ∃ Mx : Qp P.r P.TT → Matrix (M.Ty P) (M.Ty P) ℂ, (∀ q π π', ‖Mx q π π'‖ ≤ C) ∧
      ∀ (v : List (A P (DQ P))) q π, evQ P (actA P (Ph P φ * b * v.prod) j π) q =
        ((φ (Gq P q) : ℝ) : ℂ) * ∑ π', Mx q π π' * evQ P (actA P v.prod j π') q := by
  obtain ⟨-, Mx, hM, e⟩ := hb
  refine ⟨Mx, hM, fun v q π => ?_⟩
  rw [mul_assoc, act_Ph hφ]
  show evQ P (toSm P (fun q => ((φ (Gq P q) : ℝ) : ℂ)) * actA P (b * v.prod) j π) q = _
  rw [MAx2.Jet.evQ_mul, ← Phi0_eq P hφ, eval_cutoff_operator_zero P hφ, F.actA_mul, e]

theorem sq_bound (a b : ℝ) : a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

theorem int_gen {m : ℕ} (hD : JDecay P L j m) {φ : ℝ → ℝ} (hφ : admitted φ) {b : A P (DQ P)} {C : ℝ} (hb : I4.PW b C)
    {v W : List (A P (DQ P))} (hv : ∀ a ∈ v, a ∈ hatSet P L) (hW : ∀ a ∈ W, a ∈ hatSet P L)
    (hvl : v.length ≤ m) (hWl : W.length ≤ m) (π : M.Ty P) :
    Integrable (fun q => evQ P (actA P (Ph P φ * b * v.prod) j π) q * conj (evQ P (actA P W.prod j π) q))
      (mu0 P.r P.TT) := by
  obtain ⟨Mx, hM, e⟩ := ev_gen (j := j) hφ.1 hb
  obtain ⟨Cφ, hCφ⟩ := hφ.2.2 0
  have hC0 : 0 ≤ C := hb.1
  have hg : Integrable (fun q => |Cφ| * C * ∑ π', (‖evQ P (actA P v.prod j π') q‖ ^ 2 +
      ‖evQ P (actA P W.prod j π) q‖ ^ 2)) (mu0 P.r P.TT) :=
    (integrable_finset_sum _ fun π' _ => (hD v hvl hv π').add (hD W hWl hW π)).const_mul _
  refine hg.mono' (((MAx3.evQ_cont P _).mul (Complex.continuous_conj.comp (MAx3.evQ_cont P _))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun q => ?_)
  have h1 : |φ (Gq P q)| ≤ |Cφ| := by
    have := hCφ _ (Gq_pos P q); rw [ld_zero (Gq_pos P q)] at this; exact this.trans (le_abs_self _)
  have h2 : ‖∑ π', Mx q π π' * evQ P (actA P v.prod j π') q‖ ≤ ∑ π', C * ‖evQ P (actA P v.prod j π') q‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun π' _ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM q π π') (norm_nonneg _))
  rw [e v q π, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  calc |φ (Gq P q)| * ‖∑ π', Mx q π π' * evQ P (actA P v.prod j π') q‖ * ‖evQ P (actA P W.prod j π) q‖
      ≤ |Cφ| * (∑ π', C * ‖evQ P (actA P v.prod j π') q‖) * ‖evQ P (actA P W.prod j π) q‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)) (norm_nonneg _)
    _ = |Cφ| * C * ∑ π', ‖evQ P (actA P v.prod j π') q‖ * ‖evQ P (actA P W.prod j π) q‖ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ |Cφ| * C * ∑ π', (‖evQ P (actA P v.prod j π') q‖ ^ 2 + ‖evQ P (actA P W.prod j π) q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun π' _ => sq_bound _ _)
          (mul_nonneg (abs_nonneg _) hC0)

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD5

section S_Z_Z4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.I4 Formalism.FourierDecayAlt.P.MAx3.AD Formalism.FourierDecayAlt.P.MAx3.L
open Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable {P : M.Par}

def IsFnP (x : A P (DQ P)) : Prop := ∃ F Fb : SmQ P.r P.TT, x = sc P (DQ P) ((DQ P).fnP F Fb)

theorem isFnP_mul {x y : A P (DQ P)} (hx : IsFnP x) (hy : IsFnP y) : IsFnP (x * y) := by
  obtain ⟨F, Fb, rfl⟩ := hx; obtain ⟨H, Hb, rfl⟩ := hy
  exact ⟨F * H, Fb * Hb, by rw [Formalism.FourierDecayAlt.P.MAx3.G.sc_mul P]; exact congrArg (sc P (DQ P)) (MAx1.multiplierPair_mul (DQ P) F Fb H Hb)⟩

theorem isFnP_comm {x y : A P (DQ P)} (hx : IsFnP x) (hy : IsFnP y) : x * y = y * x := by
  obtain ⟨F, Fb, rfl⟩ := hx; obtain ⟨H, Hb, rfl⟩ := hy
  rw [Formalism.FourierDecayAlt.P.MAx3.G.sc_mul P, Formalism.FourierDecayAlt.P.MAx3.G.sc_mul P]
  congr 1
  refine (MAx1.multiplierPair_mul (DQ P) F Fb H Hb).trans ((congrArg₂ (DQ P).fnP (mul_comm F H) (mul_comm Fb Hb)).trans
    (MAx1.multiplierPair_mul (DQ P) H Hb F Fb).symm)

theorem isFnP_Ph (φ : ℝ → ℝ) : IsFnP (Ph P φ) := ⟨_, _, rfl⟩
theorem isFnP_Gs (t : ℝ) : IsFnP (G.Gs P t) := ⟨_, _, rfl⟩

theorem isFnP_pow {x : A P (DQ P)} (hx : IsFnP x) (n : ℕ) : IsFnP (x ^ n) := by
  induction n with
  | zero =>
    refine ⟨(1 : (DQ P).R), (1 : (DQ P).R), ?_⟩
    rw [pow_zero, MAx1.multiplierPair_one]
    show (1 : A P (DQ P)) = Matrix.scalar (M.Ty P) 1
    rw [map_one]
  | succ n ih => rw [pow_succ]; exact isFnP_mul ih hx

variable {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hL

theorem fns_fnP {x : A P (DQ P)} (hx : x ∈ L.fns) : IsFnP x := by
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, -⟩ := hL
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
  · rw [hc]; exact ⟨_, _, rfl⟩
  · rw [hci]; exact ⟨_, _, rfl⟩
  · rw [hcb]; exact ⟨_, _, rfl⟩
  · rw [hcbi]; exact ⟨_, _, rfl⟩
  · rw [hz]; exact ⟨_, _, rfl⟩
  · rw [hzi]; exact ⟨_, _, rfl⟩
  · rw [hzb]; exact ⟨_, _, rfl⟩
  · rw [hzbi]; exact ⟨_, _, rfl⟩
  · rw [hg]; exact ⟨_, _, rfl⟩
  · rw [hgi]; exact ⟨_, _, rfl⟩

theorem isMultiplierPair_list_prod {l : List (A P (DQ P))} (h : ∀ x ∈ l, x ∈ L.fns) : IsFnP l.prod := by
  induction l with
  | nil =>
    refine ⟨(1 : (DQ P).R), (1 : (DQ P).R), ?_⟩
    rw [List.prod_nil, MAx1.multiplierPair_one]
    show (1 : A P (DQ P)) = Matrix.scalar (M.Ty P) 1
    rw [map_one]
  | cons a l ih => rw [List.prod_cons]; exact isFnP_mul (fns_fnP hL (h a (by simp))) (ih fun x hx => h x (by simp [hx]))

theorem fnP_D : IsFnP L.D ∧ IsFnP L.Di ∧ IsFnP L.Db ∧ IsFnP L.Dbi ∧ IsFnP L.Dr ∧ IsFnP L.Dri ∧ IsFnP L.Drb ∧
    IsFnP L.Drbi := by
  have hDr : IsFnP L.Dr := isMultiplierPair_list_prod hL fun x hx => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact m_c L l
  have hDri : IsFnP L.Dri := isMultiplierPair_list_prod hL fun x hx => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact m_ci L l
  have hDrb : IsFnP L.Drb := isMultiplierPair_list_prod hL fun x hx => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact m_cb L l
  have hDrbi : IsFnP L.Drbi := isMultiplierPair_list_prod hL fun x hx => by obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact m_cbi L l
  exact ⟨isFnP_mul hDr (fns_fnP hL (m_ζ L)), isFnP_mul (fns_fnP hL (m_ζi L)) hDri,
    isFnP_mul hDrb (fns_fnP hL (m_ζb L)), isFnP_mul (fns_fnP hL (m_ζbi L)) hDrbi, hDr, hDri, hDrb, hDrbi⟩

variable (hLaw : (DQ P).Laws P.TT)
include hLaw

theorem SB_comm_fnP {b : A P (DQ P)} (hb : b ∈ SB L) {x : A P (DQ P)} (hx : IsFnP x) : b * x = x * b := by
  obtain ⟨F, Fb, rfl⟩ := hx
  have hSC : sc P (DQ P) ((DQ P).fnP F Fb) ∈ SC P := sc_memSC P _
  have hDG : sc P (DQ P) ((DQ P).fnP F Fb) ∈ DG P := sc_memDG P _
  have hfx : IsFnP (sc P (DQ P) ((DQ P).fnP F Fb)) := ⟨F, Fb, rfl⟩
  induction hb using Submonoid.closure_induction with
  | one => simp
  | mul a c _ _ h1 h2 => rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  | mem a ha =>
    obtain ⟨hD, hDi, hDb, hDbi, hDr, hDri, hDrb, hDrbi⟩ := fnP_D hL
    rcases ha with (((ha | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact isFnP_comm (fns_fnP hL (m_ζi L)) hfx
      · exact isFnP_comm (fns_fnP hL (m_ζbi L)) hfx
      · exact isFnP_comm (isFnP_mul hD hDbi) hfx
      · exact isFnP_comm (isFnP_mul hDb hDi) hfx
    · exact kap_comm_DG P f hDG
    · show L.Drb * L.Dri * SS P (DQ P) i * _ = _ * (L.Drb * L.Dri * SS P (DQ P) i)
      rw [mul_assoc, SS_comm_SC P i hSC, ← mul_assoc, isFnP_comm (isFnP_mul hDrb hDri) hfx, mul_assoc]
    · show star (L.Drb * L.Dri * SS P (DQ P) i) * _ = _ * star (L.Drb * L.Dri * SS P (DQ P) i)
      rw [starSSn_eq hL hLaw, mul_assoc, isFnP_comm (isFnP_mul hDr hDrbi) hfx, ← mul_assoc, SSs_comm_SC i hSC,
        mul_assoc]

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z4

section S_Z_Z5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.I4 Formalism.FourierDecayAlt.P.MAx3.AD Formalism.FourierDecayAlt.P.MAx3.L
open Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r}

theorem Ph_memZ {φ : ℝ → ℝ} (hφ : admitted φ) : Ph P φ ∈ Z P L 0 :=
  Submodule.subset_span ⟨φ, 1, [], hφ, Submonoid.one_mem _, by simp, by simp, by simp⟩

variable (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem word_memZ : ∀ (H : List (A P (DQ P))), (∀ h ∈ H, h ∈ hatSet P L) → ∀ {k : ℕ} {z : A P (DQ P)},
    z ∈ Z P L k → H.prod * z ∈ Z P L (k + H.length)
  | [], _, k, z, hz => by simpa using hz
  | X :: H, hH, k, z, hz => by
    rw [List.prod_cons, mul_assoc]
    have h1 := word_memZ H (fun h hh => hH h (by simp [hh])) hz
    have h2 := hatPast hTTp.le hL hLaw (hH X (by simp)) h1
    simpa [Nat.add_assoc, Nat.add_comm 1] using h2

theorem SB_memZ {b : A P (DQ P)} (hb : b ∈ SB L) {k : ℕ} {z : A P (DQ P)} (hz : z ∈ Z P L k) : b * z ∈ Z P L k := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, b', v, hφ, hb', hv, hlen, rfl⟩ := hx
    have e : b * (Ph P φ * b' * v.prod) = Ph P φ * (b * b') * v.prod := by
      rw [← mul_assoc, ← mul_assoc, SB_comm_fnP hL hLaw hb (isFnP_Ph φ)]; simp only [mul_assoc]
    rw [e]; exact Submodule.subset_span ⟨φ, b * b', v, hφ, Submonoid.mul_mem _ hb hb', hv, hlen, rfl⟩
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h1 => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1

theorem Ph_memZ_mul {χ : ℝ → ℝ} (hχ : admitted χ) {k : ℕ} {z : A P (DQ P)} (hz : z ∈ Z P L k) : Ph P χ * z ∈ Z P L k := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, b', v, hφ, hb', hv, hlen, rfl⟩ := hx
    have e : Ph P χ * (Ph P φ * b' * v.prod) = Ph P (fun x => χ x * φ x) * b' * v.prod := by
      rw [← mul_assoc, ← mul_assoc, Ph_mul P hχ.1 hφ.1]
    rw [e]; exact Submodule.subset_span ⟨_, b', v, isAdmissibleSplittingCharPair_mul_twist hχ hφ, hb', hv, hlen, rfl⟩
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h1 => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1

theorem Gs_memZ {k : ℕ} {z : A P (DQ P)} (hz : z ∈ Z P L k) : G.Gs P (-1) * z ∈ Z P L k := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, b', v, hφ, hb', hv, hlen, rfl⟩ := hx
    have e : G.Gs P (-1) * (Ph P φ * b' * v.prod) = Ph P (fun x => φ x * x ^ (-1 : ℝ)) * b' * v.prod := by
      rw [← mul_assoc, ← mul_assoc, isFnP_comm (isFnP_Gs (-1)) (isFnP_Ph φ), Ph_Gs P hφ.1]
    rw [e]; exact Submodule.subset_span ⟨_, b', v, admissible_mul_rpow hφ (by norm_num), hb', hv, hlen, rfl⟩
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h1 => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1

theorem Gspow_memZ (n : ℕ) {k : ℕ} {z : A P (DQ P)} (hz : z ∈ Z P L k) : G.Gs P (-1) ^ n * z ∈ Z P L k := by
  induction n with
  | zero => simpa using hz
  | succ n ih => rw [pow_succ', mul_assoc]; exact Gs_memZ hTTp hL hLaw ih

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z5

section S_Z_Z6

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.I4 Formalism.FourierDecayAlt.P.MAx3.AD Formalism.FourierDecayAlt.P.MAx3.L
open Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem star_more : star L.ζi = L.ζbi ∧ star L.ζbi = L.ζi ∧ star L.Di = L.Dbi ∧ star L.Dbi = L.Di ∧
    star L.D = L.Db ∧ star L.Db = L.D := by
  have : Fact ((DQ P).Laws P.TT) := ⟨hLaw⟩
  have hs := Formalism.FourierDecayAlt.P.MAx1.starGens P (DQ P)
  have hL' := hL
  obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, -⟩ := hL'
  have h1 : star L.ζi = L.ζbi := by rw [hzi, hzbi]; exact hs.2.2.1
  have h2 : star L.ζbi = L.ζi := by rw [← h1, star_star]
  have hDr := Q.star_Dr hL hLaw
  have hDri := H.star_Dri hL hLaw
  have hDrb : star L.Drb = L.Dr := by rw [← hDr, star_star]
  have hDrbi : star L.Drbi = L.Dri := by rw [← hDri, star_star]
  obtain ⟨-, -, -, -, -, hzs, hzbs, -⟩ := Q.star_all hL hLaw
  have c1 := cl_comm L (memDri L) (memζi L)
  have c2 := cl_comm L (memDrbi L) (memζbi L)
  have c3 := cl_comm L (memζb L) (memDrb L)
  have c4 := cl_comm L (memζ L) (memDr L)
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · unfold LevelData.Di LevelData.Dbi; rw [star_mul, hDri, h1, c2]
  · unfold LevelData.Di LevelData.Dbi; rw [star_mul, hDrbi, h2, c1]
  · unfold LevelData.D LevelData.Db; rw [star_mul, hzs, hDr, c3]
  · unfold LevelData.D LevelData.Db; rw [star_mul, hzbs, hDrb, c4]

theorem star_SB {b : A P (DQ P)} (hb : b ∈ SB L) : star b ∈ SB L := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := star_more hL hLaw
  have gen : ∀ {x}, x ∈ bddSet P L → x ∈ SB L := fun h => Submonoid.subset_closure h
  induction hb using Submonoid.closure_induction with
  | one => simp
  | mul a c _ _ ha hc => rw [star_mul]; exact Submonoid.mul_mem _ hc ha
  | mem a ha =>
    rcases ha with (((ha | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · rw [h1]; exact gen (Or.inl (Or.inl (Or.inl (by simp))))
      · rw [h2]; exact gen (Or.inl (Or.inl (Or.inl (by simp))))
      · rw [star_mul, h4, h5]
        rw [show L.Di * L.Db = L.Db * L.Di from cl_comm L (memDi L) (memDb L)]
        exact gen (Or.inl (Or.inl (Or.inl (by simp))))
      · rw [star_mul, h3, h6]
        rw [show L.Dbi * L.D = L.D * L.Dbi from cl_comm L (memDbi L) (memD L)]
        exact gen (Or.inl (Or.inl (Or.inl (by simp))))
    · have : star (kap P (DQ P) f) = kap P (DQ P) (fun π => starRingEnd ℂ (f π)) := by
        have e : ∀ g : M.Ty P → ℂ, kap P (DQ P) g = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (g π) :=
          fun g => rfl
        rw [e, e]
        ext π π'
        rw [Matrix.star_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
        by_cases h : π = π'
        · subst h; simp [← algebraMap_star_comm]
        · simp [h, Ne.symm h]
      rw [this]; exact gen (Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))
    · exact gen (Or.inr ⟨i, hi, rfl⟩)
    · show star (star (L.Drb * L.Dri * SS P (DQ P) i)) ∈ SB L
      rw [star_star]; exact gen (Or.inl (Or.inr ⟨i, hi, rfl⟩))

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z6

section S_Z_Z7

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.I4 Formalism.FourierDecayAlt.P.MAx3.AD Formalism.FourierDecayAlt.P.MAx3.L
open Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

theorem mid_id {R : Type} [Ring R] (s k t u w v : R) (hus : u * s = s * u) (hkt : (u * w) * (k * t) = (k * t) * (u * w)) :
    u * s * (w * k * (t * v)) = (s * k * t) * (u * w * v) := by
  calc u * s * (w * k * (t * v)) = s * u * (w * k * (t * v)) := by rw [hus]
    _ = s * ((u * w) * (k * t)) * v := by simp only [mul_assoc]
    _ = s * ((k * t) * (u * w)) * v := by rw [hkt]
    _ = (s * k * t) * (u * w * v) := by simp only [mul_assoc]

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem DWD_pow (N : ℕ) : L.Di ^ N * (L.ζ * L.ζb * L.GGi) ^ N * L.Dbi ^ N = G.Gs P (-1) ^ N := by
  obtain ⟨hD, hDi, hDb, hDbi, -⟩ := fnP_D hL
  have hW : IsFnP (L.ζ * L.ζb * L.GGi) :=
    isFnP_mul (isFnP_mul (fns_fnP hL (m_ζ L)) (fns_fnP hL (m_ζb L))) (fns_fnP hL (m_GGi L))
  have c1 : Commute L.Di (L.ζ * L.ζb * L.GGi) := isFnP_comm hDi hW
  have c2 : Commute (L.Di * (L.ζ * L.ζb * L.GGi)) L.Dbi := isFnP_comm (isFnP_mul hDi hW) hDbi
  have e : L.Di * (L.ζ * L.ζb * L.GGi) * L.Dbi = L.ζ * L.ζb * L.GGi * (L.Di * L.Dbi) := by
    rw [c1.eq, mul_assoc]
  rw [← c1.mul_pow, ← c2.mul_pow, e, WDD hTTp hL hLaw]

theorem gen_sandwich {χ : ℝ → ℝ} (hχ : admitted χ) (N : ℕ) (f : M.Ty P → ℂ) {b1 b2 : A P (DQ P)} (hb1 : b1 ∈ SB L)
    (hb2 : b2 ∈ SB L) {H1 H2 : List (A P (DQ P))} (hH1 : ∀ h ∈ H1, h ∈ plusHats L) (hH2 : ∀ h ∈ H2, h ∈ plusHats L)
    (hl1 : H1.length = N) (hl2 : H2.length = N) :
    Ph P χ * star (b1 * L.Dbi ^ N * H1.prod) * ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) f *
      (b2 * L.Dbi ^ N * H2.prod)) * Ph P χ ∈ Z P L (N + N) := by
  obtain ⟨-, -, -, h4, -, -⟩ := star_more hL hLaw
  obtain ⟨hD, hDi, hDb, hDbi, -⟩ := fnP_D hL
  have hW : IsFnP (L.ζ * L.ζb * L.GGi) :=
    isFnP_mul (isFnP_mul (fns_fnP hL (m_ζ L)) (fns_fnP hL (m_ζb L))) (fns_fnP hL (m_GGi L))
  have hs : star b1 ∈ SB L := star_SB hL hLaw hb1
  have hk : kap P (DQ P) f ∈ SB L := Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))
  have hplus : ∀ h ∈ H2, h ∈ hatSet P L := fun h hh => Or.inl (Or.inl (hH2 h hh))
  have hplus1 : ∀ h ∈ H1, h ∈ hatSet P L := fun h hh => Or.inl (Or.inl (hH1 h hh))
  have hmid := mid_id (star b1) (kap P (DQ P) f) b2 (L.Di ^ N) ((L.ζ * L.ζb * L.GGi) ^ N) (L.Dbi ^ N)
    (SB_comm_fnP hL hLaw hs (isFnP_pow hDi N)).symm
    (SB_comm_fnP hL hLaw (Submonoid.mul_mem _ hk hb2) (isFnP_mul (isFnP_pow hDi N) (isFnP_pow hW N))).symm
  rw [DWD_pow hTTp hL hLaw] at hmid
  have e : Ph P χ * star (b1 * L.Dbi ^ N * H1.prod) * ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) f *
      (b2 * L.Dbi ^ N * H2.prod)) * Ph P χ =
      Ph P χ * (star H1.prod * ((star b1 * kap P (DQ P) f * b2) * (G.Gs P (-1) ^ N * (H2.prod * Ph P χ)))) := by
    rw [star_mul, star_mul, star_pow, h4]
    calc Ph P χ * (star H1.prod * (L.Di ^ N * star b1)) * ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) f *
          (b2 * L.Dbi ^ N * H2.prod)) * Ph P χ
        = Ph P χ * (star H1.prod * (L.Di ^ N * star b1 * ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) f *
          (b2 * L.Dbi ^ N))) * (H2.prod * Ph P χ)) := by simp only [mul_assoc]
      _ = _ := by rw [hmid]; simp only [mul_assoc]
  rw [e]
  have z1 : H2.prod * Ph P χ ∈ Z P L (0 + H2.length) := word_memZ hTTp hL hLaw H2 hplus (Ph_memZ hχ)
  rw [zero_add, hl2] at z1
  have z2 := Gspow_memZ hTTp hL hLaw N z1
  have z3 := SB_memZ hTTp hL hLaw (Submonoid.mul_mem _ (Submonoid.mul_mem _ hs hk) hb2) z2
  have z4 := star_word_mem hTTp.le hL hLaw H1 hplus1 z3
  rw [hl1] at z4
  exact Ph_memZ_mul hTTp hL hLaw hχ z4

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z7

section S_I1_P1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I1

open Finset

noncomputable section

section Gen
variable {R : Type} [Ring R] [Algebra ℂ R]

def PR (f : ℝ → R) (d : ℕ) : Prop := ∃ a : ℕ → R, ∀ s : ℝ, f s = ∑ k ∈ range (d + 1), ((s : ℂ) ^ k) • a k

theorem PR_const (x : R) : PR (fun _ => x) 0 := ⟨fun _ => x, fun s => by simp⟩

theorem PR_mono {f : ℝ → R} {d d' : ℕ} (h : PR f d) (hd : d ≤ d') : PR f d' := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun k => if k ≤ d then a k else 0, fun s => ?_⟩
  dsimp only
  rw [ha, ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hd)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (d + 1) (d' + 1)) (fun k hk => by
    rw [if_neg (by simp [Finset.mem_Ico] at hk; omega), smul_zero]), add_zero]
  exact Finset.sum_congr rfl fun k hk => by rw [if_pos (by simp at hk; omega)]

theorem PR_add {f g : ℝ → R} {d : ℕ} (hf : PR f d) (hg : PR g d) : PR (fun s => f s + g s) d := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  exact ⟨fun k => a k + b k, fun s => by dsimp only; rw [ha, hb, ← Finset.sum_add_distrib]; simp only [smul_add]⟩

theorem PR_add' {f g : ℝ → R} {d1 d2 : ℕ} (hf : PR f d1) (hg : PR g d2) : PR (fun s => f s + g s) (max d1 d2) :=
  PR_add (PR_mono hf (le_max_left _ _)) (PR_mono hg (le_max_right _ _))

theorem PR_neg {f : ℝ → R} {d : ℕ} (hf : PR f d) : PR (fun s => -f s) d := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => -a k, fun s => by dsimp only; rw [ha, ← Finset.sum_neg_distrib]; simp only [smul_neg]⟩

theorem PR_sub {f g : ℝ → R} {d : ℕ} (hf : PR f d) (hg : PR g d) : PR (fun s => f s - g s) d := by
  have := PR_add hf (PR_neg hg)
  simpa [sub_eq_add_neg] using this

theorem PR_smul (z : ℂ) {f : ℝ → R} {d : ℕ} (hf : PR f d) : PR (fun s => z • f s) d := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => z • a k, fun s => by dsimp only; rw [ha, Finset.smul_sum]; simp only [smul_comm z]⟩

theorem PR_mul {f g : ℝ → R} {d1 d2 : ℕ} (hf : PR f d1) (hg : PR g d2) : PR (fun s => f s * g s) (d1 + d2) := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  refine ⟨fun k => ∑ i ∈ range (d1 + 1), ∑ j ∈ range (d2 + 1), if i + j = k then a i * b j else 0, fun s => ?_⟩
  dsimp only
  rw [ha, hb, Finset.sum_mul_sum]
  symm
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite_eq (range (d1 + d2 + 1)) (i + j), if_pos (by simp at hi hj ⊢; omega)]
  rw [smul_mul_smul_comm, pow_add]

theorem PR_sum {ι : Type} (s : Finset ι) (f : ι → ℝ → R) {d : ℕ} (h : ∀ i ∈ s, PR (f i) d) :
    PR (fun x => ∑ i ∈ s, f i x) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PR_const (0 : R) |>.elim fun a ha => ⟨fun _ => 0, fun x => by simp⟩
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have := PR_add h1 h2
    simpa [Finset.sum_insert ha] using this

theorem PR_mul_const {f : ℝ → R} {d : ℕ} (hf : PR f d) (x : R) : PR (fun s => f s * x) d := by
  have := PR_mul hf (PR_const x); simpa using this

theorem PR_const_mul {f : ℝ → R} {d : ℕ} (x : R) (hf : PR f d) : PR (fun s => x * f s) d := by
  have := PR_mul (PR_const x) hf; simpa using this

theorem PR_var : PR (fun s : ℝ => algebraMap ℂ R (s : ℂ)) 1 :=
  ⟨fun k => if k = 1 then 1 else 0, fun s => by
    dsimp only; simp [Finset.sum_range_succ, Algebra.algebraMap_eq_smul_one]⟩

theorem PR_alg_affine (c : ℂ) : PR (fun s : ℝ => algebraMap ℂ R ((s : ℂ) + c)) 1 := by
  have := PR_add PR_var (PR_mono (PR_const (algebraMap ℂ R c)) (Nat.zero_le 1))
  simpa [map_add] using this

theorem PR_prod {R : Type} [CommRing R] [Algebra ℂ R] {ι : Type} (s : Finset ι) (f : ι → ℝ → R) (d : ι → ℕ)
    (h : ∀ i ∈ s, PR (f i) (d i)) : PR (fun x => ∏ i ∈ s, f i x) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PR_const (1 : R)
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have := PR_mul h1 h2
    simpa [Finset.prod_insert ha, Finset.sum_insert ha] using this

theorem PR_star [StarRing R] [StarModule ℂ R] {f : ℝ → R} {d : ℕ} (hf : PR f d) : PR (fun s => star (f s)) d := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun k => star (a k), fun s => ?_⟩
  dsimp only
  rw [ha, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_smul]
  congr 1
  rw [star_pow, Complex.star_def, Complex.conj_ofReal]

end Gen

section Scalar

theorem PR_poly (p : Polynomial ℂ) {d : ℕ} (hd : p.natDegree ≤ d) : PR (fun s : ℝ => p.eval (s : ℂ)) d := by
  refine ⟨fun k => p.coeff k, fun s => ?_⟩
  dsimp only
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, mul_comm]

end Scalar

end

end Formalism.FourierDecayAlt.P.MAx3.I1

end S_I1_P1

section S_I1_P2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I1

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Polynomial

noncomputable section

variable (P : M.Par) (D : DAlg P.r)

theorem PR_kap {p : M.Ty P → ℝ → ℂ} {d : ℕ} (hp : ∀ π, PR (p π) d) :
    PR (fun s => kap P D (fun π => p π s)) d := by
  choose a ha using hp
  refine ⟨fun k => kap P D (fun π => a π k), fun s => ?_⟩
  dsimp only
  have : (fun π => p π s) = ∑ k ∈ range (d + 1), ((s : ℂ) ^ k) • (fun π => a π k) := by
    funext π; rw [ha π s, Finset.sum_apply]; rfl
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul]

theorem PR_xC (π : M.Ty P) : PR (fun s : ℝ => M.xC P π (s : ℂ)) (P.k - 1) := by
  have h := PR_prod (R := ℂ) (Icc 1 (P.k - 1)) (fun i s => (s : ℂ) + (M.rho P π i : ℂ)) (fun _ => 1)
    (fun i _ => by simpa using PR_alg_affine (R := ℂ) (M.rho P π i : ℂ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc] at h
  refine PR_mono ?_ le_rfl
  simpa [M.xC] using (PR_mono h (by omega))

theorem PR_xEx (ex : Finset ℕ) (π : M.Ty P) : PR (fun s : ℝ => M.xEx P ex π (s : ℂ)) (P.k - 1) := by
  have h := PR_prod (R := ℂ) (Icc 1 (P.k - 1) \ ex) (fun i s => (s : ℂ) + (M.rho P π i : ℂ)) (fun _ => 1)
    (fun i _ => by simpa using PR_alg_affine (R := ℂ) (M.rho P π i : ℂ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have hc : (Icc 1 (P.k - 1) \ ex).card ≤ P.k - 1 := by
    calc (Icc 1 (P.k - 1) \ ex).card ≤ (Icc 1 (P.k - 1)).card := Finset.card_le_card Finset.sdiff_subset
      _ = P.k - 1 := by simp
  simpa [M.xEx] using PR_mono h hc

theorem coordinate_polynomial_degree (π : M.Ty P) : (M.coordinatePolynomial P π).natDegree = P.k - 1 ∧ (M.coordinatePolynomial P π).Monic := by
  unfold M.coordinatePolynomial
  have hm : ∀ i ∈ Icc 1 (P.k - 1), (X + C ((M.rho P π i : ℂ) + 1)).Monic := fun i _ => monic_X_add_C _
  refine ⟨?_, monic_prod_of_monic _ _ hm⟩
  rw [natDegree_prod_of_monic _ _ hm, Finset.sum_congr rfl fun i _ => natDegree_X_add_C _]
  simp

theorem natDeg_wNum (π : M.Ty P) : (M.wNum P π).natDegree ≤ 2 * P.k := by
  unfold M.wNum M.qP
  refine natDegree_add_le_of_degree_le ?_ ?_
  · refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_prod_le _ _).trans ?_
    have hb : ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree ≤ 2 :=
      fun i _ => (natDegree_mul_le).trans (by rw [natDegree_X_add_C, natDegree_X_add_C])
    refine (Finset.sum_le_sum hb).trans ?_
    simp [mul_comm]
  · refine (natDegree_sum_le _ _).trans ?_
    refine Finset.sup_le fun l hl => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_mul_le).trans ?_
    have h1 : (∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (M.rho P π j : ℂ))).natDegree ≤ P.k := by
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (M.rho P π j : ℂ)).natDegree
          = ∑ j ∈ (Icc 1 (P.k - 1)).erase l, 1 := Finset.sum_congr rfl fun j _ => natDegree_X_add_C _
        _ ≤ P.k := by
          simp only [Finset.sum_const, smul_eq_mul, mul_one]
          exact (Finset.card_erase_le).trans (by simp)
    have h2 : (∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C ((M.rho P π j : ℂ) + 1))).natDegree ≤ P.k := by
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C ((M.rho P π j : ℂ) + 1)).natDegree
          = ∑ j ∈ (Icc 1 (P.k - 1)).erase l, 1 := Finset.sum_congr rfl fun j _ => natDegree_X_add_C _
        _ ≤ P.k := by
          simp only [Finset.sum_const, smul_eq_mul, mul_one]
          exact (Finset.card_erase_le).trans (by simp)
    omega

theorem PR_wC (π : M.Ty P) : PR (fun s : ℝ => M.wC P π (s : ℂ)) (P.k + 1) := by
  refine PR_poly _ ?_
  obtain ⟨h1, h2⟩ := coordinate_polynomial_degree P π
  rw [natDegree_divByMonic _ h2, h1]
  have := natDeg_wNum P π
  omega

end

end Formalism.FourierDecayAlt.P.MAx3.I1

end S_I1_P2

section S_I1_P3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I1

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.Wd Matrix

noncomputable section

section Gen
variable {R : Type} [Ring R] [Algebra ℂ R]

theorem PR_smul_var (M : R) : PR (fun s : ℝ => (s : ℂ) • M) 1 :=
  ⟨fun k => if k = 1 then M else 0, fun s => by simp [Finset.sum_range_succ]⟩

theorem PR_list_prod : ∀ (l : List (ℝ → R)), (∀ f ∈ l, PR f 1) → PR (fun s => (l.map fun f => f s).prod) l.length
  | [], _ => by simpa using PR_const (1 : R)
  | f :: l, h => by
    have h1 := h f (by simp)
    have h2 := PR_list_prod l (fun g hg => h g (by simp [hg]))
    have := PR_mul h1 h2
    simpa [Nat.add_comm] using this

theorem PR_entry {n : Type} [Fintype n] [DecidableEq n] {F : ℝ → Matrix n n R} {d : ℕ} (hF : PR F d) (i j : n) :
    PR (fun s => F s i j) d := by
  obtain ⟨a, ha⟩ := hF
  exact ⟨fun k => a k i j, fun s => by dsimp only; rw [ha, Matrix.sum_apply]; rfl⟩

end Gen

variable (P : M.Par) (D : DAlg P.r)

theorem PR_xA : PR (fun s : ℝ => xA P D (s : ℂ)) (P.k - 1) := PR_kap P D (fun π => PR_xC P π)
theorem PR_wA : PR (fun s : ℝ => kap P D fun π => M.wC P π (s : ℂ)) (P.k + 1) := PR_kap P D (fun π => PR_wC P π)

theorem polynomial_rate_lowering : PR (fun s : ℝ => l0A P D (s : ℂ)) 1 := by
  have := PR_sub (R := A P D) (PR_mono (PR_const (-nabA P D)) (Nat.zero_le 1))
    (PR_mul_const (PR_alg_affine (R := A P D) (1 / 2)) (zbA P D * ggiA P D))
  simpa [l0A, sub_eq_add_neg] using this

theorem polynomial_rate_raising_constant : PR (fun s : ℝ => m0A P D (s : ℂ)) 1 := by
  have := PR_sub (R := A P D) (PR_mono (PR_const (-nabsA P D)) (Nat.zero_le 1))
    (PR_mul_const (PR_alg_affine (R := A P D) (-(1 / 2))) (zA P D * ggiA P D))
  simpa [m0A, sub_eq_add_neg] using this

theorem polynomial_rate_lower_sum : PR (fun s : ℝ => weightedSumBis P D (s : ℂ)) (P.k - 1) :=
  PR_sum _ _ fun l _ => PR_const_mul _ (PR_kap P D fun π => PR_xEx P {l} π)

theorem polynomial_rate_upper_sum : PR (fun s : ℝ => S12 P D (s : ℂ)) (P.k - 1) :=
  PR_sum _ _ fun l _ => PR_mul_const (PR_kap P D fun π => PR_xEx P {l} π) _

theorem polynomial_rate_quartic_sum : PR (fun s : ℝ => S4 P D (s : ℂ)) (P.k - 1) :=
  PR_sum _ _ fun l _ => PR_sum _ _ fun j _ => PR_const_mul _ (PR_kap P D fun π => PR_xEx P {l, j} π)

theorem PR_QQ (hk : 1 ≤ P.k) (a b : Fin 2) : PR (fun s : ℝ => QQr P D (s : ℂ) a b) (P.k + 1) := by
  have hx := PR_xA P D; have hl := polynomial_rate_lowering P D; have hm := polynomial_rate_raising_constant P D
  have h21 := polynomial_rate_lower_sum P D; have h12 := polynomial_rate_upper_sum P D; have h4 := polynomial_rate_quartic_sum P D; have hw := PR_wA P D
  fin_cases a <;> fin_cases b
  ·
    show PR (fun s : ℝ => t11 P D (s : ℂ)) (P.k + 1)
    unfold t11
    refine PR_add (PR_add (PR_add (PR_add ?_ ?_) ?_) ?_) ?_
    · exact PR_const_mul _ hw
    · exact PR_mono (PR_mul (PR_mul (PR_const_mul _ hx) hm) hl) (by omega)
    · exact PR_mono (PR_mul (PR_mul_const (PR_const_mul _ hm) _) h21) (by omega)
    · exact PR_mono (PR_mul h12 hl) (by omega)
    · exact PR_mono (PR_const_mul _ h4) (by omega)
  · show PR (fun s : ℝ => t12 P D (s : ℂ)) (P.k + 1)
    unfold t12
    exact PR_add (PR_mono (PR_mul (PR_const_mul _ hx) hm) (by omega)) (PR_mono h12 (by omega))
  · show PR (fun s : ℝ => t21 P D (s : ℂ)) (P.k + 1)
    unfold t21
    exact PR_add (PR_mono (PR_mul (PR_const_mul _ hx) hl) (by omega)) (PR_mono h21 (by omega))
  · show PR (fun s : ℝ => t22 P D (s : ℂ)) (P.k + 1)
    unfold t22
    exact PR_mono (PR_const_mul _ hx) (by omega)

theorem PR_Ts (σ : Site (A P D)) : PR (fun s : ℝ => Ts σ (s : ℂ)) 1 := by
  have e : ∀ s : ℝ, Ts σ (s : ℂ) = (s : ℂ) • !![(1 : A P D), 0; 0, 0] + !![σ.p, -σ.c; σ.ci, 0] := by
    intro s
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Ts, Formalism.YangianSpanCharacter.T.Tm, Algebra.algebraMap_eq_smul_one, add_comm]
  have := PR_add (PR_smul_var (R := Matrix (Fin 2) (Fin 2) (A P D)) !![(1 : A P D), 0; 0, 0])
    (PR_mono (PR_const (!![σ.p, -σ.c; σ.ci, 0] : Matrix (Fin 2) (Fin 2) (A P D))) (Nat.zero_le 1))
  simpa [e] using this

theorem polynomial_rate_vector (k : Fin 2) : PR (fun s : ℝ => v0 (sites P D) (s : ℂ) k) P.r := by
  have h := PR_list_prod ((sites P D).map fun σ => fun s : ℝ => Ts σ (s : ℂ))
    (fun f hf => by obtain ⟨σ, _, rfl⟩ := List.mem_map.1 hf; exact PR_Ts P D σ)
  have hl : ((sites P D).map fun σ => fun s : ℝ => Ts σ (s : ℂ)).length = P.r := by simp [sites]
  rw [hl] at h
  have := PR_entry h k 0
  simpa [v0, List.map_map, Function.comp_def] using this

theorem polynomial_rate_constant (hk : 1 ≤ P.k) (l : ℕ) : PR (fun s : ℝ => C0 (startM P D l).QQ (sites P D) (s : ℂ)) (P.k + 2 * P.r + 1) := by
  refine PR_sum _ _ fun a _ => PR_sum _ _ fun b _ => ?_
  have h1 := PR_star (polynomial_rate_vector P D a)
  have h2 : PR (fun s : ℝ => (startM P D l).QQ (s : ℂ) a b) (P.k + 1) := by
    have := PR_smul (M.sgn P l) (PR_QQ P D hk a b)
    simpa [startM] using this
  exact PR_mono (PR_mul (PR_mul h1 h2) (polynomial_rate_vector P D b)) (by omega)

end

end Formalism.FourierDecayAlt.P.MAx3.I1

end S_I1_P3

section S_I1_P4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I1

open Finset

noncomputable section

section Gen
variable {R : Type} [Ring R] [Algebra ℂ R]

def Kp (n : ℕ) (K : ℕ → R) {N : ℕ} (κ : Fin N → Fin (n + 1)) : R :=
  ((List.ofFn fun a => K (κ a)).reverse).prod

def mono {N n : ℕ} (κ : Fin N → Fin (n + 1)) (Y : Fin N → ℝ) : ℂ := ∏ a, ((Y a : ℂ) ^ (κ a : ℕ))

theorem prod_expand (n : ℕ) (C : ℝ → R) (K : ℕ → R) (hC : ∀ s : ℝ, C s = ∑ k ∈ range (n + 1), ((s : ℂ) ^ k) • K k) :
    ∀ (N : ℕ) (Y : Fin N → ℝ), ((List.ofFn fun a => C (Y a)).reverse).prod =
      ∑ κ : Fin N → Fin (n + 1), mono κ Y • Kp n K κ
  | 0, Y => by simp [Kp, mono]
  | N + 1, Y => by
    rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton,
      prod_expand n C K hC N (fun a => Y a.succ), hC (Y 0), Finset.sum_mul_sum]
    have e1 : ∑ κ : Fin (N + 1) → Fin (n + 1), mono κ Y • Kp n K κ =
        ∑ p : Fin (n + 1) × (Fin N → Fin (n + 1)),
          mono (Fin.cons p.1 p.2 : Fin (N + 1) → Fin (n + 1)) Y • Kp n K (Fin.cons p.1 p.2 : Fin (N + 1) → Fin (n + 1)) :=
      ((Fin.consEquiv fun _ => Fin (n + 1)).sum_comp (fun κ => mono κ Y • Kp n K κ)).symm
    rw [e1, Fintype.sum_prod_type]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ' _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun k => (mono κ' fun a => Y a.succ) • Kp n K κ' * (((Y 0 : ℂ) ^ k) • K k)) (n + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mono, Kp, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, List.reverse_cons,
      List.prod_append, List.prod_singleton]
    rw [smul_mul_smul_comm, mul_comm ((Y 0 : ℂ) ^ (k : ℕ))]

end Gen

end

end Formalism.FourierDecayAlt.P.MAx3.I1

end S_I1_P4

section S_I1_P5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I1

open Finset Matrix

noncomputable section

variable {n N : ℕ} (t : Fin N → Fin (n + 1) → ℝ)

def Vd (a : Fin N) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.vandermonde fun i => (t a i : ℂ)

def Wt (κ m : Fin N → Fin (n + 1)) : ℂ := ∏ a, (Vd t a)⁻¹ (κ a) (m a)

def gp (m : Fin N → Fin (n + 1)) : Fin N → ℝ := fun a => t a (m a)

theorem Vd_inv (ht : ∀ a, Function.Injective (t a)) (a : Fin N) : (Vd t a)⁻¹ * Vd t a = 1 := by
  refine Matrix.nonsing_inv_mul _ ?_
  rw [isUnit_iff_ne_zero, Vd, Matrix.det_vandermonde_ne_zero_iff]
  intro i j h
  exact ht a (by simpa using h)

theorem mono_gp (κ m : Fin N → Fin (n + 1)) : mono κ (gp t m) = ∏ a, Vd t a (m a) (κ a) := by
  simp [mono, gp, Vd, Matrix.vandermonde_apply]

theorem Wt_mono (ht : ∀ a, Function.Injective (t a)) (κ κ' : Fin N → Fin (n + 1)) :
    ∑ m : Fin N → Fin (n + 1), Wt t κ m * mono κ' (gp t m) = if κ = κ' then 1 else 0 := by
  simp only [Wt, mono_gp, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a i => (Vd t a)⁻¹ (κ a) i * Vd t a i (κ' a))]
  have : ∀ a, ∑ i, (Vd t a)⁻¹ (κ a) i * Vd t a i (κ' a) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (κ a) (κ' a) :=
    fun a => by rw [← Vd_inv t ht a, Matrix.mul_apply]
  simp only [this, Matrix.one_apply]
  by_cases h : κ = κ'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨a, ha⟩ : ∃ a, κ a ≠ κ' a := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [if_neg ha])

theorem coeff_of_grid {V : Type} [AddCommGroup V] [Module ℂ V] (ht : ∀ a, Function.Injective (t a))
    (f : (Fin N → Fin (n + 1)) → V) (κ : Fin N → Fin (n + 1)) :
    f κ = ∑ m : Fin N → Fin (n + 1), Wt t κ m • ∑ κ' : Fin N → Fin (n + 1), mono κ' (gp t m) • f κ' := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, Wt_mono t ht, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

end

end Formalism.FourierDecayAlt.P.MAx3.I1

end S_I1_P5

section S_I1_P6

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I1

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd MeasureTheory ComplexConjugate

noncomputable section

def prodC (P : M.Par) (l : ℕ) {N : ℕ} (Y : Fin N → ℝ) : A P (DQ P) :=
  ((List.ofFn fun a => C0 (startM P (DQ P) l).QQ (sites P (DQ P)) ((Y a : ℝ) : ℂ)).reverse).prod

def IntHyp : Prop :=
  ∀ (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT)
    (lam : Fin (P.k + 2 * P.r + 1) → ℝ) (α β Lb : ℝ) (c : LE.Cut) (Ntot : ℕ), Hyps P l L j lam α β Lb Ntot →
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, N ≤ Ntot → ∀ Y : Fin N → ℝ,
      (∀ a : Fin N, Y a ∈ (sysQ P l L j lam α β Lb c Ntot).box (N - 1 - (a : ℕ))) →
      ∀ π : M.Ty P, Integrable (fun q => evQ P (actA P (prodC P l Y) (chiJ P j c ε) π) q *
        conj (evQ P (chiJ P j c ε π) q)) (mu0 P.r P.TT)

section Lin
variable (P : M.Par)

theorem actA_lin {ι : Type} (s : Finset ι) (c : ι → ℂ) (K : ι → A P (DQ P)) (v : M.Ty P → SmQ P.r P.TT)
    (π : M.Ty P) (q : Qp P.r P.TT) :
    evQ P (actA P (∑ i ∈ s, c i • K i) v π) q = ∑ i ∈ s, c i * evQ P (actA P (K i) v π) q := by
  rw [I4.evQ_actA_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [I4.actA_smul, G.evQ_smul]

end Lin

end

end Formalism.FourierDecayAlt.P.MAx3.I1

end S_I1_P6

section S_I1_P7

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I1

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd MeasureTheory ComplexConjugate

noncomputable section

theorem mono_real {N n : ℕ} (κ : Fin N → Fin (n + 1)) (Y : Fin N → ℝ) :
    mono κ Y = ((∏ a, Y a ^ (κ a : ℕ) : ℝ) : ℂ) := by
  simp [mono]

def ex {N n : ℕ} (κ : Fin N → Fin (n + 1)) : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => (κ a : ℕ)

theorem eval_ex {N n : ℕ} (κ : Fin N → Fin (n + 1)) (Y : Fin N → ℝ) (z : ℝ) :
    MvPolynomial.eval Y (MvPolynomial.monomial (ex κ) z) = z * ∏ a, Y a ^ (κ a : ℕ) := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  · simp [ex]
  · intro a; simp

theorem degreeOf_sum_ex {N n : ℕ} (z : (Fin N → Fin (n + 1)) → ℝ) (a : Fin N) :
    (∑ κ, MvPolynomial.monomial (ex κ) (z κ)).degreeOf a ≤ n := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  have hs := MvPolynomial.support_sum hm
  rw [Finset.mem_biUnion] at hs
  obtain ⟨κ, -, hκ⟩ := hs
  have := MvPolynomial.support_monomial_subset hκ
  rw [Finset.mem_singleton] at this
  subst this
  simp only [ex, Finsupp.coe_equivFunOnFinite_symm]
  exact Nat.lt_succ_iff.1 (κ a).2

theorem first_identity_of_integral (h : IntHyp) : EnergyPolynomialInPoints := by
  intro P l L j lam α β Lb c Ntot hH ε hε N hN
  have hH' := hH
  obtain ⟨⟨hOK, hl1, hlk, hL, -, -, hαβ, -⟩, -, -, -, -, -, hLb, -, -⟩ := hH'
  have hk : 1 ≤ P.k := le_trans hl1 hlk
  obtain ⟨K, hK⟩ := polynomial_rate_constant P (DQ P) hk l
  obtain ⟨n, hn⟩ : ∃ n, n = P.k + 2 * P.r + 1 := ⟨_, rfl⟩
  rw [← hn] at hK
  have hexp : ∀ Y : Fin N → ℝ, prodC P l Y = ∑ κ : Fin N → Fin (n + 1), mono κ Y • Kp n K κ :=
    fun Y => prod_expand n _ K hK N Y
  set f : (Fin N → Fin (n + 1)) → M.Ty P → Qp P.r P.TT → ℂ := fun κ π q =>
    evQ P (actA P (Kp n K κ) (chiJ P j c ε) π) q * conj (evQ P (chiJ P j c ε π) q) with hf
  have hF : ∀ (Y : Fin N → ℝ) π q, evQ P (actA P (prodC P l Y) (chiJ P j c ε) π) q * conj (evQ P (chiJ P j c ε π) q) =
      ∑ κ, mono κ Y * f κ π q := by
    intro Y π q
    rw [hexp, actA_lin, Finset.sum_mul]
    exact Finset.sum_congr rfl fun κ _ => by rw [mul_assoc]

  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hstep : 0 < Lb / ((n : ℝ) + 1) := div_pos (by linarith) hn1
  set t : Fin N → Fin (n + 1) → ℝ := fun a m =>
    α + (β - α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * Lb + (m : ℝ) * (Lb / ((n : ℝ) + 1)) with ht_def
  have ht : ∀ a, Function.Injective (t a) := by
    intro a m m' hmm
    simp only [t] at hmm
    have : ((m : ℕ) : ℝ) = ((m' : ℕ) : ℝ) := by
      have := mul_right_cancel₀ hstep.ne' (add_left_cancel hmm)
      exact_mod_cast this
    exact Fin.ext (by exact_mod_cast this)
  have hbox : ∀ (m : Fin N → Fin (n + 1)) (a : Fin N),
      gp t m a ∈ (sysQ P l L j lam α β Lb c Ntot).box (N - 1 - (a : ℕ)) := by
    intro m a
    simp only [gp, t, LE.Sys.box, sysQ, Set.mem_Icc]
    have h0 : 0 ≤ ((m a : ℕ) : ℝ) * (Lb / ((n : ℝ) + 1)) := mul_nonneg (Nat.cast_nonneg _) hstep.le
    have h1 : ((m a : ℕ) : ℝ) * (Lb / ((n : ℝ) + 1)) ≤ Lb := by
      have hm : ((m a : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (m a).2
      calc ((m a : ℕ) : ℝ) * (Lb / ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * (Lb / ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) hstep.le
        _ = Lb := by field_simp
    constructor <;> linarith

  have hint : ∀ κ π, Integrable (f κ π) (mu0 P.r P.TT) := by
    intro κ π
    have hc := coeff_of_grid t ht (fun κ => f κ π) κ
    rw [hc]
    refine integrable_finset_sum' _ fun m _ => ?_
    have hI := h P l L j lam α β Lb c Ntot hH ε hε N hN (gp t m) (hbox m) π
    have e : (∑ κ' : Fin N → Fin (n + 1), mono κ' (gp t m) • f κ' π) =
        fun q => evQ P (actA P (prodC P l (gp t m)) (chiJ P j c ε) π) q * conj (evQ P (chiJ P j c ε π) q) := by
      funext q; rw [hF]; simp [Finset.sum_apply]
    rw [e]
    exact hI.smul (Wt t κ m)

  refine ⟨∑ κ : Fin N → Fin (n + 1), MvPolynomial.monomial (ex κ) (∑ π, ∫ q, f κ π q ∂mu0 P.r P.TT).re,
    fun a => hn ▸ degreeOf_sum_ex _ a, fun sg Y _ => ?_⟩
  show cutoffEnergyForm P l j c ε (List.ofFn fun a => (sg a, Y a)) = _
  have hprod : ((List.ofFn fun a => (sg a, Y a)).reverse.map fun x =>
      C0 (startM P (DQ P) l).QQ (sites P (DQ P)) (x.2 : ℂ)).prod = prodC P l Y := by
    simp [prodC, List.map_reverse, List.map_ofFn, Function.comp_def]
  unfold cutoffEnergyForm ipA ip0
  rw [hprod, map_sum]
  simp_rw [eval_ex]
  have hI : ∀ π, ∫ q, ((actA P (prodC P l Y) (chiJ P j c ε) π : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q *
      conj (((chiJ P j c ε π : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q) ∂mu0 P.r P.TT =
      ∑ κ, mono κ Y * ∫ q, f κ π q ∂mu0 P.r P.TT := by
    intro π
    have : (fun q => ((actA P (prodC P l Y) (chiJ P j c ε) π : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q *
        conj (((chiJ P j c ε π : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q)) = fun q => ∑ κ, mono κ Y * f κ π q :=
      funext fun q => hF Y π q
    rw [this, integral_finset_sum _ (fun κ _ => (hint κ π).const_mul _)]
    exact Finset.sum_congr rfl fun κ _ => integral_const_mul _ _
  simp_rw [hI]
  rw [Finset.sum_comm, Complex.re_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [← Finset.mul_sum, mono_real, Complex.re_ofReal_mul, mul_comm]

end

end Formalism.FourierDecayAlt.P.MAx3.I1

end S_I1_P7

section S_I1_P8

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.I1

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd MeasureTheory ComplexConjugate

noncomputable section

def IntForm : Prop :=
  ForWords fun P l L j _ _ _ _ c _ N Y ε => ∀ π : M.Ty P,
    Integrable (fun q => evQ P (actA P (∑ e, ∑ e', star (gRing P l L Y e) * dRing P l L Y e e' * gRing P l L Y e')
      (chiJ P j c ε) π) q * conj (evQ P (chiJ P j c ε π) q)) (mu0 P.r P.TT)

theorem onBoxes_of {S : LE.Sys} : ∀ {N : ℕ} (Y : Fin N → ℝ), (∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ))) →
    S.OnBoxes (List.ofFn Y)
  | 0, Y, _ => by simp [LE.Sys.OnBoxes]
  | N + 1, Y, h => by
    rw [List.ofFn_succ]
    refine ⟨?_, onBoxes_of (fun a => Y a.succ) fun a => ?_⟩
    · have := h 0; simpa using this
    · have := h a.succ
      simpa [Fin.val_succ, Nat.sub_sub, Nat.add_comm] using this

theorem prodC_eq {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
    {lam : Fin (P.k + 2 * P.r + 1) → ℝ} {α β Lb : ℝ} {c : LE.Cut} {Ntot : ℕ} (hH : Hyps P l L j lam α β Lb Ntot)
    {N : ℕ} (Y : Fin N → ℝ) (hN : N ≤ Ntot) (hB : (sysQ P l L j lam α β Lb c Ntot).OnBoxes (List.ofFn Y)) :
    prodC P l Y = ∑ e, ∑ e', star (gRing P l L Y e) * dRing P l L Y e e' * gRing P l L Y e' := by
  obtain ⟨⟨hOK, hl1, hlk, hML, hu, hu', hαβ, hcut⟩, _⟩ := id hH
  have hTT : 0 ≤ P.TT := (mul_pos hOK.T_pos hOK.T'_pos).le
  have hcw := F.cutWord_of hH c (List.ofFn Y) hB (by simpa using hN)
  obtain ⟨L', hL', -, -, hFC⟩ := model_frame_analytic P hOK l hl1 hlk
  have hLL := F.level_unique P (DQ P) L' L hL' hML
  subst hLL
  have hFr := (hFC (Fin (List.ofFn Y).length) (wordP (List.ofFn Y)) hcw).2.1
  have hMW := (model_words P hOK (DQ P) (analytic_laws P.r P.TT hTT) l (Fin (List.ofFn Y).length)
    (wordP (List.ofFn Y)) (F.good_of_cut _ hcw)).1
  rw [F.prod_eq] at hMW
  rw [hFr, F.plusWord_length] at hMW
  have hp : prodC P l Y = ((LE.plus (List.ofFn Y)).reverse.map fun x =>
      C0 (startM P (DQ P) l).QQ (sites P (DQ P)) ((x.2 : ℝ) : ℂ)).prod := by
    simp [prodC, LE.plus, List.map_reverse, List.map_ofFn, Function.comp_def]
  rw [hp, ← hMW, F.sandwich]
  rfl

theorem IntHyp_of_form (h : IntForm) : IntHyp := by
  intro P l L j lam α β Lb c Ntot hH ε hε N hN Y hY π
  have hB := onBoxes_of (S := sysQ P l L j lam α β Lb c Ntot) Y hY
  rw [prodC_eq hH Y hN hB]
  exact h P l L j lam α β Lb c Ntot hH N Y hN hB ε hε π

theorem first_identity_of_form (h : IntForm) : EnergyPolynomialInPoints := first_identity_of_integral (IntHyp_of_form h)

end

end Formalism.FourierDecayAlt.P.MAx3.I1

end S_I1_P8

section S_AD_AD6

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L MeasureTheory
open ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem ipA_add_left {f1 f2 g : M.Ty P → SmQ P.r P.TT}
    (h1 : ∀ π, Integrable (fun q => evQ P (f1 π) q * conj (evQ P (g π) q)) (mu0 P.r P.TT))
    (h2 : ∀ π, Integrable (fun q => evQ P (f2 π) q * conj (evQ P (g π) q)) (mu0 P.r P.TT)) :
    ipA P (f1 + f2) g = ipA P f1 g + ipA P f2 g := by
  unfold ipA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  unfold ip0
  calc ∫ q, (((f1 + f2) π : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q * conj (((g π : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q)
          ∂mu0 P.r P.TT
      = ∫ q, (evQ P (f1 π) q * conj (evQ P (g π) q) + evQ P (f2 π) q * conj (evQ P (g π) q)) ∂mu0 P.r P.TT := by
        congr 1; funext q
        show (evQ P (f1 π) q + evQ P (f2 π) q) * conj (evQ P (g π) q) = _
        ring
    _ = _ := integral_add (h1 π) (h2 π)

theorem ipA_smul_left (c : ℂ) (f g : M.Ty P → SmQ P.r P.TT) :
    ipA P (fun π => c • f π) g = c * ipA P f g := by
  unfold ipA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  unfold ip0
  rw [← integral_const_mul]
  congr 1; funext q
  show (c * evQ P (f π) q) * conj (evQ P (g π) q) = c * (evQ P (f π) q * conj (evQ P (g π) q))
  ring

theorem ipA_zero_left (g : M.Ty P → SmQ P.r P.TT) : ipA P 0 g = 0 := by
  unfold ipA
  refine Finset.sum_eq_zero fun π _ => ?_
  unfold ip0
  have : (fun q => ((0 : M.Ty P → SmQ P.r P.TT) π : Qp P.r P.TT → ℂ) q * conj ((g π : Qp P.r P.TT → ℂ) q)) = fun _ => 0 := by
    funext q; show (0 : ℂ) * _ = 0; ring
  rw [this, integral_zero]

variable {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
variable (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem int_Z {m : ℕ} (hD : JDecay P L j m) {k : ℕ} (hk : k ≤ m) {z : A P (DQ P)} (hz : z ∈ Z P L k)
    {W : List (A P (DQ P))} (hW : ∀ a ∈ W, a ∈ hatSet P L) (hWl : W.length ≤ m) (π : M.Ty P) :
    Integrable (fun q => evQ P (actA P z j π) q * conj (evQ P (actA P W.prod j π) q)) (mu0 P.r P.TT) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, b, v, hφ, hb, hv, hlen, rfl⟩ := hx
    obtain ⟨C, hC⟩ := I4.PW_SB hTTp hL hLaw hb
    exact int_gen hD hφ hC hv hW (hlen.trans hk) hWl π
  | zero =>
    rw [F.actA_zero]
    exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun q => by
      show (0 : ℂ) = 0 * _; ring)
  | add x y _ _ h1 h2 =>
    rw [F.actA_add]
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun q => by
      rw [Pi.add_apply]
      show _ = (evQ P (actA P x j π) q + evQ P (actA P y j π) q) * conj (evQ P (actA P W.prod j π) q)
      ring)
  | smul c x _ h1 =>
    rw [F.actA_smul_mat]
    exact (h1.const_mul c).congr (Filter.Eventually.of_forall fun q => by
      show _ = (c * evQ P (actA P x j π) q) * _; ring)

theorem adjPure {m : ℕ} (hD : JDecay P L j m) (hA : JAdj P L j m) :
    ∀ (W : List (A P (DQ P))), (∀ a ∈ W, a ∈ hatSet P L) → ∀ (k : ℕ), k + W.length ≤ m →
      ∀ z ∈ Z P L k, ipA P (actA P z j) (actA P W.prod j) = ipA P (actA P (star W.prod * z) j) j
  | [], _, k, _, z, _ => by
    simp only [List.prod_nil, star_one, one_mul]
    rw [MAx2.R2.act_one]
  | X :: W', hW, k, hk, z, hz => by
    have hX : X ∈ hatSet P L := hW X (by simp)
    have hW' : ∀ a ∈ W', a ∈ hatSet P L := fun a ha => hW a (by simp [ha])
    have hk' : k + 1 + W'.length ≤ m := by simp at hk; omega
    have hsX : star X ∈ hatSet P L := star_hat hL hLaw hX

    have stepA : ipA P (actA P z j) (actA P (X * W'.prod) j) = ipA P (actA P (star X * z) j) (actA P W'.prod j) := by
      have hXW : ∀ a ∈ X :: W', a ∈ hatSet P L := hW
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨φ, b, v, hφ, hb, hv, hlen, rfl⟩ := hx
        have := jadj_bridge hA hφ hb hsX (v := v) (w := W') (by omega) hv hW'
        rw [star_star] at this
        exact this.symm
      | zero => rw [F.actA_zero, mul_zero, F.actA_zero, ipA_zero_left, ipA_zero_left]
      | add x y hx hy h1 h2 =>
        rw [F.actA_add, mul_add, F.actA_add,
          ipA_add_left (fun π => by
            have := int_Z hTTp hL hLaw hD (by omega) hx hXW (by simp; omega) π; simpa using this)
            (fun π => by
              have := int_Z hTTp hL hLaw hD (by omega) hy hXW (by simp; omega) π; simpa using this),
          ipA_add_left (int_Z hTTp hL hLaw hD (by omega) (hatPast hTTp.le hL hLaw hsX hx) hW' (by omega))
            (int_Z hTTp hL hLaw hD (by omega) (hatPast hTTp.le hL hLaw hsX hy) hW' (by omega)), h1, h2]
      | smul c x hx h1 =>
        rw [F.actA_smul_mat, mul_smul_comm, F.actA_smul_mat, ipA_smul_left, ipA_smul_left, h1]
    have hz' : star X * z ∈ Z P L (k + 1) := hatPast hTTp.le hL hLaw hsX hz
    rw [List.prod_cons, stepA, adjPure hD hA W' hW' (k + 1) hk' (star X * z) hz', star_mul, mul_assoc]

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD6

section S_Z_Z8

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.AD
open Formalism.FourierDecayAlt.P.MAx3.L
open ComplexConjugate

noncomputable section

theorem admissible_cutoff (c : LE.Cut) {ε : ℝ} (hε : 0 < ε) : admitted (PG.chi c ε) := by
  refine ⟨PG.smoothLog_chi c ε, ⟨ε / 2, by positivity, fun x hx => ?_⟩, fun p => ?_⟩
  · unfold PG.chi LE.Cut.sc
    rw [c.zero (x / ε) (by rw [div_le_iff₀ hε]; linarith), pow_one]
  · obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.cutoff_bound c 1 p le_rfl
    exact ⟨C, fun x hx => (hC ε x hε hx).1⟩

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem sandwich_span {χ : ℝ → ℝ} (hχ : admitted χ) (N : ℕ) (f : M.Ty P → ℂ) {x1 x2 : A P (DQ P)}
    (h1 : x1 ∈ NFD L N) (h2 : x2 ∈ NFD L N) :
    Ph P χ * star x1 * ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) f * x2) * Ph P χ ∈ Z P L (N + N) := by
  induction h1 using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b1, H1, hb1, hH1, hl1, rfl⟩ := ha
    induction h2 using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨b2, H2, hb2, hH2, hl2, rfl⟩ := hc
      exact gen_sandwich hTTp hL hLaw hχ N f hb1 hb2 hH1 hH2 hl1 hl2
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, mul_add, add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy => rw [star_add, mul_add, add_mul, add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [star_smul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z8

section S_Z_Z9

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.AD
open Formalism.FourierDecayAlt.P.MAx3.L
open ComplexConjugate

noncomputable section

theorem T_memZ {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
    {lam : Fin (P.k + 2 * P.r + 1) → ℝ} {α β Lb : ℝ} {c : LE.Cut} {Ntot : ℕ} (hH : Hyps P l L j lam α β Lb Ntot)
    {N : ℕ} (Y : Fin N → ℝ) (hN : N ≤ Ntot) (hB : (sysQ P l L j lam α β Lb c Ntot).OnBoxes (List.ofFn Y))
    {ε : ℝ} (hε : 0 < ε) :
    Ph P (PG.chi c ε) * (∑ e, ∑ e', star (gRing P l L Y e) * dRing P l L Y e e' * gRing P l L Y e') *
      Ph P (PG.chi c ε) ∈ Z P L ((List.ofFn Y).length + (List.ofFn Y).length) := by
  obtain ⟨⟨hOK, hl1, hlk, hML, hu, hu', hαβ, hcut⟩, hD, hA, hE, hN1, -⟩ := id hH
  have hTTp : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hLaw := analytic_laws P.r P.TT hTTp.le
  have hcw : M.CutWord P l (wordP (List.ofFn Y)) := MAx3.F.cutWord_of hH c (List.ofFn Y) hB (by simpa using hN)
  obtain ⟨L', hL', -, -, hFC⟩ := model_frame_analytic P hOK l hl1 hlk
  have hLL := MAx3.F.level_unique P (DQ P) L' L hL' hML
  subst hLL
  have hFCw := hFC (Fin (List.ofFn Y).length) (wordP (List.ofFn Y)) hcw
  have hS := sites_admissible P (DQ P) hLaw l
  have hFr : ∀ w' : List ℝ, M.CutWord P l (wordP w') → IsFrame L' (ofWord L' (startM P (DQ P) l) (wordP w')) :=
    fun w' h => (hFC _ _ h).1
  set cs0 : Ix (Fin (List.ofFn Y).length) → M.Ty P → ℂ := fun e π => cs (M.x0 P l π) (M.qC P) (wordP (List.ofFn Y)) e
    with hcs0
  have hd : dRing P l L' Y = (wt L' : SlopeTestRemainingChoices (Fin (List.ofFn Y).length) (A P (DQ P))) ^ (List.ofFn Y).length *
      Matrix.diagonal (fun e => kap P (DQ P) (cs0 e)) := by
    unfold dRing frW
    rw [hFCw.2.2.1]
  have hT : (∑ e, ∑ e', star (gRing P l L' Y e) * dRing P l L' Y e e' * gRing P l L' Y e') =
      ∑ e, star (gRing P l L' Y e) * ((L'.ζ * L'.ζb * L'.GGi) ^ (List.ofFn Y).length * kap P (DQ P) (cs0 e) *
        gRing P l L' Y e) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← PG.d_g_sum hTTp hML hLaw, Finset.mul_sum, hd]
    exact Finset.sum_congr rfl fun e' _ => by rw [mul_assoc]
  have hg : ∀ e, gRing P l L' Y e ∈ NFD L' (List.ofFn Y).length := fun e =>
    normal_form_two_le_degree hML hLaw _ (gRw_NF hML hLaw hS hFr (List.ofFn Y) hcw e)
  rw [hT, Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [← mul_assoc]
  exact sandwich_span hTTp hML hLaw (admissible_cutoff c hε) _ (cs0 e) (hg e) (hg e)

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z9

section S_Z_Z10

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.AD
open Formalism.FourierDecayAlt.P.MAx3.L
open ComplexConjugate

noncomputable section

theorem ev_Ph {P : M.Par} {j : M.Ty P → SmQ P.r P.TT} {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (y : A P (DQ P))
    (π : M.Ty P) (q : Qp P.r P.TT) :
    evQ P (actA P (Ph P φ * y) j π) q = ((φ (Gq P q) : ℝ) : ℂ) * evQ P (actA P y j π) q := by
  rw [act_Ph hφ]
  show evQ P (toSm P (fun q => ((φ (Gq P q) : ℝ) : ℂ)) * actA P y j π) q = _
  rw [MAx2.Jet.evQ_mul, ← Phi0_eq P hφ, eval_cutoff_operator_zero P hφ]

theorem chiJ_Ph {P : M.Par} (j : M.Ty P → SmQ P.r P.TT) (c : LE.Cut) (ε : ℝ) :
    chiJ P j c ε = actA P (Ph P (PG.chi c ε) * 1) j := by
  rw [mul_one, PG.chiJ_eq]
  funext π
  show _ = actA P (sc P (DQ P) (Fq P (PG.chi c ε) 0)) j π
  rw [MAx2.R2.act_sc]
  rfl

theorem intForm : MAx3.I1.IntForm := by
  intro P l L j lam α β Lb c Ntot hH N Y hN hB ε hε π
  obtain ⟨⟨hOK, hl1, hlk, hML, -⟩, hD, hA, -⟩ := id hH
  have hTTp : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hLaw := analytic_laws P.r P.TT hTTp.le
  have hz := T_memZ hH Y hN hB hε
  have hlen : (List.ofFn Y).length = N := List.length_ofFn
  set T := ∑ e, ∑ e', star (gRing P l L Y e) * dRing P l L Y e e' * gRing P l L Y e' with hT
  have hsm := PG.smoothLog_chi c ε
  have hint := int_Z hTTp hML hLaw hD (k := (List.ofFn Y).length + (List.ofFn Y).length) (by omega) hz
    (W := []) (by simp) (by simp) π
  refine hint.congr (Filter.Eventually.of_forall fun q => ?_)
  show evQ P (actA P (Ph P (PG.chi c ε) * T * Ph P (PG.chi c ε)) j π) q * conj (evQ P (actA P ([] : List (A P (DQ P))).prod j π) q) =
    evQ P (actA P T (chiJ P j c ε) π) q * conj (evQ P (chiJ P j c ε π) q)
  rw [chiJ_Ph, mul_assoc, ev_Ph hsm, ← F.actA_mul, ev_Ph hsm, List.prod_nil, mul_one, MAx2.R2.act_one, map_mul,
    Complex.conj_ofReal]
  ring

end

end Formalism.FourierDecayAlt.P.MAx3.Z

namespace Formalism.FourierDecayAlt.P

theorem first_identity : Formalism.FourierDecayAlt.MA.EnergyPolynomialInPoints := MAx3.I1.first_identity_of_form MAx3.Z.intForm

end Formalism.FourierDecayAlt.P

end S_Z_Z10

section S_AD_AD7

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L MeasureTheory
open ComplexConjugate

noncomputable section

variable {P : M.Par}

def SqB (B : Qp P.r P.TT → ℝ) : Prop :=
  Continuous B ∧ (∀ q, 0 ≤ B q) ∧ Integrable (fun q => B q ^ 2) (mu0 P.r P.TT)

theorem sqB_zero : SqB (P := P) (fun _ => 0) :=
  ⟨continuous_const, fun _ => le_rfl, by simpa using (integrable_zero _ _ _ : Integrable (fun _ : Qp P.r P.TT => (0 : ℝ)) _)⟩

theorem sqB_add {B D : Qp P.r P.TT → ℝ} (hB : SqB B) (hD : SqB D) : SqB (fun q => B q + D q) := by
  refine ⟨hB.1.add hD.1, fun q => add_nonneg (hB.2.1 q) (hD.2.1 q), ?_⟩
  refine ((hB.2.2.const_mul 2).add (hD.2.2.const_mul 2)).mono' ((hB.1.add hD.1).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show (B q + D q) ^ 2 ≤ 2 * B q ^ 2 + 2 * D q ^ 2
  nlinarith [sq_nonneg (B q - D q)]

theorem sqB_smul {B : Qp P.r P.TT → ℝ} (hB : SqB B) {c : ℝ} (hc : 0 ≤ c) : SqB (fun q => c * B q) := by
  refine ⟨continuous_const.mul hB.1, fun q => mul_nonneg hc (hB.2.1 q), ?_⟩
  have := hB.2.2.const_mul (c ^ 2)
  exact this.congr (Filter.Eventually.of_forall fun q => by ring)

theorem sqB_sum {ι : Type} (s : Finset ι) (B : ι → Qp P.r P.TT → ℝ) (h : ∀ i ∈ s, SqB (B i)) :
    SqB (fun q => ∑ i ∈ s, B i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sqB_zero (P := P)
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact sqB_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem int_of_sqB {f : Qp P.r P.TT → ℂ} (hf : Continuous f) {B D : Qp P.r P.TT → ℝ} (hB : SqB B) (hD : SqB D)
    (h : ∀ q, ‖f q‖ ≤ B q * D q) : Integrable f (mu0 P.r P.TT) :=
  (hB.2.2.add hD.2.2).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall fun q =>
    (h q).trans (sq_bound _ _))

variable {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}

theorem sqB_word {m : ℕ} (hD : JDecay P L j m) {W : List (A P (DQ P))} (hW : ∀ a ∈ W, a ∈ hatSet P L)
    (hWl : W.length ≤ m) (π : M.Ty P) : SqB (fun q => ‖evQ P (actA P W.prod j π) q‖) :=
  ⟨(MAx3.evQ_cont P _).norm, fun q => norm_nonneg _, hD W hWl hW π⟩

variable (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem zbound {m : ℕ} (hD : JDecay P L j m) {k : ℕ} (hk : k ≤ m) {z : A P (DQ P)} (hz : z ∈ Z P L k) :
    ∃ B, SqB B ∧ ∀ q π, ‖evQ P (actA P z j π) q‖ ≤ B q := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, b, v, hφ, hb, hv, hlen, rfl⟩ := hx
    obtain ⟨C, hC⟩ := I4.PW_SB hTTp hL hLaw hb
    obtain ⟨Mx, hM, e⟩ := ev_gen (j := j) hφ.1 hC
    obtain ⟨Cφ, hCφ⟩ := hφ.2.2 0
    refine ⟨fun q => |Cφ| * (C * ∑ π', ‖evQ P (actA P v.prod j π') q‖),
      sqB_smul (sqB_smul (sqB_sum _ _ fun π' _ => sqB_word hD hv (hlen.trans hk) π') hC.1) (abs_nonneg _),
      fun q π => ?_⟩
    have h1 : |φ (Gq P q)| ≤ |Cφ| := by
      have := hCφ _ (Gq_pos P q); rw [ld_zero (Gq_pos P q)] at this; exact this.trans (le_abs_self _)
    rw [e v q π, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul h1 ((norm_sum_le _ _).trans ?_) (norm_nonneg _) (abs_nonneg _)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun π' _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM q π π') (norm_nonneg _)
  | zero => exact ⟨fun _ => 0, sqB_zero, fun q π => by rw [F.actA_zero]; simp [evQ]⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨B1, hB1, e1⟩ := h1
    obtain ⟨B2, hB2, e2⟩ := h2
    refine ⟨fun q => B1 q + B2 q, sqB_add hB1 hB2, fun q π => ?_⟩
    rw [F.actA_add]
    exact (norm_add_le _ _).trans (add_le_add (e1 q π) (e2 q π))
  | smul c x _ h1 =>
    obtain ⟨B, hB, e⟩ := h1
    refine ⟨fun q => ‖c‖ * B q, sqB_smul hB (norm_nonneg _), fun q π => ?_⟩
    rw [F.actA_smul_mat]
    show ‖c * evQ P (actA P x j π) q‖ ≤ _
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (e q π) (norm_nonneg _)

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD7

section S_AD_AD8

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L MeasureTheory
open ComplexConjugate

noncomputable section

variable {P : M.Par}

def SA (x : A P (DQ P)) (Mx : Qp P.r P.TT → Matrix (M.Ty P) (M.Ty P) ℂ) : Prop :=
  (∀ (f : M.Ty P → SmQ P.r P.TT) q π, evQ P (actA P x f π) q = ∑ π', Mx q π π' * evQ P (f π') q) ∧
  (∀ (f : M.Ty P → SmQ P.r P.TT) q π, evQ P (actA P (star x) f π) q = ∑ π', conj (Mx q π' π) * evQ P (f π') q)

theorem SA_star {x : A P (DQ P)} {Mx : Qp P.r P.TT → Matrix (M.Ty P) (M.Ty P) ℂ} (h : SA x Mx) :
    SA (star x) (fun q π π' => conj (Mx q π' π)) :=
  ⟨h.2, fun f q π => by rw [star_star, h.1]; simp⟩

theorem SA_mul {x y : A P (DQ P)} {Mx My : Qp P.r P.TT → Matrix (M.Ty P) (M.Ty P) ℂ} (hx : SA x Mx) (hy : SA y My) :
    SA (x * y) (fun q => Mx q * My q) := by
  refine ⟨fun f q π => ?_, fun f q π => ?_⟩
  · rw [F.actA_mul, hx.1]
    simp_rw [hy.1, Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rw [star_mul, F.actA_mul, hy.2]
    simp_rw [hx.2, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [map_mul]; ring

theorem SA_one : SA (1 : A P (DQ P)) (fun _ => 1) := by
  refine ⟨fun f q π => ?_, fun f q π => ?_⟩ <;>
  · simp only [star_one, MAx2.R2.act_one, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, map_one, map_zero, apply_ite conj]
    try simp [eq_comm]

def CF (x : A P (DQ P)) (g : Qp P.r P.TT → ℂ) : Prop :=
  ∃ F Fb : (DQ P).R, x = sc P (DQ P) ((DQ P).fnP F Fb) ∧ (∀ q, evQ P (asS P F) q = g q) ∧
    ∀ q, evQ P (asS P Fb) q = conj (g q)

theorem CF_mul {x y : A P (DQ P)} {g h : Qp P.r P.TT → ℂ} (hx : CF x g) (hy : CF y h) :
    CF (x * y) (fun q => g q * h q) := by
  obtain ⟨F, Fb, rfl, h1, h2⟩ := hx
  obtain ⟨G', Gb, rfl, h3, h4⟩ := hy
  refine ⟨F * G', Fb * Gb, ?_, fun q => ?_, fun q => ?_⟩
  · rw [G.sc_mul, Formalism.FourierDecayAlt.P.MAx1.multiplierPair_mul]
  · show evQ P (asS P F * asS P G') q = _
    rw [MAx2.Jet.evQ_mul, h1, h3]
  · show evQ P (asS P Fb * asS P Gb) q = _
    rw [MAx2.Jet.evQ_mul, h2, h4, map_mul]

theorem CF_one : CF (1 : A P (DQ P)) (fun _ => 1) :=
  ⟨1, 1, by rw [Formalism.FourierDecayAlt.P.MAx1.multiplierPair_one]; simp [sc], fun q => rfl, fun q => by
    show (1 : ℂ) = conj 1; simp⟩

theorem CF_prod {n : ℕ} (x : Fin n → A P (DQ P)) (g : Fin n → Qp P.r P.TT → ℂ) (h : ∀ i, CF (x i) (g i)) :
    CF (List.ofFn x).prod (fun q => ∏ i, g i q) := by
  induction n with
  | zero => simpa using (CF_one (P := P))
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have := CF_mul (h 0) (ih (fun i => x i.succ) (fun i => g i.succ) fun i => h i.succ)
    simpa [Fin.prod_univ_succ] using this

theorem SA_of_CF {x : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (hx : CF x g) :
    SA x (fun q => Matrix.diagonal fun _ => g q) := by
  obtain ⟨F, Fb, rfl, h1, h2⟩ := hx
  refine ⟨fun f q π => ?_, fun f q π => ?_⟩ <;> dsimp only
  · rw [MAx2.R2.act_sc, Finset.sum_eq_single π (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul])
      (by simp), Matrix.diagonal_apply_eq, ← h1 q]
    show evQ P (asS P F * f π) q = _
    rw [MAx2.Jet.evQ_mul]
  · rw [MAx2.R2.star_sc, MAx2.R2.act_sc, Finset.sum_eq_single π (fun b _ hb => by
      rw [Matrix.diagonal_apply_ne _ hb, map_zero, zero_mul]) (by simp), Matrix.diagonal_apply_eq, ← h2 q]
    show evQ P (asS P Fb * f π) q = _
    rw [MAx2.Jet.evQ_mul]

theorem SA_scalars (x : A P (DQ P)) (c : M.Ty P → M.Ty P → ℂ) (hc : ∀ π π', x π π' = algebraMap ℂ (DQ P).Pr (c π π')) :
    SA x (fun _ => Matrix.of c) := by
  refine ⟨fun f q π => ?_, fun f q π => ?_⟩
  · rw [MAx2.R2.actA_eq, MAx2.Jet.evQ_sum]
    refine Finset.sum_congr rfl fun π' _ => ?_
    rw [hc]; rfl
  · rw [MAx2.R2.actA_eq, MAx2.Jet.evQ_sum]
    refine Finset.sum_congr rfl fun π' _ => ?_
    rw [Matrix.star_apply, hc, ← algebraMap_star_comm]; rfl

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD8

section S_AD_AD9

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L MeasureTheory
open ComplexConjugate

noncomputable section

variable {P : M.Par}

def SAB (x : A P (DQ P)) (C : ℝ) : Prop :=
  ∃ Mx : Qp P.r P.TT → Matrix (M.Ty P) (M.Ty P) ℂ, SA x Mx ∧ 0 ≤ C ∧ ∀ q π π', ‖Mx q π π'‖ ≤ C

theorem SAB_star {x : A P (DQ P)} {C : ℝ} (h : SAB x C) : SAB (star x) C := by
  obtain ⟨Mx, hs, h0, hb⟩ := h
  exact ⟨_, SA_star hs, h0, fun q π π' => by rw [Complex.norm_conj]; exact hb q π' π⟩

theorem SAB_mul {x y : A P (DQ P)} {C₁ C₂ : ℝ} (hx : SAB x C₁) (hy : SAB y C₂) :
    SAB (x * y) (Fintype.card (M.Ty P) * C₁ * C₂) := by
  obtain ⟨Mx, hsx, h0x, hbx⟩ := hx
  obtain ⟨My, hsy, h0y, hby⟩ := hy
  refine ⟨_, SA_mul hsx hsy, by positivity, fun q π π' => ?_⟩
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖Mx q π k * My q k π'‖ ≤ ∑ _k : M.Ty P, C₁ * C₂ :=
        Finset.sum_le_sum fun k _ => by rw [norm_mul]; exact mul_le_mul (hbx q π k) (hby q k π') (norm_nonneg _) h0x
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem SAB_one : SAB (1 : A P (DQ P)) 1 :=
  ⟨_, SA_one, zero_le_one, fun q π π' => by
    simp only [Matrix.one_apply]; split_ifs <;> simp⟩

theorem SAB_of_CF {x : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (hx : CF x g) {C : ℝ} (hC : 0 ≤ C) (hg : ∀ q, ‖g q‖ ≤ C) :
    SAB x C :=
  ⟨_, SA_of_CF hx, hC, fun q π π' => by
    simp only [Matrix.diagonal_apply]; split_ifs
    · exact hg q
    · simpa using hC⟩

theorem SAB_scalars (x : A P (DQ P)) (c : M.Ty P → M.Ty P → ℂ) (hc : ∀ π π', x π π' = algebraMap ℂ (DQ P).Pr (c π π')) :
    SAB x (∑ π, ∑ π', ‖c π π'‖) :=
  ⟨_, SA_scalars x c hc, by positivity, fun q π π' =>
    (Finset.single_le_sum (f := fun π' => ‖c π π'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ π')).trans
      (Finset.single_le_sum (f := fun π => ∑ π', ‖c π π'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ π))⟩

variable (hTT : 0 ≤ P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hTT hL

theorem cf_c (l : Fin P.r) : CF (L.c l) (fun q => q.1.1 l) := by
  rw [hL.2.2.1]; exact ⟨_, _, rfl, fun q => I4.coordE_vc l q.1, fun q => I4.coordE_vcb l q.1⟩
theorem cf_ci (l : Fin P.r) : CF (L.ci l) (fun q => (q.1.1 l)⁻¹) := by
  rw [hL.2.2.2.1]
  exact ⟨_, _, rfl, fun q => by show evQ P ((DQ P).inv ((DQ P).x (M.vc l))) q = _; rw [I4.ev_invQ hTT, I4.coordE_vc],
    fun q => by show evQ P ((DQ P).inv ((DQ P).x (M.vcb l))) q = _; rw [I4.ev_invQ hTT, I4.coordE_vcb, map_inv₀]⟩
theorem cf_cb (l : Fin P.r) : CF (L.cb l) (fun q => conj (q.1.1 l)) := by
  rw [hL.2.2.2.2.1]
  exact ⟨_, _, rfl, fun q => I4.coordE_vcb l q.1, fun q => by
    simp only [Complex.conj_conj]; exact I4.coordE_vc l q.1⟩
theorem cf_cbi (l : Fin P.r) : CF (L.cbi l) (fun q => (conj (q.1.1 l))⁻¹) := by
  rw [hL.2.2.2.2.2.1]
  exact ⟨_, _, rfl, fun q => by show evQ P ((DQ P).inv ((DQ P).x (M.vcb l))) q = _; rw [I4.ev_invQ hTT, I4.coordE_vcb],
    fun q => by
      show evQ P ((DQ P).inv ((DQ P).x (M.vc l))) q = _; rw [I4.ev_invQ hTT, I4.coordE_vc, map_inv₀, Complex.conj_conj]⟩
theorem cf_ζ : CF L.ζ (fun q => q.1.2) := by
  rw [hL.2.2.2.2.2.2.1]; exact ⟨_, _, rfl, fun q => coordE_vz q.1, fun q => coordE_vzb q.1⟩
theorem cf_ζi : CF L.ζi (fun q => (q.1.2)⁻¹) := by
  rw [hL.2.2.2.2.2.2.2.1]
  exact ⟨_, _, rfl, fun q => by show evQ P ((DQ P).inv ((DQ P).x M.vz)) q = _; rw [I4.ev_invQ hTT, coordE_vz],
    fun q => by show evQ P ((DQ P).inv ((DQ P).x M.vzb)) q = _; rw [I4.ev_invQ hTT, coordE_vzb, map_inv₀]⟩
theorem cf_ζb : CF L.ζb (fun q => conj q.1.2) := by
  rw [hL.2.2.2.2.2.2.2.2.1]
  exact ⟨_, _, rfl, fun q => coordE_vzb q.1, fun q => by simp only [Complex.conj_conj]; exact coordE_vz q.1⟩
theorem cf_ζbi : CF L.ζbi (fun q => (conj q.1.2)⁻¹) := by
  rw [hL.2.2.2.2.2.2.2.2.2.1]
  exact ⟨_, _, rfl, fun q => by show evQ P ((DQ P).inv ((DQ P).x M.vzb)) q = _; rw [I4.ev_invQ hTT, coordE_vzb],
    fun q => by show evQ P ((DQ P).inv ((DQ P).x M.vz)) q = _; rw [I4.ev_invQ hTT, coordE_vz, map_inv₀, Complex.conj_conj]⟩

theorem cf_Dr : CF L.Dr (fun q => ∏ l, q.1.1 l) := CF_prod _ _ (cf_c hTT hL)
theorem cf_Dri : CF L.Dri (fun q => ∏ l, (q.1.1 l)⁻¹) := CF_prod _ _ (cf_ci hTT hL)
theorem cf_Drb : CF L.Drb (fun q => ∏ l, conj (q.1.1 l)) := CF_prod _ _ (cf_cb hTT hL)
theorem cf_Drbi : CF L.Drbi (fun q => ∏ l, (conj (q.1.1 l))⁻¹) := CF_prod _ _ (cf_cbi hTT hL)
theorem cf_D : CF L.D (fun q => (∏ l, q.1.1 l) * q.1.2) := CF_mul (cf_Dr hTT hL) (cf_ζ hTT hL)
theorem cf_Di : CF L.Di (fun q => (q.1.2)⁻¹ * ∏ l, (q.1.1 l)⁻¹) := CF_mul (cf_ζi hTT hL) (cf_Dri hTT hL)
theorem cf_Db : CF L.Db (fun q => (∏ l, conj (q.1.1 l)) * conj q.1.2) := CF_mul (cf_Drb hTT hL) (cf_ζb hTT hL)
theorem cf_Dbi : CF L.Dbi (fun q => (conj q.1.2)⁻¹ * ∏ l, (conj (q.1.1 l))⁻¹) := CF_mul (cf_ζbi hTT hL) (cf_Drbi hTT hL)

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD9

section S_AD_AD10

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L MeasureTheory
open ComplexConjugate

noncomputable section

variable {P : M.Par}

def EC (w : (DQ P).Pr) : Submonoid (A P (DQ P)) where
  carrier := {x | ∀ π π', w * x π π' = x π π' * w}
  mul_mem' {x y} hx hy π π' := by
    rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  one_mem' π π' := by simp only [Matrix.one_apply]; split_ifs <;> simp

theorem sc_comm_EC {w : (DQ P).Pr} {x : A P (DQ P)} (hx : x ∈ EC w) : sc P (DQ P) w * x = x * sc P (DQ P) w := by
  ext π π'
  simp only [sc, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact hx π π'

theorem sc_mem_EC {w w' : (DQ P).Pr} (h : w * w' = w' * w) : sc P (DQ P) w' ∈ EC w := fun π π' => by
  simp only [sc, Matrix.scalar_apply, Matrix.diagonal_apply]; split_ifs <;> simp [h]

theorem alg_mem_EC (w : (DQ P).Pr) (x : A P (DQ P)) (c : M.Ty P → M.Ty P → ℂ)
    (hc : ∀ π π', x π π' = algebraMap ℂ (DQ P).Pr (c π π')) : x ∈ EC w := fun π π' => by
  rw [hc]; exact (Algebra.commutes _ _).symm

variable (hTTp : 0 < P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem SAB_gen {b : A P (DQ P)} (hb : b ∈ bddSet P L) : ∃ C, SAB b C := by
  have hTT := hTTp.le
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨_, SAB_of_CF (cf_ζi hTT hL) (inv_nonneg.2 (Real.sqrt_nonneg _)) fun q => I4.ζinv_le hTTp q⟩
    · exact ⟨_, SAB_of_CF (cf_ζbi hTT hL) (inv_nonneg.2 (Real.sqrt_nonneg _)) fun q => by
        rw [norm_inv, Complex.norm_conj, ← norm_inv]; exact I4.ζinv_le hTTp q⟩
    · exact ⟨1, SAB_of_CF (CF_mul (cf_D hTT hL) (cf_Dbi hTT hL)) zero_le_one fun q => by
        rw [norm_mul, I4.norm_D (hTTp := hTTp) (hL := hL), mul_comm, I4.norm_Dbi (hTTp := hTTp) (hL := hL)]⟩
    · exact ⟨1, SAB_of_CF (CF_mul (cf_Db hTT hL) (cf_Di hTT hL)) zero_le_one fun q => by
        rw [norm_mul, I4.norm_Db (hTTp := hTTp) (hL := hL), mul_comm, I4.norm_Di (hTTp := hTTp) (hL := hL)]⟩
  · classical
    exact ⟨_, SAB_scalars _ (fun π π' => if π = π' then f π else 0) fun π π' => by
      have e : kap P (DQ P) f = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (f π) := rfl
      rw [e, Matrix.diagonal_apply]; split_ifs <;> simp⟩
  · classical
    have hS := SAB_scalars (SS P (DQ P) i)
      (fun π' π => if M.Up P i π π' then ((Real.sqrt (M.Nrm P i π) : ℝ) : ℂ) else 0)
      (fun π' π => by simp only [SS, Matrix.of_apply]; split_ifs <;> simp)
    have hD := SAB_of_CF (CF_mul (cf_Drb hTT hL) (cf_Dri hTT hL)) zero_le_one fun q => by
      rw [norm_mul, norm_prod, norm_prod]
      simp only [Complex.norm_conj, norm_inv]
      rw [← Finset.prod_mul_distrib]
      exact le_of_eq (Finset.prod_eq_one fun l _ => mul_inv_cancel₀ (norm_ne_zero_iff.2 (I4.c_ne q l)))
    exact ⟨_, SAB_mul hD hS⟩
  · classical
    have hS := SAB_scalars (SS P (DQ P) i)
      (fun π' π => if M.Up P i π π' then ((Real.sqrt (M.Nrm P i π) : ℝ) : ℂ) else 0)
      (fun π' π => by simp only [SS, Matrix.of_apply]; split_ifs <;> simp)
    have hD := SAB_of_CF (CF_mul (cf_Drb hTT hL) (cf_Dri hTT hL)) zero_le_one fun q => by
      rw [norm_mul, norm_prod, norm_prod]
      simp only [Complex.norm_conj, norm_inv]
      rw [← Finset.prod_mul_distrib]
      exact le_of_eq (Finset.prod_eq_one fun l _ => mul_inv_cancel₀ (norm_ne_zero_iff.2 (I4.c_ne q l)))
    exact ⟨_, SAB_star (SAB_mul hD hS)⟩

theorem SAB_closure {b : A P (DQ P)} (hb : b ∈ Submonoid.closure (bddSet P L)) : ∃ C, SAB b C := by
  induction hb using Submonoid.closure_induction with
  | mem x hx => exact SAB_gen hTTp hL hLaw hx
  | one => exact ⟨1, SAB_one⟩
  | mul x y _ _ h1 h2 =>
    obtain ⟨C1, h1⟩ := h1
    obtain ⟨C2, h2⟩ := h2
    exact ⟨_, SAB_mul h1 h2⟩

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD10

section S_AD_AD11

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L
open MeasureTheory ComplexConjugate

noncomputable section

variable {P : M.Par}

def Good (ψ : ℝ → ℝ) : Prop := LE.SmoothLog ψ ∧ ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p ψ x| ≤ C

theorem admissible_mul_good {φ ψ : ℝ → ℝ} (hφ : admitted φ) (hψ : Good ψ) : admitted (fun x => φ x * ψ x) := by
  obtain ⟨hs, ⟨ε, hε, h0⟩, hb⟩ := hφ
  obtain ⟨hs', hb'⟩ := hψ
  refine ⟨?_, ⟨ε, hε, fun x hx => by simp [h0 x hx]⟩, fun q => ?_⟩
  · unfold LE.SmoothLog; exact hs.mul hs'
  · choose C hC using hb
    choose C' hC' using hb'
    refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * C i * C' (q - i), fun x hx => ?_⟩
    rw [ld_mul hs hs']
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 := hC i x hx
    have h2 := hC' (q - i) x hx
    have hc0 : 0 ≤ C i := (abs_nonneg _).trans h1
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (abs_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) hc0)

theorem Fq_star (φ : ℝ → ℝ) : star (Fq P φ 0) = Fq P φ 0 := rfl

theorem EC_star {w : (DQ P).Pr} (hw : star w = w) {x : A P (DQ P)} (hx : x ∈ EC w) : star x ∈ EC w := fun π π' => by
  rw [Matrix.star_apply]
  have := congrArg star (hx π' π)
  rw [star_mul, star_mul, hw] at this
  exact this.symm

variable {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem closure_EC (φ : ℝ → ℝ) {b : A P (DQ P)} (hb : b ∈ Submonoid.closure (bddSet P L)) : b ∈ EC (Fq P φ 0) := by
  have fc : ∀ F Fb : (DQ P).R, (DQ P).fnP F Fb * Fq P φ 0 = Fq P φ 0 * (DQ P).fnP F Fb := fun F Fb =>
    Formalism.FourierDecayAlt.P.MAx1.multiplierPair_comm (DQ P) _ _ _ _
  have scm : ∀ F Fb : (DQ P).R, sc P (DQ P) ((DQ P).fnP F Fb) ∈ EC (Fq P φ 0) := fun F Fb =>
    sc_mem_EC (fc F Fb).symm
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, -⟩ := hL
  have mc : ∀ l, L.c l ∈ EC (Fq P φ 0) := fun l => by rw [hc]; exact scm _ _
  have mci : ∀ l, L.ci l ∈ EC (Fq P φ 0) := fun l => by rw [hci]; exact scm _ _
  have mcb : ∀ l, L.cb l ∈ EC (Fq P φ 0) := fun l => by rw [hcb]; exact scm _ _
  have mcbi : ∀ l, L.cbi l ∈ EC (Fq P φ 0) := fun l => by rw [hcbi]; exact scm _ _
  have mz : L.ζ ∈ EC (Fq P φ 0) := by rw [hz]; exact scm _ _
  have mzi : L.ζi ∈ EC (Fq P φ 0) := by rw [hzi]; exact scm _ _
  have mzb : L.ζb ∈ EC (Fq P φ 0) := by rw [hzb]; exact scm _ _
  have mzbi : L.ζbi ∈ EC (Fq P φ 0) := by rw [hzbi]; exact scm _ _
  have lp : ∀ {n : ℕ} (x : Fin n → A P (DQ P)), (∀ i, x i ∈ EC (Fq P φ 0)) → (List.ofFn x).prod ∈ EC (Fq P φ 0) :=
    fun x h => Submonoid.list_prod_mem _ fun y hy => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy; exact h i
  have mDr := lp L.c mc
  have mDri := lp L.ci mci
  have mDrb := lp L.cb mcb
  have mDrbi := lp L.cbi mcbi
  have mSS : ∀ i, SS P (DQ P) i ∈ EC (Fq P φ 0) := fun i => by
    classical
    exact alg_mem_EC _ _ (fun π' π => if M.Up P i π π' then ((Real.sqrt (M.Nrm P i π) : ℝ) : ℂ) else 0)
      (fun π' π => by simp only [SS, Matrix.of_apply]; split_ifs <;> simp)
  have hm : ∀ x ∈ bddSet P L, x ∈ EC (Fq P φ 0) := by
    rintro x (((hx | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact mzi
      · exact mzbi
      · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ mDr mz) (Submonoid.mul_mem _ mzbi mDrbi)
      · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ mDrb mzb) (Submonoid.mul_mem _ mzi mDri)
    · classical
      exact alg_mem_EC _ _ (fun π π' => if π = π' then f π else 0) fun π π' => by
        have e : kap P (DQ P) f = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (f π) := rfl
        rw [e, Matrix.diagonal_apply]; split_ifs <;> simp
    · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ mDrb mDri) (mSS i)
    · exact EC_star (Fq_star φ) (Submonoid.mul_mem _ (Submonoid.mul_mem _ mDrb mDri) (mSS i))
  exact (Submonoid.closure_le.2 hm) hb

theorem Ph_comm {φ : ℝ → ℝ} {b : A P (DQ P)} (hb : b ∈ Submonoid.closure (bddSet P L)) : Ph P φ * b = b * Ph P φ :=
  sc_comm_EC (closure_EC hL hLaw φ hb)

theorem b_mul_Z {b : A P (DQ P)} (hb : b ∈ Submonoid.closure (bddSet P L)) {k : ℕ} {z : A P (DQ P)}
    (hz : z ∈ Z P L k) : b * z ∈ Z P L k := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, b', v, hφ, hb', hv, hlen, rfl⟩ := hx
    refine Submodule.subset_span ⟨φ, b * b', v, hφ, Submonoid.mul_mem _ hb hb', hv, hlen, ?_⟩
    rw [← mul_assoc, ← mul_assoc, ← Ph_comm hL hLaw hb, mul_assoc (Ph P φ)]
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h1 => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1

theorem good_mul_Z {ψ : ℝ → ℝ} (hψ : Good ψ) {k : ℕ} {z : A P (DQ P)} (hz : z ∈ Z P L k) :
    Ph P ψ * z ∈ Z P L k := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, b', v, hφ, hb', hv, hlen, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun x => φ x * ψ x, b', v, admissible_mul_good hφ hψ, hb', hv, hlen, ?_⟩
    rw [← Ph_mul P hφ.1 hψ.1, ← mul_assoc, ← mul_assoc]
    congr 2
    unfold Ph
    rw [G.sc_mul, G.sc_mul]
    congr 1
    exact Formalism.FourierDecayAlt.P.MAx1.multiplierPair_comm (DQ P) _ _ _ _
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h1 => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1

theorem Gs_mul_Z {t : ℝ} (ht : t ≤ 0) {k : ℕ} {z : A P (DQ P)} (hz : z ∈ Z P L k) : G.Gs P t * z ∈ Z P L k := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, b', v, hφ, hb', hv, hlen, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun x => φ x * x ^ t, b', v, admissible_mul_rpow hφ ht, hb', hv, hlen, ?_⟩
    rw [← Ph_Gs P hφ.1, ← mul_assoc, ← mul_assoc]
    congr 2
    unfold Ph G.Gs
    rw [G.sc_mul, G.sc_mul]
    congr 1
    exact Formalism.FourierDecayAlt.P.MAx1.multiplierPair_comm (DQ P) _ _ _ _
  | zero => simp
  | add x y _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h1 => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD11

section S_AD_AD12

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L
open MeasureTheory ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem CF_act {s : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (hs : CF s g) (f : M.Ty P → SmQ P.r P.TT) (q : Qp P.r P.TT)
    (π : M.Ty P) : evQ P (actA P s f π) q = g q * evQ P (f π) q ∧
      evQ P (actA P (star s) f π) q = conj (g q) * evQ P (f π) q := by
  obtain ⟨h1, h2⟩ := SA_of_CF hs
  refine ⟨?_, ?_⟩
  · rw [h1, Finset.sum_eq_single π (fun b _ hb => by dsimp only; rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul])
      (by simp)]
    simp
  · rw [h2, Finset.sum_eq_single π (fun b _ hb => by dsimp only; rw [Matrix.diagonal_apply_ne _ hb, map_zero, zero_mul])
      (by simp)]
    simp

theorem star_CF {s : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (hs : CF s g) : CF (star s) (fun q => conj (g q)) := by
  obtain ⟨F, Fb, rfl, h1, h2⟩ := hs
  exact ⟨Fb, F, by rw [MAx2.R2.star_sc]; rfl, h2, fun q => by rw [Complex.conj_conj, h1]⟩

variable {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem gens_EC (F Fb : (DQ P).R) : L.ζi ∈ EC ((DQ P).fnP F Fb) ∧ L.ζbi ∈ EC ((DQ P).fnP F Fb) ∧
    L.D * L.Dbi ∈ EC ((DQ P).fnP F Fb) ∧ L.Db * L.Di ∈ EC ((DQ P).fnP F Fb) ∧
    (∀ f, kap P (DQ P) f ∈ EC ((DQ P).fnP F Fb)) ∧ ∀ i, L.Drb * L.Dri * SS P (DQ P) i ∈ EC ((DQ P).fnP F Fb) := by
  have fc : ∀ G' Gb : (DQ P).R, (DQ P).fnP G' Gb * (DQ P).fnP F Fb = (DQ P).fnP F Fb * (DQ P).fnP G' Gb :=
    fun G' Gb => Formalism.FourierDecayAlt.P.MAx1.multiplierPair_comm (DQ P) _ _ _ _
  have scm : ∀ G' Gb : (DQ P).R, sc P (DQ P) ((DQ P).fnP G' Gb) ∈ EC ((DQ P).fnP F Fb) := fun G' Gb =>
    sc_mem_EC (fc G' Gb).symm
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, -⟩ := hL
  have lp : ∀ {n : ℕ} (x : Fin n → A P (DQ P)), (∀ i, x i ∈ EC ((DQ P).fnP F Fb)) →
      (List.ofFn x).prod ∈ EC ((DQ P).fnP F Fb) :=
    fun x h => Submonoid.list_prod_mem _ fun y hy => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy; exact h i
  have mDr := lp L.c fun l => by rw [hc]; exact scm _ _
  have mDri := lp L.ci fun l => by rw [hci]; exact scm _ _
  have mDrb := lp L.cb fun l => by rw [hcb]; exact scm _ _
  have mDrbi := lp L.cbi fun l => by rw [hcbi]; exact scm _ _
  have mz : L.ζ ∈ EC ((DQ P).fnP F Fb) := by rw [hz]; exact scm _ _
  have mzi : L.ζi ∈ EC ((DQ P).fnP F Fb) := by rw [hzi]; exact scm _ _
  have mzb : L.ζb ∈ EC ((DQ P).fnP F Fb) := by rw [hzb]; exact scm _ _
  have mzbi : L.ζbi ∈ EC ((DQ P).fnP F Fb) := by rw [hzbi]; exact scm _ _
  have mSS : ∀ i, SS P (DQ P) i ∈ EC ((DQ P).fnP F Fb) := fun i => by
    classical
    exact alg_mem_EC _ _ (fun π' π => if M.Up P i π π' then ((Real.sqrt (M.Nrm P i π) : ℝ) : ℂ) else 0)
      (fun π' π => by simp only [SS, Matrix.of_apply]; split_ifs <;> simp)
  refine ⟨mzi, mzbi, Submonoid.mul_mem _ (Submonoid.mul_mem _ mDr mz) (Submonoid.mul_mem _ mzbi mDrbi),
    Submonoid.mul_mem _ (Submonoid.mul_mem _ mDrb mzb) (Submonoid.mul_mem _ mzi mDri), fun f => ?_,
    fun i => Submonoid.mul_mem _ (Submonoid.mul_mem _ mDrb mDri) (mSS i)⟩
  classical
  exact alg_mem_EC _ _ (fun π π' => if π = π' then f π else 0) fun π π' => by
    have e : kap P (DQ P) f = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (f π) := rfl
    rw [e, Matrix.diagonal_apply]; split_ifs <;> simp

theorem closure_EC_fnP (F Fb : (DQ P).R) {b : A P (DQ P)} (hb : b ∈ Submonoid.closure (bddSet P L)) :
    b ∈ EC ((DQ P).fnP F Fb) := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := gens_EC hL hLaw F Fb
  have m6' := (gens_EC hL hLaw Fb F).2.2.2.2.2
  have hm : ∀ x ∈ bddSet P L, x ∈ EC ((DQ P).fnP F Fb) := by
    rintro x (((hx | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [m1, m2, m3, m4]
    · exact m5 f
    · exact m6 i
    · refine fun π π' => ?_
      show (DQ P).fnP F Fb * star ((L.Drb * L.Dri * SS P (DQ P) i) π' π) =
        star ((L.Drb * L.Dri * SS P (DQ P) i) π' π) * (DQ P).fnP F Fb
      have h' := congrArg star (m6' i π' π)
      rw [star_mul, star_mul] at h'
      exact h'.symm
  exact (Submonoid.closure_le.2 hm) hb

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD12

section S_AD_AD13

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L
open MeasureTheory ComplexConjugate

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hL hLaw

theorem star_zi : star L.ζi = L.ζbi ∧ star L.ζbi = L.ζi := by
  have : Fact ((DQ P).Laws P.TT) := ⟨hLaw⟩
  have hs := Formalism.FourierDecayAlt.P.MAx1.starGens P (DQ P)
  obtain ⟨-, -, -, -, -, -, -, hzi, -, hzbi, -⟩ := hL
  refine ⟨by rw [hzi, hzbi]; exact hs.2.2.1, by rw [hzi, hzbi, ← hs.2.2.1, star_star]⟩

theorem star_Ds : star L.D = L.Db ∧ star L.Db = L.D ∧ star L.Di = L.Dbi ∧ star L.Dbi = L.Di := by
  obtain ⟨-, -, -, -, -, hz, hzb, -, -, -, -⟩ := Q.star_all hL hLaw
  obtain ⟨hzi, hzbi⟩ := star_zi hL hLaw
  have hDr := Q.star_Dr hL hLaw
  have hDri := H.star_Dri hL hLaw
  have hDrb : star L.Drb = L.Dr := by rw [← hDr, star_star]
  have hDrbi : star L.Drbi = L.Dri := by rw [← hDri, star_star]
  unfold LevelData.D LevelData.Db LevelData.Di LevelData.Dbi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [star_mul, hz, hDr]; exact H.cl_comm L (H.memζb L) (H.memDrb L)
  · rw [star_mul, hzb, hDrb]; exact H.cl_comm L (H.memζ L) (H.memDr L)
  · rw [star_mul, hzi, hDri]; exact H.cl_comm L (H.memDrbi L) (H.memζbi L)
  · rw [star_mul, hzbi, hDrbi]; exact H.cl_comm L (H.memDri L) (H.memζi L)

theorem star_kap (f : M.Ty P → ℂ) : star (kap P (DQ P) f) = kap P (DQ P) (fun π => conj (f π)) := by
  have e : ∀ g : M.Ty P → ℂ, kap P (DQ P) g = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (g π) := fun g => rfl
  rw [e, e, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1; funext π
  exact (algebraMap_star_comm _).symm

theorem star_closure {b : A P (DQ P)} (hb : b ∈ Submonoid.closure (bddSet P L)) :
    star b ∈ Submonoid.closure (bddSet P L) := by
  obtain ⟨hD, hDb, hDi, hDbi⟩ := star_Ds hL hLaw
  obtain ⟨hzi, hzbi⟩ := star_zi hL hLaw
  have gen : ∀ {x}, x ∈ bddSet P L → x ∈ Submonoid.closure (bddSet P L) := fun h => Submonoid.subset_closure h
  induction hb using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with (((hx | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [hzi]; exact gen (Or.inl (Or.inl (Or.inl (by simp))))
      · rw [hzbi]; exact gen (Or.inl (Or.inl (Or.inl (by simp))))
      · rw [star_mul, hDbi, hD, H.cl_comm L (H.memDi L) (H.memDb L)]
        exact gen (Or.inl (Or.inl (Or.inl (by simp))))
      · rw [star_mul, hDi, hDb, H.cl_comm L (H.memDbi L) (H.memD L)]
        exact gen (Or.inl (Or.inl (Or.inl (by simp))))
    · rw [star_kap hL hLaw]; exact gen (Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))
    · exact gen (Or.inr ⟨i, hi, rfl⟩)
    · rw [star_star]; exact gen (Or.inl (Or.inr ⟨i, hi, rfl⟩))
  | one => rw [star_one]; exact Submonoid.one_mem _
  | mul x y _ _ h1 h2 => rw [star_mul]; exact Submonoid.mul_mem _ h2 h1

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD13

section S_AD_AD14

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L
open MeasureTheory ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem ipA_eq (f g : M.Ty P → SmQ P.r P.TT) :
    ipA P f g = ∑ π, ∫ q, evQ P (f π) q * conj (evQ P (g π) q) ∂(mu0 P.r P.TT) := rfl

variable {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
variable (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem multAdj {m : ℕ} (hD : JDecay P L j m) {a β s : A P (DQ P)} {C : ℝ} (hβ : SAB β C) {g : Qp P.r P.TT → ℂ}
    (hs : CF s g) {W : List (A P (DQ P))} (hW : ∀ x ∈ W, x ∈ hatSet P L) (hWl : W.length ≤ m) {k : ℕ} (hk : k ≤ m)
    (hsa : star s * a ∈ Z P L k) :
    (∀ π, Integrable (fun q => evQ P (actA P a j π) q * conj (evQ P (actA P (β * s * W.prod) j π) q)) (mu0 P.r P.TT)) ∧
    (∀ π, Integrable (fun q => evQ P (actA P (star (β * s) * a) j π) q * conj (evQ P (actA P W.prod j π) q))
      (mu0 P.r P.TT)) ∧
    ipA P (actA P a j) (actA P (β * s * W.prod) j) = ipA P (actA P (star (β * s) * a) j) (actA P W.prod j) := by
  obtain ⟨Mβ, hSA, hC0, hMb⟩ := hβ
  obtain ⟨B, hB, hBb⟩ := zbound hTTp hL hLaw hD hk hsa
  have hS : ∀ q π, evQ P (actA P (star s * a) j π) q = conj (g q) * evQ P (actA P a j π) q := fun q π => by
    rw [F.actA_mul, (CF_act hs _ q π).2]
  have e1 : ∀ q π, evQ P (actA P (β * s * W.prod) j π) q =
      ∑ π', Mβ q π π' * (g q * evQ P (actA P W.prod j π') q) := fun q π => by
    rw [F.actA_mul, F.actA_mul, hSA.1]
    exact Finset.sum_congr rfl fun π' _ => by rw [(CF_act hs _ q π').1]
  have e2 : ∀ q π', evQ P (actA P (star (β * s) * a) j π') q =
      ∑ π, conj (Mβ q π π') * (conj (g q) * evQ P (actA P a j π) q) := fun q π' => by
    rw [star_mul, F.actA_mul, F.actA_mul, (CF_act hs _ q π').2, hSA.2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun π _ => by ring
  have hV : SqB (fun q => ∑ π', ‖evQ P (actA P W.prod j π') q‖) := sqB_sum _ _ fun π' _ => sqB_word hD hW hWl π'
  have hCB : SqB (fun q => C * B q) := sqB_smul hB hC0
  have hcard : SqB (fun q => (Fintype.card (M.Ty P) : ℝ) * (C * B q)) := sqB_smul hCB (Nat.cast_nonneg _)
  have cont : ∀ (x : A P (DQ P)) (y : A P (DQ P)) (π π' : M.Ty P),
      Continuous fun q => evQ P (actA P x j π) q * conj (evQ P (actA P y j π') q) := fun x y π π' =>
    (MAx3.evQ_cont P _).mul (Complex.continuous_conj.comp (MAx3.evQ_cont P _))
  have int1 : ∀ π, Integrable (fun q => evQ P (actA P a j π) q * conj (evQ P (actA P (β * s * W.prod) j π) q))
      (mu0 P.r P.TT) := fun π => by
    refine int_of_sqB (cont _ _ π π) hCB hV fun q => ?_
    rw [e1, norm_mul, Complex.norm_conj]
    calc ‖evQ P (actA P a j π) q‖ * ‖∑ π', Mβ q π π' * (g q * evQ P (actA P W.prod j π') q)‖
        ≤ ‖evQ P (actA P a j π) q‖ * ∑ π', C * (‖g q‖ * ‖evQ P (actA P W.prod j π') q‖) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun π' _ => by
            rw [norm_mul, norm_mul]; exact mul_le_mul_of_nonneg_right (hMb q π π') (by positivity))) (norm_nonneg _)
      _ = C * (‖g q‖ * ‖evQ P (actA P a j π) q‖) * ∑ π', ‖evQ P (actA P W.prod j π') q‖ := by
          rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ C * B q * ∑ π', ‖evQ P (actA P W.prod j π') q‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC0) (hV.2.1 q)
          have := hBb q π; rw [hS, norm_mul, Complex.norm_conj] at this; exact this
  have int2 : ∀ π', Integrable (fun q => evQ P (actA P (star (β * s) * a) j π') q *
      conj (evQ P (actA P W.prod j π') q)) (mu0 P.r P.TT) := fun π' => by
    refine int_of_sqB (cont _ _ π' π') hcard (sqB_word hD hW hWl π') fun q => ?_
    rw [e2, norm_mul, Complex.norm_conj]
    refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans ?_) (norm_nonneg _)
    calc ∑ π, ‖conj (Mβ q π π') * (conj (g q) * evQ P (actA P a j π) q)‖ ≤ ∑ _π : M.Ty P, C * B q :=
          Finset.sum_le_sum fun π _ => by
            rw [norm_mul, Complex.norm_conj, ← hS]
            exact mul_le_mul (hMb q π π') (hBb q π) (norm_nonneg _) hC0
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨int1, int2, ?_⟩
  rw [ipA_eq, ipA_eq, ← integral_finset_sum _ fun π _ => int1 π, ← integral_finset_sum _ fun π _ => int2 π]
  congr 1; funext q
  simp only [e1, e2, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD14

section S_Z_Z11

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R MeasureTheory Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.AD Formalism.FourierDecayAlt.P.MAx3.L
open Formalism.FourierDecayAlt.P.RuleGD
open ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem ipA_add_right {f g1 g2 : M.Ty P → SmQ P.r P.TT}
    (h1 : ∀ π, Integrable (fun q => evQ P (f π) q * conj (evQ P (g1 π) q)) (mu0 P.r P.TT))
    (h2 : ∀ π, Integrable (fun q => evQ P (f π) q * conj (evQ P (g2 π) q)) (mu0 P.r P.TT)) :
    ipA P f (g1 + g2) = ipA P f g1 + ipA P f g2 := by
  rw [ipA_eq, ipA_eq, ipA_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← integral_add (h1 π) (h2 π)]
  congr 1; funext q
  show evQ P (f π) q * conj (evQ P (g1 π) q + evQ P (g2 π) q) = _
  rw [map_add, mul_add]

theorem ipA_smul_right (c : ℂ) (f g : M.Ty P → SmQ P.r P.TT) :
    ipA P f (fun π => c • g π) = conj c * ipA P f g := by
  rw [ipA_eq, ipA_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← integral_const_mul]
  congr 1; funext q
  show evQ P (f π) q * conj (c * evQ P (g π) q) = _
  rw [map_mul]; ring

theorem ipA_zero_right (f : M.Ty P → SmQ P.r P.TT) : ipA P f 0 = 0 := by
  rw [ipA_eq]
  refine Finset.sum_eq_zero fun π _ => ?_
  have : (fun q => evQ P (f π) q * conj (evQ P ((0 : M.Ty P → SmQ P.r P.TT) π) q)) = fun _ => 0 := by
    funext q; show _ * conj (0 : ℂ) = 0; simp
  rw [this, integral_zero]

variable {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}

def QA (L : LevelData (A P (DQ P)) P.r) (j : M.Ty P → SmQ P.r P.TT) (a w : A P (DQ P)) : Prop :=
  (∀ π, Integrable (fun q => evQ P (actA P a j π) q * conj (evQ P (actA P w j π) q)) (mu0 P.r P.TT)) ∧
  (∀ π, Integrable (fun q => evQ P (actA P (star w * a) j π) q * conj (evQ P (j π) q)) (mu0 P.r P.TT)) ∧
  ipA P (actA P a j) (actA P w j) = ipA P (actA P (star w * a) j) j

theorem QA_zero (a : A P (DQ P)) : QA L j a 0 := by
  refine ⟨fun π => ?_, fun π => ?_, ?_⟩
  · rw [F.actA_zero]; exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun q => by
      show (0 : ℂ) = _ * conj (0 : ℂ); simp)
  · rw [star_zero, zero_mul, F.actA_zero]; exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun q => by
      show (0 : ℂ) = (0 : ℂ) * _; simp)
  · rw [F.actA_zero, star_zero, zero_mul, F.actA_zero, ipA_zero_right, ipA_zero_left]

theorem QA_add {a w1 w2 : A P (DQ P)} (h1 : QA L j a w1) (h2 : QA L j a w2) : QA L j a (w1 + w2) := by
  obtain ⟨i1, k1, e1⟩ := h1; obtain ⟨i2, k2, e2⟩ := h2
  refine ⟨fun π => ?_, fun π => ?_, ?_⟩
  · rw [F.actA_add]; exact ((i1 π).add (i2 π)).congr (Filter.Eventually.of_forall fun q => by
      show _ = evQ P (actA P a j π) q * conj (evQ P (actA P w1 j π) q + evQ P (actA P w2 j π) q)
      rw [map_add, mul_add]; rfl)
  · rw [star_add, add_mul, F.actA_add]; exact ((k1 π).add (k2 π)).congr (Filter.Eventually.of_forall fun q => by
      show _ = (evQ P (actA P (star w1 * a) j π) q + evQ P (actA P (star w2 * a) j π) q) * _
      rw [add_mul]; rfl)
  · rw [F.actA_add, ipA_add_right i1 i2, e1, e2, star_add, add_mul, F.actA_add, ipA_add_left k1 k2]

theorem QA_smul {a w : A P (DQ P)} (c : ℂ) (h : QA L j a w) : QA L j a (c • w) := by
  obtain ⟨i1, k1, e1⟩ := h
  refine ⟨fun π => ?_, fun π => ?_, ?_⟩
  · rw [F.actA_smul_mat]; exact ((i1 π).const_mul (conj c)).congr (Filter.Eventually.of_forall fun q => by
      show _ = evQ P (actA P a j π) q * conj (c * evQ P (actA P w j π) q)
      rw [map_mul]; ring)
  · rw [star_smul, smul_mul_assoc, F.actA_smul_mat]
    exact ((k1 π).const_mul (star c)).congr (Filter.Eventually.of_forall fun q => by
      show _ = (star c * evQ P (actA P (star w * a) j π) q) * _
      ring)
  · rw [F.actA_smul_mat, ipA_smul_right, e1, star_smul, smul_mul_assoc, F.actA_smul_mat, ipA_smul_left]
    rfl

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z11

section S_Z_Z12

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R MeasureTheory Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.AD Formalism.FourierDecayAlt.P.MAx3.L
open Formalism.FourierDecayAlt.P.RuleGD
open ComplexConjugate
open Formalism.FourierDecayAlt.P.MAx2.Jet (Phi)
open Formalism.FourierDecayAlt.P.MAx3.I4 (SB)

noncomputable section

variable {P : M.Par}

theorem cf_Ph {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) : CF (Ph P φ) (fun q => ((φ (Gq P q) : ℝ) : ℂ)) :=
  ⟨Phi P φ 0, Phi P φ 0, rfl, fun q => eval_cutoff_operator_zero P hφ q, fun q => by
    show evQ P (Phi P φ 0) q = _
    rw [eval_cutoff_operator_zero P hφ q, Complex.conj_ofReal]⟩

theorem CF_pow' {x : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (hx : CF x g) (n : ℕ) : CF (x ^ n) (fun q => g q ^ n) := by
  induction n with
  | zero => simpa using (CF_one : CF (1 : A P (DQ P)) (fun _ => 1))
  | succ n ih => rw [pow_succ]; simpa [pow_succ] using CF_mul ih hx

theorem star_Ph (φ : ℝ → ℝ) : star (Ph P φ) = Ph P φ := by
  unfold Ph sc
  rw [Matrix.scalar_apply]
  refine Matrix.ext fun π π' => ?_
  rw [Matrix.star_apply]
  by_cases h : π = π'
  · subst h; rw [Matrix.diagonal_apply_eq]; exact Fq_star φ
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, star_zero]

variable {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
variable (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem QA_gen {m : ℕ} (hD : JDecay P L j m) (hA : JAdj P L j m) {a : A P (DQ P)} {N : ℕ} (hm : N + N ≤ m)
    (hsa : ∀ φ, admitted φ → Ph P φ * L.Di ^ N * a ∈ Z P L N) {β : A P (DQ P)} (hβ : β ∈ SB L) {φ : ℝ → ℝ} (hφ : admitted φ)
    {W : List (A P (DQ P))} (hW : ∀ x ∈ W, x ∈ hatSet P L) (hWl : W.length ≤ N) :
    QA L j a (β * (L.Dbi ^ N * Ph P φ) * W.prod) := by
  obtain ⟨-, -, -, h4, -, -⟩ := star_more hL hLaw
  obtain ⟨-, hDi, -, hDbi, -⟩ := fnP_D hL
  obtain ⟨Cβ, hβC⟩ := SAB_closure hTTp hL hLaw hβ
  have hs : CF (L.Dbi ^ N * Ph P φ) _ := CF_mul (CF_pow' (cf_Dbi hTTp.le hL) N) (cf_Ph hφ.1)
  have hstar : star (L.Dbi ^ N * Ph P φ) = Ph P φ * L.Di ^ N := by rw [star_mul, star_Ph, star_pow, h4]
  have hsa' : star (L.Dbi ^ N * Ph P φ) * a ∈ Z P L N := by rw [hstar]; exact hsa φ hφ
  obtain ⟨int1, -, eq1⟩ := multAdj hTTp hL hLaw hD hβC hs hW (hWl.trans (by omega)) (k := N) (by omega) hsa'
  have hsβ : star β ∈ SB L := star_SB hL hLaw hβ
  have hz : star (β * (L.Dbi ^ N * Ph P φ)) * a ∈ Z P L N := by
    rw [star_mul, ← SB_comm_fnP hL hLaw hsβ (by rw [hstar]; exact isFnP_mul (isFnP_Ph φ) (isFnP_pow hDi N)), mul_assoc]
    exact SB_memZ hTTp hL hLaw hsβ hsa'
  have hp := adjPure hTTp hL hLaw hD hA W hW N (by omega) _ hz
  have hz2 : star (β * (L.Dbi ^ N * Ph P φ) * W.prod) * a ∈ Z P L (N + W.length) := by
    rw [star_mul, mul_assoc]; exact star_word_mem hTTp.le hL hLaw W hW hz
  refine ⟨int1, fun π => ?_, ?_⟩
  · have := int_Z hTTp hL hLaw hD (by omega) hz2 (W := []) (by simp) (by simp) π
    simpa [MAx2.R2.act_one] using this
  · rw [eq1, hp, star_mul (β * (L.Dbi ^ N * Ph P φ)) W.prod, mul_assoc]

theorem QA_NF {m : ℕ} (hD : JDecay P L j m) (hA : JAdj P L j m) {a : A P (DQ P)} {N : ℕ} (hm : N + N ≤ m)
    (hsa : ∀ φ, admitted φ → Ph P φ * L.Di ^ N * a ∈ Z P L N) {χ : ℝ → ℝ} (hχ : admitted χ) {y : A P (DQ P)}
    (hy : y ∈ NFD L N) : QA L j a (y * Ph P χ) := by
  obtain ⟨-, -, -, hDbi, -⟩ := fnP_D hL
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, H, hb, hH, hl, rfl⟩ := hx
    have hz : H.prod * Ph P χ ∈ Z P L (0 + H.length) :=
      word_memZ hTTp hL hLaw H (fun h hh => Or.inl (Or.inl (hH h hh))) (Ph_memZ hχ)
    rw [zero_add, hl] at hz
    rw [mul_assoc]
    suffices key : ∀ z ∈ Z P L N, QA L j a (b * L.Dbi ^ N * z) from key _ hz
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨φ, b', v, hφ, hb', hv, hlen, rfl⟩ := hz
      have e : b * L.Dbi ^ N * (Ph P φ * b' * v.prod) = (b * b') * (L.Dbi ^ N * Ph P φ) * v.prod := by
        have c := SB_comm_fnP hL hLaw hb' (isFnP_mul (isFnP_pow hDbi N) (isFnP_Ph φ))
        calc b * L.Dbi ^ N * (Ph P φ * b' * v.prod) = b * ((L.Dbi ^ N * Ph P φ) * b') * v.prod := by
              simp only [mul_assoc]
          _ = b * (b' * (L.Dbi ^ N * Ph P φ)) * v.prod := by rw [c]
          _ = _ := by simp only [mul_assoc]
      rw [e]
      exact QA_gen hTTp hL hLaw hD hA hm hsa (Submonoid.mul_mem _ hb hb') hφ hv hlen
    | zero => rw [mul_zero]; exact QA_zero a
    | add u v _ _ hu hv => rw [mul_add]; exact QA_add hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact QA_smul c hu
  | zero => rw [zero_mul]; exact QA_zero a
  | add u v _ _ hu hv => rw [add_mul]; exact QA_add hu hv
  | smul c u _ hu => rw [smul_mul_assoc]; exact QA_smul c hu

theorem hsa_U {N : ℕ} (f : M.Ty P → ℂ) {χ : ℝ → ℝ} (hχ : admitted χ) {x : A P (DQ P)} (hx : x ∈ NFD L N) :
    ∀ φ, admitted φ → Ph P φ * L.Di ^ N * ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) f * x * Ph P χ) ∈ Z P L N := by
  intro φ hφ
  obtain ⟨hD, hDi, hDb, hDbi, -⟩ := fnP_D hL
  have hW : IsFnP (L.ζ * L.ζb * L.GGi) :=
    isFnP_mul (isFnP_mul (fns_fnP hL (m_ζ L)) (fns_fnP hL (m_ζb L))) (fns_fnP hL (m_GGi L))
  have hk : kap P (DQ P) f ∈ SB L := Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b2, H2, hb2, hH2, hl2, rfl⟩ := hx
    have hβ : kap P (DQ P) f * b2 ∈ SB L := Submonoid.mul_mem _ hk hb2
    have hmid := mid_id (1 : A P (DQ P)) (kap P (DQ P) f) b2 (L.Di ^ N) ((L.ζ * L.ζb * L.GGi) ^ N) (L.Dbi ^ N)
      (by simp) (SB_comm_fnP hL hLaw hβ (isFnP_mul (isFnP_pow hDi N) (isFnP_pow hW N))).symm
    rw [DWD_pow hTTp hL hLaw, one_mul, mul_one] at hmid
    have e : Ph P φ * L.Di ^ N * ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) f * (b2 * L.Dbi ^ N * H2.prod) * Ph P χ) =
        Ph P φ * ((kap P (DQ P) f * b2) * (G.Gs P (-1) ^ N * (H2.prod * Ph P χ))) := by
      calc Ph P φ * L.Di ^ N * ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) f * (b2 * L.Dbi ^ N * H2.prod) * Ph P χ)
          = Ph P φ * (L.Di ^ N * ((L.ζ * L.ζb * L.GGi) ^ N * kap P (DQ P) f * (b2 * L.Dbi ^ N))) *
            (H2.prod * Ph P χ) := by simp only [mul_assoc]
        _ = _ := by rw [hmid]; simp only [mul_assoc]
    rw [e]
    have z1 : H2.prod * Ph P χ ∈ Z P L (0 + H2.length) :=
      word_memZ hTTp hL hLaw H2 (fun h hh => Or.inl (Or.inl (hH2 h hh))) (Ph_memZ hχ)
    rw [zero_add, hl2] at z1
    exact Ph_memZ_mul hTTp hL hLaw hφ (SB_memZ hTTp hL hLaw hβ (Gspow_memZ hTTp hL hLaw N z1))
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, add_mul, mul_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm]; exact Submodule.smul_mem _ c hu

end

end Formalism.FourierDecayAlt.P.MAx3.Z

end S_Z_Z12

section S_Z_Z13

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.Z

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.AD
open Formalism.FourierDecayAlt.P.MAx3.L
open ComplexConjugate

noncomputable section

theorem actA_finsum {P : M.Par} {ι : Type} (s : Finset ι) (x : ι → A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT) :
    actA P (∑ e ∈ s, x e) j = ∑ e ∈ s, actA P (x e) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [F.actA_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, F.actA_add, ih]

theorem ipA_sum_left {P : M.Par} {ι : Type} (s : Finset ι) (f : ι → M.Ty P → SmQ P.r P.TT) (g : M.Ty P → SmQ P.r P.TT)
    (h : ∀ e ∈ s, ∀ π, Integrable (fun q => evQ P (f e π) q * conj (evQ P (g π) q)) (mu0 P.r P.TT)) :
    ipA P (∑ e ∈ s, f e) g = ∑ e ∈ s, ipA P (f e) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ipA_zero_left g
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ π, Integrable (fun q => evQ P ((∑ e ∈ s, f e) π) q * conj (evQ P (g π) q)) (mu0 P.r P.TT) := by
      intro π
      have hint := integrable_finset_sum s (fun e he => h e (Finset.mem_insert_of_mem he) π)
      refine hint.congr (Filter.Eventually.of_forall fun q => ?_)
      simp only [Finset.sum_apply]
      rw [MAx2.Jet.evQ_sum, Finset.sum_mul]
    rw [ipA_add_left (h a (Finset.mem_insert_self a s)) hs, ih fun e he => h e (Finset.mem_insert_of_mem he)]

end

end Formalism.FourierDecayAlt.P.MAx3.Z

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.AD
open Formalism.FourierDecayAlt.P.MAx3.Z

theorem theorem_P_adjoint : Formalism.FourierDecayAlt.MA.ThmPAdj := by
  intro P l L j lam α β Lb c Ntot hH N Y hN hB ε hε
  have hz := T_memZ hH Y hN hB hε
  obtain ⟨⟨hOK, hl1, hlk, hML, hu, hu', hαβ, hcut⟩, hD, hA, hE, hN1, -⟩ := id hH
  have hTTp : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hLaw := analytic_laws P.r P.TT hTTp.le
  have hcw : M.CutWord P l (wordP (List.ofFn Y)) := MAx3.F.cutWord_of hH c (List.ofFn Y) hB (by simpa using hN)
  obtain ⟨L', hL', -, -, hFC⟩ := model_frame_analytic P hOK l hl1 hlk
  have hLL := MAx3.F.level_unique P (DQ P) L' L hL' hML
  subst hLL
  have hFCw := hFC (Fin (List.ofFn Y).length) (wordP (List.ofFn Y)) hcw
  have hS := sites_admissible P (DQ P) hLaw l
  have hFr : ∀ w' : List ℝ, M.CutWord P l (wordP w') → IsFrame L' (ofWord L' (startM P (DQ P) l) (wordP w')) :=
    fun w' h => (hFC _ _ h).1
  set cs0 : Ix (Fin (List.ofFn Y).length) → M.Ty P → ℂ := fun e π => cs (M.x0 P l π) (M.qC P) (wordP (List.ofFn Y)) e
    with hcs0
  have hd : dRing P l L' Y = (wt L' : SlopeTestRemainingChoices (Fin (List.ofFn Y).length) (A P (DQ P))) ^ (List.ofFn Y).length *
      Matrix.diagonal (fun e => kap P (DQ P) (cs0 e)) := by
    unfold dRing frW
    rw [hFCw.2.2.1]
  have hm : (List.ofFn Y).length + (List.ofFn Y).length ≤ 2 * Ntot + 2 := by rw [List.length_ofFn]; omega
  have hU : ∀ e, (∑ e', dRing P l L' Y e e' * gRing P l L' Y e') =
      (L'.ζ * L'.ζb * L'.GGi) ^ (List.ofFn Y).length * kap P (DQ P) (cs0 e) * gRing P l L' Y e := fun e => by
    rw [hd]; exact MAx3.PG.d_g_sum hTTp hML hLaw cs0 (gRing P l L' Y) e
  have hT : (∑ e, ∑ e', star (gRing P l L' Y e) * dRing P l L' Y e e' * gRing P l L' Y e') =
      ∑ e, star (gRing P l L' Y e) * ((L'.ζ * L'.ζb * L'.GGi) ^ (List.ofFn Y).length * kap P (DQ P) (cs0 e) * gRing P l L' Y e) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← hU e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e' _ => by rw [mul_assoc]
  have hg : ∀ e, gRing P l L' Y e ∈ NFD L' (List.ofFn Y).length := fun e =>
    normal_form_two_le_degree hML hLaw _ (gRw_NF hML hLaw hS hFr (List.ofFn Y) hcw e)
  have hχ : admitted (MAx3.PG.chi c ε) := admissible_cutoff c hε

  have hL1 : ipA P (actA P (∑ e, ∑ e', star (gRing P l L' Y e) * dRing P l L' Y e e' * gRing P l L' Y e') (chiJ P j c ε))
      (chiJ P j c ε) = ipA P (actA P (Ph P (MAx3.PG.chi c ε) * (∑ e, ∑ e', star (gRing P l L' Y e) * dRing P l L' Y e e' *
        gRing P l L' Y e') * Ph P (MAx3.PG.chi c ε)) j) j := by
    rw [chiJ_Ph, mul_one, ← MAx3.F.actA_mul]
    have hs : CF (Ph P (MAx3.PG.chi c ε)) _ := cf_Ph hχ.1
    have hsa : star (Ph P (MAx3.PG.chi c ε)) * ((∑ e, ∑ e', star (gRing P l L' Y e) * dRing P l L' Y e e' *
        gRing P l L' Y e') * Ph P (MAx3.PG.chi c ε)) ∈ Z P L' ((List.ofFn Y).length + (List.ofFn Y).length) := by rw [star_Ph, ← mul_assoc]; exact hz
    obtain ⟨SeriesExist, hSB1⟩ : ∃ C, SAB (1 : A P (DQ P)) C := ⟨1, SAB_one⟩
    obtain ⟨-, -, e1⟩ := multAdj hTTp hML hLaw hD hSB1 hs (W := []) (by simp) (by simp) (k := (List.ofFn Y).length + (List.ofFn Y).length) hm hsa
    simp only [List.prod_nil, mul_one, one_mul, star_one, MAx2.R2.act_one] at e1
    rw [e1, star_Ph, ← mul_assoc]

  have hR1 : ∑ e, ipA P (actA P (∑ e', dRing P l L' Y e e' * gRing P l L' Y e') (chiJ P j c ε))
      (actA P (gRing P l L' Y e) (chiJ P j c ε)) = ipA P (actA P (Ph P (MAx3.PG.chi c ε) * (∑ e, ∑ e', star (gRing P l L' Y e) *
        dRing P l L' Y e e' * gRing P l L' Y e') * Ph P (MAx3.PG.chi c ε)) j) j := by
    have hq : ∀ e, QA L' j ((L'.ζ * L'.ζb * L'.GGi) ^ (List.ofFn Y).length * kap P (DQ P) (cs0 e) * gRing P l L' Y e * Ph P (MAx3.PG.chi c ε))
        (gRing P l L' Y e * Ph P (MAx3.PG.chi c ε)) := fun e =>
      QA_NF hTTp hML hLaw hD hA hm (hsa_U hTTp hML hLaw (cs0 e) hχ (hg e)) hχ (hg e)
    have step : ∀ e, ipA P (actA P (∑ e', dRing P l L' Y e e' * gRing P l L' Y e') (chiJ P j c ε))
        (actA P (gRing P l L' Y e) (chiJ P j c ε)) =
        ipA P (actA P (star (gRing P l L' Y e * Ph P (MAx3.PG.chi c ε)) *
          ((L'.ζ * L'.ζb * L'.GGi) ^ (List.ofFn Y).length * kap P (DQ P) (cs0 e) * gRing P l L' Y e * Ph P (MAx3.PG.chi c ε))) j) j := by
      intro e
      rw [chiJ_Ph, mul_one, ← MAx3.F.actA_mul, ← MAx3.F.actA_mul, hU e]
      exact (hq e).2.2
    rw [Finset.sum_congr rfl fun e _ => step e, ← ipA_sum_left _ _ _ fun e _ => (hq e).2.1, ← actA_finsum]
    congr 2
    rw [hT, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [star_mul, star_Ph]
    simp only [mul_assoc]
  unfold formFdF formDF
  rw [hL1, hR1]

end Formalism.FourierDecayAlt.P

end S_Z_Z13

section S_AB_AB1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r) (S : Submonoid A)

def MS (n k : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ {x | ∃ β X, β ∈ S ∧ X ∈ minusHats L ∧ x = β * (L.D ^ n * L.Dbi ^ k) * X}

theorem Ahatv_Dpow (n : ℕ) (Y : ℂ) : L.Ahatv Y * L.D ^ n = L.D ^ n * L.Ahatv Y :=
  (Commute.pow_right (Ahatv_D L Y) n).eq
theorem raising_variant_D_pow (n : ℕ) (Y : ℂ) : L.R0v Y * L.D ^ n = L.D ^ n * L.R0v Y :=
  (Commute.pow_right (raising_variant_commute_D L Y) n).eq

theorem Ahatv_DD (n k : ℕ) (Y : ℂ) : L.Ahatv Y * (L.D ^ n * L.Dbi ^ k) = (L.D ^ n * L.Dbi ^ k) * L.Ahatv (Y + k) := by
  rw [← mul_assoc, Ahatv_Dpow, mul_assoc, Ahatv_Dbipow, mul_assoc]

variable {L S}

theorem MS_gen {β X : A} (hβ : β ∈ S) (hX : X ∈ minusHats L) (n k : ℕ) : β * (L.D ^ n * L.Dbi ^ k) * X ∈ MS L S n k :=
  Submodule.subset_span ⟨β, X, hβ, hX, rfl⟩

theorem MS_sum {n k : ℕ} {ι : Type} (ts : List ι) (f : ι → A) (h : ∀ x ∈ ts, f x ∈ MS L S n k) :
    (ts.map f).sum ∈ MS L S n k := by
  induction ts with
  | nil => simp
  | cons a ts ih =>
    rw [List.map_cons, List.sum_cons]
    exact Submodule.add_mem _ (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem hatv_past (hV : HypV L S) {X : A} (hX : X ∈ minusHats L) {β : A} (hβ : β ∈ S) (n k : ℕ) :
    X * (β * (L.D ^ n * L.Dbi ^ k)) ∈ MS L S n k := by
  have hc : ∀ z, z ∈ Subring.closure (FS L) → (L.D ^ n * L.Dbi ^ k) * z = z * (L.D ^ n * L.Dbi ^ k) := fun z hz =>
    cl_comm L (Subring.mul_mem _ (memPow L (memD L) n) (memPow L (memDbi L) k)) hz
  rcases hX with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨t, ht⟩ := hV.ahatv β hβ
    rw [← mul_assoc, ht, mul_assoc, Ahatv_DD, ← mul_assoc]
    exact MS_gen hβ (Or.inl ⟨_, rfl⟩) n k
  · obtain ⟨t, ts, hts, e⟩ := hV.r0v β hβ y
    obtain ⟨cs, hcs⟩ := raising_variant_D_bar_inv_pow L k (y + t)
    rw [← mul_assoc, e, add_mul]
    refine Submodule.add_mem _ ?_ ?_
    ·
      have e2 : β * L.R0v (y + t) * (L.D ^ n * L.Dbi ^ k) = β * (L.D ^ n * L.Dbi ^ k) * L.R0v (y + t + k) +
          (cs.map fun x => x.1 • ((β * (L.Dr * L.Dbi)) * (L.D ^ n * L.Dbi ^ k) * L.Ahatv x.2)).sum := by
        rw [mul_assoc β, ← mul_assoc (L.R0v _), raising_variant_D_pow, mul_assoc, hcs, mul_add, mul_add, mul_add]
        congr 1
        · simp only [mul_assoc]
        · rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
          congr 1
          refine List.map_congr_left fun x _ => ?_
          simp only [mul_smul_comm]
          congr 1
          have h1 := hc (L.Dr * L.Dbi) (Subring.mul_mem _ (memDr L) (memDbi L))
          calc β * (L.D ^ n * (L.Dbi ^ k * (L.Dr * L.Dbi * L.Ahatv x.2)))
              = β * ((L.D ^ n * L.Dbi ^ k) * (L.Dr * L.Dbi) * L.Ahatv x.2) := by simp only [mul_assoc]
            _ = β * ((L.Dr * L.Dbi) * (L.D ^ n * L.Dbi ^ k) * L.Ahatv x.2) := by rw [h1]
            _ = _ := by simp only [mul_assoc]
      rw [e2]
      refine Submodule.add_mem _ (MS_gen hβ (Or.inr ⟨_, rfl⟩) n k) (MS_sum _ _ fun x _ => ?_)
      exact Submodule.smul_mem _ _ (MS_gen (S.mul_mem hβ hV.drv) (Or.inl ⟨_, rfl⟩) n k)
    ·
      rw [← List.sum_map_mul_right]
      refine MS_sum _ _ fun x hx => ?_
      simp only [smul_mul_assoc]
      refine Submodule.smul_mem _ _ ?_
      rw [mul_assoc, Ahatv_DD, ← mul_assoc]
      exact MS_gen (hts x hx) (Or.inl ⟨_, rfl⟩) n k

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB1

section S_AD_AD15

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L
open MeasureTheory ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem ipA_add_right {f g1 g2 : M.Ty P → SmQ P.r P.TT}
    (h1 : ∀ π, Integrable (fun q => evQ P (f π) q * conj (evQ P (g1 π) q)) (mu0 P.r P.TT))
    (h2 : ∀ π, Integrable (fun q => evQ P (f π) q * conj (evQ P (g2 π) q)) (mu0 P.r P.TT)) :
    ipA P f (g1 + g2) = ipA P f g1 + ipA P f g2 := by
  rw [ipA_eq, ipA_eq, ipA_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← integral_add (h1 π) (h2 π)]
  congr 1; funext q
  show evQ P (f π) q * conj (evQ P (g1 π) q + evQ P (g2 π) q) = _
  rw [map_add]; ring

theorem ipA_smul_right (c : ℂ) (f g : M.Ty P → SmQ P.r P.TT) :
    ipA P f (fun π => c • g π) = conj c * ipA P f g := by
  rw [ipA_eq, ipA_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← integral_const_mul]
  congr 1; funext q
  show evQ P (f π) q * conj (c * evQ P (g π) q) = _
  rw [map_mul]; ring

theorem ipA_zero_right (f : M.Ty P → SmQ P.r P.TT) : ipA P f 0 = 0 := by
  rw [ipA_eq]
  refine Finset.sum_eq_zero fun π _ => ?_
  have : (fun q => evQ P (f π) q * conj (evQ P ((0 : M.Ty P → SmQ P.r P.TT) π) q)) = fun _ => 0 := by
    funext q; show _ * conj (0 : ℂ) = 0; simp
  rw [this, integral_zero]

variable {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
variable (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

def CanonTerm (L : LevelData (A P (DQ P)) P.r) (m : ℕ) (a : A P (DQ P)) (t : ℂ × A P (DQ P) × A P (DQ P) × List (A P (DQ P))) :
    Prop :=
  t.2.1 ∈ Submonoid.closure (bddSet P L) ∧ (∃ g, CF t.2.2.1 g) ∧ (∀ x ∈ t.2.2.2, x ∈ hatSet P L) ∧
    ∃ k, k + t.2.2.2.length ≤ m ∧ star t.2.2.1 * a ∈ Z P L k

def canonSum (ts : List (ℂ × A P (DQ P) × A P (DQ P) × List (A P (DQ P)))) : A P (DQ P) :=
  (ts.map fun t => t.1 • (t.2.1 * t.2.2.1 * t.2.2.2.prod)).sum

theorem canonical_sum_integrable {m : ℕ} (hD : JDecay P L j m) (hA : JAdj P L j m) (a : A P (DQ P)) :
    ∀ ts : List (ℂ × A P (DQ P) × A P (DQ P) × List (A P (DQ P))), (∀ t ∈ ts, CanonTerm L m a t) →
      (∀ π, Integrable (fun q => evQ P (actA P a j π) q * conj (evQ P (actA P (canonSum ts) j π) q)) (mu0 P.r P.TT)) ∧
      (∀ π, Integrable (fun q => evQ P (actA P (star (canonSum ts) * a) j π) q * conj (evQ P (j π) q)) (mu0 P.r P.TT)) ∧
      ipA P (actA P a j) (actA P (canonSum ts) j) = ipA P (actA P (star (canonSum ts) * a) j) j
  | [], _ => by
    simp only [canonSum, List.map_nil, List.sum_nil, star_zero, zero_mul, F.actA_zero]
    refine ⟨fun π => ?_, fun π => ?_, by rw [ipA_zero_right, ipA_zero_left]⟩ <;>
    · exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun q => by
        show (0 : ℂ) = _; simp [evQ])
  | t :: ts, h => by
    obtain ⟨c, β, s, W⟩ := t
    obtain ⟨hβ, ⟨g, hs⟩, hW, k, hkm, hsa⟩ := h (c, β, s, W) (by simp)
    obtain ⟨i1, i2, ih3⟩ := canonical_sum_integrable hD hA a ts fun t ht => h t (by simp [ht])
    obtain ⟨C, hC⟩ := SAB_closure hTTp hL hLaw hβ
    obtain ⟨m1, m2, m3⟩ := multAdj hTTp hL hLaw hD hC hs hW (by omega) (by omega) hsa

    have hz : star (β * s) * a ∈ Z P L k := by
      obtain ⟨F, Fb, rfl, -, -⟩ := hs
      have hsb := star_closure hL hLaw hβ
      have hc : star (sc P (DQ P) ((DQ P).fnP F Fb)) * star β = star β * star (sc P (DQ P) ((DQ P).fnP F Fb)) := by
        rw [MAx2.R2.star_sc]
        exact sc_comm_EC (closure_EC_fnP hL hLaw Fb F hsb)
      rw [star_mul, hc, mul_assoc]
      exact b_mul_Z hL hLaw hsb hsa
    have hzW : star W.prod * (star (β * s) * a) ∈ Z P L (k + W.length) := star_word_mem hTTp.le hL hLaw W hW hz
    have pure := adjPure hTTp hL hLaw hD hA W hW k hkm _ hz
    have eT : star (c • (β * s * W.prod)) * a = conj c • (star W.prod * (star (β * s) * a)) := by
      rw [star_smul, smul_mul_assoc, star_mul, mul_assoc]; rfl
    have hj : actA P ([] : List (A P (DQ P))).prod j = j := by rw [List.prod_nil, MAx2.R2.act_one]
    have iT : ∀ π, Integrable (fun q => evQ P (actA P (star (c • (β * s * W.prod)) * a) j π) q *
        conj (evQ P (j π) q)) (mu0 P.r P.TT) := fun π => by
      have := int_Z hTTp hL hLaw hD (by omega) hzW (W := []) (by simp) (by simp) π
      rw [hj] at this
      have e : (fun q => evQ P (actA P (star (c • (β * s * W.prod)) * a) j π) q * conj (evQ P (j π) q)) =
          fun q => conj c * (evQ P (actA P (star W.prod * (star (β * s) * a)) j π) q * conj (evQ P (j π) q)) := by
        funext q; rw [eT, F.actA_smul_mat]
        show (conj c * evQ P (actA P (star W.prod * (star (β * s) * a)) j π) q) * conj (evQ P (j π) q) = _
        ring
      rw [e]; exact this.const_mul _
    have iA : ∀ π, Integrable (fun q => evQ P (actA P a j π) q * conj (evQ P (actA P (c • (β * s * W.prod)) j π) q))
        (mu0 P.r P.TT) := fun π => by
      have e : (fun q => evQ P (actA P a j π) q * conj (evQ P (actA P (c • (β * s * W.prod)) j π) q)) =
          fun q => conj c * (evQ P (actA P a j π) q * conj (evQ P (actA P (β * s * W.prod) j π) q)) := by
        funext q; rw [F.actA_smul_mat]
        show evQ P (actA P a j π) q * conj (c * evQ P (actA P (β * s * W.prod) j π) q) = _
        rw [map_mul]; ring
      rw [e]; exact (m1 π).const_mul _
    have hsum : canonSum ((c, β, s, W) :: ts) = c • (β * s * W.prod) + canonSum ts := by
      simp [canonSum]
    rw [hsum]
    refine ⟨fun π => ?_, fun π => ?_, ?_⟩
    · have e : (fun q => evQ P (actA P a j π) q *
            conj (evQ P (actA P (c • (β * s * W.prod) + canonSum ts) j π) q)) =
          fun q => evQ P (actA P a j π) q * conj (evQ P (actA P (c • (β * s * W.prod)) j π) q) +
            evQ P (actA P a j π) q * conj (evQ P (actA P (canonSum ts) j π) q) := by
        funext q; rw [F.actA_add]
        show evQ P (actA P a j π) q * conj (evQ P (actA P (c • (β * s * W.prod)) j π) q +
          evQ P (actA P (canonSum ts) j π) q) = _
        rw [map_add]; ring
      rw [e]; exact (iA π).add (i1 π)
    · have e : (fun q => evQ P (actA P (star (c • (β * s * W.prod) + canonSum ts) * a) j π) q * conj (evQ P (j π) q)) =
          fun q => evQ P (actA P (star (c • (β * s * W.prod)) * a) j π) q * conj (evQ P (j π) q) +
            evQ P (actA P (star (canonSum ts) * a) j π) q * conj (evQ P (j π) q) := by
        funext q; rw [star_add, add_mul, F.actA_add]
        show (evQ P (actA P (star (c • (β * s * W.prod)) * a) j π) q +
          evQ P (actA P (star (canonSum ts) * a) j π) q) * conj (evQ P (j π) q) = _
        ring
      rw [e]; exact (iT π).add (i2 π)
    · rw [F.actA_add, ipA_add_right iA i1, star_add, add_mul, F.actA_add, ipA_add_left iT i2, ih3]
      congr 1
      rw [F.actA_smul_mat, ipA_smul_right, m3, pure, eT, F.actA_smul_mat, ipA_smul_left]

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD15

section S_AB_AB2

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem W_eq : L.ζ * L.ζb * L.GGi = L.D * L.Db * G.Gs P (-1) := by
  have h := WDD hTTp hL hLaw
  obtain ⟨hD, hDi, hDb, hDbi, -⟩ := fnP_D hL
  have hW : IsFnP (L.ζ * L.ζb * L.GGi) :=
    isFnP_mul (isFnP_mul (fns_fnP hL (m_ζ L)) (fns_fnP hL (m_ζb L))) (fns_fnP hL (m_GGi L))
  calc L.ζ * L.ζb * L.GGi = L.ζ * L.ζb * L.GGi * ((L.Di * L.D) * (L.Dbi * L.Db)) := by
        rw [Di_D, Dbi_Db, mul_one, mul_one]
    _ = L.ζ * L.ζb * L.GGi * (L.Di * L.Dbi) * (L.D * L.Db) := by
        rw [mul_assoc (L.Di) L.D, ← mul_assoc L.D, isFnP_comm hD hDbi]; simp only [mul_assoc]
    _ = L.D * L.Db * G.Gs P (-1) := by rw [h, isFnP_comm (isFnP_Gs (-1)) (isFnP_mul hD hDb)]

theorem hatv_Gs {X : A P (DQ P)} (hX : X ∈ minusHats L) : ∃ X', X' ∈ minusHats L ∧ X * G.Gs P (-1) = G.Gs P (-1) * X' := by
  rcases hX with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · refine ⟨L.Ahatv (y + 1), Or.inl ⟨_, rfl⟩, ?_⟩
    have h := (Formalism.FourierDecayAlt.P.MAx3.L.conj_hatv hTTp.le hL (-1) y).1
    rw [neg_neg] at h
    have e : y - ((-1 : ℝ) : ℂ) = y + 1 := by push_cast; ring
    rw [e] at h
    rw [← h, ← mul_assoc, ← mul_assoc, show G.Gs P (-1) * G.Gs P 1 = 1 by simpa using G.Gs_mul_neg P (-1), one_mul]
  · refine ⟨L.R0v (y + 1), Or.inr ⟨_, rfl⟩, ?_⟩
    have h := (Formalism.FourierDecayAlt.P.MAx3.L.conj_hatv hTTp.le hL (-1) y).2
    rw [neg_neg] at h
    have e : y - ((-1 : ℝ) : ℂ) = y + 1 := by push_cast; ring
    rw [e] at h
    rw [← h, ← mul_assoc, ← mul_assoc, show G.Gs P (-1) * G.Gs P 1 = 1 by simpa using G.Gs_mul_neg P (-1), one_mul]

theorem hatv_Gspow {X : A P (DQ P)} (hX : X ∈ minusHats L) (m : ℕ) :
    ∃ X', X' ∈ minusHats L ∧ X * G.Gs P (-1) ^ m = G.Gs P (-1) ^ m * X' := by
  induction m generalizing X with
  | zero => exact ⟨X, hX, by simp⟩
  | succ m ih =>
    obtain ⟨X1, h1, e1⟩ := hatv_Gs hTTp hL hLaw hX
    obtain ⟨X2, h2, e2⟩ := ih h1
    refine ⟨X2, h2, ?_⟩
    rw [pow_succ', ← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]

def MSG (L : LevelData (A P (DQ P)) P.r) (n k m : ℕ) : Submodule ℂ (A P (DQ P)) :=
  Submodule.span ℂ {x | ∃ β X, β ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L ∧ X ∈ minusHats L ∧
    x = β * (L.D ^ n * L.Dbi ^ k) * G.Gs P (-1) ^ m * X}

theorem hatv_past_G {X : A P (DQ P)} (hX : X ∈ minusHats L) {β : A P (DQ P)} (hβ : β ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L) (n k m : ℕ) :
    X * (β * (L.D ^ n * L.Dbi ^ k) * G.Gs P (-1) ^ m) ∈ MSG L n k m := by
  have h := hatv_past (hypV_model hL hLaw) hX hβ n k
  rw [← mul_assoc]
  refine span_mul_right h ?_
  · intro x hx
    obtain ⟨β', X', hβ', hX', rfl⟩ := hx
    obtain ⟨X'', h'', e⟩ := hatv_Gspow hTTp hL hLaw hX' m
    rw [mul_assoc, e, ← mul_assoc]
    exact Submodule.subset_span ⟨β', X'', hβ', h'', rfl⟩
where
  span_mul_right {T : Set (A P (DQ P))} {M : Submodule ℂ (A P (DQ P))} {x : A P (DQ P)} (hx : x ∈ Submodule.span ℂ T)
      (h : ∀ y ∈ T, y * G.Gs P (-1) ^ m ∈ M) : x * G.Gs P (-1) ^ m ∈ M := by
    induction hx using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp
    | add a b _ _ h1 h2 => rw [add_mul]; exact M.add_mem h1 h2
    | smul c a _ h1 => rw [smul_mul_assoc]; exact M.smul_mem c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB2

section S_AB_AB3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem minus_sub_hat {X : A P (DQ P)} (hX : X ∈ minusHats L) : X ∈ hatSet P L := by
  rcases hX with hX | hX
  · exact Or.inl (Or.inr hX)
  · exact Or.inr hX

theorem MSG_Z {N n k m : ℕ} (hγ : L.Di ^ N * (L.D ^ n * L.Dbi ^ k) ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L) {ψ : ℝ → ℝ} (hψ : admitted ψ)
    {H : List (A P (DQ P))} (hH : ∀ h ∈ H, h ∈ hatSet P L) {z : A P (DQ P)} (hz : z ∈ MSG L n k m) :
    L.Di ^ N * Ph P ψ * (z * H.prod) ∈ Z P L (H.length + 1) := by
  obtain ⟨hD, hDi, hDb, hDbi, -⟩ := fnP_D hL
  have hDD : IsFnP (L.D ^ n * L.Dbi ^ k) := isFnP_mul (isFnP_pow hD n) (isFnP_pow hDbi k)
  have hGm : IsFnP (G.Gs P (-1) ^ m) := isFnP_pow (isFnP_Gs (-1)) m
  have hDiN : IsFnP (L.Di ^ N) := isFnP_pow hDi N
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, X, hβ, hX, rfl⟩ := hx
    have e : L.Di ^ N * Ph P ψ * (β * (L.D ^ n * L.Dbi ^ k) * G.Gs P (-1) ^ m * X * H.prod) =
        G.Gs P (-1) ^ m * (Ph P ψ * (β * (L.Di ^ N * (L.D ^ n * L.Dbi ^ k))) * (X :: H).prod) := by
      have c1 : L.Di ^ N * Ph P ψ = Ph P ψ * L.Di ^ N := isFnP_comm hDiN (isFnP_Ph ψ)
      have c2 : L.Di ^ N * β = β * L.Di ^ N := (SB_comm_fnP hL hLaw hβ hDiN).symm
      have c3 : L.D ^ n * L.Dbi ^ k * G.Gs P (-1) ^ m = G.Gs P (-1) ^ m * (L.D ^ n * L.Dbi ^ k) := isFnP_comm hDD hGm
      have c4 : L.Di ^ N * G.Gs P (-1) ^ m = G.Gs P (-1) ^ m * L.Di ^ N := isFnP_comm hDiN hGm
      have c5 : β * G.Gs P (-1) ^ m = G.Gs P (-1) ^ m * β := SB_comm_fnP hL hLaw hβ hGm
      have c6 : Ph P ψ * G.Gs P (-1) ^ m = G.Gs P (-1) ^ m * Ph P ψ := isFnP_comm (isFnP_Ph ψ) hGm
      rw [List.prod_cons]
      calc L.Di ^ N * Ph P ψ * (β * (L.D ^ n * L.Dbi ^ k) * G.Gs P (-1) ^ m * X * H.prod)
          = Ph P ψ * (L.Di ^ N * β) * ((L.D ^ n * L.Dbi ^ k) * G.Gs P (-1) ^ m) * (X * H.prod) := by
            rw [c1]; simp only [mul_assoc]
        _ = Ph P ψ * β * (L.Di ^ N * (G.Gs P (-1) ^ m * (L.D ^ n * L.Dbi ^ k))) * (X * H.prod) := by
            rw [c2, c3]; simp only [mul_assoc]
        _ = Ph P ψ * (β * G.Gs P (-1) ^ m) * (L.Di ^ N * (L.D ^ n * L.Dbi ^ k)) * (X * H.prod) := by
            rw [← mul_assoc (L.Di ^ N), c4]; simp only [mul_assoc]
        _ = (Ph P ψ * G.Gs P (-1) ^ m) * β * (L.Di ^ N * (L.D ^ n * L.Dbi ^ k)) * (X * H.prod) := by
            rw [c5]; simp only [mul_assoc]
        _ = _ := by rw [c6]; simp only [mul_assoc]
    rw [e]
    refine Gspow_memZ hTTp hL hLaw m (Submodule.subset_span ⟨ψ, _, X :: H, hψ, Submonoid.mul_mem _ hβ hγ, ?_, by simp, rfl⟩)
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact minus_sub_hat hTTp hL hLaw hX
    · exact hH h hh
  | zero => simp
  | add a b _ _ h1 h2 => rw [add_mul, mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c a _ h1 => rw [smul_mul_assoc, mul_smul_comm]; exact Submodule.smul_mem _ c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB3

section S_AB_AB4

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par}

abbrev FnS (P : M.Par) : Subring (A P (DQ P)) := Subring.closure {x | IsFnP x}

instance : CommRing (FnS P) := Subring.closureCommRingOfComm fun x hx y hy => isFnP_comm hx hy

def f (x : A P (DQ P)) (hx : IsFnP x) : FnS P := ⟨x, Subring.subset_closure hx⟩

variable {L : LevelData (A P (DQ P)) P.r} (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L)
  (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem fnPs : IsFnP L.D ∧ IsFnP L.Di ∧ IsFnP L.Db ∧ IsFnP L.Dbi ∧ IsFnP (G.Gs P (-1)) ∧
    IsFnP (L.ζ * L.ζb * L.GGi) := by
  obtain ⟨hD, hDi, hDb, hDbi, -⟩ := fnP_D hL
  exact ⟨hD, hDi, hDb, hDbi, isFnP_Gs (-1),
    isFnP_mul (isFnP_mul (fns_fnP hL (m_ζ L)) (fns_fnP hL (m_ζb L))) (fns_fnP hL (m_GGi L))⟩

theorem rels : let h := fnPs hTTp hL hLaw
    f L.D h.1 * f L.Di h.2.1 = 1 ∧ f L.Db h.2.2.1 * f L.Dbi h.2.2.2.1 = 1 ∧
    f (L.ζ * L.ζb * L.GGi) h.2.2.2.2.2 = f L.D h.1 * f L.Db h.2.2.1 * f (G.Gs P (-1)) h.2.2.2.2.1 := by
  refine ⟨Subtype.ext (D_Di L), Subtype.ext (Db_Dbi L), Subtype.ext (W_eq hTTp hL hLaw)⟩

theorem D_power_identity_one (N : ℕ) : L.Dbi * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * L.Dbi ^ (N + 1)) =
    L.D ^ (N + 1) * L.Dbi * G.Gs P (-1) ^ (N + 1) := by
  obtain ⟨hD, hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨r1, r2, r3⟩ := rels hTTp hL hLaw
  have key : f L.Dbi hDbi * ((f _ hW) ^ (N + 1) * (f L.Dbi hDbi) ^ (N + 1)) =
      (f L.D hD) ^ (N + 1) * f L.Dbi hDbi * (f _ hG) ^ (N + 1) := by
    rw [r3]
    have : (f L.Db hDb * f L.Dbi hDbi) ^ (N + 1) = 1 := by rw [r2, one_pow]
    linear_combination (f L.Dbi hDbi * (f L.D hD) ^ (N + 1) * (f _ hG) ^ (N + 1)) * this
  simpa [f] using congrArg Subtype.val key

theorem D_power_identity_two (N : ℕ) : L.Di * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * L.Dbi ^ (N + 1)) = L.D ^ N * G.Gs P (-1) ^ (N + 1) := by
  obtain ⟨hD, hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨r1, r2, r3⟩ := rels hTTp hL hLaw
  have key : f L.Di hDi * ((f _ hW) ^ (N + 1) * (f L.Dbi hDbi) ^ (N + 1)) = (f L.D hD) ^ N * (f _ hG) ^ (N + 1) := by
    rw [r3]
    have h2 : (f L.Db hDb * f L.Dbi hDbi) ^ (N + 1) = 1 := by rw [r2, one_pow]
    linear_combination (f L.Di hDi * (f L.D hD) ^ (N + 1) * (f _ hG) ^ (N + 1)) * h2 +
      ((f L.D hD) ^ N * (f _ hG) ^ (N + 1)) * r1
  simpa [f] using congrArg Subtype.val key

theorem D_power_identity_three (N : ℕ) : (L.ζ * L.ζb * L.GGi) ^ (N + 1) * L.Dbi ^ (N + 1) = L.D ^ (N + 1) * G.Gs P (-1) ^ (N + 1) := by
  obtain ⟨hD, hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨r1, r2, r3⟩ := rels hTTp hL hLaw
  have key : (f _ hW) ^ (N + 1) * (f L.Dbi hDbi) ^ (N + 1) = (f L.D hD) ^ (N + 1) * (f _ hG) ^ (N + 1) := by
    rw [r3]
    have h2 : (f L.Db hDb * f L.Dbi hDbi) ^ (N + 1) = 1 := by rw [r2, one_pow]
    linear_combination ((f L.D hD) ^ (N + 1) * (f _ hG) ^ (N + 1)) * h2
  simpa [f] using congrArg Subtype.val key

theorem D_power_identity_four (N : ℕ) : L.Di * L.Db ^ (N + 1) * L.Dbi ^ N = L.Db * L.Di ∧ L.Db ^ N * L.Dbi ^ N = 1 := by
  obtain ⟨hD, hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨r1, r2, r3⟩ := rels hTTp hL hLaw
  have h2 : (f L.Db hDb * f L.Dbi hDbi) ^ N = 1 := by rw [r2, one_pow]
  constructor
  · have key : f L.Di hDi * (f L.Db hDb) ^ (N + 1) * (f L.Dbi hDbi) ^ N = f L.Db hDb * f L.Di hDi := by
      linear_combination (f L.Di hDi * f L.Db hDb) * h2
    simpa [f] using congrArg Subtype.val key
  · have key : (f L.Db hDb) ^ N * (f L.Dbi hDbi) ^ N = 1 := by linear_combination h2
    simpa [f] using congrArg Subtype.val key

theorem D_power_identity_five (N : ℕ) : L.Db ^ (N + 1) * L.Di * L.Dbi ^ N = L.Db * L.Di ∧ L.Db ^ (N + 1) * L.Dbi * L.Dbi ^ N = 1 := by
  obtain ⟨hD, hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨r1, r2, r3⟩ := rels hTTp hL hLaw
  have h2 : (f L.Db hDb * f L.Dbi hDbi) ^ N = 1 := by rw [r2, one_pow]
  constructor
  · have key : (f L.Db hDb) ^ (N + 1) * f L.Di hDi * (f L.Dbi hDbi) ^ N = f L.Db hDb * f L.Di hDi := by
      linear_combination (f L.Db hDb * f L.Di hDi) * h2
    simpa [f] using congrArg Subtype.val key
  · have key : (f L.Db hDb) ^ (N + 1) * f L.Dbi hDbi * (f L.Dbi hDbi) ^ N = 1 := by
      have h3 : (f L.Db hDb * f L.Dbi hDbi) ^ (N + 1) = 1 := by rw [r2, one_pow]
      linear_combination h3
    simpa [f] using congrArg Subtype.val key

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB4

section S_AD_AD16

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AD

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.MAx1.An Formalism.FourierDecayAlt.P.MAx2.Jet Formalism.FourierDecayAlt.P.MAx3.L
open MeasureTheory ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem cf_Ph {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) : CF (Ph P φ) (fun q => ((φ (Gq P q) : ℝ) : ℂ)) :=
  ⟨Phi P φ 0, Phi P φ 0, rfl, fun q => eval_cutoff_operator_zero P hφ q, fun q => by rw [Complex.conj_ofReal]; exact eval_cutoff_operator_zero P hφ q⟩

theorem cf_Gs (t : ℝ) : CF (G.Gs P t) (fun q => ((Gq P q ^ t : ℝ) : ℂ)) :=
  cf_Ph (φ := fun x : ℝ => x ^ t) (G.smoothLog_rpow t)

variable {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}

theorem Ph_mem_Z {φ : ℝ → ℝ} (hφ : admitted φ) : Ph P φ ∈ Z P L 0 :=
  Submodule.subset_span ⟨φ, 1, [], hφ, Submonoid.one_mem _, by simp, by simp, by simp⟩

theorem DDbi_pow_mem (n : ℕ) : (L.D * L.Dbi) ^ n ∈ Submonoid.closure (bddSet P L) := by
  have h : L.D * L.Dbi ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  exact Submonoid.pow_mem _ (Submonoid.subset_closure h) n

theorem DbDi_pow_mem (n : ℕ) : (L.Db * L.Di) ^ n ∈ Submonoid.closure (bddSet P L) := by
  have h : L.Db * L.Di ∈ bddSet P L := Or.inl (Or.inl (Or.inl (by simp)))
  exact Submonoid.pow_mem _ (Submonoid.subset_closure h) n

variable (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem word_mul_Z : ∀ (W : List (A P (DQ P))), (∀ x ∈ W, x ∈ hatSet P L) → ∀ {k : ℕ} {z : A P (DQ P)},
    z ∈ Z P L k → W.prod * z ∈ Z P L (k + W.length)
  | [], _, k, z, hz => by simpa using hz
  | X :: W, hW, k, z, hz => by
    rw [List.prod_cons, mul_assoc]
    have h1 := word_mul_Z W (fun x hx => hW x (by simp [hx])) hz
    have h2 := hatPast hTTp.le hL hLaw (hW X (by simp)) h1
    simpa [Nat.add_assoc, Nat.add_comm 1] using h2

theorem canon {m : ℕ} (hD : JDecay P L j m) (hA : JAdj P L j m) (a : A P (DQ P))
    (ts : List (ℂ × A P (DQ P) × A P (DQ P) × List (A P (DQ P)))) (hts : ∀ t ∈ ts, CanonTerm L m a t) :
    ipA P (actA P a j) (actA P (canonSum ts) j) = ipA P (actA P (star (canonSum ts) * a) j) j :=
  (canonical_sum_integrable hTTp hL hLaw hD hA a ts hts).2.2

end

end Formalism.FourierDecayAlt.P.MAx3.AD

end S_AD_AD16

section S_AB_AB5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem isFnP_of_CF {s : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (hs : CF s g) : IsFnP s := by
  obtain ⟨F, Fb, rfl, -, -⟩ := hs; exact ⟨F, Fb, rfl⟩

theorem isFnP_star {s : A P (DQ P)} (hs : IsFnP s) : IsFnP (star s) := by
  obtain ⟨F, Fb, rfl⟩ := hs
  rw [MAx2.R2.star_sc]
  exact ⟨Fb, F, rfl⟩

theorem QA_term {m : ℕ} (hD : JDecay P L j m) (hA : JAdj P L j m) {a : A P (DQ P)} {β : A P (DQ P)}
    (hβ : β ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L) {s : A P (DQ P)} {g : Qp P.r P.TT → ℂ} (hs : CF s g)
    {W : List (A P (DQ P))} (hW : ∀ x ∈ W, x ∈ hatSet P L) {k : ℕ} (hkm : k + W.length ≤ m)
    (hsa : star s * a ∈ Z P L k) : QA L j a (β * s * W.prod) := by
  obtain ⟨Cβ, hβC⟩ := SAB_closure hTTp hL hLaw hβ
  obtain ⟨int1, -, eq1⟩ := multAdj hTTp hL hLaw hD hβC hs hW (by omega) (k := k) (by omega) hsa
  have hsβ : star β ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L := star_SB hL hLaw hβ
  have hz : star (β * s) * a ∈ Z P L k := by
    rw [star_mul, ← SB_comm_fnP hL hLaw hsβ (isFnP_star hTTp hL hLaw (isFnP_of_CF hTTp hL hLaw hs)), mul_assoc]
    exact SB_memZ hTTp hL hLaw hsβ hsa
  have hp := adjPure hTTp hL hLaw hD hA W hW k hkm _ hz
  have hz2 : star (β * s * W.prod) * a ∈ Z P L (k + W.length) := by
    rw [star_mul, mul_assoc]; exact star_word_mem hTTp.le hL hLaw W hW hz
  refine ⟨int1, fun π => ?_, ?_⟩
  · have := int_Z hTTp hL hLaw hD (by omega) hz2 (W := []) (by simp) (by simp) π
    simpa [MAx2.R2.act_one] using this
  · rw [eq1, hp, star_mul (β * s) W.prod, mul_assoc]

theorem QA_span {a : A P (DQ P)} {T : Set (A P (DQ P))} (h : ∀ w ∈ T, QA L j a w) {w : A P (DQ P)}
    (hw : w ∈ Submodule.span ℂ T) : QA L j a w := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact QA_zero a
  | add x y _ _ h1 h2 => exact QA_add h1 h2
  | smul c x _ h1 => exact QA_smul c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB5

section S_AB_AB6

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem BA_span {E : A P (DQ P)} (hE : E ∈ Formalism.FourierDecayAlt.P.MAx3.I4.BA L) :
    E ∈ Submodule.span ℂ (Formalism.FourierDecayAlt.P.MAx3.I4.SB L : Set (A P (DQ P))) := by
  have : E ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (bddSet P L)) := hE
  rwa [Algebra.adjoin_eq_span] at this

theorem BA_memZ {E : A P (DQ P)} (hE : E ∈ Formalism.FourierDecayAlt.P.MAx3.I4.BA L) {k : ℕ} {z : A P (DQ P)} (hz : z ∈ Z P L k) :
    E * z ∈ Z P L k := by
  have h := BA_span hTTp hL hLaw hE
  clear hE
  induction h using Submodule.span_induction with
  | mem b hb => exact SB_memZ hTTp hL hLaw hb hz
  | zero => simp
  | add a b _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c a _ h1 => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h1

theorem BA_comm_fnP {E : A P (DQ P)} (hE : E ∈ Formalism.FourierDecayAlt.P.MAx3.I4.BA L) {s : A P (DQ P)} (hs : IsFnP s) :
    E * s = s * E := by
  have h := BA_span hTTp hL hLaw hE
  clear hE
  induction h using Submodule.span_induction with
  | mem b hb => exact SB_comm_fnP hL hLaw hb hs
  | zero => simp
  | add a b _ _ h1 h2 => rw [add_mul, mul_add, h1, h2]
  | smul c a _ h1 => rw [smul_mul_assoc, mul_smul_comm, h1]

theorem star_Gs (t : ℝ) : star (G.Gs P t) = G.Gs P t := by
  have : G.Gs P t = Ph P (fun x : ℝ => x ^ t) := rfl
  rw [this, star_Ph]

theorem left_cond {N n k m : ℕ} (hγ : L.Di ^ k * L.Db ^ n * L.Dbi ^ N ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L) {ψ : ℝ → ℝ}
    (hψ : admitted ψ) {x : A P (DQ P)} (hx : x ∈ NFD L N) :
    star (L.D ^ n * L.Dbi ^ k * G.Gs P (-1) ^ m) * (Ph P ψ * x) ∈ Z P L N := by
  obtain ⟨-, -, -, h4, h5, -⟩ := star_more hL hLaw
  obtain ⟨hD, hDi, hDb, hDbi, -⟩ := fnP_D hL
  have hst : star (L.D ^ n * L.Dbi ^ k * G.Gs P (-1) ^ m) = G.Gs P (-1) ^ m * (L.Di ^ k * L.Db ^ n) := by
    rw [star_mul, star_mul, star_pow, star_pow, star_pow, star_Gs hTTp hL hLaw, h4, h5]
  rw [hst]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, H, hβ, hH, hl, rfl⟩ := hy
    have hG : IsFnP (L.Di ^ k * L.Db ^ n) := isFnP_mul (isFnP_pow hDi k) (isFnP_pow hDb n)
    have e : G.Gs P (-1) ^ m * (L.Di ^ k * L.Db ^ n) * (Ph P ψ * (β * L.Dbi ^ N * H.prod)) =
        G.Gs P (-1) ^ m * (Ph P ψ * (β * (L.Di ^ k * L.Db ^ n * L.Dbi ^ N)) * H.prod) := by
      have c1 : L.Di ^ k * L.Db ^ n * Ph P ψ = Ph P ψ * (L.Di ^ k * L.Db ^ n) := isFnP_comm hG (isFnP_Ph ψ)
      have c2 : L.Di ^ k * L.Db ^ n * β = β * (L.Di ^ k * L.Db ^ n) := (SB_comm_fnP hL hLaw hβ hG).symm
      calc G.Gs P (-1) ^ m * (L.Di ^ k * L.Db ^ n) * (Ph P ψ * (β * L.Dbi ^ N * H.prod))
          = G.Gs P (-1) ^ m * ((L.Di ^ k * L.Db ^ n * Ph P ψ) * β * L.Dbi ^ N * H.prod) := by simp only [mul_assoc]
        _ = G.Gs P (-1) ^ m * (Ph P ψ * ((L.Di ^ k * L.Db ^ n) * β) * L.Dbi ^ N * H.prod) := by
            rw [c1]; simp only [mul_assoc]
        _ = _ := by rw [c2]; simp only [mul_assoc]
    rw [e]
    refine Gspow_memZ hTTp hL hLaw m (Submodule.subset_span ⟨ψ, _, H, hψ, Submonoid.mul_mem _ hβ hγ,
      fun h hh => Or.inl (Or.inl (hH h hh)), hl.le, rfl⟩)
  | zero => simp
  | add a b _ _ h1 h2 => rw [mul_add, mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c a _ h1 => rw [mul_smul_comm, mul_smul_comm]; exact Submodule.smul_mem _ c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB6

section S_AB_AB7

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem QA_LX {m0 : ℕ} (hD : JDecay P L j m0) (hA : JAdj P L j m0) {N n k m : ℕ} (hm0 : N + (N + 2) ≤ m0)
    (hγ : L.Di ^ k * L.Db ^ n * L.Dbi ^ N ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L) {ψ : ℝ → ℝ} (hψ : admitted ψ) {x : A P (DQ P)}
    (hx : x ∈ NFD L N) {X : A P (DQ P)} (hX : X ∈ minusHats L) {β : A P (DQ P)} (hβ : β ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L)
    {H : List (A P (DQ P))} (hH : ∀ h ∈ H, h ∈ plusHats L) (hl : H.length = N + 1) :
    QA L j (Ph P ψ * x) (X * (β * (L.D ^ n * L.Dbi ^ k) * G.Gs P (-1) ^ m) * H.prod) := by
  have hz := hatv_past_G hTTp hL hLaw hX hβ n k m
  have hs : CF (L.D ^ n * L.Dbi ^ k * G.Gs P (-1) ^ m) _ :=
    CF_mul (CF_mul (CF_pow' (cf_D hTTp.le hL) n) (CF_pow' (cf_Dbi hTTp.le hL) k)) (CF_pow' (cf_Gs (-1)) m)
  have hsa := left_cond hTTp hL hLaw (m := m) hγ hψ hx
  suffices key : ∀ z ∈ MSG L n k m, QA L j (Ph P ψ * x) (z * H.prod) from key _ hz
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨β', X', hβ', hX', rfl⟩ := hz
    have e : β' * (L.D ^ n * L.Dbi ^ k) * G.Gs P (-1) ^ m * X' * H.prod =
        β' * (L.D ^ n * L.Dbi ^ k * G.Gs P (-1) ^ m) * (X' :: H).prod := by
      rw [List.prod_cons]; simp only [mul_assoc]
    rw [e]
    refine QA_term hTTp hL hLaw hD hA hβ' hs (fun h hh => ?_) (k := N) (by simp [hl]; omega) hsa
    rcases List.mem_cons.1 hh with rfl | hh
    · exact minus_sub_hat hTTp hL hLaw hX'
    · exact Or.inl (Or.inl (hH h hh))
  | zero => rw [zero_mul]; exact QA_zero _
  | add a b _ _ h1 h2 => rw [add_mul]; exact QA_add h1 h2
  | smul c a _ h1 => rw [smul_mul_assoc]; exact QA_smul c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB7

section S_AB_AB8

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem kap_SB (κ : M.Ty P → ℂ) : kap P (DQ P) κ ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨κ, rfl⟩)))

theorem star_letA (Y : ℝ) : star (L.Di * L.Ahat (Y : ℂ)) = L.Ahatv ((Y : ℂ) - 1) * L.Dbi := by
  obtain ⟨-, -, h3, -, -, -⟩ := star_more hL hLaw
  rw [star_mul, Q.star_Ahat hL hLaw, h3, Complex.conj_ofReal]

theorem star_letR (Y : ℝ) : star (L.Dbi * L.R0 (Y : ℂ)) = L.R0v (Y : ℂ) * L.Di := by
  obtain ⟨-, -, -, h4, -, -⟩ := star_more hL hLaw
  rw [star_mul, Q.star_raising hL hLaw, h4, Complex.conj_ofReal]

theorem rearr1 (N : ℕ) (κ : M.Ty P → ℂ) {β : A P (DQ P)} (hβ : β ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L) (F : A P (DQ P))
    (hF : IsFnP F) (Hp : A P (DQ P)) :
    F * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ * (β * L.Dbi ^ (N + 1) * Hp)) =
      (kap P (DQ P) κ * β) * (F * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * L.Dbi ^ (N + 1))) * Hp := by
  obtain ⟨hD, hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  have hkβ : kap P (DQ P) κ * β ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L := Submonoid.mul_mem _ (kap_SB hTTp hL hLaw κ) hβ
  have c1 : (L.ζ * L.ζb * L.GGi) ^ (N + 1) * (kap P (DQ P) κ * β) = (kap P (DQ P) κ * β) * (L.ζ * L.ζb * L.GGi) ^ (N + 1) :=
    (SB_comm_fnP hL hLaw hkβ (isFnP_pow hW (N + 1))).symm
  have c2 : F * (kap P (DQ P) κ * β) = (kap P (DQ P) κ * β) * F := (SB_comm_fnP hL hLaw hkβ hF).symm
  calc F * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ * (β * L.Dbi ^ (N + 1) * Hp))
      = F * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * (kap P (DQ P) κ * β)) * L.Dbi ^ (N + 1) * Hp := by simp only [mul_assoc]
    _ = (F * (kap P (DQ P) κ * β)) * (L.ζ * L.ζb * L.GGi) ^ (N + 1) * L.Dbi ^ (N + 1) * Hp := by
        rw [c1]; simp only [mul_assoc]
    _ = _ := by rw [c2]; simp only [mul_assoc]

theorem quadratic_form_lowering {m0 : ℕ} (hD : JDecay P L j m0) (hA : JAdj P L j m0) {N : ℕ} (hm0 : N + (N + 2) ≤ m0) {ψ : ℝ → ℝ}
    (hψ : admitted ψ) {x : A P (DQ P)} (hx : x ∈ NFD L N) (Y : ℝ) (κ : M.Ty P → ℂ) {y : A P (DQ P)}
    (hy : y ∈ NFD L (N + 1)) :
    QA L j (Ph P ψ * x) (star (L.Di * L.Ahat (Y : ℂ)) * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ * y)) := by
  obtain ⟨hD', hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨hγ, -⟩ := D_power_identity_four hTTp hL hLaw N
  have hγ' : L.Di ^ 1 * L.Db ^ (N + 1) * L.Dbi ^ N ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L := by
    rw [pow_one, hγ]; exact Submonoid.subset_closure (Or.inl (Or.inl (Or.inl (by simp))))
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, H, hβ, hH, hl, rfl⟩ := hy
    have e : star (L.Di * L.Ahat (Y : ℂ)) * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ *
        (β * L.Dbi ^ (N + 1) * H.prod)) = L.Ahatv ((Y : ℂ) - 1) *
        ((kap P (DQ P) κ * β) * (L.D ^ (N + 1) * L.Dbi ^ 1) * G.Gs P (-1) ^ (N + 1)) * H.prod := by
      rw [star_letA hTTp hL hLaw, mul_assoc, rearr1 hTTp hL hLaw N κ hβ L.Dbi hDbi, D_power_identity_one hTTp hL hLaw, pow_one]
      simp only [mul_assoc]
    rw [e]
    exact QA_LX hTTp hL hLaw hD hA hm0 hγ' hψ hx (Or.inl ⟨_, rfl⟩)
      (Submonoid.mul_mem _ (kap_SB hTTp hL hLaw κ) hβ) hH hl
  | zero => rw [mul_zero, mul_zero]; exact QA_zero _
  | add a b _ _ h1 h2 => rw [mul_add, mul_add]; exact QA_add h1 h2
  | smul c a _ h1 => rw [mul_smul_comm, mul_smul_comm]; exact QA_smul c h1

theorem quadratic_form_raising {m0 : ℕ} (hD : JDecay P L j m0) (hA : JAdj P L j m0) {N : ℕ} (hm0 : N + (N + 2) ≤ m0) {ψ : ℝ → ℝ}
    (hψ : admitted ψ) {x : A P (DQ P)} (hx : x ∈ NFD L N) (Y : ℝ) (κ : M.Ty P → ℂ) {y : A P (DQ P)}
    (hy : y ∈ NFD L (N + 1)) :
    QA L j (Ph P ψ * x) (star (L.Dbi * L.R0 (Y : ℂ)) * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ * y)) := by
  obtain ⟨hD', hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨-, hγ⟩ := D_power_identity_four hTTp hL hLaw N
  have hγ' : L.Di ^ 0 * L.Db ^ N * L.Dbi ^ N ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L := by
    rw [pow_zero, one_mul, hγ]; exact Submonoid.one_mem _
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, H, hβ, hH, hl, rfl⟩ := hy
    have e : star (L.Dbi * L.R0 (Y : ℂ)) * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ *
        (β * L.Dbi ^ (N + 1) * H.prod)) = L.R0v (Y : ℂ) *
        ((kap P (DQ P) κ * β) * (L.D ^ N * L.Dbi ^ 0) * G.Gs P (-1) ^ (N + 1)) * H.prod := by
      rw [star_letR hTTp hL hLaw, mul_assoc, rearr1 hTTp hL hLaw N κ hβ L.Di hDi, D_power_identity_two hTTp hL hLaw, pow_zero, mul_one]
      simp only [mul_assoc]
    rw [e]
    exact QA_LX hTTp hL hLaw hD hA hm0 hγ' hψ hx (Or.inr ⟨_, rfl⟩)
      (Submonoid.mul_mem _ (kap_SB hTTp hL hLaw κ) hβ) hH hl
  | zero => rw [mul_zero, mul_zero]; exact QA_zero _
  | add a b _ _ h1 h2 => rw [mul_add, mul_add]; exact QA_add h1 h2
  | smul c a _ h1 => rw [mul_smul_comm, mul_smul_comm]; exact QA_smul c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB8

section S_AB_AB9

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem star_BA_span {E : A P (DQ P)} (hE : E ∈ Formalism.FourierDecayAlt.P.MAx3.I4.BA L) :
    star E ∈ Submodule.span ℂ (Formalism.FourierDecayAlt.P.MAx3.I4.SB L : Set (A P (DQ P))) := by
  have h := BA_span hTTp hL hLaw hE
  clear hE
  induction h using Submodule.span_induction with
  | mem b hb => exact Submodule.subset_span (star_SB hL hLaw hb)
  | zero => simp
  | add a b _ _ h1 h2 => rw [star_add]; exact Submodule.add_mem _ h1 h2
  | smul c a _ h1 => rw [star_smul]; exact Submodule.smul_mem _ _ h1

theorem quadratic_form_lowering_base {m0 : ℕ} (hD : JDecay P L j m0) (hA : JAdj P L j m0) {N : ℕ} (hm0 : N + (N + 2) ≤ m0) {ψ : ℝ → ℝ}
    (hψ : admitted ψ) {x : A P (DQ P)} (hx : x ∈ NFD L N) (Y : ℝ) (κ : M.Ty P → ℂ) {E : A P (DQ P)}
    (hE : E ∈ Formalism.FourierDecayAlt.P.MAx3.I4.BA L) {y : A P (DQ P)} (hy : y ∈ NFD L (N + 1)) :
    QA L j (Ph P ψ * x) (star (E * (L.Di * L.Ahat (Y : ℂ))) * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ * y)) := by
  obtain ⟨hD', hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨hγ, -⟩ := D_power_identity_four hTTp hL hLaw N
  have hγ' : L.Di ^ 1 * L.Db ^ (N + 1) * L.Dbi ^ N ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L := by
    rw [pow_one, hγ]; exact Submonoid.subset_closure (Or.inl (Or.inl (Or.inl (by simp))))
  rw [star_mul, star_letA hTTp hL hLaw]
  have hsE := star_BA_span hTTp hL hLaw hE
  generalize star E = e at hsE
  clear hE
  induction hsE using Submodule.span_induction with
  | mem b hb =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨β, H, hβ, hH, hl, rfl⟩ := hy
      have e1 : L.Ahatv ((Y : ℂ) - 1) * L.Dbi * b * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ *
          (β * L.Dbi ^ (N + 1) * H.prod)) = L.Ahatv ((Y : ℂ) - 1) *
          ((b * (kap P (DQ P) κ * β)) * (L.D ^ (N + 1) * L.Dbi ^ 1) * G.Gs P (-1) ^ (N + 1)) * H.prod := by
        have cb : L.Dbi * b = b * L.Dbi := (SB_comm_fnP hL hLaw hb hDbi).symm
        rw [mul_assoc (L.Ahatv _), cb, mul_assoc, mul_assoc, rearr1 hTTp hL hLaw N κ hβ L.Dbi hDbi,
          D_power_identity_one hTTp hL hLaw, pow_one]
        simp only [mul_assoc]
      rw [e1]
      exact QA_LX hTTp hL hLaw hD hA hm0 hγ' hψ hx (Or.inl ⟨_, rfl⟩)
        (Submonoid.mul_mem _ hb (Submonoid.mul_mem _ (kap_SB hTTp hL hLaw κ) hβ)) hH hl
    | zero => rw [mul_zero, mul_zero]; exact QA_zero _
    | add a c _ _ h1 h2 => rw [mul_add, mul_add]; exact QA_add h1 h2
    | smul c a _ h1 => rw [mul_smul_comm, mul_smul_comm]; exact QA_smul c h1
  | zero => rw [mul_zero, zero_mul]; exact QA_zero _
  | add a c _ _ h1 h2 => rw [mul_add, add_mul]; exact QA_add h1 h2
  | smul c a _ h1 => rw [mul_smul_comm, smul_mul_assoc]; exact QA_smul c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB9

section S_AB_AB10

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem QA_R {m0 : ℕ} (hD : JDecay P L j m0) (hA : JAdj P L j m0) {N : ℕ} (hm0 : (N + 1) + (N + 1) ≤ m0)
    {a : A P (DQ P)} (ha : G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * a ∈ Z P L (N + 1)) (κ : M.Ty P → ℂ)
    {y : A P (DQ P)} (hy : y ∈ NFD L (N + 1)) :
    QA L j a ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ * y) := by
  obtain ⟨-, -, -, -, h5, -⟩ := star_more hL hLaw
  have hs : CF (L.D ^ (N + 1) * G.Gs P (-1) ^ (N + 1)) _ :=
    CF_mul (CF_pow' (cf_D hTTp.le hL) (N + 1)) (CF_pow' (cf_Gs (-1)) (N + 1))
  have hsa : star (L.D ^ (N + 1) * G.Gs P (-1) ^ (N + 1)) * a ∈ Z P L (N + 1) := by
    rw [star_mul, star_pow, star_pow, star_Gs hTTp hL hLaw, h5]; exact ha
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, H, hβ, hH, hl, rfl⟩ := hy
    have e : (L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ * (β * L.Dbi ^ (N + 1) * H.prod) =
        (kap P (DQ P) κ * β) * (L.D ^ (N + 1) * G.Gs P (-1) ^ (N + 1)) * H.prod := by
      obtain ⟨-, -, -, -, -, hW⟩ := fnPs hTTp hL hLaw
      have hkβ : kap P (DQ P) κ * β ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L := Submonoid.mul_mem _ (kap_SB hTTp hL hLaw κ) hβ
      have c1 : (L.ζ * L.ζb * L.GGi) ^ (N + 1) * (kap P (DQ P) κ * β) =
          (kap P (DQ P) κ * β) * (L.ζ * L.ζb * L.GGi) ^ (N + 1) :=
        (SB_comm_fnP hL hLaw hkβ (isFnP_pow hW (N + 1))).symm
      calc (L.ζ * L.ζb * L.GGi) ^ (N + 1) * kap P (DQ P) κ * (β * L.Dbi ^ (N + 1) * H.prod)
          = ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * (kap P (DQ P) κ * β)) * L.Dbi ^ (N + 1) * H.prod := by
            simp only [mul_assoc]
        _ = (kap P (DQ P) κ * β) * ((L.ζ * L.ζb * L.GGi) ^ (N + 1) * L.Dbi ^ (N + 1)) * H.prod := by
            rw [c1]; simp only [mul_assoc]
        _ = _ := by rw [D_power_identity_three hTTp hL hLaw]
    rw [e]
    exact QA_term hTTp hL hLaw hD hA (Submonoid.mul_mem _ (kap_SB hTTp hL hLaw κ) hβ) hs
      (fun h hh => Or.inl (Or.inl (hH h hh))) (k := N + 1) (by rw [hl]; omega) hsa
  | zero => rw [mul_zero]; exact QA_zero _
  | add a' b _ _ h1 h2 => rw [mul_add]; exact QA_add h1 h2
  | smul c a' _ h1 => rw [mul_smul_comm]; exact QA_smul c h1

theorem rc1 {N : ℕ} {ψ : ℝ → ℝ} (hψ : admitted ψ) {x : A P (DQ P)} (hx : x ∈ NFD L N) (Y : ℂ) :
    G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (L.Di * L.Ahat Y * (Ph P ψ * x)) ∈ Z P L (N + 1) := by
  obtain ⟨hD', hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨hI, -⟩ := D_power_identity_five hTTp hL hLaw N
  have hDD : L.Db * L.Di ∈ Formalism.FourierDecayAlt.P.MAx3.I4.SB L := Submonoid.subset_closure (Or.inl (Or.inl (Or.inl (by simp))))
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, H, hβ, hH, hl, rfl⟩ := hy
    have e : G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (L.Di * L.Ahat Y * (Ph P ψ * (β * L.Dbi ^ N * H.prod))) =
        G.Gs P (-1) ^ (N + 1) * ((L.Db ^ (N + 1) * L.Di * L.Dbi ^ N) * (L.Ahat Y * (Ph P ψ * β * H.prod))) := by
      have c1 : Ph P ψ * (β * L.Dbi ^ N) = L.Dbi ^ N * (Ph P ψ * β) := by
        rw [SB_comm_fnP hL hLaw hβ (isFnP_pow hDbi N), ← mul_assoc, isFnP_comm (isFnP_Ph ψ) (isFnP_pow hDbi N),
          mul_assoc]
      calc G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (L.Di * L.Ahat Y * (Ph P ψ * (β * L.Dbi ^ N * H.prod)))
          = G.Gs P (-1) ^ (N + 1) * (L.Db ^ (N + 1) * L.Di * (L.Ahat Y * ((Ph P ψ * (β * L.Dbi ^ N)) * H.prod))) := by
            simp only [mul_assoc]
        _ = G.Gs P (-1) ^ (N + 1) * (L.Db ^ (N + 1) * L.Di * ((L.Ahat Y * L.Dbi ^ N) * (Ph P ψ * β * H.prod))) := by
            rw [c1]; simp only [mul_assoc]
        _ = _ := by rw [comm_Dbipow_A]; simp only [mul_assoc]
    rw [e, hI]
    refine Gspow_memZ hTTp hL hLaw (N + 1) (SB_memZ hTTp hL hLaw hDD ?_)
    have hz : Ph P ψ * β * H.prod ∈ Z P L N :=
      Submodule.subset_span ⟨ψ, β, H, hψ, hβ, fun h hh => Or.inl (Or.inl (hH h hh)), hl.le, rfl⟩
    exact hatPast hTTp.le hL hLaw (Or.inl (Or.inl (Or.inl ⟨Y, rfl⟩))) hz
  | zero => simp
  | add a b _ _ h1 h2 => rw [mul_add, mul_add, mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c a _ h1 => rw [mul_smul_comm, mul_smul_comm, mul_smul_comm]; exact Submodule.smul_mem _ c h1

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB10

section S_AB_AB11

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD

noncomputable section

variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT}
  (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
include hTTp hL hLaw

theorem rc2 {N : ℕ} {ψ : ℝ → ℝ} (hψ : admitted ψ) {x : A P (DQ P)} (hx : x ∈ NFD L N) (Y : ℂ) :
    G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (L.Dbi * L.R0 Y * (Ph P ψ * x)) ∈ Z P L (N + 1) := by
  obtain ⟨hD', hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  obtain ⟨-, hI⟩ := D_power_identity_five hTTp hL hLaw N
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, H, hβ, hH, hl, rfl⟩ := hy
    have c1 : Ph P ψ * (β * L.Dbi ^ N) = L.Dbi ^ N * (Ph P ψ * β) := by
      rw [SB_comm_fnP hL hLaw hβ (isFnP_pow hDbi N), ← mul_assoc, isFnP_comm (isFnP_Ph ψ) (isFnP_pow hDbi N),
        mul_assoc]
    have e : G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (L.Dbi * L.R0 Y * (Ph P ψ * (β * L.Dbi ^ N * H.prod))) =
        G.Gs P (-1) ^ (N + 1) * ((L.Db ^ (N + 1) * L.Dbi * L.Dbi ^ N) * (L.R0 Y * (Ph P ψ * β * H.prod))) := by
      calc G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (L.Dbi * L.R0 Y * (Ph P ψ * (β * L.Dbi ^ N * H.prod)))
          = G.Gs P (-1) ^ (N + 1) * (L.Db ^ (N + 1) * L.Dbi * (L.R0 Y * ((Ph P ψ * (β * L.Dbi ^ N)) * H.prod))) := by
            simp only [mul_assoc]
        _ = G.Gs P (-1) ^ (N + 1) * (L.Db ^ (N + 1) * L.Dbi * ((L.R0 Y * L.Dbi ^ N) * (Ph P ψ * β * H.prod))) := by
            rw [c1]; simp only [mul_assoc]
        _ = _ := by rw [comm_Dbipow_R]; simp only [mul_assoc]
    rw [e, hI, one_mul]
    refine Gspow_memZ hTTp hL hLaw (N + 1) ?_
    have hz : Ph P ψ * β * H.prod ∈ Z P L N :=
      Submodule.subset_span ⟨ψ, β, H, hψ, hβ, fun h hh => Or.inl (Or.inl (hH h hh)), hl.le, rfl⟩
    exact hatPast hTTp.le hL hLaw (Or.inl (Or.inl (Or.inr ⟨Y, rfl⟩))) hz
  | zero => simp
  | add a b _ _ h1 h2 => rw [mul_add, mul_add, mul_add]; exact Submodule.add_mem _ h1 h2
  | smul c a _ h1 => rw [mul_smul_comm, mul_smul_comm, mul_smul_comm]; exact Submodule.smul_mem _ c h1

theorem rc3 {N : ℕ} {ψ : ℝ → ℝ} (hψ : admitted ψ) {x : A P (DQ P)} (hx : x ∈ NFD L N) (Y : ℂ) {E : A P (DQ P)}
    (hE : E ∈ Formalism.FourierDecayAlt.P.MAx3.I4.BA L) :
    G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (E * (L.Di * L.Ahat Y) * (Ph P ψ * x)) ∈ Z P L (N + 1) := by
  obtain ⟨hD', hDi, hDb, hDbi, hG, hW⟩ := fnPs hTTp hL hLaw
  have hc : E * (G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1)) = (G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1)) * E :=
    BA_comm_fnP hTTp hL hLaw hE (isFnP_mul (isFnP_pow hG (N + 1)) (isFnP_pow hDb (N + 1)))
  have e : G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (E * (L.Di * L.Ahat Y) * (Ph P ψ * x)) =
      E * (G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (L.Di * L.Ahat Y * (Ph P ψ * x))) := by
    calc G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1) * (E * (L.Di * L.Ahat Y) * (Ph P ψ * x))
        = (G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1)) * E * (L.Di * L.Ahat Y * (Ph P ψ * x)) := by simp only [mul_assoc]
      _ = E * (G.Gs P (-1) ^ (N + 1) * L.Db ^ (N + 1)) * (L.Di * L.Ahat Y * (Ph P ψ * x)) := by rw [hc]
      _ = _ := by simp only [mul_assoc]
  rw [e]
  exact BA_memZ hTTp hL hLaw hE (rc1 hTTp hL hLaw hψ hx Y)

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB11

section S_AB_AB12

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD
open ComplexConjugate

noncomputable section

variable {P : M.Par}

theorem int_conj {f : Qp P.r P.TT → ℂ} (hf : Integrable f (mu0 P.r P.TT)) :
    Integrable (fun q => conj (f q)) (mu0 P.r P.TT) :=
  Integrable.mono' hf.norm (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun q => by simp)

theorem ipA_conj (f g : M.Ty P → SmQ P.r P.TT) : ipA P f g = conj (ipA P g f) := by
  rw [AD.ipA_eq, AD.ipA_eq, map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← integral_conj]
  congr 1; funext q
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem pair_sum {N : ℕ} (j : M.Ty P → SmQ P.r P.TT) (F Gf : Qp P.r P.TT → Iota P N → ℂ) (U V : Ix (Fin N) → A P (DQ P))
    (hF : ∀ ω e π, F ω (iotaOf P N e π) = evQ P (actA P (U e) j π) ω)
    (hG : ∀ ω e π, Gf ω (iotaOf P N e π) = evQ P (actA P (V e) j π) ω)
    (hint : ∀ e π, Integrable (fun q => evQ P (actA P (U e) j π) q * conj (evQ P (actA P (V e) j π) q)) (mu0 P.r P.TT)) :
    ∫ ω, ∑ i, F ω i * conj (Gf ω i) ∂(mu0 P.r P.TT) = ∑ e, ipA P (actA P (U e) j) (actA P (V e) j) := by
  have hpt : ∀ ω, ∑ i, F ω i * conj (Gf ω i) =
      ∑ e, ∑ π, evQ P (actA P (U e) j π) ω * conj (evQ P (actA P (V e) j π) ω) := by
    intro ω
    rw [← Formalism.FourierDecayAlt.P.MAx3.G.sum_iota P (fun e π => evQ P (actA P (U e) j π) ω * conj (evQ P (actA P (V e) j π) ω))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hF, ← hG, Formalism.FourierDecayAlt.P.MAx3.G.iotaOf_ixOf]
  simp_rw [hpt]
  rw [integral_finset_sum _ fun e _ => integrable_finset_sum _ fun π _ => hint e π]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finset_sum _ fun π _ => hint e π, AD.ipA_eq]

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB12

section S_AB_AB13

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD
open ComplexConjugate

noncomputable section

variable (P : M.Par) (l : ℕ) (L : LevelData (A P (DQ P)) P.r) (w : List ℝ) (Y : ℝ) (ψ : ℝ → ℝ)

def xv (e : Ix (Fin w.length)) : A P (DQ P) := F.gRw P (DQ P) L l w e
def gb (b : Bool) : SlopeTestRemainingChoices (Fin w.length) (A P (DQ P)) := if b then g2 P l L w Y else g1 P L w Y
def yv (b : Bool) (e : Ix (Fin w.length)) : A P (DQ P) := ∑ e', gb P l L w Y b e e' * xv P l L w e'
def vv (e : Ix (Fin w.length)) : A P (DQ P) := Ph P ψ * xv P l L w e
def yv' (b : Bool) (e : Ix (Fin w.length)) : A P (DQ P) := ∑ e', gb P l L w Y b e e' * vv P l L w ψ e'
def κv (b : Bool) (e : Ix (Fin w.length)) : M.Ty P → ℂ := fun π =>
  ((cs (M.x0 P l π) (M.qC P) (wordP (Y :: w)) (Fin.snoc (α := fun _ => Fin 2) e (if b then 1 else 0))).re : ℂ)
def uv (b : Bool) (e : Ix (Fin w.length)) : A P (DQ P) :=
  (L.ζ * L.ζb * L.GGi) ^ (w.length + 1) * kap P (DQ P) (κv P l w Y b e) * yv P l L w Y b e
def zv (e : Ix (Fin w.length)) : A P (DQ P) :=
  ∑ e', (star (g1 P L w Y)) e e' * uv P l L w Y false e' + ∑ e', (star (g2 P l L w Y)) e e' * uv P l L w Y true e'

variable {P l L w Y ψ} {j : M.Ty P → SmQ P.r P.TT}
variable (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
  (hS : SitesOK (K := ℂ) (startM P (DQ P) l).QQ (sites P (DQ P)))
  (hFr : ∀ w : List ℝ, M.CutWord P l (wordP w) → IsFrame L (ofWord L (startM P (DQ P) l) (wordP w)))
  (hcw : M.CutWord P l (wordP w))
include hTTp hL hLaw hS hFr hcw

theorem hXv : ∀ q i, Xw P l L (ju P j) w q i = evQ P (actA P (xv P l L w (ixOf P _ i).1) j (ixOf P _ i).2) q :=
  fun q i => F.Xw_eq hL hS hFr j w hcw i q

theorem F_mulF {ψ : ℝ → ℝ} (hψ : LE.SmoothLog ψ) : ∀ (q : Qp P.r P.TT) i, LE.mulF (baseQ P) ψ (Xw P l L (ju P j) w) q i =
    evQ P (actA P (vv P l L w ψ (ixOf P _ i).1) j (ixOf P _ i).2) q := by
  intro q i
  show ((ψ (Gq P q) : ℝ) : ℂ) * Xw P l L (ju P j) w q i = _
  rw [hXv hTTp hL hLaw hS hFr hcw, vv, ev_Ph hψ]

theorem F_gX (b : Bool) (i : Iota P w.length) (q : Qp P.r P.TT) :
    gL P l L w Y (Xw P l L (ju P j) w) q (b, i) = evQ P (actA P (yv P l L w Y b (ixOf P _ i).1) j (ixOf P _ i).2) q :=
  I4.apply_matrix_vector P _ _ j _ (hXv hTTp hL hLaw hS hFr hcw) q i

theorem F_gmulF {ψ : ℝ → ℝ} (hψ : LE.SmoothLog ψ) (b : Bool) (i : Iota P w.length) (q : Qp P.r P.TT) :
    gL P l L w Y (LE.mulF (baseQ P) ψ (Xw P l L (ju P j) w)) q (b, i) =
      evQ P (actA P (yv' P l L w Y ψ b (ixOf P _ i).1) j (ixOf P _ i).2) q :=
  I4.apply_matrix_vector P _ _ j _ (F_mulF hTTp hL hLaw hS hFr hcw hψ) q i

theorem F_dgX (b : Bool) (i : Iota P w.length) (q : Qp P.r P.TT) :
    (dwW P l (Y :: w) q (b, i) : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) q (b, i) =
      evQ P (actA P (uv P l L w Y b (ixOf P _ i).1) j (ixOf P _ i).2) q := by
  rw [F_gX hTTp hL hLaw hS hFr hcw, uv, PG.act_dg hTTp hL hLaw]
  unfold dwW κv
  simp only [List.length_cons]
  rw [F.ixOf_succ]
  push_cast
  ring

theorem F_gst (i : Iota P w.length) (q : Qp P.r P.TT) :
    gstL P l L w Y (fun ω k => (dwW P l (Y :: w) ω k : ℂ) * gL P l L w Y (Xw P l L (ju P j) w) ω k) q i =
      evQ P (actA P (zv P l L w Y (ixOf P _ i).1) j (ixOf P _ i).2) q := by
  have h : ∀ (b : Bool) q i', (fun q' i'' => (dwW P l (Y :: w) q' (b, i'') : ℂ) *
      gL P l L w Y (Xw P l L (ju P j) w) q' (b, i'')) q i' =
      evQ P (actA P (uv P l L w Y b (ixOf P _ i').1) j (ixOf P _ i').2) q :=
    fun b q i' => F_dgX hTTp hL hLaw hS hFr hcw b i' q
  unfold gstL
  rw [I4.apply_matrix_vector P _ _ j _ (h false) q i, I4.apply_matrix_vector P _ _ j _ (h true) q i, zv, F.actA_add]
  rfl

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB13

section S_AB_AB14

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD
open ComplexConjugate

noncomputable section

theorem QA_finsum {P : M.Par} {L : LevelData (A P (DQ P)) P.r} {j : M.Ty P → SmQ P.r P.TT} {ι : Type}
    (s : Finset ι) {a : A P (DQ P)} (f : ι → A P (DQ P)) (h : ∀ i ∈ s, QA L j a (f i)) : QA L j a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact QA_zero a
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact QA_add (h b (Finset.mem_insert_self b s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem io_apply {P : M.Par} {N : ℕ} (x : A P (DQ P)) (e e' : Ix (Fin N)) :
    (io x : SlopeTestRemainingChoices (Fin N) (A P (DQ P))) e e' = if e = e' then x else 0 := by
  simp [io, Matrix.scalar_apply, Matrix.diagonal_apply]

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {w : List ℝ} {Y : ℝ} {j : M.Ty P → SmQ P.r P.TT}
variable (hTTp : 0 < P.TT) (hL : IsModelLevel P (DQ P) L) (hLaw : (DQ P).Laws P.TT)
  (hS : SitesOK (K := ℂ) (startM P (DQ P) l).QQ (sites P (DQ P)))
  (hFr : ∀ w : List ℝ, M.CutWord P l (wordP w) → IsFrame L (ofWord L (startM P (DQ P) l) (wordP w)))
  (hcw : M.CutWord P l (wordP w))
include hTTp hL hLaw hS hFr hcw

theorem xv_NFD (e : Ix (Fin w.length)) : xv P l L w e ∈ NFD L w.length :=
  normal_form_two_le_degree hL hLaw _ (gRw_NF hL hLaw hS hFr w hcw e)

theorem ee_BA (e e' : Ix (Fin w.length)) : (frW P l L w).ee (Y : ℂ) e e' ∈ Formalism.FourierDecayAlt.P.MAx3.I4.BA L :=
  (I4.frame_memB hL hLaw l (wordP w)).1 (Y : ℂ) e e'

theorem yv_NFD (b : Bool) (e : Ix (Fin w.length)) : yv P l L w Y b e ∈ NFD L (w.length + 1) := by
  refine normal_form_two_le_degree hL hLaw _ ?_
  have := I4.letter_vec_NF hL hLaw (Y : ℂ) (Y : ℂ) ((frW P l L w).ee (Y : ℂ))
    ((I4.frame_memB hL hLaw l (wordP w)).1 (Y : ℂ)) (xv P l L w) (fun e => gRw_NF hL hLaw hS hFr w hcw e) b e
  cases b <;> exact this

theorem gb_apply (b : Bool) (e e' : Ix (Fin w.length)) : gb P l L w Y b e e' =
    if b then ((if e = e' then L.Dbi * L.R0 (Y : ℂ) else 0) + (frW P l L w).ee (Y : ℂ) e e' * (L.Di * L.Ahat (Y : ℂ)))
    else (if e = e' then L.Di * L.Ahat (Y : ℂ) else 0) :=
  I4.letter_entry hL hLaw (Y : ℂ) (Y : ℂ) ((frW P l L w).ee (Y : ℂ)) b e e'

theorem QA_left {m0 : ℕ} (hD : JDecay P L j m0) (hA : JAdj P L j m0) (hm0 : w.length + (w.length + 2) ≤ m0)
    {ψ : ℝ → ℝ} (hψ : admitted ψ) (e : Ix (Fin w.length)) : QA L j (vv P l L w ψ e) (zv P l L w Y e) := by
  have hx := xv_NFD hTTp hL hLaw hS hFr hcw e
  unfold zv
  refine QA_add (QA_finsum _ _ fun e' _ => ?_) (QA_finsum _ _ fun e' _ => ?_)
  · rw [Matrix.star_apply]
    unfold g1
    rw [io_apply]
    by_cases h : e' = e
    · rw [if_pos h]
      exact quadratic_form_lowering hTTp hL hLaw hD hA hm0 hψ hx Y _ (yv_NFD hTTp hL hLaw hS hFr hcw false e')
    · rw [if_neg h, star_zero, zero_mul]; exact QA_zero _
  · rw [Matrix.star_apply]
    have e2 : g2 P l L w Y e' e = gb P l L w Y true e' e := rfl
    rw [e2, gb_apply hTTp hL hLaw hS hFr hcw, if_pos rfl, star_add, add_mul]
    refine QA_add ?_ (quadratic_form_lowering_base hTTp hL hLaw hD hA hm0 hψ hx Y _ (ee_BA hTTp hL hLaw hS hFr hcw e' e)
      (yv_NFD hTTp hL hLaw hS hFr hcw true e'))
    by_cases h : e' = e
    · rw [if_pos h]
      exact quadratic_form_raising hTTp hL hLaw hD hA hm0 hψ hx Y _ (yv_NFD hTTp hL hLaw hS hFr hcw true e')
    · rw [if_neg h, star_zero, zero_mul]; exact QA_zero _

theorem QA_right {m0 : ℕ} (hD : JDecay P L j m0) (hA : JAdj P L j m0) (hm0 : (w.length + 1) + (w.length + 1) ≤ m0)
    {ψ : ℝ → ℝ} (hψ : admitted ψ) (b : Bool) (e : Ix (Fin w.length)) :
    QA L j (yv' P l L w Y ψ b e) (uv P l L w Y b e) := by
  refine QA_R hTTp hL hLaw hD hA hm0 ?_ _ (yv_NFD hTTp hL hLaw hS hFr hcw b e)
  unfold yv'
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun e' _ => ?_
  have hx := xv_NFD hTTp hL hLaw hS hFr hcw e'
  rw [gb_apply hTTp hL hLaw hS hFr hcw]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    by_cases h : e = e'
    · rw [if_pos h]; exact rc1 hTTp hL hLaw hψ hx (Y : ℂ)
    · rw [if_neg h, zero_mul, mul_zero]; exact Submodule.zero_mem _
  · simp only [if_true]
    rw [add_mul, mul_add]
    refine Submodule.add_mem _ ?_ (rc3 hTTp hL hLaw hψ hx (Y : ℂ) (ee_BA hTTp hL hLaw hS hFr hcw e e'))
    by_cases h : e = e'
    · rw [if_pos h]; exact rc2 hTTp hL hLaw hψ hx (Y : ℂ)
    · rw [if_neg h, zero_mul, mul_zero]; exact Submodule.zero_mem _

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB14

section S_AB_AB15

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD
open ComplexConjugate

noncomputable section

variable {P : M.Par} {l : ℕ} {L : LevelData (A P (DQ P)) P.r} {w : List ℝ} {Y : ℝ} {ψ : ℝ → ℝ}

theorem ring_id_abs {R : Type} [Ring R] [StarRing R] {ι : Type} [Fintype ι] (G1 G2 : Matrix ι ι R) (u0 u1 v : ι → R) :
    ∑ e, star (∑ e', (star G1) e e' * u0 e' + ∑ e', (star G2) e e' * u1 e') * v e =
      (∑ e', star (u1 e') * ∑ e, G2 e' e * v e) + ∑ e', star (u0 e') * ∑ e, G1 e' e * v e := by
  have hz : ∀ e, star (∑ e', (star G1) e e' * u0 e' + ∑ e', (star G2) e e' * u1 e') =
      ∑ e', star (u0 e') * G1 e' e + ∑ e', star (u1 e') * G2 e' e := by
    intro e
    rw [star_add, star_sum, star_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun e' _ => ?_ <;> rw [star_mul, Matrix.star_apply, star_star]
  simp only [hz, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_assoc]
  · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_assoc]

theorem ring_id : ∑ e, star (zv P l L w Y e) * vv P l L w ψ e =
    ∑ b : Bool, ∑ e', star (uv P l L w Y b e') * yv' P l L w Y ψ b e' := by
  have h := ring_id_abs (g1 P L w Y) (g2 P l L w Y) (uv P l L w Y false) (uv P l L w Y true) (vv P l L w ψ)
  have e1 : ∀ e', yv' P l L w Y ψ true e' = ∑ e, g2 P l L w Y e' e * vv P l L w ψ e := fun e' => rfl
  have e0 : ∀ e', yv' P l L w Y ψ false e' = ∑ e, g1 P L w Y e' e * vv P l L w ψ e := fun e' => rfl
  have ez : ∀ e, zv P l L w Y e = ∑ e', (star (g1 P L w Y)) e e' * uv P l L w Y false e' +
      ∑ e', (star (g2 P l L w Y)) e e' * uv P l L w Y true e' := fun e => rfl
  rw [Fintype.sum_bool]
  simp only [e1, e0, ez]
  exact h

theorem pair_int {N : ℕ} (j : M.Ty P → SmQ P.r P.TT) (F Gf : Qp P.r P.TT → Iota P N → ℂ) (U V : Ix (Fin N) → A P (DQ P))
    (hF : ∀ ω e π, F ω (iotaOf P N e π) = evQ P (actA P (U e) j π) ω)
    (hG : ∀ ω e π, Gf ω (iotaOf P N e π) = evQ P (actA P (V e) j π) ω)
    (hint : ∀ e π, Integrable (fun q => evQ P (actA P (U e) j π) q * conj (evQ P (actA P (V e) j π) q)) (mu0 P.r P.TT)) :
    Integrable (fun ω => ∑ i, F ω i * conj (Gf ω i)) (mu0 P.r P.TT) := by
  have hpt : ∀ ω, ∑ i, F ω i * conj (Gf ω i) =
      ∑ e, ∑ π, evQ P (actA P (U e) j π) ω * conj (evQ P (actA P (V e) j π) ω) := by
    intro ω
    rw [← Formalism.FourierDecayAlt.P.MAx3.G.sum_iota P (fun e π => evQ P (actA P (U e) j π) ω * conj (evQ P (actA P (V e) j π) ω))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hF, ← hG, Formalism.FourierDecayAlt.P.MAx3.G.iotaOf_ixOf]
  simp_rw [hpt]
  exact integrable_finset_sum _ fun e _ => integrable_finset_sum _ fun π _ => hint e π

theorem swap_int {f g : Qp P.r P.TT → ℂ} (h : Integrable (fun q => f q * conj (g q)) (mu0 P.r P.TT)) :
    Integrable (fun q => g q * conj (f q)) (mu0 P.r P.TT) :=
  (int_conj h).congr (Filter.Eventually.of_forall fun q => by simp only [map_mul, Complex.conj_conj, mul_comm])

end

end Formalism.FourierDecayAlt.P.MAx3.AB

end S_AB_AB15

section S_AB_AB16

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx3.AB

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD
open ComplexConjugate

noncomputable section

theorem admissible_cutoff_product (c : LE.Cut) {ε ε₂ σ : ℝ} (hε : 0 < ε) (hε₂ : 0 < ε₂) (hσ : 4 ≤ σ) :
    admitted (fun y => c.sc ε₂ 1 y * LE.th ε σ y) := by
  refine ⟨(PG.smoothLog_chi c ε₂).mul (Formalism.FourierDecayAlt.P.le_thetaSmooth_proof ε σ hε), ⟨ε₂ / 2, by positivity, fun x hx => ?_⟩,
    fun p => ?_⟩
  · show c.χ (x / ε₂) ^ 1 * LE.th ε σ x = 0
    rw [c.zero (x / ε₂) (by rw [div_le_iff₀ hε₂]; linarith), pow_one, zero_mul]
  · obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.cutoff_theta Formalism.FourierDecayAlt.P.cauchy_theta_identity c σ ε hσ hε p
    refine ⟨|C|, fun x hx => ?_⟩
    have h1 := (hC ε₂ x hε₂ hx).1
    have h2 := Formalism.FourierDecayAlt.P.le_thetaRange_proof ε σ x hε (by linarith) hx
    calc |LE.ld p (fun y => c.sc ε₂ 1 y * LE.th ε σ y) x| ≤ C * LE.th ε σ x := h1
      _ ≤ |C| * LE.th ε σ x := mul_le_mul_of_nonneg_right (le_abs_self C) h2.1.le
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h2.2 (abs_nonneg C)
      _ = |C| := mul_one _

theorem ipA_sum_j {P : M.Par} {ι : Type} (s : Finset ι) (x : ι → A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT)
    (h : ∀ e ∈ s, ∀ π, Integrable (fun q => evQ P (actA P (x e) j π) q * conj (evQ P (j π) q)) (mu0 P.r P.TT)) :
    ∑ e ∈ s, ipA P (actA P (x e) j) j = ipA P (actA P (∑ e ∈ s, x e) j) j := by
  rw [actA_finsum, ipA_sum_left s (fun e => actA P (x e) j) j h]

theorem int_sum_j {P : M.Par} {ι : Type} (s : Finset ι) (x : ι → A P (DQ P)) (j : M.Ty P → SmQ P.r P.TT)
    (h : ∀ e ∈ s, ∀ π, Integrable (fun q => evQ P (actA P (x e) j π) q * conj (evQ P (j π) q)) (mu0 P.r P.TT)) (π : M.Ty P) :
    Integrable (fun q => evQ P (actA P (∑ e ∈ s, x e) j π) q * conj (evQ P (j π) q)) (mu0 P.r P.TT) := by
  have := integrable_finset_sum s (fun e he => h e he π)
  refine this.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Finset.sum_apply]
  rw [actA_finsum, Finset.sum_apply, MAx2.Jet.evQ_sum, Finset.sum_mul]

end

end Formalism.FourierDecayAlt.P.MAx3.AB

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr MeasureTheory
open Formalism.FourierDecayAlt.P.MAx3.Z Formalism.FourierDecayAlt.P.MAx3.AD Formalism.FourierDecayAlt.P.MAx3.AB
open ComplexConjugate

theorem adjoint_bounded : Formalism.FourierDecayAlt.MA.AdjBQ := by
  intro P l L j lam α β Lb c Ntot hH w hw hl Y hY ε ε₂ hε hε₂
  obtain ⟨⟨hOK, hl1, hlk, hML, hu, hu', hαβ, hcut⟩, hD, hA, hE, hN1, -⟩ := id hH
  have hTTp : 0 < P.TT := mul_pos hOK.T_pos hOK.T'_pos
  have hLaw := analytic_laws P.r P.TT hTTp.le
  have hcw : M.CutWord P l (wordP w) := MAx3.F.cutWord_of hH c w hw (by omega)
  obtain ⟨L', hL', -, -, hFC⟩ := model_frame_analytic P hOK l hl1 hlk
  have hLL := MAx3.F.level_unique P (DQ P) L' L hL' hML
  subst hLL
  have hS := sites_admissible P (DQ P) hLaw l
  have hFr : ∀ w' : List ℝ, M.CutWord P l (wordP w') → IsFrame L' (ofWord L' (startM P (DQ P) l) (wordP w')) :=
    fun w' h => (hFC _ _ h).1
  have hσ : (4 : ℝ) ≤ 4 * (Ntot : ℝ) := by
    have : (1 : ℝ) ≤ Ntot := by exact_mod_cast (show 1 ≤ Ntot by omega)
    linarith
  have hψ := admissible_cutoff_product c hε hε₂ hσ
  set ψ : ℝ → ℝ := fun y => c.sc ε₂ 1 y * LE.th ε (4 * (Ntot : ℝ)) y with hψdef
  have hm0 : w.length + (w.length + 2) ≤ 2 * Ntot + 2 := by omega
  have hm0' : (w.length + 1) + (w.length + 1) ≤ 2 * Ntot + 2 := by omega
  have QL := fun e => QA_left (Y := Y) hTTp hML hLaw hS hFr hcw hD hA hm0 hψ e
  have QR := fun b e => QA_right (Y := Y) hTTp hML hLaw hS hFr hcw hD hA hm0' hψ b e

  have hLHS : (∫ ω, LE.pr (baseQ P) (fun _ _ => 1)
      (gstL P l L' w Y (fun ω k => (dwW P l (Y :: w) ω k : ℂ) * gL P l L' w Y (Xw P l L' (ju P j) w) ω k))
      (LE.mulF (baseQ P) ψ (Xw P l L' (ju P j) w)) ω ∂(mu0 P.r P.TT)) =
      ∑ e, ipA P (actA P (zv P l L' w Y e) j) (actA P (vv P l L' w ψ e) j) := by
    refine pair_sum j _ _ _ _ (fun ω e π => ?_) (fun ω e π => ?_) (fun e π => swap_int ((QL e).1 π))
    · show ((1 : ℝ) : ℂ) * _ = _
      rw [Complex.ofReal_one, one_mul, F_gst hTTp hML hLaw hS hFr hcw, MAx3.G.ixOf_iotaOf]
    · rw [F_mulF hTTp hML hLaw hS hFr hcw hψ.1, MAx3.G.ixOf_iotaOf]

  have hRHS : (∫ ω, LE.pr (baseQ P) (dwW P l (Y :: w)) (gL P l L' w Y (Xw P l L' (ju P j) w))
      (gL P l L' w Y (LE.mulF (baseQ P) ψ (Xw P l L' (ju P j) w))) ω ∂(mu0 P.r P.TT)) =
      ∑ b, ∑ e, ipA P (actA P (uv P l L' w Y b e) j) (actA P (yv' P l L' w Y ψ b e) j) := by
    have hF : ∀ b ω e π, (fun ω i => (dwW P l (Y :: w) ω (b, i) : ℂ) * gL P l L' w Y (Xw P l L' (ju P j) w) ω (b, i))
        ω (iotaOf P w.length e π) = evQ P (actA P (uv P l L' w Y b e) j π) ω := fun b ω e π => by
      show _ * _ = _
      rw [F_dgX hTTp hML hLaw hS hFr hcw, MAx3.G.ixOf_iotaOf]
    have hG : ∀ b ω e π, (fun ω i => gL P l L' w Y (LE.mulF (baseQ P) ψ (Xw P l L' (ju P j) w)) ω (b, i))
        ω (iotaOf P w.length e π) = evQ P (actA P (yv' P l L' w Y ψ b e) j π) ω := fun b ω e π => by
      show gL P l L' w Y _ ω (b, _) = _
      rw [F_gmulF hTTp hML hLaw hS hFr hcw hψ.1, MAx3.G.ixOf_iotaOf]
    have hpt : ∀ ω : Qp P.r P.TT, LE.pr (baseQ P) (dwW P l (Y :: w)) (gL P l L' w Y (Xw P l L' (ju P j) w))
        (gL P l L' w Y (LE.mulF (baseQ P) ψ (Xw P l L' (ju P j) w))) ω =
        ∑ b : Bool, ∑ i : Iota P w.length, (fun ω i => (dwW P l (Y :: w) ω (b, i) : ℂ) *
          gL P l L' w Y (Xw P l L' (ju P j) w) ω (b, i)) ω i *
          conj ((fun ω i => gL P l L' w Y (LE.mulF (baseQ P) ψ (Xw P l L' (ju P j) w)) ω (b, i)) ω i) := by
      intro ω
      unfold LE.pr
      exact Fintype.sum_prod_type _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_finset_sum _ fun b _ => pair_int j _ _ _ _ (hF b) (hG b) (fun e π => swap_int ((QR b e).1 π))]
    exact Finset.sum_congr rfl fun b _ => pair_sum j _ _ _ _ (hF b) (hG b) (fun e π => swap_int ((QR b e).1 π))
  show (∫ ω, LE.pr (baseQ P) (fun _ _ => 1)
      (gstL P l L' w Y (fun ω k => (dwW P l (Y :: w) ω k : ℂ) * gL P l L' w Y (Xw P l L' (ju P j) w) ω k))
      (LE.mulF (baseQ P) ψ (Xw P l L' (ju P j) w)) ω ∂(mu0 P.r P.TT)) =
    ∫ ω, LE.pr (baseQ P) (dwW P l (Y :: w)) (gL P l L' w Y (Xw P l L' (ju P j) w))
      (gL P l L' w Y (LE.mulF (baseQ P) ψ (Xw P l L' (ju P j) w))) ω ∂(mu0 P.r P.TT)
  rw [hLHS, hRHS]
  have eL : ∀ e, ipA P (actA P (zv P l L' w Y e) j) (actA P (vv P l L' w ψ e) j) =
      conj (ipA P (actA P (star (zv P l L' w Y e) * vv P l L' w ψ e) j) j) := fun e => by
    rw [Formalism.FourierDecayAlt.P.MAx3.AB.ipA_conj, (QL e).2.2]
  have eR : ∀ b e, ipA P (actA P (uv P l L' w Y b e) j) (actA P (yv' P l L' w Y ψ b e) j) =
      conj (ipA P (actA P (star (uv P l L' w Y b e) * yv' P l L' w Y ψ b e) j) j) := fun b e => by
    rw [Formalism.FourierDecayAlt.P.MAx3.AB.ipA_conj, (QR b e).2.2]
  simp only [eL, eR, ← map_sum]
  congr 1
  rw [ipA_sum_j Finset.univ _ j (fun e _ => (QL e).2.1)]
  have inner : ∀ b, ∑ e, ipA P (actA P (star (uv P l L' w Y b e) * yv' P l L' w Y ψ b e) j) j =
      ipA P (actA P (∑ e, star (uv P l L' w Y b e) * yv' P l L' w Y ψ b e) j) j :=
    fun b => ipA_sum_j Finset.univ _ j (fun e _ => (QR b e).2.1)
  simp only [inner]
  rw [ipA_sum_j Finset.univ _ j (fun b _ => int_sum_j Finset.univ _ j (fun e _ => (QR b e).2.1)), ring_id]

end Formalism.FourierDecayAlt.P

end S_AB_AB16

namespace Formalism.FourierDecayAlt.P

theorem weight_ratio : Formalism.FourierDecayAlt.MA.WeightRatioQ := MAx3.R.weightRatio

theorem residuesAlt : Formalism.FourierDecayAlt.MA.ResiduesQ := MAx3.R.residues

theorem family_imports : Formalism.FourierDecayAlt.MA.FamImportsQ :=
  family_imports_of_parts factor_exists factor_chosen family_restriction

theorem theorem_P : Formalism.FourierDecayAlt.MA.ThmPQ :=
  theorem_P_of_parts theorem_P_form theorem_P_adjoint theorem_P_weight

theorem induction_imports : Formalism.FourierDecayAlt.MA.StepImportsQ :=
  induction_imports_of_parts measure_regular weight_positive polynomial_regular third_identity adjoint_bounded jet_module_closed
    fourth_identity fourth_identity_dual fifth_identity_first residuesAlt weight_ratio probability_ratio

theorem lemma_model : Formalism.FourierDecayAlt.MA.LemmaEModel :=
  lemma_model_of_parts le_E_proof constants_choice induction_imports family_imports
    roots_outside first_identity jacobi_square_integrable theorem_P jacobi_norm

end Formalism.FourierDecayAlt.P
