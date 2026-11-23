import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.HatProd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

open Formalism.FourierDecayAlt.P.CutMP

theorem kbs_arith (R n N o A : ℝ) (hR : 0 ≤ R) (hn : 1 ≤ n) (hN : 0 ≤ N) (ho : o ≤ N * n)
    (hA : 18 * (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) ≤ A) : 12 * (R + 1) * n ^ 2 + 6 * R * o + 0 ≤ A := by
  have hρ4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hn2 : n ≤ n ^ 2 := le_self_pow₀ hn (by norm_num)
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by norm_num)
  have h1 : (R + 1) * n ^ 2 ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul hρ4 hn23 (by positivity) (by positivity)
  have h2 : R * o ≤ (R + 1) ^ 4 * (N * n ^ 2) :=
    calc R * o ≤ R * (N * n) := mul_le_mul_of_nonneg_left ho hR
      _ ≤ (R + 1) ^ 4 * (N * n ^ 2) :=
        mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hn2 hN) (by positivity) (by positivity)
  have h3 : 0 ≤ (R + 1) ^ 4 * n ^ 3 := by positivity
  have h4 : 0 ≤ (R + 1) ^ 4 * (N * n ^ 2) := by positivity
  nlinarith

theorem hatProdJB (hH : HatProdB) (hPoly : JDPolyOK) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (he : Gauge.IsFrameB P Bs e)
    (hQ : IsGaugeQQB P Bs e) (hL : MA.IsModelLevel P (MA.DQ P) L) (N : ℕ) (u : List (MA.A P (MA.DQ P)))
    (hN : u.length ≤ N) (hu : ∀ a ∈ u, a ∈ MA.hatSet P L) :
    ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (Th : Fin m → B.DiffOp P.k P.r Wp Wq),
      (∀ k, b k ∈ Submonoid.closure (MA.bddSet P L)) ∧
      (∀ k, B.SmoothCoef (B.GPos Bs) (Th k) ∧ B.Commutes Bs (B.GPos Bs) (Th k) ∧
        GlobCoef (Th k) (1 * ((P.r : ℝ) + 1) * nDim P.k P.r * ((N : ℝ) + 1)) ∧
        (B.opOrder (Th k) : ℝ) ≤ 1 * nDim P.k P.r * ((N : ℝ) + 1)) ∧
      ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
        18 * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
        B.JF Bs F ∈ FFB P Bs →
        MA.actA P u.prod (Gauge.trJB P Bs e (B.JF Bs F)) =
          ∑ k, MA.actA P (b k) (Gauge.trJB P Bs e (B.JF Bs (B.opApply (Th k) F))) := by
  obtain ⟨ts, hts, hJ⟩ := hH Wp Wq P Bs hpl hk e he hQ L hL u hu
  have hn : (1 : ℝ) ≤ nDim P.k P.r := by
    unfold nDim; exact_mod_cast Nat.le_add_left 1 _
  have hNr : (u.length : ℝ) ≤ N := by exact_mod_cast hN
  have hord : ∀ t ∈ ts, (B.opOrder t.2 : ℝ) ≤ (N : ℝ) * nDim P.k P.r := fun t ht => by
    have h := (hPoly _ _ _ _ _ _ _ (hts t ht).2.1).2.2
    have h' : (B.opOrder t.2 : ℝ) ≤ (u.length : ℝ) * nDim P.k P.r := by unfold nDim; exact_mod_cast h
    exact h'.trans (mul_le_mul_of_nonneg_right hNr (by linarith))
  refine ⟨ts.length, fun i => (ts.get i).1, fun i => (ts.get i).2, fun i => (hts _ (List.get_mem ts i)).1,
    fun i => ?_, fun F A _ hCC hA hJF => ?_⟩
  · have ht := List.get_mem ts i
    obtain ⟨hs, hg, -⟩ := hPoly _ _ _ _ _ _ _ (hts _ ht).2.1
    refine ⟨hs _, (hts _ ht).2.2, hg _ ?_, (hord _ ht).trans ?_⟩
    · have e1 : ((u.length * ((P.r + 1) * (2 * P.r + P.k + 1)) : ℕ) : ℝ) =
          (u.length : ℝ) * (((P.r : ℝ) + 1) * nDim P.k P.r) := by unfold nDim; push_cast; ring
      have h0 : 0 ≤ ((P.r : ℝ) + 1) * nDim P.k P.r := by positivity
      rw [e1]
      nlinarith
    · nlinarith
  · have hid : MA.actA P u.prod (Gauge.trJB P Bs e (B.JF Bs F)) = _ := hJ _ hJF
    show MA.actA P u.prod (Gauge.trJB P Bs e (B.JF Bs F)) =
      ∑ k : Fin ts.length, MA.actA P (ts.get k).1
        (Gauge.trJB P Bs e (B.JF Bs (B.opApply (ts.get k).2 F)))
    rw [hid, ← Fin.sum_univ_fun_getElem]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ht := List.get_mem ts i
    have hnE : nDim P.k P.r = 2 * (P.r : ℝ) + P.k + 1 := by unfold nDim; push_cast; ring
    have hT := jdc_thrW (k := P.k) (r := P.r) (B.opOrder (ts.get i).2) A 0 le_rfl
      (kbs_arith _ _ N _ A (Nat.cast_nonneg _) hn (Nat.cast_nonneg _) (hord _ ht) (by rw [hnE]; exact hA))
    have hth := Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ Bs A _ F (ts.get i).2 _ subset_rfl le_rfl hT (hCC _)
      (fun s hs f' hf' g hg => (hts _ ht).2.2 s hs f' hf' g (jdc_om_sub_gpos _ hg))
    exact congrArg _ (trJB_congr hpl e fun g hg => hth g (jdc_om_of _ _ hg.1 hg.2))

end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
