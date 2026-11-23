import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDRed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def JDHatOpQQ : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ X ∈ MA.hatSet (D.parOf S v) L,
        ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
          (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ B.SmoothCoef (B.GPos (T v).base) t.2 ∧
            B.Commutes (T v).base (B.GPos (T v).base) t.2 ∧
            GlobCoef t.2 (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder t.2 : ℝ) ≤ Cc * nDim S.G.k S.G.r) ∧
          ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
            MA.actA (D.parOf S v) X (trJ S T v e J) =
              (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

theorem jDHatOpQQ_of (h : JDHatOp) : JDHatOpQQ := by
  obtain ⟨Cc, hCc, H⟩ := h
  exact ⟨Cc, hCc, fun E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa _ hL =>
    H E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL⟩

def JDecayTrQQd : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      MA.JDecay (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

theorem jDecayTrQQd_of_leaves (h1 : JDHatBdd) (h2 : JDHatOpQQ) (h3 : JDJComm) (h4 : JDCCLower) (h5 : TransferSquareIntegrable)
    (h6 : BoundedOperatorsSquareIntegrable) : JDecayTrQQd := by
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C3, H3⟩ := h3
  obtain ⟨C5, H5⟩ := h5
  unfold JDecayTrQQd
  refine ⟨8 * C2 + |C3| + |C5|, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL hJf
  have hmono : ∀ c, c ≤ 8 * C2 + |C3| + |C5| → BuiltOW c S T f χ ν' m₀ top A₀ := fun c hc =>
    ⟨isBuiltPlace_mono hc hB.1, hB.2⟩
  have hB2 := hmono C2 (by linarith [abs_nonneg C3, abs_nonneg C5])
  have hB3 := hmono C3 (by linarith [le_abs_self C3, abs_nonneg C5])
  have hB5 := hmono C5 (by linarith [le_abs_self C5, abs_nonneg C3])
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hTTpos : 0 < (D.parOf S v).TT := by rw [hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  have hInCC : ∀ m : ℕ, B.InCC A₀ m (f v) := (hB.1.2.2.2.1.2 v).2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hCk, -, hA, -⟩ := hB.1

  have hR : (0 : ℝ) ≤ (S.G.r : ℝ) := Nat.cast_nonneg _
  have hnE : nDim S.G.k S.G.r = 2 * (S.G.r : ℝ) + S.G.k + 1 := by unfold nDim; push_cast; ring
  have hn : (1 : ℝ) ≤ nDim S.G.k S.G.r := by
    rw [hnE]; have := Nat.cast_nonneg (α := ℝ) S.G.k; linarith
  have hA' : (8 * C2 + |C3| + |C5|) * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * nDim S.G.k S.G.r ^ 2 + nDim S.G.k S.G.r ^ 3) ≤ A₀ := by rw [hnE]; exact hA
  obtain ⟨hK3', hK5'⟩ := jd_arith C2 C3 C5 _ _ _ A₀ hC2 hR hn (Nat.cast_nonneg _) hA'
  have hdm0 : 0 ≤ C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r := by
    have := le_trans zero_le_one hn; positivity
  have hK3 : ∀ i : ℕ, i ≤ 2 * S.Ntop + 1 → ∀ o : ℝ, o ≤ C2 * nDim S.G.k S.G.r →
      C3 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * o +
      C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ≤ A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by
    intro i hi o ho
    refine hK3' _ _ ?_ ho
    have : ((i : ℕ) : ℝ) ≤ ((2 * S.Ntop + 1 : ℕ) : ℝ) := by exact_mod_cast hi
    push_cast at this; linarith
  have hK5 : ∀ i : ℕ, i ≤ 2 * S.Ntop + 2 → C5 * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r ≤
      A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by
    intro i hi
    refine hK5' _ ?_
    have : ((i : ℕ) : ℝ) ≤ ((2 * S.Ntop + 2 : ℕ) : ℝ) := by exact_mod_cast hi
    push_cast at this; linarith

  let Good : ℕ → (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → Prop := fun i F =>
    B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ (∀ m : ℕ, B.InCC (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) m F) ∧
      B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)
  let tr : (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → M.Ty (D.parOf S v) →
      MA.SmQ (D.parOf S v).r (D.parOf S v).TT := fun F => trJ S T v e (B.JF (T v).base F)
  have hStep : ∀ i, i < 2 * S.Ntop + 2 → ∀ F, Good i F → ∀ X ∈ MA.hatSet (D.parOf S v) L,
      ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))),
        (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ Good (i + 1) t.2) ∧
        MA.actA (D.parOf S v) X (tr F) = (ts.map fun t => MA.actA (D.parOf S v) t.1 (tr t.2)).sum := by
    intro i hi F hF X hX
    obtain ⟨hCkF, hCCF, hFF⟩ := hF
    obtain ⟨ts, hts, hid⟩ := H2 E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e L hFr hGa hQQ hL X hX
    have hthr : ∀ t ∈ ts, C3 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder t.2 : ℝ) +
        C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ≤ A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) :=
      fun t ht => hK3 i (by omega) _ (hts t ht).2.2.2.2
    have l3 : ∀ t ∈ ts, _ := fun t ht =>
      H3 E Wp Wq S T f χ ν' m₀ top A₀ hB3 v t.2 (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) hdm0
        (hts t ht).2.1 (hts t ht).2.2.1 (hts t ht).2.2.2.1 (hthr t ht) F hCkF hCCF hFF
    refine ⟨ts.map fun t => (t.1, B.opApply t.2 F), ?_, ?_⟩
    · intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
      have l4 := h4 _ _ _ _ t0.2 (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) hdm0 (hts t0 ht0).2.2.2.1 F hCkF hCCF
      refine ⟨(hts t0 ht0).1, l4.1, fun m => ?_, (l3 t0 ht0).1⟩
      have e : A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) - (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) = A₀ - ((i + 1 : ℕ) : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by push_cast; ring
      rw [← e]; exact l4.2 m
    · rw [hid (B.JF (T v).base F) hFF, List.map_map]
      congr 1
      refine List.map_congr_left fun t ht => ?_
      simp only [Function.comp]
      congr 1
      exact trJ_congr S T v e _ _ (l3 t ht).2
  intro w hw hwh π
  have hG0 : Good 0 (f v) := ⟨hCk v, fun m => by simpa using hInCC m, hJf⟩
  have hmem := jd_word_span L Good tr (2 * S.Ntop + 2) (h1 _ L hTTpos.le hL) hStep w hw hwh (f v) hG0
  have hgen : ∀ u ∈ {u | ∃ b ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L), ∃ F', Good w.length F' ∧
      u = MA.actA (D.parOf S v) b (tr F')}, componentwiseL2 (D.parOf S v) u := by
    rintro u ⟨b, hb, F', ⟨hCk', hCC', hFF'⟩, rfl⟩
    have l5 := H5 E Wp Wq S T f χ ν' m₀ top A₀ hB5 v e hFr (A₀ - (w.length : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) (hK5 _ hw) F' hCk' hCC' hFF'
    exact (componentwiseL2_iff_integrable _ _).2 (h6 _ L hTTpos hL b hb _ l5)
  exact (componentwiseL2_iff_integrable _ _).1 (componentwiseL2_of_span _ _ hgen _ hmem) π

theorem jDecayTrQQd_of_open (h2 : JDHatOpQQ) : JDecayTrQQd :=
  jDecayTrQQd_of_leaves hat_bounded_decay_holds h2 transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable

theorem jDecayTr_of_hatOp (h2 : JDHatOp) : JDecayTr := jDecayTr_of_open h2 transfer_commutation_holds

end

end Formalism.FourierDecayAlt.P.CutMP
