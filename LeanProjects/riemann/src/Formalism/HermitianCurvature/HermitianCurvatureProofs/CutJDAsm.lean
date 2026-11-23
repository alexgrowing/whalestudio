import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAsm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section gen

variable (P : M.Par)

theorem jd_actA_add (a b : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (a + b) x = MA.actA P a x + MA.actA P b x := by
  funext π
  show ∑ π', ((a + b) π π').1 (x π') = ∑ π', (a π π').1 (x π') + ∑ π', (b π π').1 (x π')
  rw [← Finset.sum_add_distrib]
  rfl

theorem jd_actA_zero (x : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 0 x = 0 := by
  funext π
  show ∑ π', ((0 : MA.A P (MA.DQ P)) π π').1 (x π') = 0
  exact Finset.sum_eq_zero fun _ _ => rfl

theorem jd_actA_addR (a : MA.A P (MA.DQ P)) (x y : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (x + y) = MA.actA P a x + MA.actA P a y := by
  funext π
  show ∑ π', (a π π').1 (x π' + y π') = ∑ π', (a π π').1 (x π') + ∑ π', (a π π').1 (y π')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => map_add _ _ _

theorem jd_actA_smulR (a : MA.A P (MA.DQ P)) (c : ℂ) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (c • x) = c • MA.actA P a x := by
  funext π
  show ∑ π', (a π π').1 (c • x π') = c • ∑ π', (a π π').1 (x π')
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => map_smul _ _ _

theorem jd_actA_zeroR (a : MA.A P (MA.DQ P)) : MA.actA P a 0 = 0 := by
  have h := jd_actA_smulR P a 0 0
  rw [zero_smul, zero_smul] at h
  exact h

theorem jd_actA_listsum {ι : Type} (a : MA.A P (MA.DQ P)) (l : List ι) (g : ι → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (l.map g).sum = (l.map fun i => MA.actA P a (g i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact jd_actA_zeroR P a
  | cons i l ih => rw [List.map_cons, List.sum_cons, jd_actA_addR, ih, List.map_cons, List.sum_cons]

variable {P}

theorem jd_word_span {Fn : Type} (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (Good : ℕ → Fn → Prop)
    (tr : Fn → M.Ty P → MA.SmQ P.r P.TT) (m : ℕ)
    (hBdd : ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L))
    (hStep : ∀ i, i < m → ∀ F, Good i F → ∀ X ∈ MA.hatSet P L,
      ∃ ts : List (MA.A P (MA.DQ P) × Fn), (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet P L) ∧ Good (i + 1) t.2) ∧
        MA.actA P X (tr F) = (ts.map fun t => MA.actA P t.1 (tr t.2)).sum) :
    ∀ w : List (MA.A P (MA.DQ P)), w.length ≤ m → (∀ a ∈ w, a ∈ MA.hatSet P L) → ∀ F, Good 0 F →
      MA.actA P w.prod (tr F) ∈ Submodule.span ℂ
        {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good w.length F' ∧ u = MA.actA P b (tr F')} := by
  intro w
  induction w with
  | nil =>
    intro _ _ F hF
    refine Submodule.subset_span ⟨1, Submonoid.one_mem _, F, hF, ?_⟩
    rw [List.prod_nil, actA_one]
  | cons a w ih =>
    intro hlen hw F hF
    have ha : a ∈ MA.hatSet P L := hw a (List.mem_cons_self ..)
    have hlt : w.length < m := by simp only [List.length_cons] at hlen; omega
    have hIH := ih hlt.le (fun x hx => hw x (List.mem_cons_of_mem _ hx)) F hF
    rw [List.prod_cons, actA_mul]
    have hgen : ∀ c ∈ Submodule.span ℂ (bddHat P L), ∀ F', Good w.length F' →
        MA.actA P c (tr F') ∈ Submodule.span ℂ
          {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good (a :: w).length F' ∧ u = MA.actA P b (tr F')} := by
      intro c hc F' hF'
      induction hc using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b', hb', X', hX', rfl⟩ := hx
        obtain ⟨ts, hts, he⟩ := hStep w.length hlt F' hF' X' hX'
        rw [actA_mul, he, jd_actA_listsum]
        refine list_sum_mem fun u hu => ?_
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
        rw [← actA_mul]
        exact Submodule.subset_span ⟨b' * t.1, Submonoid.mul_mem _ hb' (hts t ht).1, t.2, (hts t ht).2, rfl⟩
      | zero => rw [jd_actA_zero]; exact Submodule.zero_mem _
      | add x y _ _ h1 h2 => rw [jd_actA_add]; exact Submodule.add_mem _ h1 h2
      | smul c x _ h1 => rw [actA_smul]; exact Submodule.smul_mem _ c h1
    have key : ∀ x ∈ Submodule.span ℂ
        {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good w.length F' ∧ u = MA.actA P b (tr F')},
        MA.actA P a x ∈ Submodule.span ℂ
          {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good (a :: w).length F' ∧ u = MA.actA P b (tr F')} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, F', hF', rfl⟩ := hx
        rw [← actA_mul]
        exact hgen _ (hBdd a ha b hb) F' hF'
      | zero => rw [jd_actA_zeroR]; exact Submodule.zero_mem _
      | add x y _ _ h1 h2 => rw [jd_actA_addR]; exact Submodule.add_mem _ h1 h2
      | smul c x _ h1 => rw [jd_actA_smulR]; exact Submodule.smul_mem _ c h1
    exact key _ hIH

variable (P)

theorem jd_evQ_meas (g : MA.SmQ P.r P.TT) : AEStronglyMeasurable (MA.evQ P g) (MA.mu0 P.r P.TT) := by
  have hs : ContDiffOn ℝ MA.sm (MA.ext (g : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := g.2
  have h2 := hs.continuousOn.comp_continuous continuous_subtype_val (fun q => q.2)
  have hc : Continuous (MA.evQ P g) := h2.congr fun q => by
    simp only [Function.comp, MA.ext, dif_pos q.2]
    rfl
  exact hc.aestronglyMeasurable

def componentwiseL2 (u : M.Ty P → MA.SmQ P.r P.TT) : Prop := ∀ π, MemLp (MA.evQ P (u π)) 2 (MA.mu0 P.r P.TT)

theorem componentwiseL2_iff_integrable (u : M.Ty P → MA.SmQ P.r P.TT) :
    componentwiseL2 P u ↔ ∀ π, Integrable (fun q => ‖MA.evQ P (u π) q‖ ^ 2) (MA.mu0 P.r P.TT) :=
  forall_congr' fun π => memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π))

theorem componentwiseL2_of_span (G : Set (M.Ty P → MA.SmQ P.r P.TT)) (h : ∀ u ∈ G, componentwiseL2 P u) :
    ∀ u ∈ Submodule.span ℂ G, componentwiseL2 P u := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro π; exact MemLp.zero
  | add x y _ _ h1 h2 => intro π; exact (h1 π).add (h2 π)
  | smul c x _ h1 => intro π; exact (h1 π).const_smul c

end gen

theorem jd_arith (C2 C3 C5 R n N A₀ : ℝ) (hC2 : 0 ≤ C2) (hR : 0 ≤ R) (hn : 1 ≤ n) (hN : 0 ≤ N)
    (hA : (8 * C2 + |C3| + |C5|) * (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) ≤ A₀) :
    (∀ i o : ℝ, i + 1 ≤ 2 * N + 2 → o ≤ C2 * n →
      C3 * (R + 1) * n ^ 2 + 6 * R * o + C2 * (R + 1) * n ≤ A₀ - i * (C2 * (R + 1) * n)) ∧
      (∀ i : ℝ, i ≤ 2 * N + 2 → C5 * (R + 1) ^ 2 * n ≤ A₀ - i * (C2 * (R + 1) * n)) := by
  have hρ : 1 ≤ R + 1 := by linarith
  have hρ0 : 0 ≤ R + 1 := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hρ4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ hρ (by norm_num)
  have hR4 : R ≤ (R + 1) ^ 4 := by linarith
  have hρ24 : (R + 1) ^ 2 ≤ (R + 1) ^ 4 := pow_le_pow_right₀ hρ (by norm_num)
  have hn2 : n ≤ n ^ 2 := le_self_pow₀ hn (by norm_num)
  have hn3 : n ≤ n ^ 3 := le_self_pow₀ hn (by norm_num)
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by norm_num)
  have hNn : 0 ≤ N * n ^ 2 := by positivity
  set X : ℝ := (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) with hX
  have hX0 : 0 ≤ X := by positivity
  have hY : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ (R + 1) ^ 4 → b ≤ n ^ 3 → a * b ≤ X := by
    intro a b ha hb h1 h2
    calc a * b ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul h1 h2 hb (by positivity)
      _ ≤ X := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hXa : (R + 1) * n ^ 2 ≤ X := hY _ _ hρ0 (by positivity) hρ4 hn23
  have hXa' : (R + 1) ^ 2 * n ≤ X := hY _ _ (by positivity) hn0 hρ24 hn3
  have hXc : R * n ≤ X := hY _ _ hR hn0 hR4 hn3
  have hXb : (2 * N + 2) * ((R + 1) * n) ≤ 2 * X := by
    have h1' : N * n ≤ N * n ^ 2 := mul_le_mul_of_nonneg_left hn2 hN
    have h2' : (R + 1) * (N * n + n) ≤ (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) :=
      mul_le_mul hρ4 (by linarith) (by positivity) (by positivity)
    have e : (2 * N + 2) * ((R + 1) * n) = 2 * ((R + 1) * (N * n + n)) := by ring
    rw [e, hX]; linarith
  have hdm0 : 0 ≤ C2 * (R + 1) * n := by positivity
  have e2 : (2 * N + 2) * (C2 * (R + 1) * n) ≤ 2 * C2 * X := by
    have := mul_le_mul_of_nonneg_left hXb hC2
    have e : (2 * N + 2) * (C2 * (R + 1) * n) = C2 * ((2 * N + 2) * ((R + 1) * n)) := by ring
    rw [e]; linarith
  have e3 : C3 * (R + 1) * n ^ 2 ≤ |C3| * X :=
    calc C3 * (R + 1) * n ^ 2 = C3 * ((R + 1) * n ^ 2) := by ring
      _ ≤ |C3| * ((R + 1) * n ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self C3) (by positivity)
      _ ≤ |C3| * X := mul_le_mul_of_nonneg_left hXa (abs_nonneg C3)
  have e3' : C5 * (R + 1) ^ 2 * n ≤ |C5| * X :=
    calc C5 * (R + 1) ^ 2 * n = C5 * ((R + 1) ^ 2 * n) := by ring
      _ ≤ |C5| * ((R + 1) ^ 2 * n) := mul_le_mul_of_nonneg_right (le_abs_self C5) (by positivity)
      _ ≤ |C5| * X := mul_le_mul_of_nonneg_left hXa' (abs_nonneg C5)
  have e4 : 0 ≤ |C5| * X := mul_nonneg (abs_nonneg _) hX0
  have e4' : 0 ≤ |C3| * X := mul_nonneg (abs_nonneg _) hX0
  have hA2 : (8 * C2 + |C3| + |C5|) * X ≤ A₀ := by
    have e : (8 * C2 + |C3| + |C5|) * X = (8 * C2 + |C3| + |C5|) * (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
      rw [hX]; ring
    rw [e]; exact hA
  have hsplit : (8 * C2 + |C3| + |C5|) * X = 2 * C2 * X + 6 * C2 * X + |C3| * X + |C5| * X := by ring
  have e6 : 0 ≤ 6 * C2 * X := by positivity
  constructor
  · intro i o hi ho
    have e1 : (i + 1) * (C2 * (R + 1) * n) ≤ (2 * N + 2) * (C2 * (R + 1) * n) := mul_le_mul_of_nonneg_right hi hdm0
    have e5 : 6 * R * o ≤ 6 * C2 * X := by
      have h1 : R * o ≤ R * (C2 * n) := mul_le_mul_of_nonneg_left ho hR
      have h2 : R * (C2 * n) = C2 * (R * n) := by ring
      have h3 : C2 * (R * n) ≤ C2 * X := mul_le_mul_of_nonneg_left hXc hC2
      linarith
    have e : C3 * (R + 1) * n ^ 2 + 6 * R * o + C2 * (R + 1) * n + i * (C2 * (R + 1) * n) =
        C3 * (R + 1) * n ^ 2 + 6 * R * o + (i + 1) * (C2 * (R + 1) * n) := by ring
    linarith
  · intro i hi
    have e1 : i * (C2 * (R + 1) * n) ≤ (2 * N + 2) * (C2 * (R + 1) * n) := mul_le_mul_of_nonneg_right hi hdm0
    linarith

theorem jDecayTr_of_leaves (h1 : JDHatBdd) (h2 : JDHatOp) (h3 : JDJComm) (h4 : JDCCLower) (h5 : TransferSquareIntegrable)
    (h6 : BoundedOperatorsSquareIntegrable) : JDecayTr := by
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C3, H3⟩ := h3
  obtain ⟨C5, H5⟩ := h5
  unfold JDecayTr
  refine ⟨8 * C2 + |C3| + |C5|, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL hJf
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
    obtain ⟨ts, hts, hid⟩ := H2 E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e L hFr hGa hL X hX
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

end

end Formalism.FourierDecayAlt.P.CutMP
