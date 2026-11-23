import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedOfMemBoundedFactorsMonoidStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersMemNormalFormProductSpanStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ListProdHatLettersMemNormalFormProductSpanStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialMultipliersSatisfyNormalFormRelationsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedRadialOpsClosureAndFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorColumnMemNormalFormProductSpanStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersProdMulMultiplierLeibnizStatement

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.RadBound

section abstract

variable {ι α : Type}

def Bd (p : ι → Prop) (ok : α → Prop) (val : α → ι → ℝ) (wt f : ι → ℝ) : Prop :=
  ∃ (C : ℝ) (Ts : List α), 0 ≤ C ∧ (∀ H ∈ Ts, ok H) ∧
    ∀ i, p i → f i ≤ C * wt i * (Ts.map fun H => val H i).sum

variable {p : ι → Prop} {ok : α → Prop} {val : α → ι → ℝ}

theorem sum_val_nonneg (hv : ∀ H i, 0 ≤ val H i) (Ts : List α) (i : ι) :
    0 ≤ (Ts.map fun H => val H i).sum :=
  List.sum_nonneg (by
    intro y hy
    obtain ⟨H, -, rfl⟩ := List.mem_map.1 hy
    exact hv H i)

theorem Bd.zero {wt : ι → ℝ} : Bd p ok val wt (fun _ => 0) :=
  ⟨0, [], le_rfl, by simp, by simp⟩

theorem Bd.add (hv : ∀ H i, 0 ≤ val H i) {wt f g : ι → ℝ} (hw : ∀ i, p i → 0 ≤ wt i)
    (hf : Bd p ok val wt f) (hg : Bd p ok val wt g) : Bd p ok val wt (fun i => f i + g i) := by
  obtain ⟨C, Ts, hC, hT, h⟩ := hf
  obtain ⟨C', Ts', hC', hT', h'⟩ := hg
  refine ⟨C + C', Ts ++ Ts', add_nonneg hC hC', ?_, fun i hi => ?_⟩
  · intro H hH
    rcases List.mem_append.1 hH with h1 | h1
    · exact hT H h1
    · exact hT' H h1
  · rw [List.map_append, List.sum_append]
    have h1 := h i hi
    have h2 := h' i hi
    have s1 := sum_val_nonneg hv Ts i
    have s2 := sum_val_nonneg hv Ts' i
    have w := hw i hi
    have e1 := mul_nonneg (mul_nonneg hC w) s2
    have e2 := mul_nonneg (mul_nonneg hC' w) s1
    nlinarith

theorem Bd.mono {wt wt' f g u : ι → ℝ} {K : ℝ} (hK : 0 ≤ K) (hu : ∀ i, p i → 0 ≤ u i)
    (hg : Bd p ok val wt g) (hfg : ∀ i, p i → f i ≤ K * u i * g i) (hw : ∀ i, p i → wt' i = u i * wt i) :
    Bd p ok val wt' f := by
  obtain ⟨C, Ts, hC, hT, h⟩ := hg
  refine ⟨K * C, Ts, mul_nonneg hK hC, hT, fun i hi => (hfg i hi).trans ?_⟩
  have := mul_le_mul_of_nonneg_left (h i hi) (mul_nonneg hK (hu i hi))
  rw [hw i hi]
  refine this.trans (le_of_eq ?_)
  ring

theorem Bd.listSum {β : Type} (hv : ∀ H i, 0 ≤ val H i) {wt : ι → ℝ} (hw : ∀ i, p i → 0 ≤ wt i)
    (g : β → ι → ℝ) (l : List β) (h : ∀ t ∈ l, Bd p ok val wt (g t)) :
    Bd p ok val wt (fun i => (l.map fun t => g t i).sum) := by
  induction l with
  | nil => simpa using Bd.zero
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Bd.add hv hw (h t (by simp)) (ih fun t' ht' => h t' (by simp [ht']))

end abstract

section actual

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem nv_nonneg (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    0 ≤ nv Φ x := norm_nonneg _

theorem nv_add (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (Φ + Ψ) x ≤ nv Φ x + nv Ψ x := by
  have h : ∀ A A' : Wq →L[ℂ] Wp, B.hsVec (A + A') = B.hsVec A + B.hsVec A' := fun _ _ => rfl
  unfold nv
  rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, h]
  exact norm_add_le _ _

theorem nv_smul (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (c • Φ) x = ‖c‖ * nv Φ x := by
  have h : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := fun _ _ => rfl
  unfold nv
  rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, h, norm_smul]

theorem nv_zero (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') x = 0 := by
  have := nv_smul (0 : ℂ) (0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') x
  simpa using this

theorem nv_mulOp {W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hW : P5.multiplicationOperator W m)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv (W Φ) x = ‖m x.1 x.2‖ * nv Φ x := by
  have h : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := fun _ _ => rfl
  unfold nv
  rw [hW, h, norm_smul]

theorem fst_mul (a b : RA P Bs) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (a * b).1 Φ = a.1 (b.1 Φ) := rfl

theorem fst_add (a b : RA P Bs) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (a + b).1 Φ = a.1 Φ + b.1 Φ := rfl

theorem fst_zero (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : (0 : RA P Bs).1 Φ = 0 := rfl

theorem fst_one (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : (1 : RA P Bs).1 Φ = Φ := rfl

theorem fst_smul (c : ℂ) (a : RA P Bs) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (c • a).1 Φ = c • a.1 Φ := rfl

theorem nv_pow {y : RA P Bs} {x : (Fin P.r → ℂ) × Q.Mx P.k P.r} {t : ℝ}
    (h : ∀ Φ, nv (y.1 Φ) x = t * nv Φ x) (n : ℕ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    nv ((y ^ n).1 Φ) x = t ^ n * nv Φ x := by
  induction n with
  | zero => rw [pow_zero, pow_zero, fst_one, one_mul]
  | succ n ih => rw [pow_succ', fst_mul, h, ih, pow_succ']; ring

theorem nv_listSum {β : Type} (g : β → RA P Bs) (l : List β) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) :
    nv ((l.map g).sum.1 Φ) x ≤ (l.map fun t => nv ((g t).1 Φ) x).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, fst_zero, nv_zero, le_refl]
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, fst_add]
    exact (nv_add _ _ _).trans (by linarith)

theorem span_bd {X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'} {μ : Measure (Mt P.k P.r)}
    {L : LevelData (RA P Bs) P.r} {st : Start (RA P Bs)} {l0 : ℕ} {d : Q.NFData P (RA P Bs)}
    (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) (hN : IsNF X d) (T : Set (RA P Bs)) (i j n : ℕ)
    (y : RA P Bs) (hy : y ∈ nfSpan d T i j n) :
    Bd (fun q : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' × ((Fin P.r → ℂ) × Q.Mx P.k P.r) =>
        q.2 ∈ Q.DomR P.k P.r Bs.z Bs.z')
      (fun H : List (RA P Bs) => H.length = n ∧ ∀ h ∈ H, h ∈ T) (fun H q => nv (H.prod.1 q.1) q.2)
      (fun q => (dR P Bs q.2.1 q.2.2)⁻¹ ^ i * (gR P Bs q.2.1 q.2.2)⁻¹ ^ j) (fun q => nv (y.1 q.1) q.2) := by
  have hb := (GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions Wp Wq P Bs X μ L st l0 d hD hN).2.2.2.2.2.2.2
  have hw : ∀ q : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' × ((Fin P.r → ℂ) × Q.Mx P.k P.r),
      q.2 ∈ Q.DomR P.k P.r Bs.z Bs.z' →
      0 ≤ (dR P Bs q.2.1 q.2.2)⁻¹ ^ i * (gR P Bs q.2.1 q.2.2)⁻¹ ^ j := by
    intro q hq
    have h1 := (hb q.1 q.2 hq).1
    have h2 := (hb q.1 q.2 hq).2.1
    positivity
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hbm, H, hl, hH, rfl⟩ := hy
    obtain ⟨C, hC, hCb⟩ := GlobalTheory.T.pointwiseBounded_of_mem_boundedFactors_monoid Wp Wq P Bs X μ L st l0 d hD hN b hbm
    refine ⟨C, [H], hC, by simpa using ⟨hl, hH⟩, fun q hq => ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, fst_mul]
    refine (hCb _ _ hq).trans (le_of_eq ?_)
    rw [nv_pow (fun Φ => (hb Φ q.2 hq).2.2.1), nv_pow (fun Φ => (hb Φ q.2 hq).2.2.2)]
    ring
  | zero => simpa only [fst_zero, nv_zero] using Bd.zero
  | add y z _ _ hy hz =>
    refine Bd.mono (K := 1) (u := fun _ => 1) zero_le_one (fun _ _ => zero_le_one)
      (Bd.add (fun _ _ => nv_nonneg _ _) hw hy hz) (fun q _ => ?_) (fun _ _ => (one_mul _).symm)
    rw [fst_add, one_mul, one_mul]
    exact nv_add _ _ _
  | smul c y _ hy =>
    refine Bd.mono (K := ‖c‖) (u := fun _ => 1) (norm_nonneg _) (fun _ _ => zero_le_one)
      hy (fun q _ => ?_) (fun _ _ => (one_mul _).symm)
    rw [fst_smul, nv_smul, mul_one]

end actual

theorem word_bound : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (T : Set (RA P Bs)) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ w : List (Letter ℂ S), admitted st w → ∃ (C : ℝ) (J : ℕ) (Ts : List (List (RA P Bs))), 0 ≤ C ∧ (∀ H ∈ Ts, H.length = w.length ∧ ∀ h ∈ H, h ∈ T) ∧ ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : Ix S), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (W 0 Φ)) x ≤ C * ((dR P Bs x.1 x.2)⁻¹ ^ w.length * (gR P Bs x.1 x.2)⁻¹ ^ (a * w.length)) * (∑ j ∈ Finset.range (J + 1), |LE.ld j φ (gR P Bs x.1 x.2)|) * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN S _ _ T a hT w hw
  obtain ⟨hH, hTie⟩ := GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN
  have hb := (GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions Wp Wq P Bs X μ L st l0 d hD hN).2.2.2.2.2.2.2
  have hhat := GlobalTheory.T.hatLetters_mem_normalFormProductSpan P _ d hH T a hT
  set N := w.length with hNdef
  let ι : Type := (ℝ → ℝ) × (ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ×
    Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' × ((Fin P.r → ℂ) × Q.Mx P.k P.r)
  let p : ι → Prop := fun q => LE.SmoothLog q.1 ∧ IsMulG P Bs q.1 q.2.1 ∧ q.2.2.2 ∈ Q.DomR P.k P.r Bs.z Bs.z'
  let ok : List (RA P Bs) → Prop := fun H => H.length = N ∧ ∀ h ∈ H, h ∈ T
  let val : List (RA P Bs) → ι → ℝ := fun H q => nv (H.prod.1 q.2.2.1) q.2.2.2
  let G : ι → ℝ := fun q => (gR P Bs q.2.2.2.1 q.2.2.2.2)⁻¹ ^ (a * N)
  let Dd : ι → ℝ := fun q => (dR P Bs q.2.2.2.1 q.2.2.2.2)⁻¹ ^ N
  let Sg : ι → ℝ := fun q => ∑ j ∈ Finset.range (N * (P.r + 1) + 1), |LE.ld j q.1 (gR P Bs q.2.2.2.1 q.2.2.2.2)|
  have hv : ∀ H q, 0 ≤ val H q := fun _ _ => nv_nonneg _ _
  have hG : ∀ q, p q → 0 ≤ G q := fun q hq => by
    have h2 := (hb q.2.2.1 q.2.2.2 hq.2.2).2.1
    positivity
  have hDd : ∀ q, p q → 0 ≤ Dd q := fun q hq => by
    have h2 := (hb q.2.2.1 q.2.2.2 hq.2.2).1
    positivity
  have hS : ∀ q, p q → 0 ≤ Sg q := fun q _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : ∀ H : List (RA P Bs), H.length = N → (∀ h ∈ H, h ∈ hats d.L) →
      Bd p ok val G (fun q => nv (H.prod.1 q.2.2.1) q.2.2.2) := by
    intro H hl hh
    have hm := GlobalTheory.T.list_prod_hatLetters_mem_normalFormProductSpan P _ d hH T a hhat H hh
    rw [hl] at hm
    obtain ⟨C, Ts, hC, hTs, h⟩ := span_bd hD hN T 0 (a * N) N _ hm
    refine ⟨C, Ts, hC, hTs, fun q hq => ?_⟩
    have := h q.2.2 hq.2.2
    simpa only [pow_zero, one_mul] using this
  have h2 : ∀ H : List (RA P Bs), H.length = N → (∀ h ∈ H, h ∈ hats d.L) →
      Bd p ok val (fun q => Sg q * G q) (fun q => nv (H.prod.1 (q.2.1 0 q.2.2.1)) q.2.2.2) := by
    intro H hl hh
    obtain ⟨ts, hts, hmul⟩ := GlobalTheory.T.hatLetters_prod_mul_multiplier_leibniz _ P.r d.L H hh
    have h3 : ∀ t ∈ ts, Bd p ok val (fun q => Sg q * G q)
        (fun q => nv ((t.2.1 • (Q.mkP (q.2.1 (0 + t.1)) (q.2.1 (0 + t.1)) * t.2.2.prod : RA P Bs)).1 q.2.2.1)
          q.2.2.2) := by
      intro t ht
      obtain ⟨hj, hl', hh'⟩ := hts t ht
      refine Bd.mono (K := ‖t.2.1‖) (u := Sg) (norm_nonneg _) hS (h1 t.2.2 (hl'.trans hl) hh')
        (fun q hq => ?_) (fun _ _ => rfl)
      rw [fst_smul, nv_smul, fst_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      change nv (q.2.1 (0 + t.1) _) _ ≤ _
      rw [nv_mulOp (hq.2.1 _), Complex.norm_real, Real.norm_eq_abs, zero_add]
      refine mul_le_mul_of_nonneg_right ?_ (nv_nonneg _ _)
      refine Finset.single_le_sum (f := fun j => |LE.ld j q.1 (gR P Bs q.2.2.2.1 q.2.2.2.2)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 ?_)
      rw [hl] at hj
      omega
    refine Bd.mono (K := 1) (u := fun _ => 1) zero_le_one (fun _ _ => zero_le_one)
      (Bd.listSum hv (fun q hq => mul_nonneg (hS q hq) (hG q hq)) _ ts h3) (fun q hq => ?_)
      (fun _ _ => (one_mul _).symm)
    have hr := hmul _ (GlobalTheory.T.radialMultipliers_satisfy_normalForm_relations Wp Wq P Bs X μ L st l0 d hD hN q.1 q.2.1 hq.1 hq.2.1) 0
    rw [one_mul, one_mul]
    have e : H.prod.1 (q.2.1 0 q.2.2.1) = (H.prod * (Q.mkP (q.2.1 0) (q.2.1 0) : RA P Bs)).1 q.2.2.1 := rfl
    rw [e, hr]
    exact nv_listSum _ _ _ _
  have h4 : ∀ e : Ix S, Bd p ok val (fun q => Dd q * (Sg q * G q))
      (fun q => nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (q.2.1 0 q.2.2.1)) q.2.2.2) := by
    intro e
    obtain ⟨C, Hs, hC, hHs, h⟩ := span_bd hD hN _ _ _ _ _ (GlobalTheory.T.wordOperator_column_mem_normalFormProductSpan P _ d hH L st _ hTie S w hw e)
    refine Bd.mono (K := C) (u := Dd) hC hDd
      (Bd.listSum hv (fun q hq => mul_nonneg (hS q hq) (hG q hq)) _ Hs
        (fun H hH' => h2 H (hHs H hH').1 (hHs H hH').2)) (fun q hq => ?_) (fun _ _ => rfl)
    have := h (q.2.1 0 q.2.2.1, q.2.2.2) hq.2.2
    simpa only [pow_zero, mul_one] using this
  obtain ⟨C, Ts, hC, hTs, h⟩ := Bd.listSum hv (fun q hq => mul_nonneg (hDd q hq) (mul_nonneg (hS q hq) (hG q hq)))
    _ (Finset.univ : Finset (Ix S)).toList (fun e _ => h4 e)
  refine ⟨C, N * (P.r + 1), Ts, hC, hTs, fun φ W hφ hW Φ e x hx => ?_⟩
  have h5 := h (φ, W, Φ, x) ⟨hφ, hW, hx⟩
  beta_reduce at h5
  rw [Finset.sum_map_toList] at h5
  refine (Finset.single_le_sum (f := fun e : Ix S => nv ((((ofWord L st w).F * TL.bTA L w) e e1).1 (W 0 Φ)) x)
    (fun _ _ => nv_nonneg _ _) (Finset.mem_univ e)).trans (h5.trans (le_of_eq ?_))
  simp only [Dd, Sg, G, val]
  ring

end GlobalTheory.HatNF.RadBound
