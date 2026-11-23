import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk

def iN : P := ⟨-Complex.I, by simp⟩

def bs {I : Type} (e : I → Bool) : X I := fun v => if e v then iP else iN

theorem kap_pos (a z : P) (ha : a.1.im = 1 ∨ a.1.im = -1) (h : 0 < a.1.im * z.1.im) : 0 < kap a z := by
  unfold kap
  rw [if_pos h]
  apply div_pos (by linarith)
  apply pow_pos
  apply norm_pos_iff.2
  intro h0
  have h1 := congrArg Complex.im h0
  simp at h1
  rcases ha with ha | ha <;> rw [ha] at h h1 <;> nlinarith

theorem kap_bs_pos {I : Type} (z : X I) (v : I) :
    0 < kap (bs (fun i => decide (0 < (z v).1.im)) v) (z v) := by
  have hz := (z v).2
  unfold bs
  by_cases h : 0 < (z v).1.im
  · simp only [h, decide_true, if_true]
    exact kap_pos _ _ (Or.inl (by simp [iP])) (by simpa [iP] using h)
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    have h' : (z v).1.im < 0 := lt_of_le_of_ne (not_lt.1 h) hz
    exact kap_pos _ _ (Or.inr (by simp [iN])) (by simp [iN]; linarith)

theorem Kap_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hk0 _ _) _

open Classical in

def uX {I : Type} [Fintype I] (z : X I) : ℝ := ∑ e : I → Bool, Kap (fun _ => 4) (bs e) z

theorem uX_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 ≤ uX z :=
  Finset.sum_nonneg fun e _ => Kap_nonneg hk0 _ _ _

theorem uX_pos {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 < uX z := by
  classical
  unfold uX
  refine Finset.sum_pos' (fun e _ => Kap_nonneg hk0 _ _ _) ⟨fun v => decide (0 < (z v).1.im), Finset.mem_univ _, ?_⟩
  exact Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (kap_bs_pos z v) _

theorem uX_cont {I : Type} [Fintype I] (hkc : Continuous fun p : P × P => kap p.1 p.2) :
    Continuous (uX : X I → ℝ) := by
  unfold uX Kap
  refine continuous_finsetSum _ fun _ _ => continuous_finsetProd _ fun v _ => ?_
  exact (hkc.comp (continuous_const.prodMk (continuous_apply v))).rpow_const fun _ => Or.inr (by positivity)

theorem tsum_le_fiber {G Ω : Type} (φ : G → Ω) (w : Ω → ℝ≥0∞) (K : G → ℝ≥0∞) (M : ℝ≥0∞)
    (hK : ∀ ω', ∑' g : {g // φ g = ω'}, K g.1 ≤ M) : ∑' g, w (φ g) * K g ≤ (∑' ω', w ω') * M := by
  rw [← ENNReal.tsum_fiberwise _ φ, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun ω' => ?_
  calc ∑' b : φ ⁻¹' {ω'}, w (φ b) * K b = ∑' b : φ ⁻¹' {ω'}, w ω' * K b :=
        tsum_congr fun b => by rw [show φ b = ω' from b.2]
    _ = w ω' * ∑' b : φ ⁻¹' {ω'}, K b := ENNReal.tsum_mul_left
    _ ≤ w ω' * M := by gcongr; exact hK ω'

end UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_Ecut : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.Ecut := by
  intro _ hB hC hE _ hK F I Gf _ _ _ D hax
  obtain ⟨hcount, -, hpres, -⟩ := hE F I Gf D hax
  have : Countable (PG F) := hcount
  have : Countable D.Om := hax.cO
  obtain ⟨hk0', -, -, -, hkc, -⟩ := hB
  have hk0 : ∀ z w : P, 0 ≤ kap z w := fun z w => (hk0' z w).1
  obtain ⟨c₀, hc₀, hmk⟩ := hax.mink
  obtain ⟨C, hCK⟩ := hK F I Gf D hax (fun _ => 4) (fun _ => le_rfl) c₀ hc₀
  have hmX : ∀ g : PG F, Measurable fun z : D.Xs => g • z := fun g => (hpres g).measurable
  have hfib : ∀ y : D.Y, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ (e : I → Bool) (ω' : D.Om),
      ∑' γ : {γ : PG F // γ • y.1 = ω'}, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • y.2 : D.Xs)) ≤ M := by
    intro y
    obtain ⟨s, hs, hsy⟩ := hmk y.2 (D.rep y.1)
    exact ⟨_, ENNReal.ofReal_ne_top, fun e ω' => hCK y s hs hsy ω' (TruncationKernelLemmas.bs e)⟩
  have hucont : Continuous (TruncationKernelLemmas.uX : X I → ℝ) := TruncationKernelLemmas.uX_cont hkc
  have hsplit : ∀ z : X I, ENNReal.ofReal (TruncationKernelLemmas.uX z) =
      ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) z) := by
    intro z
    rw [TruncationKernelLemmas.uX, ENNReal.ofReal_sum_of_nonneg (fun e _ => TruncationKernelLemmas.Kap_nonneg hk0 _ _ _)]
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat D.Om
  set w : D.Om → ℝ := fun ω => (1 / 2 : ℝ) ^ f ω with hw
  have hW : ∑' ω, ENNReal.ofReal (w ω) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, (1 / 2 : ℝ) ^ n))
      ((ENNReal.tsum_comp_le_tsum_of_injective hf (fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ n))).trans (le_of_eq ?_))
    exact (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two).symm
  refine ⟨?_, ?_⟩
  · refine (hC (PG F) D.Y).1 ?_ (fun y => w y.1 * TruncationKernelLemmas.uX y.2) ?_ ?_ ?_ ?_
    · intro g
      exact (Measurable.of_discrete.comp measurable_fst).prodMk ((hmX g).comp measurable_snd)
    · have h1 : Measurable fun y : D.Y => w y.1 := (Measurable.of_discrete (f := w)).comp measurable_fst
      have h2 : Measurable fun y : D.Y => TruncationKernelLemmas.uX (y.2 : X I) := hucont.measurable.comp measurable_snd
      exact h1.mul h2
    · exact fun y => mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _)
    · exact fun y => ⟨1, by simpa using mul_pos (by positivity : (0 : ℝ) < w y.1) (TruncationKernelLemmas.uX_pos hk0 y.2)⟩
    · intro y
      obtain ⟨M, hM, hMb⟩ := hfib y
      have hle : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≤
          ∑ e : I → Bool, (∑' ω, ENNReal.ofReal (w ω)) * M := by
        calc ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2)
            = ∑' g : PG F, ∑ e : I → Bool, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) := by
              refine tsum_congr fun g => ?_
              exact (ENNReal.ofReal_mul (by positivity)).trans
                ((congrArg (fun t => ENNReal.ofReal (w (g • y.1)) * t) (hsplit _)).trans (by rw [Finset.mul_sum]; rfl))
          _ = ∑ e : I → Bool, ∑' g : PG F, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ => TruncationKernelLemmas.tsum_le_fiber (fun g : PG F => g • y.1)
                (fun ω => ENNReal.ofReal (w ω))
                (fun g : PG F => ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs))) M (hMb e)
      have hfin : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => ENNReal.mul_lt_top hW.lt_top hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _))
  · intro ω S hS
    refine (hC S D.Xs).1 ?_ TruncationKernelLemmas.uX ?_ ?_ ?_ ?_
    · intro g
      exact hmX (g : PG F)
    · exact hucont.measurable
    · exact TruncationKernelLemmas.uX_nonneg hk0
    · exact fun z => ⟨1, by simpa using TruncationKernelLemmas.uX_pos hk0 z⟩
    · intro z
      obtain ⟨M, hM, hMb⟩ := hfib ((ω, z) : D.Y)
      have hinj : Function.Injective (fun g : S => (⟨(g : PG F), hS g.2⟩ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω})) :=
by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun x : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} => x.1) h
      have hle : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≤ ∑ e : I → Bool, M := by
        calc ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs))
            = ∑' g : S, ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              tsum_congr fun g => hsplit _
          _ = ∑ e : I → Bool, ∑' g : S, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ =>
              (ENNReal.tsum_comp_le_tsum_of_injective hinj
                (fun γ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} =>
                  ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • ((ω, z) : D.Y).2 : D.Xs)))).trans (hMb e ω)
      have hfin : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (TruncationKernelLemmas.uX_nonneg hk0 _)
