import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintSph
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIndicatorFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOrdLConjGramDetOfUnitGramAdicCompletion

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8 UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

section Block

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def sc (n : ℕ) (w : Pl E) (s : (w.adicCompletion E)ˣ) : GLw n w :=
  Units.map (Matrix.scalar (Fin n) : w.adicCompletion E →+* Matrix (Fin n) (Fin n) (w.adicCompletion E)).toMonoidHom s

private theorem sc_val (n : ℕ) (w : Pl E) (s : (w.adicCompletion E)ˣ) :
    (sc n w s).val = (s : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  ext i j
  simp [sc, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

private theorem sc_inv_val (n : ℕ) (w : Pl E) (s : (w.adicCompletion E)ˣ) :
    ((sc n w s)⁻¹).val = ((s⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  have : (sc n w s)⁻¹ = sc n w s⁻¹ := by simp [sc]
  rw [this, sc_val]

private theorem Tj_lr {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ) (c d y : GL (Fin n) L)
    (hc : c ∈ GLint (Fin n) O) (hd : d ∈ GLint (Fin n) O) :
    Tj ℂ n O ϖ j (c * y * d) = Tj ℂ n O ϖ j y := by
  unfold Tj
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  refine if_congr ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨c⁻¹ * a, mul_mem (inv_mem hc) ha, b * d⁻¹, mul_mem hb (inv_mem hd), ?_⟩,
    fun ⟨a, ha, b, hb, e⟩ => ⟨c * a, mul_mem hc ha, b * d, mul_mem hb hd, ?_⟩⟩ rfl rfl
  · have h : y.val = (c⁻¹).val * (c * y * d).val * (d⁻¹).val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [h, e]
    simp only [Units.val_mul, Matrix.mul_assoc]
  · simp only [Units.val_mul, e, Matrix.mul_assoc]

private theorem Tj_top (n : ℕ) (w : Pl E) (ϖ : w.adicCompletion E) (s : (w.adicCompletion E)ˣ) (hs : (s : w.adicCompletion E) = ϖ)
    (y : GLw n w) : Tj ℂ n (Ov E w) ϖ n y = if ∃ k ∈ KGL w n, y = sc n w s * k then 1 else 0 := by
  have hD : Formalism.UG.diagJ n ϖ n = (sc n w s).val := by
    rw [sc_val, hs, Formalism.UG.diagJ]
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hcomm : ∀ g : GLw n w, (sc n w s).val * g.val = g.val * (sc n w s).val := fun g => by
    rw [sc_val, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  unfold Tj
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  refine if_congr ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a * b, mul_mem ha hb, Units.ext ?_⟩,
    fun ⟨k, hk, e⟩ => ⟨1, one_mem _, k, hk, ?_⟩⟩ rfl rfl
  · rw [e, hD, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, hcomm a]
  · rw [e, hD, Units.val_mul, Units.val_one, Matrix.one_mul]

private theorem isInt_iff_v (w : Pl E) {r s : Type} (M : Matrix r s (w.adicCompletion E)) :
    GlobalTheory.CompanionTheory.CtS.IsInt w M ↔ ∀ i j, Valued.v (M i j) ≤ 1 :=
  forall_congr' fun _ => forall_congr' fun _ => HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w

private theorem det_ne (n : ℕ) (w : Pl E) (g : GLw n w) : g.val.det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact Units.ne_zero _

private theorem Tj_twist (w : Pl E) (n j : ℕ) (hj : j ≤ n) (ϖ : w.adicCompletion E) (hu : IsUnifV E w ϖ)
    (s : (w.adicCompletion E)ˣ) (hs : (s : w.adicCompletion E) = ϖ) (y : GLw n w) :
    Tj ℂ n (Ov E w) ϖ j (thetaGL n (cj w) ((sc n w s)⁻¹ * y)) = Tj ℂ n (Ov E w) ϖ (n - j) y := by
  rw [GlobalTheory.CompanionTheory.CtS.Tj_eq_ite E w n j ϖ hu hj, GlobalTheory.CompanionTheory.CtS.Tj_eq_ite E w n (n - j) ϖ hu (Nat.sub_le _ _)]
  set x : GLw n w := (sc n w s)⁻¹ * y with hx
  have hxv : ∀ i k, x.val i k = ((s⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * y.val i k := by
    intro i k
    rw [hx, Units.val_mul, sc_inv_val, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hxi : ∀ i k, (x⁻¹).val i k = (s : w.adicCompletion E) * (y⁻¹).val i k := by
    have h : x⁻¹ = y⁻¹ * sc n w s := by rw [hx, _root_.mul_inv_rev, inv_inv]
    intro i k
    rw [h, Units.val_mul, sc_val, Matrix.mul_smul, Matrix.mul_one]
    rfl
  have hvs : Valued.v (s : w.adicCompletion E) * Valued.v ((s⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [← map_mul]
    simp
  have h1 : GlobalTheory.CompanionTheory.CtS.IsInt w (thetaGL n (cj w) x).val ↔ GlobalTheory.CompanionTheory.CtS.IsInt w (ϖ • (y⁻¹).val) := by
    have hv : ∀ i k, Valued.v ((thetaGL n (cj w) x).val i k) = Valued.v ((ϖ • (y⁻¹).val) k.rev i.rev) := by
      intro i k
      rw [GlobalTheory.CompanionTheory.IwFacts.v_thetaGL_apply, hxi, Matrix.smul_apply, smul_eq_mul, hs]
    rw [isInt_iff_v, isInt_iff_v]
    constructor
    · intro h i k
      have := h k.rev i.rev
      rw [hv, Fin.rev_rev, Fin.rev_rev] at this
      exact this
    · intro h i k
      rw [hv]
      exact h _ _
  have h2 : GlobalTheory.CompanionTheory.CtS.IsInt w (ϖ • ((thetaGL n (cj w) x)⁻¹).val) ↔ GlobalTheory.CompanionTheory.CtS.IsInt w y.val := by
    have hv : ∀ i k, Valued.v ((ϖ • ((thetaGL n (cj w) x)⁻¹).val) i k) = Valued.v (y.val k.rev i.rev) := by
      intro i k
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, ← map_inv, GlobalTheory.CompanionTheory.IwFacts.v_thetaGL_apply, inv_inv, hxv, map_mul,
        ← mul_assoc, ← hs, hvs, one_mul]
    rw [isInt_iff_v, isInt_iff_v]
    constructor
    · intro h i k
      have := h k.rev i.rev
      rw [hv, Fin.rev_rev, Fin.rev_rev] at this
      exact this
    · intro h i k
      rw [hv]
      exact h _ _
  have hdx : x.val.det = ((s⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ n * y.val.det := by
    rw [hx, Units.val_mul, Matrix.det_mul, sc_inv_val, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hdt : Valued.v (thetaGL n (cj w) x).val.det = (Valued.v x.val.det)⁻¹ := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_thetaGL, Units.val_inv_eq_inv_val, map_inv₀, Units.coe_map]
    change (Valued.v (cj w _))⁻¹ = _
    rw [GlobalTheory.PrincCong.v_cj, Matrix.GeneralLinearGroup.val_det_apply]
  have h3 : ordL (thetaGL n (cj w) x).val.det + ordL y.val.det = n := by
    rw [← GlobalTheory.GramParity.ordL_mul (det_ne n w _) (det_ne n w _)]
    have hϖ : ϖ ≠ 0 := hs ▸ s.ne_zero
    have hv : Valued.v ((thetaGL n (cj w) x).val.det * y.val.det) =
        ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      have hy : Valued.v y.val.det ≠ 0 := (Valuation.ne_zero_iff _).2 (det_ne n w y)
      have hs0 : Valued.v ((s⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
      have hi : (Valued.v ((s⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E))⁻¹ = Valued.v ϖ := by
        rw [← hs]
        exact inv_eq_of_mul_eq_one_left hvs
      rw [map_mul, hdt, hdx, map_mul, map_pow, mul_inv, mul_assoc, inv_mul_cancel₀ hy, mul_one, ← inv_pow, hi]
      have := hu
      unfold IsUnifV at this
      rw [this, ← WithZero.coe_pow, ← ofAdd_nsmul]
      simp
    have hne := mul_ne_zero (det_ne n w (thetaGL n (cj w) x)) (det_ne n w y)
    exact GlobalTheory.GramParity.ordL_eq_of hne hv
  refine if_congr ?_ rfl rfl
  rw [h1, h2]
  have hc : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  rw [hc]
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨b, a, by omega⟩
  · rintro ⟨a, b, c⟩
    exact ⟨b, a, by omega⟩

end Block

theorem genTw : GenTw := by
  intro E _ _ _ hU a b w hs p
  have hu : IsUnifV E w (unif w) := Classical.epsilon_spec (GlobalTheory.LFun.exists_isUnifV w)
  have h0 : unif w ≠ 0 := fun h => by simp [IsUnifV, h] at hu
  set s : (w.adicCompletion E)ˣ := Units.mk0 (unif w) h0 with hsdef
  have hsv : (s : w.adicCompletion E) = unif w := rfl
  have hgen : ∀ (q : Fin (a + 1) × Fin (b + 1)) (y : GLw a w × GLw b w), gen2 a b w q y =
      Tj ℂ a (Ov E w) (unif w) q.1 y.1 * Tj ℂ b (Ov E w) (unif w) q.2 y.2 := fun _ _ => rfl
  have hth : ∀ n, thL n w = thetaGL n (cj w) := fun n => by rw [thL, if_neg hs]
  have hKa : ∀ n {k : GLw n w}, k ∈ KGL w n → thetaGL n (cj w) k ∈ KGL w n := fun n _ hk =>
    GlobalTheory.CompanionTheory.IwFacts.thetaGL_mem_KGL w n hk
  set z : GLw a w × GLw b w := (sc a w s, sc b w s) with hz
  set f := gen2 a b w (Fin.last a, Fin.last b) with hf
  set g := gen2 a b w p ∘ th2 a b w with hg
  have hl : ∀ (q : Fin (a + 1) × Fin (b + 1)) (k x : GLw a w × GLw b w), k ∈ K2 a b w → gen2 a b w q (k * x) = gen2 a b w q x := by
    intro q k x hk
    have e1 := Tj_lr a (Ov E w) (unif w) q.1 k.1 1 x.1 hk.1 (one_mem _)
    have e2 := Tj_lr b (Ov E w) (unif w) q.2 k.2 1 x.2 hk.2 (one_mem _)
    rw [mul_one] at e1 e2
    rw [hgen, hgen, Prod.fst_mul, Prod.snd_mul, e1, e2]
  have hr : ∀ (q : Fin (a + 1) × Fin (b + 1)) (k x : GLw a w × GLw b w), k ∈ K2 a b w → gen2 a b w q (x * k) = gen2 a b w q x := by
    intro q k x hk
    have e1 := Tj_lr a (Ov E w) (unif w) q.1 1 k.1 x.1 (one_mem _) hk.1
    have e2 := Tj_lr b (Ov E w) (unif w) q.2 1 k.2 x.2 (one_mem _) hk.2
    rw [one_mul] at e1 e2
    rw [hgen, hgen, Prod.fst_mul, Prod.snd_mul, e1, e2]
  have hthK : ∀ k ∈ K2 a b w, th2 a b w k ∈ K2 a b w := by
    intro k hk
    refine ⟨?_, ?_⟩
    · change thL a w k.1 ∈ _
      rw [hth]
      exact hKa a hk.1
    · change thL b w k.2 ∈ _
      rw [hth]
      exact hKa b hk.2
  have hgl : ∀ k ∈ K2 a b w, ∀ x, g (k * x) = g x := by
    intro k hk x
    simp only [hg, Function.comp_apply, map_mul]
    exact hl p _ _ (hthK k hk)
  have hfz : ∀ x, f x = if ∃ k ∈ K2 a b w, x = z * k then 1 else 0 := by
    intro x
    rw [hf, hgen, Fin.val_last, Fin.val_last, Tj_top a w _ s hsv, Tj_top b w _ s hsv]
    by_cases h : ∃ k ∈ K2 a b w, x = z * k
    · obtain ⟨k, hk, rfl⟩ := h
      rw [if_pos ⟨k.1, hk.1, rfl⟩, if_pos ⟨k.2, hk.2, rfl⟩, if_pos ⟨k, hk, rfl⟩, one_mul]
    · rw [if_neg h]
      by_cases h1 : ∃ k ∈ KGL w a, x.1 = sc a w s * k
      · by_cases h2 : ∃ k ∈ KGL w b, x.2 = sc b w s * k
        · obtain ⟨k1, hk1, e1⟩ := h1
          obtain ⟨k2, hk2, e2⟩ := h2
          exact absurd ⟨(k1, k2), ⟨hk1, hk2⟩, Prod.ext e1 e2⟩ h
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  funext y
  have hinv : ∀ k ∈ K2 a b w, ∀ x, (fun x => f x * g (x⁻¹ * y)) (x * k) = (fun x => f x * g (x⁻¹ * y)) x := by
    intro k hk x
    have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
    simp only [hf, hr _ k x hk, e, hgl k⁻¹ (inv_mem hk)]
  have hc : cv (K2 a b w) f g y = ∑ᶠ q : (GLw a w × GLw b w) ⧸ K2 a b w, f q.out * g (q.out⁻¹ * y) :=
    hintSph _ (K2 a b w) _ hinv
  rw [hc, finsum_eq_single _ (QuotientGroup.mk z : (GLw a w × GLw b w) ⧸ K2 a b w)]
  · obtain ⟨k, e⟩ := QuotientGroup.mk_out_eq_mul (K2 a b w) z
    have e2 := hinv k k.2 z
    simp only at e2
    rw [e, e2, hfz z, if_pos ⟨1, one_mem _, (mul_one _).symm⟩, one_mul, hg, Function.comp_apply, hgen, hgen]
    have hp1 : ((p.1.rev : Fin (a + 1)) : ℕ) = a - p.1 := by rw [Fin.val_rev]; omega
    have hp2 : ((p.2.rev : Fin (b + 1)) : ℕ) = b - p.2 := by rw [Fin.val_rev]; omega
    rw [hp1, hp2, ← Tj_twist w a p.1 (by omega) _ hu s hsv, ← Tj_twist w b p.2 (by omega) _ hu s hsv]
    change Tj ℂ a _ _ _ (thL a w _) * Tj ℂ b _ _ _ (thL b w _) = _
    rw [hth, hth]
    rfl
  · intro q hq
    have : f q.out = 0 := by
      rw [hfz, if_neg]
      rintro ⟨k, hk, e⟩
      apply hq
      rw [← QuotientGroup.out_eq' q, e]
      exact QuotientGroup.eq.2 (by simpa using inv_mem hk)
    rw [this, zero_mul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
