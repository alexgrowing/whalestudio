import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondStd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors WithZero

namespace Formalism.L2.SG.Pf.LocTr

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isDiffVal_dV : Formalism.L2.SG.LocVol.IsDiffVal v (Formalism.L2.SG.LocVol.dV v) := by
  classical

  have hex : ∃ d, Formalism.L2.SG.LocVol.IsDiffVal v d := by
    have hne : differentIdeal ℤ (𝓞 F) ≠ ⊥ := by
      first
        | exact differentIdeal_ne_bot
        | exact differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)
    obtain ⟨x0, hx0D, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (differentIdeal ℤ (𝓞 F)) :
      (differentIdeal ℤ (𝓞 F)).FG)
    obtain ⟨g, hgs, hgmax⟩ := Finset.exists_max_image (insert x0 s)
      (fun x : 𝓞 F => Valued.v (algebraMap F (v.adicCompletion F) (x : F)))
      (Finset.insert_nonempty _ _)
    have hgD : g ∈ differentIdeal ℤ (𝓞 F) := by
      rcases Finset.mem_insert.mp hgs with h | h
      · rw [h]; exact hx0D
      · rw [← hs]; exact Submodule.subset_span h
    have hv0 : Valued.v (algebraMap F (v.adicCompletion F) (x0 : F)) ≠ 0 := by
      rw [Ne, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap F (v.adicCompletion F)).injective]
      exact fun h => hx0 (by exact_mod_cast h)
    have hle0 := hgmax x0 (Finset.mem_insert_self _ _)
    refine ⟨algebraMap F (v.adicCompletion F) (g : F), ?_, ?_, ⟨g, hgD, rfl⟩⟩
    · intro h0
      rw [h0, Valuation.map_zero] at hle0
      exact hv0 (le_antisymm hle0 zero_le')
    · intro x hx
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hgmax y (Finset.mem_insert_of_mem hy)
      | zero => simp
      | add a b _ _ ha hb =>
        rw [show ((a + b : 𝓞 F) : F) = (a : F) + (b : F) from rfl, map_add]
        exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)
      | smul a b _ hb =>
        rw [show ((a • b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul, Valuation.map_mul]
        have ha1 : Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1 := by
          have e : Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = v.valuation F (a : F) := by
            show Valued.v ((a : F) : v.adicCompletion F) = v.valuation F (a : F)
            first
              | exact valuedAdicCompletion_eq_valuation v (a : F)
              | exact v.valuedAdicCompletion_eq_valuation (a : F)
              | exact valuedAdicCompletion_eq_valuation (a : F)
              | exact valuedAdicCompletion_eq_valuation F v (a : F)
              | simp
          rw [e]
          first
            | exact v.valuation_le_one a
            | exact v.valuation_le_one F a
            | exact valuation_le_one v a
            | exact valuation_le_one F v a
            | simp
        calc _ ≤ 1 * Valued.v (algebraMap F (v.adicCompletion F) (g : F)) := mul_le_mul' ha1 hb
          _ = _ := one_mul _
  rw [show Formalism.L2.SG.LocVol.dV v = hex.choose from dif_pos hex]
  exact hex.choose_spec

open Classical in
theorem single_at (y : Fv F v) : (singleV F v y) v = y := by
  first
    | exact Pi.single_eq_same v y
    | exact Pi.single_eq_same (f := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v y
    | simp [singleV]
    | rfl

open Classical in
theorem single_at_ne (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : (singleV F v y) w = 0 := by
  first
    | exact Pi.single_eq_of_ne h y
    | exact Pi.single_eq_of_ne' (Ne.symm h) y
    | simp [singleV, h]

theorem alg_at (q : F) (w : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (Af F) q) w = (q : w.adicCompletion F) := by
  first
    | rfl
    | simp

theorem val_coe (w : HeightOneSpectrum (𝓞 F)) (q : F) :
    Valued.v (q : w.adicCompletion F) = w.valuation F q := by
  first
    | exact valuedAdicCompletion_eq_valuation w q
    | exact w.valuedAdicCompletion_eq_valuation q
    | exact valuedAdicCompletion_eq_valuation q
    | exact valuedAdicCompletion_eq_valuation F w q
    | simp

theorem val_int_le (w : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    Valued.v ((algebraMap (𝓞 F) F d : F) : w.adicCompletion F) ≤ 1 := by
  rw [val_coe w]
  first
    | exact w.valuation_le_one d
    | exact w.valuation_le_one F d
    | exact valuation_le_one w d
    | exact valuation_le_one F w d
    | simp

private theorem diff_coe_lemma :
    ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
  first
    | exact coeIdeal_differentIdeal ℤ ℚ
    | exact coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := F) (B := 𝓞 F)
    | exact coeIdeal_differentIdeal (A := ℤ) (K := ℚ)
    | exact coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
    | rw [coeIdeal_differentIdeal (A := ℤ) (K := ℚ)]

theorem trace_int_of (q : F)
    (h : ∀ d0 ∈ differentIdeal ℤ (𝓞 F), q * algebraMap (𝓞 F) F d0 ∈ (algebraMap (𝓞 F) F).range) :
    ∃ n : ℤ, Algebra.trace ℚ F q = n := by
  have hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hD0 : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [diff_coe_lemma]; exact inv_ne_zero hJ

  have hq : q ∈ ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hD0]
    intro z hz
    obtain ⟨d0, hd0, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp (h d0 hd0)
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨c, hc⟩
  rw [diff_coe_lemma, inv_inv, FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) (one_ne_zero : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0)] at hq
  obtain ⟨n, hn⟩ := RingHom.mem_range.mp (hq 1 (FractionalIdeal.one_mem_one _))
  refine ⟨n, ?_⟩
  rw [Algebra.traceForm_apply, mul_one] at hn
  rw [← hn]
  simp

end Formalism.L2.SG.Pf.LocTr

namespace Formalism.L2.SG.Pf.LocTr

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem sub_at (a b : Af F) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := rfl

theorem mem_intAd {a : Af F} : a ∈ Formalism.UG.intAd F ↔ ∀ w, Valued.v (a w) ≤ 1 := by
  first
    | exact Iff.rfl
    | exact ⟨fun h w => h w, fun h w => h w⟩

theorem val_alg (w : HeightOneSpectrum (𝓞 F)) (q : F) :
    Valued.v (algebraMap F (w.adicCompletion F) q) = w.valuation F q := by
  first
    | exact val_coe w q
    | simp [val_coe]

theorem bwd (x : Fv F v) (hx : Formalism.L2.SG.LocVol.dV v * x ∈ v.adicCompletionIntegers F)
    (y : Fv F v) (hy : y ∈ v.adicCompletionIntegers F) (q : F)
    (hq : singleV F v (x * y) - algebraMap F (Af F) q ∈ Formalism.UG.intAd F) : ∃ n : ℤ, Algebra.trace ℚ F q = n := by
  apply trace_int_of q
  intro d0 hd0

  have hD : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d0)) ≤
      Valued.v (Formalism.L2.SG.LocVol.dV v) := (isDiffVal_dV v).2.1 d0 hd0
  have hI := mem_intAd.mp hq
  apply mem_integers_of_valuation_le_one
  intro w
  rw [← val_alg w, map_mul]
  have had : Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F d0)) ≤ 1 :=
    val_int_le w d0
  by_cases hw : w = v
  · rw [hw] at had ⊢
    have h1 := hI v
    rw [sub_at, alg_at, single_at v] at h1
    have hc : algebraMap F (v.adicCompletion F) q = (q : v.adicCompletion F) := rfl
    have e : algebraMap F (v.adicCompletion F) q * algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d0) =
        x * y * algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d0) -
          (x * y - (q : v.adicCompletion F)) * algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d0) := by
      rw [hc]; ring
    rw [e]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · have hy' : Valued.v y ≤ 1 := hy
      have hx' : Valued.v (Formalism.L2.SG.LocVol.dV v * x) ≤ 1 := hx
      calc Valued.v (x * y * algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d0))
          = Valued.v x * Valued.v y * Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d0)) := by
            rw [Valuation.map_mul, Valuation.map_mul]
        _ ≤ Valued.v x * 1 * Valued.v (Formalism.L2.SG.LocVol.dV v) := mul_le_mul' (mul_le_mul' le_rfl hy') hD
        _ = Valued.v (Formalism.L2.SG.LocVol.dV v * x) := by rw [mul_one, Valuation.map_mul, mul_comm]
        _ ≤ 1 := hx'
    · rw [Valuation.map_mul]
      exact mul_le_one' h1 had
  · have h1 := hI w
    rw [sub_at, alg_at, single_at_ne v (x * y) hw, zero_sub, Valuation.map_neg] at h1
    have h1' : Valued.v (algebraMap F (w.adicCompletion F) q) ≤ 1 := by
      rw [val_alg w, ← val_coe w]; exact h1
    rw [Valuation.map_mul]
    exact mul_le_one' h1' had

end Formalism.L2.SG.Pf.LocTr

namespace Formalism.L2.SG.Pf.LocTr

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem mul_diff_int (y : F)
    (hy : ∀ z : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (y * algebraMap (𝓞 F) F z) = n)
    (d : 𝓞 F) (hd : d ∈ differentIdeal ℤ (𝓞 F)) :
    ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = y * algebraMap (𝓞 F) F d := by
  have hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero

  have hyJ : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) (one_ne_zero : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0)]
    intro a ha
    rw [FractionalIdeal.mem_one_iff] at ha
    obtain ⟨z, rfl⟩ := ha
    obtain ⟨n, hn⟩ := hy z
    rw [Algebra.traceForm_apply, hn]
    exact RingHom.mem_range.mpr ⟨n, by simp⟩
  have hd' : algebraMap (𝓞 F) F d ∈
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩
  rw [diff_coe_lemma] at hd'
  have hm := FractionalIdeal.mul_mem_mul hyJ hd'
  rw [mul_inv_cancel₀ hJ, FractionalIdeal.mem_one_iff] at hm
  obtain ⟨c, hc⟩ := hm
  exact ⟨c, hc⟩

theorem fwd (x : Fv F v)
    (hP : ∀ y ∈ v.adicCompletionIntegers F, ∀ q : F,
      singleV F v (x * y) - algebraMap F (Af F) q ∈ Formalism.UG.intAd F → ∃ n : ℤ, Algebra.trace ℚ F q = n) :
    Formalism.L2.SG.LocVol.dV v * x ∈ v.adicCompletionIntegers F := by
  have hD := isDiffVal_dV v
  by_contra hnot
  rw [mem_adicCompletionIntegers, not_le] at hnot
  set δ := Formalism.L2.SG.LocVol.dV v with hδ
  have hδ0 : Valued.v δ ≠ 0 := by rw [Ne, map_eq_zero]; exact hD.1
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [mul_zero, map_zero] at hnot
    exact not_lt.2 zero_le_one hnot
  have hvx0 : Valued.v x ≠ 0 := by rw [Ne, map_eq_zero]; exact hx0
  set a := WithZero.log (Valued.v δ) with ha
  set b := WithZero.log (Valued.v x) with hb
  have hvδ : Valued.v δ = WithZero.exp a := (WithZero.exp_log hδ0).symm
  have hvx : Valued.v x = WithZero.exp b := (WithZero.exp_log hvx0).symm
  have hab : 1 ≤ a + b := by
    rw [map_mul, hvδ, hvx, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hnot
    omega

  obtain ⟨d1, hd1, hd1v⟩ := hD.2.2
  have ha0 : a ≤ 0 := by
    have h1 : Valued.v δ ≤ 1 := by
      rw [← hd1v, val_alg]; exact v.valuation_le_one d1
    rw [hvδ, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1

  obtain ⟨ϖ, hϖ⟩ := v.valuation_exists_uniformizer F
  set W := algebraMap F (v.adicCompletion F) ϖ with hW
  have hvW : Valued.v W = WithZero.exp (-1) := by rw [hW, val_alg, hϖ]
  set t0 : Fv F v := (δ * W)⁻¹ with ht0
  have hvt0 : Valued.v t0 = WithZero.exp (1 - a) := by
    rw [ht0, map_inv₀, map_mul, hvδ, hvW, ← WithZero.exp_add, ← WithZero.exp_neg]
    congr 1; ring
  obtain ⟨qs, hqs⟩ := Formalism.L2.SG.Pf.CondStd.fin_approx (singleV F v t0)
  have hqsv : Valued.v (algebraMap F (v.adicCompletion F) qs) = WithZero.exp (1 - a) := by
    have h := (mem_intAd.1 hqs) v
    rw [sub_at, single_at, alg_at] at h
    have hlt : Valued.v (t0 - algebraMap F (v.adicCompletion F) qs) < Valued.v t0 := by
      refine lt_of_le_of_lt h ?_
      rw [hvt0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have e : algebraMap F (v.adicCompletion F) qs = t0 + -(t0 - algebraMap F (v.adicCompletion F) qs) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left, hvt0]
    rwa [Valuation.map_neg]
  have hqsw : ∀ w, w ≠ v → Valued.v (algebraMap F (w.adicCompletion F) qs) ≤ 1 := by
    intro w hw
    have h := (mem_intAd.1 hqs) w
    rw [sub_at, single_at_ne _ _ hw, alg_at, zero_sub, Valuation.map_neg] at h
    exact h

  have hA : ∀ q : F, (∀ w, w ≠ v → Valued.v (algebraMap F (w.adicCompletion F) q) ≤ 1) →
      Valued.v (algebraMap F (v.adicCompletion F) q) ≤ WithZero.exp (1 - a) → ∃ n : ℤ, Algebra.trace ℚ F q = n := by
    intro q hw hv
    set Qv := algebraMap F (v.adicCompletion F) q with hQv
    have hy : Qv / x ∈ v.adicCompletionIntegers F := by
      rw [mem_adicCompletionIntegers, map_div₀, div_le_one₀ (zero_lt_iff.2 hvx0)]
      refine hv.trans ?_
      rw [hvx, WithZero.exp_le_exp]
      omega
    refine hP (Qv / x) hy q ?_
    rw [mul_div_cancel₀ _ hx0]
    refine mem_intAd.2 fun w => ?_
    rw [sub_at]
    by_cases hwv : w = v
    · subst hwv
      have e : (algebraMap F (Af F) q) w = Qv := (alg_at q w).trans rfl
      rw [single_at, e, sub_self, map_zero]
      exact zero_le_one
    · rw [single_at_ne _ _ hwv, alg_at, zero_sub, Valuation.map_neg]
      exact hw w hwv

  have hB : ∀ z : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (qs * algebraMap (𝓞 F) F z) = n := by
    intro z
    apply hA
    · intro w hw
      rw [map_mul, map_mul]
      exact mul_le_one' (hqsw w hw) (val_int_le w z)
    · rw [map_mul, map_mul, hqsv]
      calc WithZero.exp (1 - a) * Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F z))
          ≤ WithZero.exp (1 - a) * 1 := mul_le_mul' le_rfl (val_int_le v z)
        _ = WithZero.exp (1 - a) := mul_one _
  obtain ⟨c, hc⟩ := mul_diff_int qs hB d1 hd1
  have hc1 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c)) ≤ 1 := val_int_le v c
  rw [hc, map_mul, map_mul, hqsv, hd1v, hvδ, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at hc1
  omega

theorem local_trace_duality : Formalism.L2.SG.Pf.CondStd.LocTrDual := by
  intro F _ _ v x
  exact ⟨fwd v x, fun h y hy q hq => bwd v x h y hy q hq⟩

end Formalism.L2.SG.Pf.LocTr
