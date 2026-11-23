import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLTendstoNeZeroAtOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConjStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTerm

noncomputable section

open NumberField IsDedekindDomain Filter Topology GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.HeckeGal.Model

namespace GlobalTheory.JSW.Rigid

section lemmas
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem hasProd_exp_logRS {a b : ℕ} {σ : CG E a} {σ' : CG E b} (hσ : σ.IsUnitary) (hσ' : σ'.IsUnitary)
    {T : Finset (HeightOneSpectrum (𝓞 E))} (hT : UnrOutside T σ) (hT' : UnrOutside T σ') {x : ℝ} (hx : 1 < x) :
    HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1)
      ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (Complex.exp (logRS T σ σ' x)) :=
  (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T hT hT' x hx).2

theorem rsTerm_shift {a b : ℕ} (σ : CG E a) (σ' : CG E b) (y d : ℝ) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) :
    rsTerm σ σ' (y + d) w r = rsTerm σ σ' y w r * (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (d : ℂ))) := by
  have hq0 : (Ideal.absNorm w.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (by have := NumberField.HeightOneSpectrum.one_lt_absNorm w; omega)
  have e : (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * ((y + d : ℝ) : ℂ))) =
      (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (y : ℂ))) *
      (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (d : ℂ))) := by
    rw [← Complex.cpow_add _ _ hq0]
    congr 1
    push_cast
    ring
  rw [rsTerm, rsTerm, e]
  ring

theorem norm_logRS_add_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖logRS T σ σ' (x + δ)‖ ≤ C := by
  intro E _ _ _ a b σ σ' hσ hσ' T hT hT' δ hδ
  have hs := fun y (hy : 1 < y) => (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T hT hT' y hy).1
  refine ⟨∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, ‖rsTerm σ σ' (1 + δ) p.1.1 p.2‖, fun x hx => ?_⟩
  have h0 : Summable fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ‖rsTerm σ σ' (1 + δ) p.1.1 p.2‖ :=
    hs (1 + δ) (by linarith)
  have h1 : Summable fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ‖rsTerm σ σ' (x + δ) p.1.1 p.2‖ :=
    hs (x + δ) (by linarith)
  refine (norm_tsum_le_tsum_norm h1).trans (Summable.tsum_le_tsum (fun p => ?_) h1 h0)
  have e : x + δ = (1 + δ) + (x - 1) := by ring
  rw [e, rsTerm_shift, norm_mul]
  have hq := NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1
  have hn : ‖(Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * ((x - 1 : ℝ) : ℂ)))‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq.le) ?_
    have : (-(((p.2 : ℂ) + 1) * ((x - 1 : ℝ) : ℂ))).re = -(((p.2 : ℝ) + 1) * (x - 1)) := by
      simp [Complex.mul_re]
    rw [this]
    have : 0 ≤ ((p.2 : ℝ) + 1) * (x - 1) := mul_nonneg (by positivity) (by linarith)
    linarith
  calc ‖rsTerm σ σ' (1 + δ) p.1.1 p.2‖ * _ ≤ ‖rsTerm σ σ' (1 + δ) p.1.1 p.2‖ * 1 :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := mul_one _

theorem abs_re_logRS_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∃ C : ℝ, ∀ᶠ x in 𝓝[>] (1 : ℝ), |(logRS T σ σ' x).re| ≤ C := by
  intro E _ _ _ a b σ σ' ha hb hσ hσ' hne T hT hT'
  obtain ⟨z, hz, hlim⟩ := GlobalTheory.T.rankinSelberg_partialL_tendsto_ne_zero_at_one E a b σ σ' ha hb hσ hσ' hne T hT hT'
  have hx1 : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := self_mem_nhdsWithin
  have h1 : Tendsto (fun x : ℝ => Complex.exp (logRS T σ σ' x)) (𝓝[>] 1) (𝓝 z) :=
    hlim.congr' (hx1.mono fun x hx => (hasProd_exp_logRS hσ hσ' hT hT' hx).tprod_eq)
  have h2 : Tendsto (fun x : ℝ => (logRS T σ σ' x).re) (𝓝[>] 1) (𝓝 (Real.log ‖z‖)) := by
    have h3 := (h1.norm.log (norm_ne_zero_iff.2 hz))
    refine h3.congr fun x => ?_
    rw [Complex.norm_exp, Real.log_exp]
  have h4 := h2.eventually (Icc_mem_nhds (show Real.log ‖z‖ - 1 < Real.log ‖z‖ by linarith)
    (show Real.log ‖z‖ < Real.log ‖z‖ + 1 by linarith))
  refine ⟨|Real.log ‖z‖| + 1, h4.mono fun x hx => abs_le.2 ⟨?_, ?_⟩⟩
  · linarith [hx.1, neg_abs_le (Real.log ‖z‖)]
  · linarith [hx.2, le_abs_self (Real.log ‖z‖)]

theorem tendsto_re_logRS_self : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π → Tendsto (fun x : ℝ => (logRS T π π x).re) (𝓝[>] 1) atTop := by
  intro E _ _ _ a π ha hπ T hT
  obtain ⟨L, hL, -, c, hc, hlim⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a π ha hπ T hT
  have hx1 : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := self_mem_nhdsWithin
  have he : ∀ x : ℝ, 1 < x → (logRS T π π x).re = Real.log (L x) := fun x hx => by
    have e := (hL x hx).1.unique (hasProd_exp_logRS hπ hπ hT hT hx)
    have e2 := congrArg (fun u : ℂ => ‖u‖) e
    simp only [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs] at e2
    rw [abs_of_pos (by linarith [(hL x hx).2])] at e2
    rw [e2, Real.log_exp]
  have hsub : Tendsto (fun x : ℝ => x - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hx1.mono fun x hx => ?_⟩
    · have : Tendsto (fun x : ℝ => x - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact sub_pos.2 hx
  have hinv : Tendsto (fun x : ℝ => (x - 1)⁻¹) (𝓝[>] 1) atTop := tendsto_inv_nhdsGT_zero.comp hsub
  have hLtop : Tendsto L (𝓝[>] 1) atTop := by
    refine (hlim.pos_mul_atTop hc hinv).congr' (hx1.mono fun x hx => ?_)
    field_simp [(sub_pos.2 hx).ne']
  exact (Real.tendsto_log_atTop.comp hLtop).congr' (hx1.mono fun x hx => (he x hx).symm)
end lemmas

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem exists_equiv_of_map_eq {ι κ α : Type} [Fintype ι] [Fintype κ] (f : ι → α) (g : κ → α)
    (h : (Finset.univ.val.map f : Multiset α) = Finset.univ.val.map g) : ∃ s : ι ≃ κ, ∀ i, f i = g (s i) := by
  classical
  have hc : ∀ c, Fintype.card {i // f i = c} = Fintype.card {j // g j = c} := by
    intro c
    have h1 := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using h1
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c), fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩

theorem eventually_bdd_sum {ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ) (l : Filter ℝ)
    (h : ∀ i ∈ s, ∃ C, ∀ᶠ x in l, |f i x| ≤ C) : ∃ C, ∀ᶠ x in l, |∑ i ∈ s, f i x| ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Eventually.of_forall fun x => by simp⟩
  | insert i s hi ih =>
    obtain ⟨C1, h1⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨C2, h2⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ⟨C1 + C2, (h1.and h2).mono fun x hx => ?_⟩
    rw [Finset.sum_insert hi]
    exact (abs_add_le _ _).trans (add_le_add hx.1 hx.2)

theorem summable_rsTerm {a b : ℕ} {σ : CG E a} {σ' : CG E b} (hσ : σ.IsUnitary) (hσ' : σ'.IsUnitary)
    {T : Finset (HeightOneSpectrum (𝓞 E))} (hT : UnrOutside T σ) (hT' : UnrOutside T σ') {y : ℝ} (hy : 1 < y) :
    Summable fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => rsTerm σ σ' y p.1.1 p.2 :=
  Summable.of_norm (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T hT hT' y hy).1

theorem vanish (T : Finset (HeightOneSpectrum (𝓞 E))) (S : Finset ((Σ a, CG E a) × ℝ)) (c : (Σ a, CG E a) × ℝ → ℤ)
    (hS : ∀ p ∈ S, 1 ≤ p.1.1 ∧ p.1.2.IsUnitary ∧ UnrOutside T p.1.2)
    (hid : ∀ w ∉ T, ∀ r : ℕ, ∑ p ∈ S, (c p : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (p.2 : ℂ))) *
      ((sat p.1.2 w).map fun α => (α : ℂ) ^ (r + 1)).sum) = 0) :
    ∀ p ∈ S, c p = 0 := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨p1, hp1S, hp1⟩ := hne
  set S' := S.filter fun p => c p ≠ 0 with hS'
  have hS'ne : S'.Nonempty := ⟨p1, Finset.mem_filter.2 ⟨hp1S, hp1⟩⟩
  obtain ⟨p0, hp0, hmin⟩ := S'.exists_min_image (fun p => p.2) hS'ne
  have hp0S := (Finset.mem_filter.1 hp0).1
  have hc0 := (Finset.mem_filter.1 hp0).2
  obtain ⟨hm0, hu0, hT0⟩ := hS p0 hp0S
  let ℓ : (Σ a, CG E a) × ℝ → ℝ → ℂ := fun p x => logRS T p.1.2 p0.1.2 (x + (p.2 - p0.2))
  have hzero : ∀ x : ℝ, 1 < x → ∑ p ∈ S', (c p : ℂ) * ℓ p x = 0 := by
    intro x hx
    have hsum : ∀ p ∈ S', Summable fun q : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ =>
        (c p : ℂ) * rsTerm p.1.2 p0.1.2 (x + (p.2 - p0.2)) q.1.1 q.2 := by
      intro p hp
      obtain ⟨-, hu, hT⟩ := hS p (Finset.mem_filter.1 hp).1
      exact (summable_rsTerm hu hu0 hT hT0 (by linarith [hmin p hp])).mul_left _
    simp only [ℓ, logRS, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum hsum]
    refine (tsum_congr fun q => ?_).trans tsum_zero
    have hq0 : (Ideal.absNorm q.1.1.asIdeal : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (by have := NumberField.HeightOneSpectrum.one_lt_absNorm q.1.1; omega)
    have hterm : ∀ p : (Σ a, CG E a) × ℝ, (c p : ℂ) * rsTerm p.1.2 p0.1.2 (x + (p.2 - p0.2)) q.1.1 q.2 =
        (c p : ℂ) * ((Ideal.absNorm q.1.1.asIdeal : ℂ) ^ (-(((q.2 : ℂ) + 1) * (p.2 : ℂ))) *
          ((sat p.1.2 q.1.1).map fun α => (α : ℂ) ^ (q.2 + 1)).sum) *
        (((sat p0.1.2 q.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (q.2 + 1)).sum *
          (Ideal.absNorm q.1.1.asIdeal : ℂ) ^ (-(((q.2 : ℂ) + 1) * ((x - p0.2 : ℝ) : ℂ))) / ((q.2 : ℂ) + 1)) := by
      intro p
      have e : (Ideal.absNorm q.1.1.asIdeal : ℂ) ^ (-(((q.2 : ℂ) + 1) * ((x + (p.2 - p0.2) : ℝ) : ℂ))) =
          (Ideal.absNorm q.1.1.asIdeal : ℂ) ^ (-(((q.2 : ℂ) + 1) * (p.2 : ℂ))) *
          (Ideal.absNorm q.1.1.asIdeal : ℂ) ^ (-(((q.2 : ℂ) + 1) * ((x - p0.2 : ℝ) : ℂ))) := by
        rw [← Complex.cpow_add _ _ hq0]
        congr 1
        push_cast
        ring
      rw [rsTerm, e]
      ring
    rw [hS', Finset.sum_filter_of_ne (p := fun p => c p ≠ 0) fun p _ h hc => h (by rw [hc, Int.cast_zero, zero_mul]),
      Finset.sum_congr rfl fun p _ => hterm p, ← Finset.sum_mul, hid q.1.1 q.1.2 q.2, zero_mul]
  have hre : ∀ x : ℝ, 1 < x → ∑ p ∈ S', (c p : ℝ) * (ℓ p x).re = 0 := by
    intro x hx
    have := congrArg Complex.re (hzero x hx)
    simpa [Complex.re_sum] using this
  have hb : ∀ p ∈ S'.erase p0, ∃ C, ∀ᶠ x in 𝓝[>] (1 : ℝ), |(c p : ℝ) * (ℓ p x).re| ≤ C := by
    intro p hp
    have hpS' := Finset.mem_of_mem_erase hp
    have hne := Finset.ne_of_mem_erase hp
    obtain ⟨hm1, hu, hT⟩ := hS p (Finset.mem_filter.1 hpS').1
    rcases (hmin p hpS').lt_or_eq with hlt | heq
    · obtain ⟨C, hC⟩ := norm_logRS_add_le E _ _ p.1.2 p0.1.2 hu hu0 T hT hT0 (p.2 - p0.2) (by linarith)
      refine ⟨|(c p : ℝ)| * C, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hC x hx)) (abs_nonneg _)
    · have hne' : p.1 ≠ p0.1 := fun h => hne (Prod.ext h heq.symm)
      obtain ⟨C, hC⟩ := abs_re_logRS_bdd E _ _ p.1.2 p0.1.2 hm1 hm0 hu hu0 hne' T hT hT0
      refine ⟨|(c p : ℝ)| * C, hC.mono fun x hx => ?_⟩
      have e : ℓ p x = logRS T p.1.2 p0.1.2 x := by simp only [ℓ, heq, sub_self, add_zero]
      rw [abs_mul, e]
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  obtain ⟨C, hC⟩ := eventually_bdd_sum (S'.erase p0) (fun p x => (c p : ℝ) * (ℓ p x).re) _ hb
  have hpole := tendsto_re_logRS_self E _ p0.1.2 hm0 hu0 T hT0
  have hℓ0 : ∀ x, ℓ p0 x = logRS T p0.1.2 p0.1.2 x := fun x => by simp only [ℓ, sub_self, add_zero]
  have hev : ∀ᶠ x in 𝓝[>] (1 : ℝ), C + 1 ≤ (logRS T p0.1.2 p0.1.2 x).re := hpole.eventually_ge_atTop _
  have hx1 : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := self_mem_nhdsWithin
  obtain ⟨x, hCx, hevx, hx⟩ := (hC.and (hev.and hx1)).exists
  have h1 := hre x hx
  rw [← Finset.add_sum_erase _ _ hp0, hℓ0] at h1
  have hc0' : (1 : ℝ) ≤ |(c p0 : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc0
  have e1 : (c p0 : ℝ) * (logRS T p0.1.2 p0.1.2 x).re = -∑ p ∈ S'.erase p0, (c p : ℝ) * (ℓ p x).re := by linarith
  have e2 : |(c p0 : ℝ) * (logRS T p0.1.2 p0.1.2 x).re| ≤ C := by rw [e1, abs_neg]; exact hCx
  have e3 : (logRS T p0.1.2 p0.1.2 x).re ≤ |(c p0 : ℝ) * (logRS T p0.1.2 p0.1.2 x).re| := by
    rw [abs_mul]
    calc (logRS T p0.1.2 p0.1.2 x).re ≤ |(logRS T p0.1.2 p0.1.2 x).re| := le_abs_self _
      _ = 1 * |(logRS T p0.1.2 p0.1.2 x).re| := (one_mul _).symm
      _ ≤ |(c p0 : ℝ)| * |(logRS T p0.1.2 p0.1.2 x).re| := mul_le_mul_of_nonneg_right hc0' (abs_nonneg _)
  linarith

theorem map_coe_pow (A : Multiset ℂˣ) (r : ℕ) :
    (A.map fun α => (α : ℂ) ^ (r + 1)) = (A.map fun α : ℂˣ => (α : ℂ) ^ (r + 1)) := by
  simp [Multiset.bind_singleton]

theorem sum_map_pow_twist (s : ℝ) (w : HeightOneSpectrum (𝓞 E)) (A : Multiset ℂˣ) (r : ℕ) :
    ((A.map (· * (absPow E s).val w)).map fun α : ℂˣ => (α : ℂ) ^ (r + 1)).sum =
      (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (s : ℂ))) * (A.map fun α => (α : ℂ) ^ (r + 1)).sum := by
  rw [map_coe_pow, Multiset.map_map, ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, Units.val_mul, (absPow_isAbsPow E s).2.1 w, mul_pow]
  rw [mul_comm, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

theorem hasSat_sat {a : ℕ} {σ : CG E a} {T : Finset (HeightOneSpectrum (𝓞 E))} (h : UnrOutside T σ)
    {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ T) : σ.HasSat w (sat σ w) := by
  unfold sat
  rw [dif_pos (h w hw)]
  exact (h w hw).choose_spec

theorem unrOutside_of_twist {a : ℕ} {σ σ₀ : CG E a} {s : ℝ} (he : σ = σ₀.twist (absPow E s))
    {T : Finset (HeightOneSpectrum (𝓞 E))} (h : ∀ w ∉ T, ∃ B, σ.HasSat w B) : UnrOutside T σ₀ := by
  intro w hw
  obtain ⟨B, hB⟩ := h w hw
  have e : σ.twist (absPow E (-s)) = σ₀ := by
    rw [he, ← CG.twist_mul, mul_comm, CG.absPow_neg_mul, CG.twist_one]
  rw [← e]
  exact ⟨_, (hB.twist_absPow (-s)).1⟩

end GlobalTheory.JSW.Rigid

open GlobalTheory.JSW.Rigid in

theorem GlobalTheory.JSW.jacquetShalikaRigidity_holds : GlobalTheory.Published.JacquetShalikaRigidity := by
  intro E _ _ _ ι κ _ _ m m' π π' hm hm' hw
  classical
  choose π0 t hu0 he0 using fun i => CG.exists_isUnitary_twist_absPow (π i) (hm i)
  choose π0' t' hu0' he0' using fun j => CG.exists_isUnitary_twist_absPow (π' j) (hm' j)
  have hfin := Filter.eventually_cofinite.1 hw
  set T := hfin.toFinset with hTdef
  have hgood : ∀ w ∉ T, ∃ (B : ι → Multiset ℂˣ) (B' : κ → Multiset ℂˣ),
      (∀ i, (π i).HasSat w (B i)) ∧ (∀ j, (π' j).HasSat w (B' j)) ∧ ∑ i, B i = ∑ j, B' j := by
    intro w hw'
    by_contra h
    exact hw' (hfin.mem_toFinset.2 h)
  have hT0 : ∀ i, UnrOutside T (π0 i) := fun i => unrOutside_of_twist (he0 i) fun w hw => by
    obtain ⟨B, -, hB, -, -⟩ := hgood w hw; exact ⟨_, hB i⟩
  have hT0' : ∀ j, UnrOutside T (π0' j) := fun j => unrOutside_of_twist (he0' j) fun w hw => by
    obtain ⟨-, B', -, hB', -⟩ := hgood w hw; exact ⟨_, hB' j⟩
  set M : Multiset ((Σ a, CG E a) × ℝ) := Finset.univ.val.map fun i => ((⟨m i, π0 i⟩ : Σ a, CG E a), t i) with hM
  set M' : Multiset ((Σ a, CG E a) × ℝ) := Finset.univ.val.map fun j => ((⟨m' j, π0' j⟩ : Σ a, CG E a), t' j)
    with hM'
  set S := (M + M').toFinset with hSdef
  let c : (Σ a, CG E a) × ℝ → ℤ := fun p => (M.count p : ℤ) - M'.count p
  let f : HeightOneSpectrum (𝓞 E) → ℕ → (Σ a, CG E a) × ℝ → ℂ := fun w r p =>
    (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (p.2 : ℂ))) * ((sat p.1.2 w).map fun α => (α : ℂ) ^ (r + 1)).sum
  have hcount : ∀ N : Multiset ((Σ a, CG E a) × ℝ), N ≤ M + M' → ∀ g : (Σ a, CG E a) × ℝ → ℂ,
      ∑ p ∈ S, (N.count p : ℂ) * g p = (N.map g).sum := by
    intro N hN g
    rw [Finset.sum_multiset_map_count]
    simp_rw [nsmul_eq_mul]
    symm
    apply Finset.sum_subset
    · exact Multiset.toFinset_subset.2 (Multiset.subset_of_le hN)
    · intro p _ hp
      rw [Multiset.count_eq_zero.2 (fun h => hp (Multiset.mem_toFinset.2 h))]
      simp
  have hpw : ∀ (N : Multiset ℂˣ) (r : ℕ), (N.map fun α : ℂˣ => (α : ℂ) ^ (r + 1)).sum =
      (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom fun α : ℂˣ => (α : ℂ) ^ (r + 1))) N := fun _ _ => rfl
  have hMsum : ∀ w ∉ T, ∀ r, (M.map (f w r)).sum = (M'.map (f w r)).sum := by
    intro w hw r
    obtain ⟨B, B', hB, hB', hBB⟩ := hgood w hw
    have e1 : ∀ i, B i = (sat (π0 i) w).map (· * (absPow E (t i)).val w) := fun i =>
      (hB i).unique (by rw [he0 i]; exact ((hasSat_sat (hT0 i) hw).twist_absPow (t i)).1)
    have e1' : ∀ j, B' j = (sat (π0' j) w).map (· * (absPow E (t' j)).val w) := fun j =>
      (hB' j).unique (by rw [he0' j]; exact ((hasSat_sat (hT0' j) hw).twist_absPow (t' j)).1)
    have hL : (M.map (f w r)).sum = ((∑ i, B i).map fun α : ℂˣ => (α : ℂ) ^ (r + 1)).sum := by
      rw [hpw, map_sum, hM, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hpw, e1 i, sum_map_pow_twist]
      rfl
    have hR : (M'.map (f w r)).sum = ((∑ j, B' j).map fun α : ℂˣ => (α : ℂ) ^ (r + 1)).sum := by
      rw [hpw, map_sum, hM', Multiset.map_map, ← Finset.sum_eq_multiset_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hpw, e1' j, sum_map_pow_twist]
      rfl
    rw [hL, hR, hBB]
  have hS : ∀ p ∈ S, 1 ≤ p.1.1 ∧ p.1.2.IsUnitary ∧ UnrOutside T p.1.2 := by
    intro p hp
    rw [hSdef, Multiset.mem_toFinset, Multiset.mem_add, hM, hM'] at hp
    rcases hp with hp | hp
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hp
      exact ⟨hm i, hu0 i, hT0 i⟩
    · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hp
      exact ⟨hm' j, hu0' j, hT0' j⟩
  have hv := vanish T S c hS fun w hw r => by
    change ∑ p ∈ S, (c p : ℂ) * f w r p = 0
    simp only [c, Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib]
    rw [hcount M (Multiset.le_add_right _ _), hcount M' (Multiset.le_add_left _ _), hMsum w hw r, sub_self]
  have hMM : M = M' := by
    refine Multiset.ext.2 fun p => ?_
    by_cases hp : p ∈ S
    · have := hv p hp
      simp only [c] at this
      omega
    · rw [hSdef, Multiset.mem_toFinset, Multiset.mem_add, not_or] at hp
      rw [Multiset.count_eq_zero.2 hp.1, Multiset.count_eq_zero.2 hp.2]
  let tw : (Σ a, CG E a) × ℝ → Σ a, CG E a := fun p => ⟨p.1.1, p.1.2.twist (absPow E p.2)⟩
  have h1 : (Finset.univ.val.map fun i => (⟨m i, π i⟩ : Σ a, CG E a)) = M.map tw := by
    rw [hM, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, tw, ← he0 i]
  have h2 : (Finset.univ.val.map fun j => (⟨m' j, π' j⟩ : Σ a, CG E a)) = M'.map tw := by
    rw [hM', Multiset.map_map]
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, tw, ← he0' j]
  exact exists_equiv_of_map_eq (fun i => (⟨m i, π i⟩ : Σ a, CG E a)) (fun j => (⟨m' j, π' j⟩ : Σ a, CG E a))
    (by rw [h1, h2, hMM])
