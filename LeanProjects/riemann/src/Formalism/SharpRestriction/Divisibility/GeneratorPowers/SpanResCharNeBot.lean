import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

def H1algLinkStatement (D : D7) : Prop :=
  @RStatement D → @GEndStatement D → @H1algStatement D

namespace H1algLink

open Formalism.L2.Pj.Crude

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem liesOver_resChar : la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  have hl := resCharOf_prime la
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ la.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) ((resCharOf la : ℕ) : ℤ) ∈ la.asIdeal
    rw [map_natCast]
    exact crv_char_mem la
  have hne : la.asIdeal.under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ la.asIdeal.under ℤ := by rw [h]; trivial
    change algebraMap ℤ (𝓞 K) 1 ∈ la.asIdeal at h1
    rwa [map_one] at h1
  exact ⟨hmax.eq_of_le hne hle⟩

theorem span_resChar_ne_bot : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast (resCharOf_prime la).ne_zero

theorem eWL_eq : eWL K la = ramOverZ la := by
  have := liesOver_resChar la
  unfold eWL ramOverZ
  exact (Ideal.ramificationIdx'_eq_ramificationIdx _ _ (span_resChar_ne_bot la)).symm

theorem ramOverZ_ne_zero : ramOverZ la ≠ 0 := by
  have := liesOver_resChar la
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la.asIdeal (span_resChar_ne_bot la)

theorem prime_mem_iff {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la = p := by
  constructor
  · intro hm
    by_contra hne
    have hnd : ¬ resCharOf la ∣ p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq (resCharOf_prime la) hp).1 hd)
    exact crv_not_mem la hnd hm
  · intro h
    rw [← h]
    exact crv_char_mem la

variable {D : D7}

theorem domW_wtA {j : ℕ} {Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum Hh)
    (w : WeightFamilies.Wt D j) : DomW Dw (wtA w) := by
  intro τ i i' hii
  unfold wtA
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone t) hii
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti t) hii
    · exact le_rfl

theorem reduce_aux (a r c : ℝ) (hr : r ≠ 0) : r * (a / r + c) = a + r * c := by
  field_simp

end H1algLink

open H1algLink in

theorem h1alg_of (D : D7) : H1algLinkStatement D := by
  intro hR hG L P Tp hK T h hinj EX H C2 A2 CR j hj hjm hE hS hMb hemb hH3 hRR hPP hnW hDF la y
  by_cases hg : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal
  · have hres : resCharOf la = D.host.g 0 ∨ resCharOf la = D.host.g 1 := by
      obtain ⟨i, hi⟩ := hg
      rw [prime_mem_iff la (D.host.g_prime i)] at hi
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    exact hG L P Tp hK T h hinj EX H C2 A2 CR j hj hjm hE hS hMb hemb hH3 hRR hPP hnW hDF la hres y
  have hg' : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal := fun i hi => hg ⟨i, hi⟩
  have hpins := h.toLawsCore.pins
  have hM : (T.Q.l.M : ℕ) = D.host.g 0 * D.host.g 1 := hpins.2.1.1
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hrd : D.host.rdE ^ 2 = |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) := by
    show (|(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))) ^ 2 = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  have hRR' : D.host.rdE ^ 2 / (4 * D.R.f) ≤ WeightFamilies.RRv D CR := by
    rw [hrd]
    rw [hfr] at hRR ⊢
    have e4 : (4 * (D.R.f : ℝ)) = 2 * ((2 * D.R.f : ℕ) : ℝ) := by push_cast; ring
    rw [e4]
    exact hRR
  have hPP' : ((2 * D.R.f * D.R.m : ℕ) : ℝ) ^ 3 ≤ WeightFamilies.PPv D L C2 A2 := by
    have h0 : (0 : ℝ) ≤ (2 * D.R.f * D.R.m : ℝ) ^ 4 * Tp.nWn := by positivity
    have h3 : (0 : ℝ) ≤ (2 * D.R.f * D.R.m : ℝ) ^ 3 := by positivity
    push_cast
    linarith
  have hqpos : 0 < WeightAlgebra.qq D := by
    unfold WeightAlgebra.qq
    exact lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hq0 : (0 : ℝ) < (WeightAlgebra.qq D : ℝ) := by exact_mod_cast hqpos
  have hqg : WeightAlgebra.qq D ≤ D.host.g 0 := min_le_left _ _
  have hg01 : D.host.g 0 ≤ D.host.g 0 * D.host.g 1 := Nat.le_mul_of_pos_right _ (D.host.g_prime 1).pos
  have hqle : (WeightAlgebra.qq D : ℝ) ≤ ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by exact_mod_cast hqg.trans hg01
  have hDF' : (WeightAlgebra.DF (lR Tp hK j) : ℝ) * 2 * Real.sqrt ((2 * D.R.f * D.R.m : ℕ) : ℝ) <
      ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by
    have h1 := hDF 0
    have h2 : (D.host.g 0 : ℝ) ≤ ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by exact_mod_cast hg01
    push_cast at h2 ⊢
    linarith
  have h4 : 4 * WeightAlgebra.DF (lR Tp hK j) + 4 ≤ D.host.g 0 * D.host.g 1 := by
    have hc := hH3.2.2.2.2.2
    have hd : (0 : ℝ) ≤ (WeightFamilies.dimY D j : ℝ) := Nat.cast_nonneg _
    have hf : (0 : ℝ) ≤ (WeightAlgebra.DF (lR Tp hK j) : ℝ) := Nat.cast_nonneg _
    have hr : (4 * (WeightAlgebra.DF (lR Tp hK j) : ℝ) + 2) ≤ (WeightAlgebra.qq D : ℝ) := by nlinarith
    have hn : 4 * WeightAlgebra.DF (lR Tp hK j) + 2 ≤ WeightAlgebra.qq D := by exact_mod_cast hr
    have h2 : WeightAlgebra.qq D * 2 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul hqg (D.host.g_prime 1).two_le
    omega
  let _ := T.Q.H.starRing
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hpins.2.2.2 j hj).1, (hpins.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  have hn : Fintype.card (Lt1 (T.Q.Dw j)) ≤ Tp.nWn := by
    refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]
    have : 2 * D.R.f * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := by
      rcases Nat.eq_zero_or_pos D.R.r with h0 | h0
      · simp [h0]
      · calc 2 * D.R.f * D.R.r = D.R.f * D.R.r * 2 := by ring
          _ ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hfin := nuW_le_crude hE hS la T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn (domW_wtA _ _) hn
  have hne_top : nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hfin
    rcases le_total (0 : EReal) (crudeBd la (DF (T.Q.Dw j) (wtA (lR Tp hK j))) : EReal) with h0 | h0
    · rw [max_eq_right h0]; exact EReal.coe_ne_top _
    · rw [max_eq_left h0]; exact EReal.zero_ne_top
  have hne_bot : nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn ≠ ⊥ :=
    ne_bot_of_le_ne_bot EReal.zero_ne_bot (le_max_left _ _)
  have hcoe : nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn =
      (((nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hne_top hne_bot).symm
  have he : (eWL (recB h.toLawsCore).KO la : ℝ) = ramOverZ la := by exact_mod_cast eWL_eq la
  have hr0 : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast ramOverZ_ne_zero la
  have hnus : (runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).nus la =
      (nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn).toReal + (ramOverZ la : ℝ) * clOf (lR Tp hK j) la := by
    show nusOf (recB h.toLawsCore) (lR Tp hK j) (nuWWOf T Tp hK j) la = _
    unfold nusOf
    split
    · next hh => exact absurd hh hg
    · rw [he]
      unfold nuWWOf
      rw [reduce_aux _ _ _ hr0]
      rfl
  obtain ⟨T', io, e, ho, z, hz, eta, heta, hq⟩ := (show T.PtA j la from y).2
  have key := hR L P Tp hK T h hinj EX (nuWWOf T Tp hK) j hj (WeightFamilies.RRv D CR) (WeightFamilies.PPv D L C2 A2) (WeightAlgebra.qq D)
    hjm hE hM hRR' hPP' hq0 hqle hDF' h4 la hg' y T' io e ho z hz eta heta hq
  have hle1 : nuLoc z e T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn ≤
      nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn :=
    le_max_of_le_right (le_iSup_of_le T' (le_iSup_of_le io (le_iSup_of_le e (le_iSup_of_le ho
      (le_iSup_of_le z (le_iSup_of_le hz le_rfl))))))
  refine key.trans ((add_le_add hle1 le_rfl).trans (le_of_eq ?_))
  rw [hcoe, ← EReal.coe_add, hnus]
  congr 1
  unfold WeightAlgebra.cc
  ring

end Formalism.MainNotions.ModuliIntegralCharts.H1
