import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.MajorantW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisBL

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
open GlobalTheory.Cont PositivityTheory.SiegelWeilFormula.Khead
namespace PositivityTheory.SiegelWeilFormula.Aeis
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem majorant_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) :
    ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ C : Set d.G, IsCompact C →
      ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q := by
  have hKc : IsCompact (d.K : Set d.G) := _root_.PositivityTheory.SiegelWeilFormula.Aeis.isCompact_K_w_k d.ok.good d.ok.stdK
  obtain ⟨hac, hpos⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.height_pos_w_k d.ok.good d.ok.stdK d.ok.hgt
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.flat_section_growth_bound d.K d.a hKc d.ok.hgt hpos d.χ s₁ f hf
  obtain ⟨σ₀, hσ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.godement_sum_w_k d.ok.good d.ok.frame d.ok.stdK d.ok.hgt
  refine ⟨σ₀ - (d.n : ℝ) / 2, fun z hz C hC => ?_⟩
  set σ' : ℝ := z.re + (d.n : ℝ) / 2 with hσ'
  have h1 : σ₀ < σ' := by linarith
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup d.G := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hKC : IsCompact ((d.K : Set d.G) * C) := hKc.mul hC
  obtain ⟨M, hM⟩ := hKC.exists_bound_of_continuousOn hac.continuousOn
  obtain ⟨M', hM'⟩ := hKC.exists_bound_of_continuousOn (hac.inv₀ fun y => (hpos y).ne').continuousOn
  have hr : ∀ x, ∀ c ∈ C, d.a (x * c) ^ σ' ≤ (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a x ^ σ' := by
    intro x c hc
    obtain ⟨k, hk, e⟩ := hgt_mul_right d.ok.hgt x c
    have hkc : k * c ∈ (d.K : Set d.G) * C := Set.mul_mem_mul hk hc
    have r0 := hpos (k * c)
    have rM : d.a (k * c) ≤ |M| := (Real.le_norm_self _).trans ((hM _ hkc).trans (le_abs_self M))
    have hm := hM' _ hkc
    rw [Pi.inv_apply, norm_inv, Real.norm_of_nonneg r0.le] at hm
    have hM'pos : 0 < |M'| := lt_of_lt_of_le (inv_pos.2 r0) (hm.trans (le_abs_self _))
    have rm : |M'|⁻¹ ≤ d.a (k * c) := (inv_le_comm₀ hM'pos r0).2 (hm.trans (le_abs_self _))
    have hb : d.a (k * c) ^ σ' ≤ |M| ^ σ' + (|M'|⁻¹) ^ σ' := by
      rcases le_total 0 σ' with hs | hs
      · exact (Real.rpow_le_rpow r0.le rM hs).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg (inv_nonneg.2 (abs_nonneg _)) _))
      · exact (Real.rpow_le_rpow_of_nonpos (inv_pos.2 hM'pos) rm hs).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _))
    rw [e, Real.mul_rpow (hpos x).le r0.le, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (hpos x).le _)
  obtain ⟨_, _, hsum⟩ := hσ σ' h1
  refine ⟨fun q => |C0| * (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a ((Quotient.out q).1 * 1) ^ σ', (hsum 1).1.mul_left _,
    fun g hg q => ?_⟩
  have hΦ : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) = flat d.a f s₁ z := funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, flat]
    rw [Real.coe_toNNReal _ (hpos y).le]
  rw [hΦ]
  show ‖flat d.a f s₁ z ((Quotient.out q).1 * g)‖ ≤ _
  simp only [mul_one]
  calc _ ≤ C0 * d.a ((Quotient.out q).1 * g) ^ σ' := hC0 z _
    _ ≤ |C0| * d.a ((Quotient.out q).1 * g) ^ σ' := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (hpos _).le _)
    _ ≤ |C0| * ((|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a (Quotient.out q).1 ^ σ') :=
        mul_le_mul_of_nonneg_left (hr _ g hg) (abs_nonneg _)
    _ = _ := by ring
theorem eisWk_k : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k := by
  intro F E _ _ _ _ _ σ d s₁ f hf s₀
  obtain ⟨Ê, ⟨t, hsum, hdiff⟩, hw⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisBLW_k F E σ d.B d.n d.Y d.ok.good d.ok.hn d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt s₁ f hf
  have hp : ∀ s₀ : ℂ, ∃ (k : ℕ) (H : ℂ → d.G → ℂ), An.Reg (fun x : d.G => (ht2 x : ℝ)) H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * Ê s x := by
    intro s₀
    obtain ⟨k, U, H, hU, he, hd⟩ := hw s₀
    refine ⟨k, fun s => (H s).1, reg_of_weak hU hd, ?_⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hU, self_mem_nhdsWithin] with s hs hne
    exact he s hs hne
  have hr : ∀ s : ℂ, t < s.re → An.Reg (fun x : d.G => (ht2 x : ℝ)) Ê s := fun s hs => by
    obtain ⟨k, H, a, e⟩ := hp s
    exact a.remove one_le_height_GL2 e ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) hdiff
  obtain ⟨U, p, G, hUo, hUr, hs₀, hp0, hreg, heq⟩ := strip one_le_height_GL2 hp hr s₀
  obtain ⟨hGd, hGc⟩ := diff_cont_of_reg hreg
  obtain ⟨t2, hmaj⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.majorant_w_k d hf
  have hinv := eis_left_rat_w d.ok.hgt hf d.ok.hecke t Ê hsum
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s₁) * f y) = flat d.a f s₁ z := fun z => funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, flat]
    rw [Real.coe_toNNReal _ (GlobalTheory.CompanionTheory.EisRat.hgt_nonneg d.ok.hgt y)]
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → ∀ g, d.eis f s₁ z g = Ê z g := fun z hz g => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis]
    rw [hfl z]
    exact (hsum z hz g).tsum_eq
  refine ⟨U, p, G, max t t2, hUo, hUr, hs₀, hp0, hGd, hGc, ?_, fun z hz =>
    ⟨hmaj z (lt_of_le_of_lt (le_max_right _ _) hz), fun g => ?_⟩⟩
  · intro z hz γ hγ g
    obtain ⟨τ, hτ⟩ := hUr.1
    have han : ∀ x, AnalyticOnNhd ℂ (G · x) U := fun x => (hGd x).analyticOnNhd hUo
    have hz₀ : (((max τ t + 1 : ℝ)) : ℂ) ∈ rightOf (max τ t) := by simp
    refine (han (γ * g)).eqOn_of_preconnected_of_eventuallyEq (han g) hUr.isPreconnected
      (hτ (rightOf_subset (le_max_left _ _) hz₀)) ?_ hz
    filter_upwards [(isOpen_rightOf _).mem_nhds hz₀] with w hw
    have hw' : t < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    rw [heq w hw', heq w hw', hinv w hw' γ hγ g]
  · have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
    rw [heq z hz1, Heisenberg₂ z hz1]
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
