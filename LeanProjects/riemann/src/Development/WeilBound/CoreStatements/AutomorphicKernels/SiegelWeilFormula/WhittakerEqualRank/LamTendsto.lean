import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerEqualRank.UnrXDifferentiable

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter PositivityTheory.SiegelWeilFormula.Gen.W
open scoped TensorProduct Matrix Topology Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_gt (S : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (Z H : ℂ → ℂ)
    (hp : ∀ s : ℂ, 1 < s.re →
      HasProd (fun v : {v // v ∉ S} => 1 - c v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s))
    (j : ℂ) (hj : 1 < j.re) (hH : AnalyticAt ℂ H j) (he : ∀ᶠ s in 𝓝[≠] j, H s = Z s) : H j = Z j := by
  obtain ⟨d, hd, hdp⟩ := euler_prod (ι := {v // v ∉ S}) (fun v => Ideal.absNorm v.1.asIdeal)
    (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
    (fun s hs => (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective
      (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective))
    (fun v => c v.1) (fun v => hc v.1) 0
  have hZd : ∀ s : ℂ, 1 < s.re → Z s = d ((s - 1) / 2) := by
    intro s hs
    have h1 : 0 < ((s - 1) / 2).re := by simp; linarith
    refine (hp s hs).unique ?_
    convert hdp _ h1 using 3 with v
    push_cast
    ring_nf
  have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcd : ContinuousAt (fun s : ℂ => d ((s - 1) / 2)) j := by
    have h1 : 0 < ((j - 1) / 2).re := by simp; linarith
    have hdo : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have := (hd.differentiableAt (hdo.mem_nhds h1)).continuousAt
    exact ContinuousAt.comp (g := d) (f := fun s : ℂ => (s - 1) / 2) this
      ((continuous_id.sub continuous_const).div_const 2).continuousAt
  have hev : H =ᶠ[𝓝[≠] j] fun s => d ((s - 1) / 2) := by
    filter_upwards [he, nhdsWithin_le_nhds (ho.mem_nhds hj)] with s hs hs'
    rw [hs, hZd s hs']
  have t1 : Tendsto H (𝓝[≠] j) (𝓝 (H j)) := hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto H (𝓝[≠] j) (𝓝 (d ((j - 1) / 2))) :=
    (hcd.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  rw [tendsto_nhds_unique t1 t2, hZd j hj]

theorem lam_tendsto (S : Finset (HeightOneSpectrum (𝓞 F))) (Z H : ℂ → ℂ)
    (hp : ∀ s : ℂ, 1 < s.re →
      HasProd (fun v : {v // v ∉ S} => 1 - eSp E v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s))
    (hH : AnalyticAt ℂ H 1) (he : ∀ᶠ s in 𝓝[≠] (1 : ℂ), H s = Z s) :
    Tendsto (fun s : ℝ => ∏' v : HeightOneSpectrum (𝓞 F),
          (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) (𝓝[>] 1)
      (𝓝 ((∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) * H 1)) := by
  have hofR : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds |>.trans (by simp))
      (eventually_nhdsWithin_of_forall fun s hs => ?_)
    show (s : ℂ) ≠ 1
    exact_mod_cast ne_of_gt (show (1 : ℝ) < s from hs)
  have hH1 : Tendsto (fun s : ℝ => H s) (𝓝[>] 1) (𝓝 (H 1)) :=
    (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).comp hofR
  have hfin : Tendsto (fun s : ℝ => ∏ v ∈ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) (𝓝[>] 1)
      (𝓝 (∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ)))) := by
    have hc : Continuous (fun s : ℝ => ∏ v ∈ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) := by
      refine continuous_finsetProd S fun v _ => continuous_const.sub (continuous_const.mul ?_)
      have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
        have := NumberField.HeightOneSpectrum.one_lt_absNorm v
        exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
      exact Continuous.const_cpow (Complex.continuous_ofReal.neg) (Or.inl hq)
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    convert this using 2
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [Complex.cpow_neg_one, div_eq_mul_inv]
  refine (hfin.mul hH1).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hofR.eventually he] with s hs hs'
  have hs1 : 1 < ((s : ℂ)).re := by simpa using hs
  rw [((hasProd_split' (fun v => 1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) S _
    (hp s hs1)).tprod_eq), hs']

end PositivityTheory.SiegelWeilFormula.Gen.WQ

end
