import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.MixedIntegralInclusionExclusion
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

private theorem fderiv2_add_lemma {D : ℕ} {g₁ g₂ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    {y : Fin D → ℂ} (hU : IsOpen U) (hy : y ∈ U) (h₁ : ContDiffOn ℝ 2 g₁ U) (h₂ : ContDiffOn ℝ 2 g₂ U) :
    fderiv ℝ (fderiv ℝ (fun z => g₁ z + g₂ z)) y = fderiv ℝ (fderiv ℝ g₁) y + fderiv ℝ (fderiv ℝ g₂) y := by
  have hev : fderiv ℝ (fun z => g₁ z + g₂ z) =ᶠ[𝓝 y] fun z => fderiv ℝ g₁ z + fderiv ℝ g₂ z := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact fderiv_add ((h₁.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      ((h₂.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  exact fderiv_add
    (((h₁.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (((h₂.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

private theorem hessL_add_lemma_2 {D : ℕ} (H₁ H₂ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    hessL (H₁ + H₂) = hessL H₁ + hessL H₂ := by
  funext i k
  simp only [hessL, ContinuousLinearMap.add_apply, Pi.add_apply]
  push_cast
  ring

theorem conv_dens_of_open {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (V : Set X) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ)
    (phT : Fin e → ℝ → X → ℝ) (hB : IsOpen V) (hΘ : IsPotential A Θ)
    (hth : ∀ i, IsPotential A (th i)) (hph : ∀ i, A.SmoothOn V (ph i))
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ i, A.Smooth (phT i t))
    (hC2 : ∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V, IsCompact K' →
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT i t ∘ (A.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph i ∘ (A.chart j).symm))) (nhdsWithin 0 (Set.Ioi 0)) K')
    (j : Fin A.n) (K : Set (Fin e → ℂ))
    (hK : K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V) (hKc : IsCompact K) :
    TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
      (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (nhdsWithin 0 (Set.Ioi 0)) K := by
  classical
  have hS : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) :=
    (A.chart j).isOpen_inter_preimage_symm hB
  let a : Fin e → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k y =>
    hessC (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y
  let b : (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun y =>
    hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y
  let q : Fin e → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k y =>
    hessL (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) y)
  let p : Fin e → ℝ → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k t y =>
    hessL (fderiv ℝ (fderiv ℝ (phT k t ∘ (A.chart j).symm)) y)

  have hsplit : ∀ (k : Fin e) (u : X → ℝ) (W : Set (Fin e → ℂ)) (y : Fin e → ℂ), IsOpen W → y ∈ W →
      y ∈ (A.chart j).target → ContDiffOn ℝ 2 (u ∘ (A.chart j).symm) W →
      hessC (fun y' => (th k + LocPot.ofFun u + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
        a k y + hessL (fderiv ℝ (fderiv ℝ (u ∘ (A.chart j).symm)) y) + b y := by
    intro k u W y hW hyW hyt hu
    have h1 : ContDiffOn ℝ 2 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) :=
      contDiffOn_infty.1 ((hth k).1 ((A.chart j).symm y) j) 2
    have h3 : ContDiffOn ℝ 2 (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y'))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y)) :=
      contDiffOn_infty.1 (hΘ.1 ((A.chart j).symm y) j) 2
    have o1 := (A.chart j).isOpen_inter_preimage_symm ((th k).isOpen_U ((A.chart j).symm y))
    have o3 := (A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U ((A.chart j).symm y))
    have oU := (o1.inter hW).inter o3
    have mU : y ∈ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) ∩ W ∩
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y)) :=
      ⟨⟨⟨hyt, (th k).mem_U _⟩, hyW⟩, ⟨hyt, Θ.mem_U _⟩⟩
    have hu' : ContDiffOn ℝ 2 (fun y' => u ((A.chart j).symm y')) W := hu
    have e12 : ContDiffOn ℝ 2 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
        u ((A.chart j).symm y'))
        (((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) ∩ W ∩
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y))) :=
      (h1.mono fun z hz => hz.1.1).add (hu'.mono fun z hz => hz.1.2)
    show hessL (fderiv ℝ (fderiv ℝ (fun y' => ((th k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
      u ((A.chart j).symm y')) + Θ.φ ((A.chart j).symm y) ((A.chart j).symm y'))) y) = _
    rw [fderiv2_add_lemma oU mU e12 (h3.mono fun z hz => hz.2),
      fderiv2_add_lemma oU mU (h1.mono fun z hz => hz.1.1) (hu'.mono fun z hz => hz.1.2),
      hessL_add_lemma_2, hessL_add_lemma_2]
    rfl

  have hq0 : ∀ k, ContinuousOn (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) := fun k =>
    ((contDiffOn_infty.1 (hph k j) 2).fderiv_of_isOpen hS (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
      hS (by norm_num)
  have hq_cont : ∀ k, ContinuousOn (q k) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) := fun k =>
    continuous_hessL.comp_continuousOn (hq0 k)
  have hpq : ∀ k, TendstoUniformlyOn (p k) (q k) (nhdsWithin 0 (Set.Ioi 0)) K := by
    intro k
    have hbdd : Bornology.IsBounded (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) '' K) :=
      (hKc.image_of_continuousOn ((hq0 k).mono hK)).isBounded
    exact tendstoUniformlyOn_comp_continuous hessL continuous_hessL _ _ hbdd (hC2 k j K hK hKc)
  have hW : TendstoUniformlyOn (fun t y => fun k => a k y + p k t y + b y)
      (fun y k => a k y + q k y + b y) (nhdsWithin 0 (Set.Ioi 0)) K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hk : ∀ k, ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ y ∈ K, dist (q k y) (p k t y) < ε :=
      fun k => Metric.tendstoUniformlyOn_iff.1 (hpq k) ε hε
    filter_upwards [Filter.eventually_all.2 hk] with t ht y hy
    rw [dist_pi_lt_iff hε]
    intro k
    rw [dist_add_right, dist_add_left]
    exact ht k y hy
  have hWc : ContinuousOn (fun y k => a k y + q k y + b y) K := by
    refine continuousOn_pi.2 fun k => ?_
    have ha : ContinuousOn (a k) (A.chart j).target := hessC_base_continuousOn A (th k) (hth k) j
    have hb : ContinuousOn b (A.chart j).target := hessC_base_continuousOn A Θ hΘ j
    exact ((ha.mono fun z hz => (hK hz).1).add ((hq_cont k).mono hK)).add (hb.mono fun z hz => (hK hz).1)
  have hG : Continuous (fun w : Fin e → Fin e → Fin e → ℂ =>
      (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => w k).re) := by
    simp only [mdisc]
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    refine continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_const.mul ?_)
    exact Continuous.matrix_det (continuous_finsetSum _ fun k _ => continuous_apply k)
  have hmain := tendstoUniformlyOn_comp_continuous _ hG _ _
    (hKc.image_of_continuousOn hWc).isBounded hW
  refine (hmain.congr ?_).congr_right ?_
  · filter_upwards [hT] with t ht y hy
    have hfun : (fun k => a k y + p k t y + b y) = fun k => hessC
        (fun y' => (th k + LocPot.ofFun (phT k t) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
      funext fun k => (hsplit k (phT k t) _ y ((A.chart j).isOpen_inter_preimage_symm isOpen_univ)
        ⟨(hK hy).1, trivial⟩ (hK hy).1 (contDiffOn_infty.1 (ht k j) 2)).symm
    show (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => (fun k => a k y + p k t y + b y) k).re = _
    rw [hfun]
    rfl
  · intro y hy
    have hfun : (fun k => a k y + q k y + b y) = fun k => hessC
        (fun y' => (th k + LocPot.ofFun (ph k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
      funext fun k => (hsplit k (ph k) _ y hS (hK hy) (hK hy).1 (contDiffOn_infty.1 (hph k j) 2)).symm
    show (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => (fun k => a k y + q k y + b y) k).re = _
    rw [hfun]
    rfl

end GlobalTheory.CompanionTheory.Ar.Giv
