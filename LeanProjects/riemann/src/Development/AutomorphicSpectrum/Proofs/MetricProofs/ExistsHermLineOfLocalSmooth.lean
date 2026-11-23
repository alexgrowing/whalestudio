import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariant

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace CExt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth Topology Filter Set
open scoped Manifold

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def colMap (p : (k : K) → ι k) (m : (Σ k, ι k × ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => m ⟨q.1, (q.2, p q.1)⟩

theorem colMap_contDiff (p : (k : K) → ι k) {n : WithTop ℕ∞} : ContDiff ℝ n (colMap p) :=
  contDiff_pi.2 fun q => contDiff_apply ℝ ℂ (⟨q.1, (q.2, p q.1)⟩ : Σ k, ι k × ι k)

theorem sameOrbit_colMap {p : (k : K) → ι k} {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι)
    (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) : SameOrbit (colMap p (prMap z)) z := by
  refine ⟨fun k => (starRingEnd ℂ) (z ⟨k, p k⟩) / (blockSq z k : ℂ), fun k =>
    div_ne_zero ((map_ne_zero _).2 (hp k)) (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne'), ?_⟩
  funext q
  simp only [colMap, prMap]
  ring

theorem prMap_diag_ne_zero {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι) {k : K} {i : ι k}
    (hi : z ⟨k, i⟩ ≠ 0) : prMap z ⟨k, (i, i)⟩ ≠ 0 :=
  div_ne_zero (mul_ne_zero hi ((map_ne_zero _).2 hi))
    (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne')

theorem ne_zero_of_prMap_diag {z : (Σ k, ι k) → ℂ} {k : K} {i : ι k}
    (h : prMap z ⟨k, (i, i)⟩ ≠ 0) : z ⟨k, i⟩ ≠ 0 := by
  intro h0
  apply h
  simp [prMap, h0]

theorem isClosed_prMap_image {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsClosed (prMap '' mcPts P) := by
  have hA : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hC := (isCompact_unitBlocks (K := K) (ι := ι)).inter_right hA
  have hcont : ContinuousOn (prMap (K := K) (ι := ι)) (unitBlocks K ι ∩
      {z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}) := fun z hz =>
    (prMap_continuousAt (unitBlocks_subset hz.1)).continuousWithinAt
  convert (hC.image_of_continuousOn hcont).isClosed using 1
  ext m
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, hc, hu⟩ := exists_normalize (K := K) (ι := ι) hz.1
    exact ⟨_, ⟨hu, (mcPts_smul hP c hc hz).2⟩, prMap_smul c z hc⟩
  · rintro ⟨z, ⟨hu, hz⟩, rfl⟩
    exact ⟨z, ⟨unitBlocks_subset hu, hz⟩, rfl⟩

theorem exists_smooth_on_matrices {P : Ideal (MRing ι)} {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hP : IsMultiHomogIdeal P) (hinv : ∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') :
    ∃ g : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ z ∈ mcPts P, g (prMap z) = u z := by
  have ht : ∀ m : (Σ k, ι k × ι k) → ℂ,
      Convex ℝ {r : ℝ | ∀ z ∈ mcPts P, prMap z = m → r = u z} := by
    intro m x hx y hy a b _ _ hab z hz hzm
    rw [smul_eq_mul, smul_eq_mul, hx z hz hzm, hy z hz hzm, ← add_mul, hab, one_mul]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := (⊤ : ℕ∞))
    (M := (Σ k, ι k × ι k) → ℂ) (F := ℝ) 𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) ht (fun x => by
    by_cases hx : x ∈ prMap '' mcPts P
    · obtain ⟨z₀, hz₀, rfl⟩ := hx
      choose p hp using hz₀.1
      obtain ⟨V, w, hV, hmem, hw, hwu⟩ := hloc (colMap p (prMap z₀))
        (mem_mcPts_of_sameOrbit hP (sameOrbit_colMap hz₀.1 hp) hz₀)
      have hO : IsOpen (colMap p ⁻¹' V ∩ {m | ∀ k, m ⟨k, (p k, p k)⟩ ≠ 0}) := by
        refine (hV.preimage (colMap_contDiff p (n := 0)).continuous).inter ?_
        simp only [setOf_forall]
        exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
      refine ⟨_, hO.mem_nhds ⟨hmem, fun k => prMap_diag_ne_zero hz₀.1 (hp k)⟩, w ∘ colMap p, ?_, ?_⟩
      · exact contMDiffOn_iff_contDiffOn.2
          (hw.comp (colMap_contDiff p).contDiffOn fun y hy => hy.1)
      · rintro y ⟨hy1, hy2⟩ z hz rfl
        have ho := sameOrbit_colMap hz.1 fun k => ne_zero_of_prMap_diag (hy2 k)
        show w (colMap p (prMap z)) = u z
        rw [hwu _ ⟨hy1, mem_mcPts_of_sameOrbit hP ho hz⟩]
        exact hinv z hz _ ho
    · refine ⟨_, (isClosed_prMap_image hP).isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy z hz hzy
      exact absurd ⟨z, hz, hzy⟩ hy)
  exact ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z hz => hg _ z hz rfl⟩

variable (ι) in

def expLine (g : ((Σ k, ι k × ι k) → ℂ) → ℝ) : HermLine ι where
  a := 0
  h z := by
    classical
    exact if z ∈ nzBlocks K ι then Real.exp (g (prMap z)) else 1
  pos z hz := by
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  smul c z hc := by
    classical
    have hiff : (fun p : Σ k, ι k => c p.1 * z p) ∈ nzBlocks K ι ↔ z ∈ nzBlocks K ι := by
      refine forall_congr' fun k => exists_congr fun i => ?_
      simp [hc k]
    simp only [hiff, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul, prMap_smul c z hc]

end CExt

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem exists_hermLine_of_local_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (u : ((Σ k, ι k) → ℂ) → ℝ), IsMultiHomogIdeal P → (∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') → ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ z ∈ mcPts P, Real.log (B.h z) = u z := by
  intro K _ ι _ P u hP hinv hloc
  obtain ⟨g, hg, hgu⟩ := CExt.exists_smooth_on_matrices hP hinv hloc
  refine ⟨CExt.expLine ι g, rfl, ?_, fun z hz => ?_⟩
  · have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)))
        (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.nzBlocks K ι) :=
      Real.contDiff_exp.comp_contDiffOn
        (hg.comp_contDiffOn GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap_contDiffOn)
    refine h1.congr fun z hz => ?_
    exact if_pos hz
  · have h2 : (CExt.expLine ι g).h z = Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)) :=
      if_pos hz.1
    rw [h2, Real.log_exp, hgu z hz]

end GlobalTheory.CompanionTheory.Ar.PB
