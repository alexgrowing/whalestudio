import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviFormGbPotOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

namespace MACompact

variable {D : ℕ} {Ω : Set (Fin D → ℂ)}

theorem maDens_eq_topDens (f ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : f =ᶠ[𝓝 z] fun y => ψ y / 2) : maDens (fun _ : Fin D => f) z = topDens ψ z := by
  have h2 : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ fun y => ψ y / 2) z :=
    h.fderiv.fderiv_eq
  have h3 : hessC f z = cxHessian (fun y => ψ y / 2) z := by
    unfold hessC cxHessian
    rw [h2]
  simp only [maDens, topDens, maDensity, mdisc, mixedDisc, h3]

theorem topDens_congr {ψ ψ' : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : ψ =ᶠ[𝓝 z] ψ') :
    topDens ψ z = topDens ψ' z := by
  have h1 : (fun y => ψ y / 2) =ᶠ[𝓝 z] fun y => ψ' y / 2 := h.fun_comp (· / 2)
  exact (maDens_eq_topDens _ ψ z EventuallyEq.rfl).symm.trans (maDens_eq_topDens _ ψ' z h1)

theorem topDens_continuousOn {ψ : (Fin D → ℂ) → ℝ} (hΩ : IsOpen Ω) (hψ : ContDiffOn ℝ ∞ ψ Ω) :
    ContinuousOn (topDens ψ) Ω := by
  have e : topDens ψ = maDens (fun _ : Fin D => fun y => ψ y / 2) :=
    funext fun z => (maDens_eq_topDens _ ψ z EventuallyEq.rfl).symm
  rw [e]
  exact maDens_continuousOn _ Ω hΩ fun _ => (hψ.div_const 2).of_le (WithTop.coe_le_coe.2 le_top)

def inclChart (hΩ : IsOpen Ω) [Nonempty Ω] : OpenPartialHomeomorph Ω (Fin D → ℂ) :=
  hΩ.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

theorem inclChart_source (hΩ : IsOpen Ω) [Nonempty Ω] : (inclChart hΩ).source = Set.univ := by
  simp [inclChart]

theorem inclChart_target (hΩ : IsOpen Ω) [Nonempty Ω] : (inclChart hΩ).target = Ω := by
  simp [inclChart]

theorem inclChart_symm (hΩ : IsOpen Ω) [Nonempty Ω] (y : Fin D → ℂ) (hy : y ∈ Ω) :
    (((inclChart hΩ).symm y : Ω) : Fin D → ℂ) = y := by
  have h := (inclChart hΩ).right_inv (by rw [inclChart_target]; exact hy)
  simpa [inclChart] using h

def oneChartAtlas (hΩ : IsOpen Ω) [Nonempty Ω] : FinHolAtlas D Ω where
  n := 1
  chart _ := inclChart hΩ
  cover x := ⟨⟨0, Nat.one_pos⟩, by rw [inclChart_source]; trivial⟩
  holo := by
    intro _ _ y hy
    have hyΩ : y ∈ Ω := by rw [← inclChart_target hΩ]; exact hy.1
    refine analyticAt_id.congr ?_
    filter_upwards [hΩ.mem_nhds hyΩ] with z hz
    exact ((inclChart hΩ).right_inv (by rw [inclChart_target]; exact hz)).symm

def j0 (hΩ : IsOpen Ω) [Nonempty Ω] : Fin (oneChartAtlas hΩ).n := ⟨0, Nat.one_pos⟩

theorem oneChartAtlas_index_eq (hΩ : IsOpen Ω) [Nonempty Ω] (j : Fin (oneChartAtlas hΩ).n) : j = j0 hΩ :=
  Fin.ext (by have h1 : j.val < 1 := j.isLt; show j.val = 0; omega)

theorem oneChartAtlas_smooth (hΩ : IsOpen Ω) [Nonempty Ω] {f : (Fin D → ℂ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) : (oneChartAtlas hΩ).Smooth (fun x : Ω => f x) := by
  intro j
  have hs : (inclChart hΩ).target ∩ (inclChart hΩ).symm ⁻¹' Set.univ = Ω := by
    simp [inclChart_target]
  show ContDiffOn ℝ ∞ ((fun x : Ω => f x) ∘ (inclChart hΩ).symm)
    ((inclChart hΩ).target ∩ (inclChart hΩ).symm ⁻¹' Set.univ)
  rw [hs]
  exact hf.congr fun y hy => by simp only [Function.comp_apply, inclChart_symm hΩ y hy]

theorem oneChartAtlas_mInt (hΩ : IsOpen Ω) [Nonempty Ω] (Φ : Fin D → LocPot Ω) (g : Ω → ℝ) :
    mInt (oneChartAtlas hΩ) Φ g =
      ∫ y in Ω, g ((inclChart hΩ).symm y) * locDens (oneChartAtlas hΩ) Φ (j0 hΩ) y := by
  have hne : Nonempty (ChartPartition (oneChartAtlas hΩ)) :=
    ⟨{ χ := fun _ _ => 1
       smooth := fun _ _ => contDiffOn_const
       nonneg := fun _ _ => zero_le_one
       tsupport_subset := fun _ => by
         show _ ⊆ (inclChart hΩ).source
         rw [inclChart_source]; exact Set.subset_univ _
       sum_eq_one := fun _ => by show ∑ _j : Fin 1, (1 : ℝ) = 1; simp }⟩
  rw [mInt, dif_pos hne, integralWith]
  have hχ : ∀ j x, hne.some.χ j x = 1 := by
    intro j x
    have h := hne.some.sum_eq_one x
    rwa [Finset.sum_eq_single j (fun b _ hb => absurd ((oneChartAtlas_index_eq hΩ b).trans (oneChartAtlas_index_eq hΩ j).symm) hb)
      (by simp)] at h
  have hterm : ∀ j : Fin (oneChartAtlas hΩ).n,
      (∫ y in ((oneChartAtlas hΩ).chart j).target,
        hne.some.χ j (((oneChartAtlas hΩ).chart j).symm y) * g (((oneChartAtlas hΩ).chart j).symm y) *
          locDens (oneChartAtlas hΩ) Φ j y) =
      ∫ y in Ω, g ((inclChart hΩ).symm y) * locDens (oneChartAtlas hΩ) Φ (j0 hΩ) y := by
    intro j
    rw [oneChartAtlas_index_eq hΩ j]
    simp only [hχ, one_mul]
    show (∫ y in (inclChart hΩ).target, _) = _
    rw [inclChart_target]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  exact one_smul _ _

theorem oneChartAtlas_locDens (hΩ : IsOpen Ω) [Nonempty Ω] (L : LocPot Ω) (ψ : (Fin D → ℂ) → ℝ)
    (hL : ∀ x x', L.φ x x' = ψ x' / 2) (y : Fin D → ℂ) (hy : y ∈ Ω) :
    locDens (oneChartAtlas hΩ) (fun _ => L) (j0 hΩ) y = topDens ψ y := by
  unfold locDens
  simp only [hL]
  apply maDens_eq_topDens
  filter_upwards [hΩ.mem_nhds hy] with z hz
  show ψ ((inclChart hΩ).symm z : Fin D → ℂ) / 2 = ψ z / 2
  rw [inclChart_symm hΩ z hz]

end MACompact

open MACompact in

theorem MACompact.of_manifold
    (hA : GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange.Statement) :
    MACompact.Statement := by
  rintro D Ω φ v ⟨hΩ, hφ, hv, hvc, hvΩ⟩
  rcases Ω.eq_empty_or_nonempty with rfl | hne
  · simp
  have : Nonempty Ω := hne.to_subtype
  set T := tsupport v with hT
  let P : LocPot Ω := LocPot.ofFun fun x => φ x / 2
  let w : Ω → ℝ := fun x => v x / 2
  let K : Set Ω := Subtype.val ⁻¹' T
  have hKc : IsCompact K := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.2 hvΩ]
    exact hvc
  have hwK : tsupport w ⊆ K := by
    refine closure_minimal ?_ ((isClosed_tsupport v).preimage continuous_subtype_val)
    intro x hx
    exact subset_tsupport v fun h0 => hx (by simp [w, h0])
  have hmain := hA (oneChartAtlas hΩ) P w K
    ⟨isPotential_ofFun _ _ (oneChartAtlas_smooth hΩ (hφ.div_const 2)),
      oneChartAtlas_smooth hΩ (hv.div_const 2),
      hKc.of_isClosed_subset (isClosed_tsupport w) hwK, hKc, hwK⟩
  rw [oneChartAtlas_mInt, oneChartAtlas_mInt] at hmain
  have hind : ∀ y ∈ Ω, K.indicator (1 : Ω → ℝ) ((inclChart hΩ).symm y) =
      T.indicator (1 : (Fin D → ℂ) → ℝ) y := by
    intro y hy
    have hm : (inclChart hΩ).symm y ∈ K ↔ y ∈ T := by
      show (((inclChart hΩ).symm y : Ω) : Fin D → ℂ) ∈ T ↔ y ∈ T
      rw [inclChart_symm hΩ y hy]
    by_cases h : y ∈ T
    · rw [Set.indicator_of_mem (hm.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (mt hm.1 h), Set.indicator_of_notMem h]
  have hL1 : Set.EqOn (fun y => K.indicator 1 ((inclChart hΩ).symm y) *
      locDens (oneChartAtlas hΩ) (fun _ => P + LocPot.ofFun w) (j0 hΩ) y)
      (T.indicator (topDens (φ + v))) Ω := by
    intro y hy
    simp only
    rw [hind y hy, oneChartAtlas_locDens hΩ _ (φ + v) (fun x x' => by
      show φ x' / 2 + v x' / 2 = (φ + v) x' / 2
      rw [Pi.add_apply, add_div]) y hy]
    by_cases h : y ∈ T <;> simp [h]
  have hL2 : Set.EqOn (fun y => K.indicator 1 ((inclChart hΩ).symm y) *
      locDens (oneChartAtlas hΩ) (fun _ => P) (j0 hΩ) y) (T.indicator (topDens φ)) Ω := by
    intro y hy
    simp only
    rw [hind y hy, oneChartAtlas_locDens hΩ _ φ (fun x x' => rfl) y hy]
    by_cases h : y ∈ T <;> simp [h]
  rw [setIntegral_congr_fun hΩ.measurableSet hL1, setIntegral_congr_fun hΩ.measurableSet hL2]
    at hmain
  have hint : ∀ ψ : (Fin D → ℂ) → ℝ, ContDiffOn ℝ ∞ ψ Ω →
      IntegrableOn (T.indicator (topDens ψ)) Ω := fun ψ hψ =>
    (((topDens_continuousOn hΩ hψ).mono hvΩ).integrableOn_compact hvc).integrable_indicator
      (isClosed_tsupport v).measurableSet |>.integrableOn
  have heq : Set.EqOn (fun z => topDens (φ + v) z - topDens φ z)
      (fun z => T.indicator (topDens (φ + v)) z - T.indicator (topDens φ) z) Ω := by
    intro z _
    by_cases hz : z ∈ T
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, sub_zero, sub_eq_zero]
      exact topDens_congr ((notMem_tsupport_iff_eventuallyEq.1 hz).mono fun y hy => by
        simp only [Pi.add_apply, hy, Pi.zero_apply, add_zero])
  rw [setIntegral_congr_fun hΩ.measurableSet heq, integral_sub (hint (φ + v) (hφ.add hv)) (hint φ hφ),
    hmain, sub_self]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
