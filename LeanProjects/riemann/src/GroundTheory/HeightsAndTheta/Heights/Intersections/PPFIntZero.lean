import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFIntZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExMapAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFIntZeroMixed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def eulerDirs {n : ℕ} (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∃ c : K → ℂ, fderiv ℂ F y x = bsmul c (F y)}
  add_mem' := by
    rintro x x' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', by rw [map_add, hc, hc']; funext p; simp [bsmul, add_mul]⟩
  zero_mem' := ⟨0, by rw [map_zero]; funext p; simp [bsmul]⟩
  smul_mem' := by
    rintro a x ⟨c, hc⟩
    exact ⟨a • c, by rw [map_smul, hc]; funext p; simp [bsmul, mul_assoc]⟩

theorem eulerDirs_finrank (hR : pointFormRank_holds.Statement) {Q : Ideal (MRing ι)} {d n : ℕ} (hQ : IsArithVar Q d)
    {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ} (hF : AnalyticAt ℂ F y)
    (hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) : n < Module.finrank ℂ (eulerDirs F y) + d := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (eulerDirs F y)
  have hsum := Submodule.finrank_add_eq_of_isCompl hU
  rw [Module.finrank_fin_fun] at hsum
  have hdm : d ≤ Module.finrank ℂ U := by omega
  set bU := Module.finBasis ℂ U
  let Mlin : (Fin (Module.finrank ℂ U) → ℂ) →ₗ[ℂ] (Fin n → ℂ) := U.subtype ∘ₗ bU.equivFun.symm.toLinearMap
  let M : (Fin (Module.finrank ℂ U) → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap Mlin
  have hMU : ∀ x, M x ∈ U := fun x => Submodule.coe_mem (bU.equivFun.symm x)
  have hMinj : Function.Injective M := fun a b h => bU.equivFun.symm.injective (Subtype.ext h)
  have hA : HasFDerivAt (fun y' => y + M y') M 0 := (M.hasFDerivAt).const_add y
  have hy : y + M 0 = y := by rw [map_zero, add_zero]
  have hF' : AnalyticAt ℂ F (y + M 0) := by rw [hy]; exact hF
  have hGa : AnalyticAt ℂ (fun y' => F (y + M y')) 0 :=
    hF'.comp (f := fun y' => y + M y') (analyticAt_const.add (M.analyticAt 0))
  have hGQ : ∀ᶠ y' in 𝓝 (0 : Fin (Module.finrank ℂ U) → ℂ), F (y + M y') ∈ mcPts Q := by
    have ht : Tendsto (fun y' => y + M y') (𝓝 0) (𝓝 y) := by
      have := hA.continuousAt.tendsto
      rwa [hy] at this
    exact ht.eventually hFQ
  obtain ⟨x, hx, c, hxc⟩ := hR K ι Q d _ (fun y' => F (y + M y')) 0 hQ hdm hGa hGQ
  have hFd : HasFDerivAt F (fderiv ℂ F y) (y + M 0) := by rw [hy]; exact hF.differentiableAt.hasFDerivAt
  have hGd : HasFDerivAt (fun y' => F (y + M y')) ((fderiv ℂ F y).comp M) 0 :=
    hFd.comp (f := fun y' => y + M y') 0 hA
  rw [hGd.fderiv, ContinuousLinearMap.comp_apply, hy] at hxc
  have hmem : M x ∈ eulerDirs F y ⊓ U := ⟨⟨c, hxc⟩, hMU x⟩
  rw [hU.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hx (hMinj (by rw [hmem, map_zero]))

theorem map_star_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    M.map (starRingEnd ℂ) *ᵥ x = star (M *ᵥ star x) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem PFIntZero.maDensity_eq_zero (hR : pointFormRank_holds.Statement)
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d r : ℕ}
    {L : Fin d → HermLine ι} {L' : Fin d → HermLine ι'} (N : Fin r → HermLine ι') (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (d + r + 1) → ℂ)} {y : Fin (d + r) → ℂ}
    {w : ((k : K') → ι' k) → ℂ} {γ : (Fin (d + r) → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((Fin.append L' N j).h (γ y'))) y = 0 := by
  set F : (Fin (d + r) → ℂ) → (Σ k, ι k) → ℂ := fun y' p => γ y' (v p) with hF
  have hγa : AnalyticAt ℂ γ y := sheet_analyticAt osgood hγ
  have hFa : AnalyticAt ℂ F y := analyticAt_pi_iff.mpr fun p => analyticAt_coord hγa (v p)
  have hFy : ∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0 := blocks_ne_zero_restrict hv hγ.2.self_of_nhds.2.1.1
  have hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts (imageZ v P') := by
    filter_upwards [hγ.2] with y' h
    refine ⟨blocks_ne_zero_restrict hv h.2.1.1, fun f hf => ?_⟩
    have h0 := h.2.1.2 _ (Ideal.mem_comap.mp hf)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h0
    exact h0
  set A : Fin (d + r) → Matrix (Fin (d + r)) (Fin (d + r)) ℂ :=
    fun j => cxHessian (fun y' => Real.log ((Fin.append L' N j).h (γ y'))) y with hAdef
  have hker : ∀ k ∈ Finset.univ.map (Fin.castAddEmb r), ∀ x ∈ eulerDirs F y,
      (A k).map (starRingEnd ℂ) *ᵥ x = 0 := by
    intro k hk x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨c, hc⟩ := hx
    have hpot : (fun y' => Real.log ((Fin.append L' N (Fin.castAddEmb r j)).h (γ y'))) =
        fun y' => Real.log ((L j).h (F y')) := by
      funext y'
      rw [Fin.coe_castAddEmb, Fin.append_left, (hLL j).2]
    have h := pointFormEuler_holds.proof K ι (L j) (d + r) F y x c (hL j) hFa hFy hc
    rw [map_star_mulVec, hAdef]
    simp only
    rw [hpot, h, star_zero]
  have hmix := mixedDisc_eq_zero_of_ker (fun k => (A k).map (starRingEnd ℂ)) (eulerDirs F y) _
    (by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]; exact eulerDirs_finrank hR hQ hFa hFQ) hker
  rw [mixedDisc_map_star, map_eq_zero] at hmix
  show _ * _ * (mixedDisc A).re = 0
  rw [hmix, Complex.zero_re, mul_zero]

theorem PFIntZero.proof (hR : pointFormRank_holds.Statement) : PFIntZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N A s hv _ hQ hL hLL
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P' hΨ.choose (fun j z => Real.log ((Fin.append L' N j).h z)) (logNorm A s) y w
        = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · exact mul_eq_zero_of_right _ (PFIntZero.maDensity_eq_zero hR N hv hQ hL hLL hγ.choose_spec)
      · rfl
    simp [h0]
  · rfl

end GroundTheory.Heights₂.Heights.Inter
