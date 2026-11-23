import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocallyIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem zeroSetIn_subset_closure_diff (hvan : VanishNearPoint.Statement) {σ : Type} [Fintype σ]
    (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (hI : I.IsPrime) (hh : h ∉ I) :
    zeroSetIn I ⊆ closure (zeroSetIn I \ {z | eval z h = 0}) := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  set e := Fintype.equivFin σ with he
  set J : Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ) := I.comap (rename e.symm) with hJ
  have hre : ∀ q : MvPolynomial (Fin (Fintype.card σ)) ℂ, rename e (rename e.symm q) = q := by
    intro q
    rw [rename_rename, show (⇑e ∘ ⇑e.symm) = id from funext e.apply_symm_apply, rename_id_apply]
  have hre' : ∀ p : MvPolynomial σ ℂ, rename e.symm (rename e p) = p := by
    intro p
    rw [rename_rename, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply, rename_id_apply]
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hmemJ : ∀ y : Fin (Fintype.card σ) → ℂ, y ∘ e ∈ zeroSetIn I → y ∈ zeroLocus J := by
    intro y hy q hq
    rw [← hre q, eval_rename]
    exact hy _ hq
  have hJZ : ∀ y : Fin (Fintype.card σ) → ℂ, y ∈ zeroLocus J → y ∘ e ∈ zeroSetIn I := by
    intro y hy p hp
    have := hy (rename e p) (by rw [hJ, Ideal.mem_comap, hre']; exact hp)
    rwa [eval_rename] at this
  have hx : z ∘ e.symm ∈ zeroLocus J := hmemJ _ (by
    rw [Function.comp_assoc, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply]
    exact hz)
  have hcont : Continuous fun y : Fin (Fintype.card σ) → ℂ => y ∘ e :=
    continuous_pi fun i => continuous_apply _
  have hlim : Filter.Tendsto (fun y : Fin (Fintype.card σ) → ℂ => y ∘ e) (𝓝 (z ∘ e.symm)) (𝓝 z) := by
    have := hcont.tendsto (z ∘ e.symm)
    rwa [Function.comp_assoc, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply,
      Function.comp_id] at this
  have hev : ∀ᶠ y in 𝓝 (z ∘ e.symm), y ∈ zeroLocus J → eval y (rename e h) = 0 := by
    filter_upwards [hlim ht] with y hyt hyJ
    rw [eval_rename]
    by_contra hne'
    exact hne ⟨y ∘ e, hyt, hJZ y hyJ, hne'⟩
  have hmem := hvan _ J (rename e h) _ hJp hx hev
  apply hh
  rw [hJ, Ideal.mem_comap, hre'] at hmem
  exact hmem

theorem NormalLocallyIrreducible.proof (hvan : VanishNearPoint.Statement)
    (hcon : NormalComplementConnected.Statement) : NormalLocallyIrreducible.Statement := by
  intro σ _ I h w hI hnorm hh hw U hU
  obtain ⟨B, hBo, hwB, hBU, hpre⟩ := hcon σ I h w hI hnorm hh hw U hU
  refine ⟨B, hBo, hwB, hBU, hpre, ?_⟩
  rintro z ⟨hzZ, hzB⟩
  have h1 : z ∈ B ∩ closure (zeroSetIn I \ {z | eval z h = 0}) :=
    ⟨hzB, zeroSetIn_subset_closure_diff hvan I h hI hh hzZ⟩
  refine closure_mono ?_ (hBo.inter_closure h1)
  rintro y ⟨hyB, hyZ, hyh⟩
  exact ⟨⟨hyZ, hyB⟩, hyh⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
