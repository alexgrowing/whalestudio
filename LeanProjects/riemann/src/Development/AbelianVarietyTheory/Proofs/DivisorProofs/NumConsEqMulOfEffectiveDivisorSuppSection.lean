import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycle
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush.Dbl

theorem num_cons_eq_mul_of_supp_eq_range : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ Θ : CartierDiv W.Z, Θ.Eff → (Θ.supp : Set W.Z) = Set.range W.δ → ∃ μ : ℤ, μ ≠ 0 ∧ ∀ y : Fin Y.dim → CartierDiv W.Z, letI := algebraΓOfHom (W.p₁ ≫ Y.str); W.num (Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) = μ * interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) fun i => toLB (y i) := by
  intro F _ Y W hW Θ hΘ hsupp
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hstr : strHom F W.Z = W.p₁ ≫ Y.str := GlobalTheory.strHom_eq fun _ => rfl
  have hp : IsProjOver (strHom F W.Z) := hstr ▸ W.proj
  have : IsLocallyNoetherian W.Z := by
    obtain ⟨N, ι, _, h⟩ := hp
    have : LocallyOfFiniteType (strHom F W.Z) := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (strHom F W.Z)
  obtain ⟨s, hs, e⟩ := GlobalTheory.RatSecCycle.exists_sec_divOfSec_eq Θ hΘ
  set η := genericPoint Y.X
  set w₀ := W.δ η
  have hδ := W.δ.isClosedEmbedding
  have hcl : closure ({w₀} : Set W.Z) = Set.range W.δ := by
    rw [← Set.image_singleton, hδ.closure_image_eq, (genericPoint_spec Y.X).def, Set.image_univ]
  have hd : topologicalKrullDim (closure ({w₀} : Set W.Z)) = Y.dim := by
    rw [topologicalKrullDim_eq_of_isEmbedding hδ.isEmbedding hcl.symm, Y.topologicalKrullDim_eq]
  have hw₀ : w₀ ∈ Θ.supp := by
    show w₀ ∈ (Θ.supp : Set W.Z); rw [hsupp]; exact ⟨η, rfl⟩
  have hmax : ¬ IsMax w₀ := fun h =>
    Θ.genericPoint_notMem_supp ((h (genericPoint_specializes w₀)).mem_closed Θ.supp.isClosed hw₀)
  have hc := GlobalTheory.SecCycle.coheight_eq_one_of_dim_closure hW hmax hd
  refine ⟨Θ.mult w₀, ?_, fun y => ?_⟩
  · have hws : w₀ ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := fun h =>
      (GlobalTheory.Cartier.notMem_supp_divOfSec.2 h) (e.symm ▸ hw₀)
    have := GlobalTheory.SecCycle.mult_divOfSec_ne_zero (isLB_toLB Θ) s hs hc hws
    rwa [e] at this
  · have hcons : (fun i => toLB ((Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) i)) =
        (Fin.cons (toLB Θ) (fun i => toLB (y i)) : Fin (Y.dim + 1) → LB W.Z) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hF := GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult F W.Z hp Y.dim hW (toLB Θ)
      (isLB_toLB Θ) (fun i => toLB (y i)) (fun i => isLB_toLB (y i)) s hs
    rw [e] at hF
    show interNum F (structureModule W.Z) _ = _
    rw [hcons, hF]
    refine finsum_eq_single _ w₀ fun w hw => ?_
    by_cases hm : Θ.mult w = 0
    · rw [hm, zero_mul]
    obtain ⟨y', rfl⟩ : w ∈ Set.range W.δ := by
      rw [← hsupp]; exact CartierDiv.mem_supp_of_mult_ne_zero hm
    have hy' : y' ≠ η := fun h => hw (by rw [h])
    have hnot : w₀ ∉ closure ({W.δ y'} : Set W.Z) := fun h => by
      have h1 : W.δ y' ⤳ W.δ η := specializes_iff_mem_closure.2 h
      have h2 : y' ⤳ η := hδ.isInducing.specializes_iff.1 h1
      exact hy' (h2.antisymm (genericPoint_specializes y')).eq
    have hsp : w₀ ⤳ W.δ y' := specializes_iff_mem_closure.2 (hcl.symm ▸ ⟨y', rfl⟩ : W.δ y' ∈ closure ({w₀} : Set W.Z))
    have h1 : topologicalKrullDim (closure ({W.δ y'} : Set W.Z)) + 1 ≤ topologicalKrullDim (closure ({w₀} : Set W.Z)) :=
      topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun z hz =>
        ⟨w₀, subset_closure rfl, hnot, hsp.trans (specializes_iff_mem_closure.2 hz)⟩
    rw [hd] at h1
    have hlt : topologicalKrullDim (closure ({W.δ y'} : Set W.Z)) < (Fintype.card (Fin Y.dim) : ℕ) := by
      rw [Fintype.card_fin]; exact GlobalTheory.SheafCycle.lt_of_add_one_le_natCast h1
    rw [GlobalTheory.SheafCycle.interNumRed_eq_zero F hp (fun i => isLB_toLB (y i)) _ hlt, mul_zero]

end GlobalTheory.FlagPush.Dbl
