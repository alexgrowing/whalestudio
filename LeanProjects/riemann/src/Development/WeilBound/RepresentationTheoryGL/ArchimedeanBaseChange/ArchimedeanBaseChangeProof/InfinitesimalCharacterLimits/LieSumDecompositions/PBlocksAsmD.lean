import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmC
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksLag

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

def FgSl : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (U : Submodule ℂ (Sm E (r + s)))
  (c : ℂ) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)), IsAutSt U → IsSliceMap U c T → FinGen U →
  (∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ LS U T ∧
    ∀ W : Submodule ℂ (Sm E r), IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → LS U T ≤ W) ∧
  (∃ S₂ : Finset (Sm E s), (↑S₂ : Set (Sm E s)) ⊆ RS U T ∧
    ∀ W : Submodule ℂ (Sm E s), IsStable W → (↑S₂ : Set (Sm E s)) ⊆ W → RS U T ≤ W)

theorem blocks_of (hfg : FgSl) : Blocks := by
  intro E _ _ _ r s τ hr hs U hH hSI c T hT hpE
  classical
  obtain ⟨hAS, hFG, hNP, hCI, -, hRA⟩ := hH
  choose mm hmmI hmmN using hRA
  obtain ⟨hfgL, hfgR⟩ := hfg E r s U c T hAS hT hFG
  have hLle := LS_le_iSup hAS hT mm hmmN hmmI
  have hRle := RS_le_iSup hAS hT mm hmmN hmmI
  obtain ⟨z₁, hz₁c, hz₁E, hz₁s⟩ := BlockLagrange.proj_exists (LS U T) (adm mm r) ((s : ℂ) / 2) hLle
  obtain ⟨z₂, hz₂c, hz₂E, hz₂s⟩ := BlockLagrange.proj_exists (RS U T) (adm mm s) (-(r : ℂ) / 2) hRle
  have hMI := BlockSlices.memInd2 hAS hT
  have hLst := BlockSlices.LS_stable hAS hT
  have hRst := BlockSlices.RS_stable hAS hT

  have hind := fun p : ((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ) =>
    indMap_holds E r s U (LS U T) (RS U T) T (z₁ p.1) (z₂ p.2) hAS.1 hAS.2 hLst hRst hT.equiv hMI
      (fun o ψ _ => LinearMap.congr_fun (hz₁c p.1 o).eq ψ) (fun o ψ _ => LinearMap.congr_fun (hz₂c p.2 o).eq ψ)
  choose T' hT'e hT'u hT'l using hind

  have hvan : ∀ p, ∀ ψ ∈ U, T ψ = 0 → T' p ψ = 0 := by
    intro p ψ hψ h0
    refine eq_zero_of_levi (hT'u p ψ hψ) fun k g m => ?_
    have := hT'l p ψ hψ k g 0 Fin.elim0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0) (fun m' => by
      rw [h0]; simp) m
    simpa using this
  choose P' hP' using fun p => factor U T (T' p) (hvan p)

  set SS := adm mm r ×ˢ adm mm s with hSS
  have hsum : ∀ ψ ∈ U, ∑ p ∈ SS, T' p ψ = T ψ := by
    intro ψ hψ
    refine eq_of_levi (fun x g => ?_) (hT.unipInv ψ hψ) fun k g m => ?_
    · simp only [Submodule.coe_sum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun p _ => hT'u p ψ hψ x g
    · obtain ⟨n, ψ₁, ψ₂, h₁, h₂, he⟩ := ParabolicProjection.tensor_pair_finite_sum ((hMI ψ hψ).2 k g)
      have he' : ∀ m', (T ψ).1 (lev (Ad E) r s m' * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
          ∑ i, (ψ₁ i).1 m'.1 * (ψ₂ i).1 m'.2 := fun m' => he m'
      simp only [Submodule.coe_sum, Finset.sum_apply]
      rw [Finset.sum_congr rfl fun p _ => hT'l p ψ hψ k g n ψ₁ ψ₂ h₁ h₂ he' m, he' m, hSS, Finset.sum_product]
      have e1 : ∀ i, ∑ σ ∈ adm mm r, (z₁ σ (ψ₁ i)).1 m.1 = (ψ₁ i).1 m.1 := fun i => by
        rw [← Finset.sum_apply, ← Submodule.coe_sum, hz₁s _ (h₁ i)]
      have e2 : ∀ i, ∑ ρ ∈ adm mm s, (z₂ ρ (ψ₂ i)).1 m.2 = (ψ₂ i).1 m.2 := fun i => by
        rw [← Finset.sum_apply, ← Submodule.coe_sum, hz₂s _ (h₂ i)]
      have key : ∀ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 =
          ∑ σ ∈ adm mm r, ∑ ρ ∈ adm mm s, (z₁ σ (ψ₁ i)).1 m.1 * (z₂ ρ (ψ₂ i)).1 m.2 := fun i => by
        rw [← e1 i, ← e2 i, Finset.sum_mul_sum]
      rw [Finset.sum_congr rfl fun i _ => key i]
      symm
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_comm

  set N := SS.card
  let dec : ℕ → ((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ) := fun j =>
    if h : j < N then (SS.equivFin.symm ⟨j, h⟩).1 else (fun _ => 0, fun _ => 0)
  have hdec : ∀ j ∈ Finset.range N, dec j ∈ SS := by
    intro j hj
    have h := Finset.mem_range.1 hj
    simp only [dec, dif_pos h]
    exact (SS.equivFin.symm ⟨j, h⟩).2
  have hreidx : ∀ f : ((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ) → Sm E (r + s),
      ∑ j ∈ Finset.range N, f (dec j) = ∑ p ∈ SS, f p := by
    intro f
    rw [Finset.sum_range (fun j => f (dec j))]
    have e : ∀ i : Fin N, f (dec i) = f (SS.equivFin.symm i).1 := fun i => by simp only [dec, dif_pos i.2, Fin.eta]
    simp only [e]
    rw [Equiv.sum_comp SS.equivFin.symm (fun x => f x.1), Finset.sum_coe_sort SS f]
  refine ⟨Finset.range N, fun j => P' (dec j), fun j => tw ((LS U T).map (z₁ (dec j).1)) (-(s : ℂ) / 2),
    fun j => tw ((RS U T).map (z₂ (dec j).2)) ((r : ℂ) / 2), fun j hj => ?_, fun j _ o ψ hψ => ?_, fun ψ hψ => ?_,
    fun j _ ψ hψ => ?_⟩
  · have hp := Finset.mem_product.1 (hdec j hj)
    exact ⟨hyp_left hAS hNP hT hpE mm hmmN hp.1 (hz₁c _) (hz₁E _) hfgL τ,
      hyp_right hAS hNP hT hpE mm hmmN hp.2 (hz₂c _) (hz₂E _) hfgR τ⟩
  · rw [← hT.equiv o ψ hψ, hP' _ _ (hAS.1 o ψ hψ), hP' _ _ hψ, hT'e _ o ψ hψ]
  · rw [Finset.sum_congr rfl fun j _ => hP' (dec j) ψ hψ, hreidx (fun p => T' p ψ), hsum ψ hψ]
  · rw [hP' _ _ hψ]
    have e1 : tw (tw ((LS U T).map (z₁ (dec j).1)) (-(s : ℂ) / 2)) ((s : ℂ) / 2) = (LS U T).map (z₁ (dec j).1) := by
      rw [show -(s : ℂ) / 2 = -((s : ℂ) / 2) by ring]
      exact BlockTwistCharacters.tw_tw_neg _ _
    have e2 : tw (tw ((RS U T).map (z₂ (dec j).2)) ((r : ℂ) / 2)) (-(r : ℂ) / 2) = (RS U T).map (z₂ (dec j).2) := by
      have := BlockTwistCharacters.tw_tw_neg ((RS U T).map (z₂ (dec j).2)) (-(r : ℂ) / 2)
      rwa [show -(-(r : ℂ) / 2) = (r : ℂ) / 2 by ring] at this
    rw [e1, e2]
    refine ⟨hT'u _ ψ hψ, fun k g => ?_⟩
    obtain ⟨n, ψ₁, ψ₂, h₁, h₂, he⟩ := ParabolicProjection.tensor_pair_finite_sum ((hMI ψ hψ).2 k g)
    have he' : ∀ m', (T ψ).1 (lev (Ad E) r s m' * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (ψ₁ i).1 m'.1 * (ψ₂ i).1 m'.2 := fun m' => he m'
    rw [show (fun m => (T' (dec j) ψ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)))
      = fun m => ∑ i, (z₁ (dec j).1 (ψ₁ i)).1 m.1 * (z₂ (dec j).2 (ψ₂ i)).1 m.2 from
      funext (hT'l _ ψ hψ k g n ψ₁ ψ₂ h₁ h₂ he')]
    exact ParabolicProjection.sum_mem_tens2 (fun i => Submodule.mem_map_of_mem (h₁ i)) (fun i => Submodule.mem_map_of_mem (h₂ i))

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
