import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open PositivityTheory.Rg.Rs.ParabolicProjection in
theorem node_holds : Node := by
  intro E _ _ _ r s _ _ U W₁ W₂ T hU hW₁ hW₂ hTe hmem hC₁ hC₂ φ₀ hφ₀U hφ₀
  obtain ⟨k₀, g₀, m₀, hm₀⟩ := exists_slice_ne hφ₀ (hmem φ₀ hφ₀U).1
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, hsum⟩ := tensor_pair_finite_sum ((hmem φ₀ hφ₀U).2 k₀ g₀)
  have hne : ∑ i, (ψ₁ i).1 m₀.1 * (ψ₂ i).1 m₀.2 ≠ 0 := (hsum m₀) ▸ hm₀

  obtain ⟨χ₁, hχ₁, hχ₁e⟩ : ∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i ∈ tw W₁ ((s : ℂ) / 2) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)
  have hχ₁0 : χ₁ ≠ 0 := fun h => sum_left_ne hne (by rw [← hχ₁e, h, map_zero])
  have hc₁ := hC₁ χ₁ hχ₁ hχ₁0
  obtain ⟨t₁, p₁, ht₁, hpos₁, hp₁e, hp₁V, hp₁0⟩ := hc₁
  have hf₁ : twMap r ((s : ℂ) / 2) p₁ (∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i) ≠ 0 := by
    rw [← hχ₁e]
    change twMap r ((s : ℂ) / 2) p₁ (mulChi r (Model.absC E ((s : ℂ) / 2)) χ₁) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₁0
  obtain ⟨b₁, hb₁⟩ := step_left (twMap r ((s : ℂ) / 2) p₁) hf₁

  obtain ⟨χ₂, hχ₂, hχ₂e⟩ : ∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw W₂ (-(r : ℂ) / 2) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)
  have hχ₂0 : χ₂ ≠ 0 := fun h => sum_right_ne hb₁ (by rw [← hχ₂e, h, map_zero])
  have hc₂ := hC₂ χ₂ hχ₂ hχ₂0
  obtain ⟨t₂, p₂, ht₂, hpos₂, hp₂e, hp₂V, hp₂0⟩ := hc₂
  have hf₂ : twMap s (-(r : ℂ) / 2) p₂ (∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁ i)).1 b₁ • ψ₂ i) ≠ 0 := by
    rw [← hχ₂e]
    change twMap s (-(r : ℂ) / 2) p₂ (mulChi s (Model.absC E (-(r : ℂ) / 2)) χ₂) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₂0
  obtain ⟨b₂, hb₂⟩ := step_right (twMap s (-(r : ℂ) / 2) p₂) hf₂

  have hI := indMap_holds E r s U (tw W₁ ((s : ℂ) / 2)) (tw W₂ (-(r : ℂ) / 2)) T (twMap r ((s : ℂ) / 2) p₁)
    (twMap s (-(r : ℂ) / 2) p₂) hU.1 hU.2 (isStable_tw hW₁.1 _) (isStable_tw hW₂.1 _) hTe hmem
    (twMap_equiv hW₁.1 hp₁e) (twMap_equiv hW₂.1 hp₂e)
  obtain ⟨T', hT'e, hT'u, hT's⟩ := hI
  have hT'm : ∀ φ ∈ U, MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) (T' φ) := by
    intro φ hφ
    refine ⟨hT'u φ hφ, fun k g => ?_⟩
    obtain ⟨n', ψ₁', ψ₂', h₁', h₂', hs'⟩ := tensor_pair_finite_sum ((hmem φ hφ).2 k g)
    have e := hT's φ hφ k g n' ψ₁' ψ₂' h₁' h₂' hs'
    rw [show (fun m : GA E r × GA E s => (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = fun m => ∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁' i)).1 m.1 *
        (twMap s (-(r : ℂ) / 2) p₂ (ψ₂' i)).1 m.2 from funext e]
    exact sum_mem_tens2 (fun i => twMap_mem hp₁V _ (h₁' i)) (fun i => twMap_mem hp₂V _ (h₂' i))
  refine ⟨Tr.node t₁ t₂, T', ⟨ht₁, ht₂⟩, ⟨hpos₁, hpos₂⟩, hT'e, fun φ hφ => ?_, fun h => ?_⟩
  · rw [Tr.space]
    exact Submodule.subset_span ⟨hT'm φ hφ,
      InducedTensorMap.Main.finVec_of_equiv hT'e hφ (hU.2 φ hφ).kfin⟩
  · have e := hT's φ₀ hφ₀U k₀ g₀ n ψ₁ ψ₂ h₁ h₂ hsum (b₁, b₂)
    rw [h] at e
    exact hb₂ e.symm

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
