import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsExtra
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StdCoordMapInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights

noncomputable section

theorem range_incl_saturated {K : Type*} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle K} (Y : HermitianExtension E' E E'') (t : 𝓞 K) (x : E.carrier)
    (ht : t ≠ 0) (hx : t • x ∈ LinearMap.range Y.incl) : x ∈ LinearMap.range Y.incl := by
  rw [← Y.exact.linearMap_ker_eq, LinearMap.mem_ker] at hx ⊢
  rw [map_smul] at hx
  exact (smul_eq_zero.mp hx).resolve_left ht

theorem S6.BundleCoordinates.proof (hA : S6.LineCoordinates.Statement)
    (hB : S6.CoordinateDegree.Statement) (hC : S6.QuotientDegreeSplit.Statement)
    (hD : S6.ExtensionDegree.Statement) (hE : S6.SaturatedSpan.Statement) :
    S6.BundleCoordinates.Statement := by
  intro K _ _ E X _ _ L hI hr ho E' E'' Y
  obtain ⟨n, e, a, d, ψ, ha, hd, hc, hψ, hrange, hfin, hline, hmet⟩ := hA K E X L hI hr ho
  obtain ⟨hFG, hspanA⟩ := LinesIdealLatticeFG.full K n a ha
  have hspan : Submodule.span K (LinearMap.range ψ : Set (Fin n → K)) = ⊤ := by
    rw [hrange]; exact hspanA
  have hdeg := hB K E n (diagMetric d) ψ hψ hspan hmet
  refine ⟨n, e, a, d, ha, hd, hc, fun i => ?_, ?_⟩
  ·
    have hu : LinearIndependent K (fun _ : Fin 1 => (Pi.single i 1 : Fin n → K)) :=
      linearIndependent_unique_iff.mpr (by simp)
    have h1 := hdeg (L (e i)) (Fin 1) _ hu (by rw [hline i, hrange, Set.range_const])
    rw [HermitianBundle.normDegree, h1, hrange]
    rfl
  ·
    set G := LinearMap.range Y.incl
    obtain ⟨b, hb, hbmap⟩ := hE K E.carrier n ψ hψ G (range_incl_saturated Y)
    have hGr : Module.finrank (𝓞 K) G = Module.finrank (𝓞 K) E'.carrier :=
      LinearMap.finrank_range_of_inj Y.incl_injective
    have hmk : Module.finrank (𝓞 K) G + E''.rank ⊤ = n := by
      rw [hGr, HermitianBundle.rank, finrank_top, ← hfin, Y.finrank_eq]
    obtain ⟨τ, -, hli⟩ := LinesExtendBasis.full K n _ _ b hb hmk
    refine ⟨_, _, b, fun j => Pi.single (τ j) 1, hli, hmk, rfl, ?_⟩
    have htop : Submodule.span K
        (Set.range (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K))) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by
        rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Module.finrank_fin_fun, hmk])
    have hE1 := hdeg ⊤ _ (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K)) hli (by
      rw [Submodule.map_top, htop, Submodule.restrictScalars_top, inf_top_eq])
    have hG1 := hdeg G _ b hb hbmap
    rw [hC K n (idealLattice a) (diagMetric d) hFG hspanA _ _ b _ hli hmk,
      HermitianBundle.normDegree, hD K E' E E'' Y, hE1, hG1, hrange]
    rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
