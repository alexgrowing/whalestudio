import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorSumProdLocalPureTensorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalPureTensorProductExpansionAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunctionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaAreRealDatumLargeDepthStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal

namespace GlobalTheory.LocAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1600000 in
open Classical in

theorem locAt_of_placeAt : Big fun ch => ∀ s, PlaceAt ch s → ConLin ch → LocAt ch s := by
  refine big_mono ?_ (Big.and GlobalTheory.T.flippedFiniteTensor_sum_prod_local_pure_tensors (Big.and GlobalTheory.T.localPureTensor_product_expansion_all_places (Big.and GlobalTheory.T.unfoldedVacuaAreRealDatum_largeDepth GlobalTheory.T.rowTest_combination_depends_on_product_function)))
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s hP hcon
  obtain ⟨hR, hS, hV, hC⟩ := h
  obtain ⟨κ, z, hz, hκ, hPl⟩ := (placeAt_iff ch s).1 hP
  refine ⟨∏ w ∈ ch.G.pl.W0, κ w, fun t => ∏ w ∈ locPl ch.G t, z t w, fun t => Subgroup.prod_mem _ fun w _ => hz t w, ?_⟩
  intro t Φ τ hτ M hM β b b₀ hb hb₀ τ' c hτ' hc
  have hζ : ∀ w : locPl ch.G t, ∃ ζ : ℂ, ((w.1 ∈ ch.G.pl.W0 → ∀ i, β w i = DoubleCoset.mk _ _
      (stair (locGrid ch.G t w.1) (unifAt w.1) (cosExp ch.G w.1) (i + 1))) → ζ = κ w.1 * (z t w.1 : ℂ)⁻¹) ∧
      PlaceCl ch s t w.1 (β w) ζ := fun w => hPl t w.1 w.2 (β w)
  choose ζ hζ1 hζ2 using hζ
  refine ⟨∏ w, ζ w, fun hst => ?_, ?_⟩
  · have e1 : ∀ w : locPl ch.G t, ζ w = κ w.1 * (z t w.1 : ℂ)⁻¹ := fun w => hζ1 w (hst w)
    rw [Finset.prod_congr rfl fun w _ => e1 w, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_coe_sort (locPl ch.G t) κ]
      exact (Finset.prod_subset Finset.subset_union_left fun w _ hw => hκ w hw).symm
    · rw [Finset.prod_coe_sort (locPl ch.G t) (fun w => ((z t w : ℂ))⁻¹), Units.coe_prod, Finset.prod_inv_distrib]
  · intro P p hp u y
    obtain ⟨e, he, hτe, hτ'p⟩ := hτ'
    obtain ⟨α, SA, xA, φ, fd, fr, hnat, hvec, hflat, hlhs⟩ := hR hcon t Φ τ hτ β e he
    have hS' : ∀ a ∈ SA, ∃ σ : (PureDat ch.G t × Combs ch.G) →₀ ℂ, _ := fun a ha =>
      hS s t β ζ hζ2 M hM b b₀ hb hb₀ e he (φ a) (hnat a ha) (fd a) (fr a) (hvec a ha).1 (hvec a ha).2
    choose! σ hσ1 hσ2 hσ3 using hS'
    set C₀ := conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀) with hC₀
    set μ : (PureDat ch.G t × Combs ch.G) →₀ ℂ := τ'.mapDomain (fun d => (d, c d)) - ∑ a ∈ SA, xA a • σ a with hμ
    have hL : ∀ G : PureDat ch.G t × Combs ch.G → ℂ, ∑ i ∈ μ.support, μ i * G i =
        (τ'.sum fun d x => x * G (d, c d)) - ∑ a ∈ SA, xA a * (σ a).sum fun k x => x * G k := fun G => by
      have e1 : ∀ {ι : Type} (G' : ι → ℂ) (ν : ι →₀ ℂ), Finsupp.linearCombination ℂ G' ν = ν.sum fun k x => x * G' k :=
        fun G' ν => by rw [Finsupp.linearCombination_apply]; rfl
      have e2 : ∑ i ∈ μ.support, μ i * G i = Finsupp.linearCombination ℂ G μ := by rw [e1]; rfl
      rw [e2, hμ, map_sub, map_sum, Finsupp.linearCombination_mapDomain, e1]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, e1, smul_eq_mul]
    have hsupp : ∀ i ∈ μ.support, (∀ j : Fin D.R.m, (i.1.1 j).e = e ∧ IsCombOf ch.W (i.1.1 j) (i.2.1 j)) ∧
        ∀ n, (i.1.2 n).e = e ∧ IsCombOf ch.W (i.1.2 n) (i.2.2 n) := by
      intro i hi
      rcases Finset.mem_union.1 (Finsupp.support_sub hi) with h1 | h2
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h1)
        exact ⟨fun j => ⟨((hτe d hd).1 j).2.1, (hc d hd).1 j⟩, fun n => ⟨((hτe d hd).2 n).2.1, (hc d hd).2 n⟩⟩
      · obtain ⟨a, ha, hi'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum h2)
        exact hσ1 a ha i (Finsupp.support_smul hi')
    have hzero := hC t e he (PureDat ch.G t × Combs ch.G) μ.support μ Prod.fst Prod.snd hsupp (fun u' y' hu hy => by
      rw [hL]
      have h1 := hτ'p u' y' hu hy
      have h2 := hflat u' y' hu hy
      rw [sub_eq_zero, Finset.sum_congr rfl fun a ha => by rw [hσ2 a ha u' y' hu hy], ← h2, ← h1]
      refine Finsupp.sum_congr fun d _ => ?_
      ring) C₀ (hV t M hM b₀ hb₀ P p hp) u y
    rw [hL, sub_eq_zero] at hzero
    rw [hlhs M hM P (p * b) u y, Finset.sum_congr rfl fun a ha => by rw [hσ3 a ha P p hp u y], hzero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.LocAsm

end
