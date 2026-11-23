import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOnLocalizedModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FreeClosedHoldsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndependentSpreadHoldsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FreeTraitHoldsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAmpleCoverLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FineDataOfConeStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.DomModels

theorem domSt_holds : DomSt := by
  have hFree : FreeSt := freeSt_of GlobalTheory.T.free_closed_holds GlobalTheory.T.independent_spread_holds GlobalTheory.T.free_trait_holds
  intro E _ _ _ H D hD Xo
  obtain ⟨s, M, hM1, hC⟩ := GlobalTheory.T.exists_finite_ample_cover_levels E H D hD Xo
  refine ⟨s, insert 1 (M.image (· ^ 2)), ?_, ?_⟩
  · intro N hN
    rcases Finset.mem_insert.1 hN with rfl | hN
    · exact one_pos
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hN
      exact pow_pos (hM1 m hm) 2
  · intro l c hg Z hZ p W hp hW b₀ hb₀
    obtain ⟨I, _, R, _, a, b, ω, C, hcov, hamp, hdom⟩ := hC l c hg
    obtain ⟨i, b', hb'b, hb'ω, hD'⟩ := hdom p W hp hW b₀ hb₀
    obtain ⟨m, hmM, hm⟩ := hamp i
    have hZC : Dominates Z (C i) (b i) := by
      refine GlobalTheory.T.ample_on_localized_model hFree extendSt GlobalTheory.ExtAtProof.extAtSt glueSt E H D l (Xo l) c Z (R i) (a i) (b i) (ω i) (C i) m
        (hcov.2.1 i).1 (hcov.2.1 i).2.1 (hcov.2.1 i).2.2 (hM1 m hmM) hm fun z => ?_
      obtain ⟨R', _, _, _, ξ, t, hmap, P, k, γ, hCN, hξ, hEt, -, hTor, hfine, hcone⟩ := hZ z
      exact ⟨R', _, _, _, ξ, t, hmap, P, hCN, hξ, hEt.1,
        GlobalTheory.T.fine_data_of_cone E H R' t P k 1 γ hCN hTor hcone (hfine 1 (Finset.mem_insert_self _ _)),
        GlobalTheory.T.fine_data_of_cone E H R' t P k (m ^ 2) γ hCN hTor hcone
          (hfine (m ^ 2) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hmM)))⟩
    have h := domTrans E H D l (Xo l) c (𝓞 c.F) (R i) (c.V W) (algebraMap (𝓞 c.F) c.F) (ω i) (c.V W).subtype Z (C i)
      (s.Y p W hp hW ⟨l, c, hg p hp⟩) (b i) b' hb'ω (hcov.2.1 i).2.1 hZC hD'
    rwa [hb'b] at h

end GlobalTheory.DomModels
