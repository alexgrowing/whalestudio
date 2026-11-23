import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCompleteConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfBaseChangeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem connected_of_hypotheses (hP : GlobalTheory.CovTop.Hypotheses2) : ConnSt := by
  intro F _ _ V _ X s Xw hI _ hPr hF hG
  obtain ⟨O, _, _, _, _, φ, hφi, hφl⟩ := GlobalTheory.T.exists_complete_dvr_extension F V
  have hpr : IsProper s := by
    obtain ⟨N, c, hc, rfl⟩ := hPr
    have := isProper_str (↥V) N
    infer_instance
  have hc := GlobalTheory.T.base_change_complete_connected V O φ hφi hφl X s Xw hI hF hG
  have hsp := GlobalTheory.T.special_fibre_connected_of_proper hP.q18.1 O (pullback s (Spec.map (CommRingCat.ofHom φ))) (pullback.snd _ _) inferInstance hc
  exact GlobalTheory.T.special_fibre_connected_of_base_change V O φ hφl X s hsp

end GlobalTheory.FlatModel
