import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty.MemberO
variable {D : D7}
end GlobalTheory.CoefDuty.MemberO
namespace GlobalTheory.CoefDuty.MemberO
set_option maxHeartbeats 1000000 in
theorem contains_fixZ_alt {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hL : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) (i : L.X.nd.Loc) :
    Contains L.lay.fixZ.nd L.lay.fixZ.naut i ↑(big (L.X.nd.w i)) := by
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hL
  intro z hz
  obtain ⟨x, hx⟩ := Sp.iq_big i z hz
  refine ⟨x, ?_⟩
  change L.Y.naut.iotaQC i (L.Y.naut.iotaQ i x) = z
  rw [Au.iotaQ, Au.iotaQC]
  exact hx
set_option maxHeartbeats 1000000 in
theorem contains_big_of_built {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D}
    {C : NChoice D} {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ}
    {L : LocAll (lay0 D)} (hL : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) (i : L.X.nd.Loc) :
    Contains (withLoc L).nd (withLoc L).naut i ↑(big (L.X.nd.w i)) :=
  _root_.GlobalTheory.CoefDuty.MemberO.contains_fixZ_alt hL i
theorem member_duties_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → ∀ i : L.X.nd.Loc, Contains (withLoc L).nd (withLoc L).naut i ↑(big (L.X.nd.w i)) ∧ Contains L.lay.fixZ.nd L.lay.fixZ.naut i ↑(big (L.X.nd.w i)) ∧ (Live (withLoc L).nd i ↔ Live L.lay.fixZ.nd i) ∧ (ZDecomp (withLoc L).nd i ↔ ZDecomp L.lay.fixZ.nd i) ∧ (∀ S, Chosen (withLoc L).nd (withLoc L).naut i S ↔ Chosen L.lay.fixZ.nd L.lay.fixZ.naut i S) ∧ ((∃ r, GoodR (withLoc L).nd i r) ↔ ∃ r, GoodR L.lay.fixZ.nd i r) ∧ ((∃ r ρ, GoodR (withLoc L).nd i r ∧ TakenWild (withLoc L).nd i r ρ) ↔ ∃ r ρ, GoodR L.lay.fixZ.nd i r ∧ TakenWild L.lay.fixZ.nd i r ρ) := fun _ _ _ _ _ _ _ _ L hL i =>
  ⟨_root_.GlobalTheory.CoefDuty.MemberO.contains_big_of_built hL i, _root_.GlobalTheory.CoefDuty.MemberO.contains_fixZ_alt hL i, live_iff L i, zdecomp_iff L i, chosen_iff L i, goodR_iff L i, taken_iff L i⟩
end GlobalTheory.CoefDuty.MemberO
end
end
