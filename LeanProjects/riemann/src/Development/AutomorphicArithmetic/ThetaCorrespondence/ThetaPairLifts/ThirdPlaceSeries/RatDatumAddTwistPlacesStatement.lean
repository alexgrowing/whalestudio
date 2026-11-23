import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairPropertyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatDatumAddTwistPlaces

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_pair_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∃ (p : ∀ j, J.Ch j → ℂ) (q : ∀ j, J.Ch (j + 1) → ℂ), (∀ j, j < B.R.m → ∀ α, ∃ n : ℕ, 0 < n ∧ (p j α * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ)) ^ n = 1) ∧ (∀ j, j < B.R.m → ∀ γ, ∃ n : ℕ, 0 < n ∧ (q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹) ^ n = 1) ∧ (∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ ∀ α, p 0 α * (J.A.chr 1 (J.A.xr 0 (J.ι 0 α)) : ℂ) = c) ∧ (∀ j, j + 1 < B.R.m → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ ∀ γ, q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹ * (p (j + 1) γ * (J.A.chr (j + 1 + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ)) = c) ∧ ∀ e₀ : AE (I.rec7 l Z), IsIdemSum e₀ ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ (Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ) (f : WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ e₀ Ξ (a.g.vac j) f → IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (e₀ + ∑ i, (J.G i).q.e) (fun z => Ξ z * (p j α * q j γ * ∏ i, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z)))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (aconv (List.ofFn fun i => (J.E i).dL j (α i) (γ i))) f) := by
  first | exact @_root_.GlobalTheory.TwPlaces.ratDatum_add_twist_places_alt | exact _root_.GlobalTheory.TwPlaces.ratDatum_add_twist_places_alt | (intros; apply _root_.GlobalTheory.TwPlaces.ratDatum_add_twist_places_alt <;> assumption)
end
