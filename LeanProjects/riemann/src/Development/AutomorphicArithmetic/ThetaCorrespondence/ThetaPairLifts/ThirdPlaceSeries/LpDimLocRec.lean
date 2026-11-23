import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtAdicCompletion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
theorem lpDim_locRec_alt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) {n : ℕ}
    (τ : IrrRep (GL (Fin n) (w.adicCompletion E))) : (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls τ)).lpDim = n := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  exact H.dim _
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
def weilDeligneParameterOfLocalDatum {σ : D.what₂.FT} {w : PlE D.host} (p : LocAt D rep σ w) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) :=
  p.2.1 ▸ _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 p.1.1.w) (cls p.1.2)
def weilDeligneParameterAtPlace (σ : D.what₂.FT) (w : PlE D.host) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) := by
  classical
  exact if h : Nonempty (LocAt D rep σ w) then _root_.GlobalTheory.RowPar.weilDeligneParameterOfLocalDatum hL D rep h.some else (unrW D).par σ w
theorem parameter_of_local_datum_eq_reciprocity {σ : D.what₂.FT} {w : PlE D.host} (p : LocAt D rep σ w) (s : SplitPlace D.host.E) (hs : s.w = w)
    (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))) (hτ : IsLocS (rep σ).S s τ) :
    _root_.GlobalTheory.RowPar.weilDeligneParameterOfLocalDatum hL D rep p = hs ▸ _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ) := by
  obtain ⟨⟨s0, τ0⟩, hw, hl⟩ := p
  subst hs
  obtain rfl := splitPlace_eq_of_isLocS _ _ s s0 hw τ τ0 hτ hl
  show _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 _) (GlobalTheory.LocLanglands.cls τ0) =
    _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 _) (GlobalTheory.LocLanglands.cls τ)
  rw [show GlobalTheory.LocLanglands.cls τ0 = GlobalTheory.LocLanglands.cls τ from
    congrArg (Sigma.mk _) (cl_eq_of_isLocS (rep σ) _ τ0 τ hl hτ)]
theorem parameter_at_place_eq_reciprocity_of_local_component (σ : D.what₂.FT) (s : SplitPlace D.host.E) (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hτ : IsLocS (rep σ).S s τ) :
    _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ s.w = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ) := by
  classical
  have h : Nonempty (LocAt D rep σ s.w) := ⟨⟨⟨s, τ⟩, rfl, hτ⟩⟩
  unfold _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace
  rw [dif_pos h]
  exact _root_.GlobalTheory.RowPar.parameter_of_local_datum_eq_reciprocity hL D rep _ s rfl τ hτ
theorem dim_parameter_at_place_eq_rank (σ : D.what₂.FT) (w : PlE D.host) : (_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ w).lpDim = D.R.r := by
  classical
  unfold _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace
  by_cases h : Nonempty (LocAt D rep σ w)
  · rw [dif_pos h]
    generalize h.some = p
    obtain ⟨⟨s0, τ0⟩, hw, hl⟩ := p
    subst hw
    exact _root_.GlobalTheory.RowPar.lpDim_locRec_alt hL _ τ0
  · rw [dif_neg h]
    exact (unrW D).dim σ w
end Loc
end GlobalTheory.RowPar
end
end
