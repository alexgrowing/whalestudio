import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRestStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeightStatement
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BridgeJMemKwOfDecLe
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.DRSstCrysPstJumpsDescend
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.WdRelOfFrobSS
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GamGalEqOfPlaceIso
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiDescent

theorem wdRel_trivWD {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (a : ℕ) :
    WDRel φ (trivWD h a) (trivWD h' a) := by
  refine ⟨a, WDRep.diag h fun _ : Fin a => 1, WDRep.diag h' fun _ : Fin a => 1, rfl, rfl, ?_, ?_⟩
  · rfl
  · intro σ σ' _
    ext v i
    simp [WDRep.diag, WDRep.ofChars, GlobalTheory.WeilDeligne.unrChar]

theorem charPol_eq {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (hy : WDRel φ y y') {σ : Weil h} {σ' : Weil h'} (hs : WeilRel φ σ σ') :
    y.charPol σ = y'.charPol σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := hy
  rw [WD.charPol_mk, WD.charPol_mk, hb σ σ' hs]

end GlobalTheory.RoadU.PhiDescent

open GlobalTheory.RoadU.PhiDescent in

theorem GlobalTheory.RoadU.holdsS_all_phi : Inputs → SphericalLevelCondition .good .crys → SphericalLevelCondition .good .phi → SphericalLevelCondition .all .phi := by
  intro hIn _ hgood E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc r hr w _ B hB Pr AI hT A h O _ _ _ Bw hj g
  have hF := GlobalTheory.automorphicFormsFiniteGL
  have hQ := GlobalTheory.QuadLiftBridge.quadLift hIn.ac hIn.js
  obtain ⟨Q, hQdec, hQsplit, hQram, hQgood⟩ := (GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split hF E Ω l a π w).nonempty
  obtain ⟨P, hP⟩ := hQ E Q.K Q.two a ha π hQram
  obtain ⟨⟨χ', hsc'⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight hF hIn.js hIn.gk E Q.K l a ha π χ P hP hsc.all
  have hsc'' : InScope .good l P χ' := ⟨hsc'.1, hsc'.2.1, hQgood P hP⟩
  have hr' := GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict E Q.K Ω l ι a π P hP r hr
  have hdec := hQdec A h
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A h hdec
  have hunder : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver h h'
    ext1
    exact this.over.symm
  obtain ⟨c, hc, hdegc, hq, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  obtain ⟨S, hS, -, -, -, -, hTw, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hunder, hq]) (by rw [hunder]; exact hB)
    simpa using this
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  have hrel : WDRel (RingEquiv.refl Ω) (wdAt Pr ι Bw h hj (r.comp (Dec (F := E) A).subtype))
      (wdAt Pr ι Bw' h' hj' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype)) := by
    by_cases hp : IsPstAt Pr Bw (r.comp (Dec (F := E) A).subtype)
    · exact GlobalTheory.RealGal.wdRelRes_gen E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r hp ι w w' h h' hj hj' i hi
    · have hp' : ¬ IsPstAt Pr Bw' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype) :=
        fun H => hp (D.2.2.2.1 H)
      rw [wdAt_of_not_isPstAt _ _ _ _ hp, wdAt_of_not_isPstAt _ _ _ _ hp']
      exact wdRel_trivWD h h' _ a
  have hsat : WDRel (RingEquiv.refl Ω) (satWD h a B) (satWD h' a B) := by
    have h0 := GlobalTheory.RSGam.Transport.wdRel_lpUnr c hc hdegc (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))
    unfold satWD
    rw [hS, hTw, (hS _ _).mp h0]
  have hgc : WeilRel (RingEquiv.refl Ω) g (c g) := (hc g (c g)).2 rfl
  have hcl := hgood Q.K Ω l ι a ha P χ' hsc'' _ hr' w' (hQsplit w' hunder) B hB' Pr AI hT A h' O Bw' hj' (c g)
  rw [charPol_eq hrel hgc, charPol_eq hsat hgc]
  exact hcl

end
