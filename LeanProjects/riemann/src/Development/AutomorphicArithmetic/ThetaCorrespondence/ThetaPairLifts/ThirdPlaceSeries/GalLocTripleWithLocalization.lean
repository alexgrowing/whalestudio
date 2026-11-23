import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisSideStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobeniusEigenvaluesAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepDefinedOverCoefficientField
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalGaloisParameterAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisLayerCommutesOfFull
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkOfBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReading
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisResTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemImpAltAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisReps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepsOfCgTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleOfSideBStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc
set_option maxHeartbeats 4000000 in
theorem galLoc_triple_with_localization_alt (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hl : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (Bs : SideB D cf Rw low Pq S hl eig θ) (L : LocAll (lay0 D))
    (ψ : (withLoc L).nd.Loc → NC.HC D.host.E)
    (hψ : ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ (withLoc L).ntw.S0 i)
    (ks : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm)
    (chiT : ChiTOk (withLoc L) (cfL L cf)) (grp : GrpSide (withLoc L)) (chr : CharSide (withLoc L) (cfL L cf))
    (val : ValLL0 (withLoc L) (cfL L cf))
    (roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 (withLoc L)).fieldRange)
    (hstar : ∀ x : (withLoc L).LL0, star (x : (withLoc L).what₂.LL) ∈ (withLoc L).LL0)
    (T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut) (cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (withLoc L) T)
    (eT : ∀ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR → GlobalTheory.TwInputs.EigTrue (withLoc L) (cfL L cf) Rw' Sb eig)
    (eO : GlobalTheory.TwInputs.EigOcc (withLoc L) ({ S with } : RatDat (withLoc L).ntw) θ hl Sb eig)
    (rp : ∀ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR → GlobalTheory.TwInputs.RowParam (withLoc L) Rw')
    (rt : ∀ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR → _root_.GlobalTheory.EigTie.ResTiedAlt (withLoc L) Rw')
    (nf : GlobalTheory.TwInputs.NoFormsOff (withLoc L)) (exT : NExpTied (withLoc L)) (cm : GlobalTheory.TwInputs.CommAll (withLoc L))
    (fa : GlobalTheory.TwInputs.FullAll (withLoc L)) :
    _root_.GlobalTheory.Triple.IsGaloisTriple (withLoc L) := by
  obtain ⟨Rw', hR, Bs', -⟩ := GlobalTheory.T.twist_second_step_kept_with_localisations D cf Rw low Pq S hl eig θ Bs L ψ hψ
  have hg := _root_.GlobalTheory.GalAway.galoisReps_of_cgTrue_alt_alt hL hP.what₂.fin hP.what₂.gal _ T cg
  have hm := GlobalTheory.T.stableGoodForms_meet_generic_type hP.greenC _ exT grp
  have hs := GlobalTheory.T.good_part_eigensystem_is_triple_eigensystem _ _ _ _ _ _ _ _ _ Bs' nf hm cm fa
  exact _root_.GlobalTheory.T.side_eigen_export_alt hP.what₂.cheb hP.what₂.art _ _ _ _ _ _ _ _ _ Bs' Sb hSb ks chiT grp chr val roots hstar (eT Rw' hR) eO
    (rp Rw' hR) (rt Rw' hR) hg hs
end GlobalTheory.GalLoc
namespace GlobalTheory.GalLoc
set_option maxHeartbeats 4000000 in
theorem galLoc_triple_at_place_alt (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hS : SerN) (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
    (hE : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig)
    (hF : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0))
    (hR : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw)
    (hC : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.TwInputs.CommAll (w.D Z) ∧ GlobalTheory.TwInputs.FullAll (w.D Z)) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => _root_.GlobalTheory.Triple.IsGaloisTriple (w.D Z) := by
  have hT := _root_.GlobalTheory.T.non_galois_residual_ties hP hL
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' hE (_root_.GlobalTheory.GalLoc.atMem_and' hF (_root_.GlobalTheory.GalLoc.atMem_and' hR (_root_.GlobalTheory.GalLoc.atMem_and' hC hT)))) ?_
  intro K B f T w Z Wt p0 t nch n xd c hN H
  obtain ⟨⟨Sb, hSb, eT, eO⟩, ⟨val, roots, hstar⟩, rp, ⟨cm, fa⟩, rt⟩ := H
  obtain ⟨e⟩ := hN
  have eq := c.a.nt.eq
  have pk := c.a.nt.pack
  let L := c.a.nt.L
  have hψ : ∃ ψ : (withLoc L).nd.Loc → NC.HC (withLoc L).host.E,
      ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0 := by
    have h0 : ∃ ψ : (w.D Z).nd.Loc → NC.HC (w.D Z).host.E,
        ∀ a, NC.ReadC (w.D Z).nd.plOm.1 ((w.D Z).ntw.psiL a) (NC.iotaC (w.D Z) a) (ψ a) 0 :=
      ⟨c.a.all.chiD.psi, c.a.all.chi.psi⟩
    exact eq ▸ h0
  obtain ⟨ψ, hψ⟩ := hψ
  have cast2 : ∀ P : (D : D7) → CharFrame D → Prop, P (w.D Z) (TC.cf w.I w.l Z) → P (withLoc L) (cfL L c.a.nt.cf) :=
    fun P h => cast (congrArg (fun x : (Σ (D₁ : D7) (c₁ : CharFrame D₁) (C₁ : NChoice D₁), TupTied D₁ c₁ C₁) => P x.1 x.2.1) pk) h
  have chr : Nonempty (CharSide (withLoc L) (cfL L c.a.nt.cf)) :=
    cast2 (fun D cf => Nonempty (CharSide D cf)) ⟨{ c.a.chrN with }⟩
  obtain ⟨chr⟩ := chr
  have val' : ValLL0 (withLoc L) (cfL L c.a.nt.cf) := cast2 (fun D cf => ValLL0 D cf) val
  have roots' : ∀ (k : Fin 2) (z : ℂ), z ^ ((withLoc L).host.g k * ((withLoc L).host.g k - 1)) = 1 →
      z ∈ (embLL0 (withLoc L)).fieldRange := eq ▸ roots
  have star' : ∀ x : (withLoc L).LL0, star (x : (withLoc L).what₂.LL) ∈ (withLoc L).LL0 := eq ▸ hstar
  have grp : Nonempty (GrpSide (withLoc L)) := by
    have g0 : Nonempty (GrpSide (w.D Z)) := by
      let Ty := c.a.all.types
      exact ⟨⟨Ty.tA, Ty.tκ, Ty.teichC_def, Ty.ζ, Ty.ζ_gen, Ty.O, Ty.eSer_def, Ty.kv, Ty.tg_tame, Ty.O_equiv, Ty.O_tw⟩⟩
    exact eq ▸ g0
  obtain ⟨grp⟩ := grp
  have rp' : ∀ Rw : RowSide (withLoc L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (withLoc L) Rw := eq ▸ rp
  have rt' : ∀ Rw : RowSide (withLoc L), HEq Rw.locR c.a.nt.A.row.locR → _root_.GlobalTheory.EigTie.ResTiedAlt (withLoc L) Rw := eq ▸ rt
  have cm' : GlobalTheory.TwInputs.CommAll (withLoc L) := eq ▸ cm
  have fa' : GlobalTheory.TwInputs.FullAll (withLoc L) := eq ▸ fa
  have exT : NExpTied (withLoc L) := eq ▸ c.a.all.exp
  have nf : GlobalTheory.TwInputs.NoFormsOff (withLoc L) := by
    have h0 : GlobalTheory.TwInputs.NoFormsOff (w.D Z) := fun i j hj b => e.ser.off i j b fun h => hj (Finset.mem_Icc.2 h)
    exact eq ▸ h0
  rw [eq]
  exact _root_.GlobalTheory.GalLoc.galLoc_triple_with_localization_alt hP hL c.a.nt.Bs L ψ hψ Sb hSb c.a.ratIn.ks c.a.nt.A.chiT grp chr val' roots' star' { c.a.nt.A.wdT with } { c.a.nt.cg with }
    eT eO rp' rt' nf exT cm' fa'
end GlobalTheory.GalLoc
namespace GlobalTheory.GalLoc
set_option maxHeartbeats 4000000 in
theorem galois_side_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ G : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, G.cf = (TC.cf w.I w.l Z) ∧ G.lam.C = (TC.cf w.I w.l Z) ∧
      Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ G.wd) := by
  intro hP hS hL
  have htr : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => _root_.GlobalTheory.Triple.IsGaloisTriple (w.D Z) :=
    _root_.GlobalTheory.GalLoc.galLoc_triple_at_place_alt hP hS hL (_root_.GlobalTheory.T.eigTrue_and_eigOcc_withLoc hP hS hL) (_root_.GlobalTheory.T.valLL0_roots_of_unity_mem_star_closed_at_members hP hS hL) (_root_.GlobalTheory.T.local_param_at_member_of_serN hP hS hL) (_root_.GlobalTheory.T.commAll_fullAll_at_members_of_serN hP hS hL)
  refine (GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices.inter htr).imp fun K _ _ _ _ H => ?_
  refine (H.1.inter H.2).imp fun B f T _ H => ?_
  intro hK w Z Wt p0 t nch n xd c hE hX hC
  obtain ⟨e⟩ := hE
  have hs := H.1 hK T w Z
  exact _root_.GlobalTheory.TwInputs.JoinModel.exists_galSide_of_rank_ge_hundred e (H.2 hK w Z Wt p0 t nch n xd c ⟨e⟩ hX hC) hs.1 hs.2.1
end GlobalTheory.GalLoc
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galSide_cf_eq_cgTrue_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ G : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, G.cf = (TC.cf w.I w.l Z) ∧ G.lam.C = (TC.cf w.I w.l Z) ∧ Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ G.wd) := by
  first | exact @_root_.GlobalTheory.GalLoc.galois_side_at_place_alt | exact _root_.GlobalTheory.GalLoc.galois_side_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.galois_side_at_place_alt <;> assumption)
end
end
