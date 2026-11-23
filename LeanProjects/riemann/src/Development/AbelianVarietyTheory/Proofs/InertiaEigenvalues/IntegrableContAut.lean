import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmallerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinear
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumInertPlaceStandardCayleyPairStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEvenStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySatakeTransformEqOfBaseChangeSatakeParame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseChangeThetaLiftSatakeParameterEqAddSegmentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTransformEqAtThetaLiftOfVacuumEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjoint
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminedByLowTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueInertPlaceAndSegment

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar antiG)
open GlobalTheory.LGrp (bcParam)
open Formalism.UG (qV IsUnramInv GU KU IsInertAt Hecke SatU antiJ)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DownInert

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem satU_sub (hU : IsUnramInv ϖ σ q) {n : ℕ} {f f' : GU σ n → ℂ} (hf : f ∈ Hecke ℂ (KU σ n))
    (hf' : f' ∈ Hecke ℂ (KU σ n)) (α : Fin (n / 2) → ℂˣ) :
    SatU ϖ q (f - f') (fun i => (α i : ℂ)) = SatU ϖ q f (fun i => (α i : ℂ)) - SatU ϖ q f' (fun i => (α i : ℂ)) := by
  obtain ⟨y, hy⟩ := (hasSatU_psFunU hU α).exists_vec
  have h := heckeVec_add (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n) (psFunU σ q α) (sub_mem hf hf') hf' y
  rw [sub_add_cancel, hy.2.2 _ hf, hy.2.2 _ hf', hy.2.2 _ (sub_mem hf hf'), ← add_smul] at h
  exact eq_sub_of_add_eq (smul_left_injective ℂ hy.1 h).symm

theorem howe_down [CharZero L] (hH : GlobalTheory.Hk3.HoweUnram) {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ} {M : Type} [AddCommGroup M]
    [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} {ω : GU σ n × GU σ n' →* Module.End ℂ M} {s : M}
    (hS : IsStd ϖ σ q δ ψ ρ ω s) (hC : CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s)
    (hC' : CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s) (hn : n' ≤ n) {qu : ℂˣ} (hq : (qu : ℂ) = q)
    {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    ∃ h' ∈ Hecke ℂ (KU σ n'), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s =
      heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s ∧
      ∀ α : Fin (n' / 2) → ℂˣ, SatU ϖ q h' (fun i => (α i : ℂ)) = SatU ϖ q h (fun i => (liftPar qu n' n α i : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.Hk3.HoweSwap.locPair_swap L ϖ σ q δ n n' (antiG L n) (antiG L n') ψ M ρ ω hS.1
  have hS' : IsStd ϖ σ q (-δ) ψ _ (ω.comp (MulEquiv.prodComm : GU σ n' × GU σ n ≃* _).toMonoidHom) s :=
    ⟨h1, hS.2.1, h2 s hS.2.2.1, h3 s hS.2.2.2⟩
  have hσ := hS.1.unr.1
  have key : ∀ e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L (Fin n) (Fin n'), ∀ v,
      e (ρ ((((antiG L n')⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (u.map σ)ᵀ *
        ((antiG L n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) v) = e v) →
      ∀ u ∈ intMat L (Fin n') (Fin n), ∀ v, e (ρ u v) = e v := fun e he u hu v => by
    have := he (Matrix.of fun i j => σ (u j.rev i.rev)) (fun i j => GlobalTheory.SphTheta.mem_intL.2 ((hS.1.unr.2.1 _).trans_le (hu _ _))) v
    have hu' : ((((antiG L n')⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *
        ((Matrix.of fun i j => σ (u j.rev i.rev) : Matrix (Fin n) (Fin n') L).map σ)ᵀ *
        ((antiG L n : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = u := by
      ext i j
      show (antiJ L n' * ((Matrix.of fun i j => σ (u j.rev i.rev) : Matrix (Fin n) (Fin n') L).map σ)ᵀ * antiJ L n) i j = _
      rw [GlobalTheory.SphTheta.mul_antiJ_apply, GlobalTheory.SphTheta.antiJ_mul_apply]
      simp [hσ]
    rwa [hu'] at this
  obtain ⟨h', hh', e⟩ := GlobalTheory.T.unramified_hecke_vacuum_larger_eq_smaller hH L ϖ σ q (-δ) ψ n' n M _ _ s hS' h hh
  exact ⟨h', hh', e.symm, GlobalTheory.T.satakeTransform_eq_at_thetaLift_of_vacuum_eq L ϖ σ q (-δ) ψ n' n M _ _ s hS' (fun e he => hC' e (key e he))
    (fun e he => hC e (key e he)) hn h' hh' h hh e qu hq⟩

end Local

section Place

variable {D : D7}

theorem heckeVec_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (h : G → ℂ) : heckeVec ρ K h 0 = 0 := by
  simp [heckeVec]

def piRep {G U : Type} [Group G] [AddCommGroup U] [Module ℂ U] (ι : Type) (π : Representation ℂ G U) :
    Representation ℂ G (ι → U) where
  toFun g := LinearMap.pi fun j => (π g).comp (LinearMap.proj j)
  map_one' := by ext F j; simp
  map_mul' g g' := by ext F j; simp

theorem hecke_down (hH : GlobalTheory.Hk3.HoweUnram) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hle : T.rank ≤ S.rank)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = v)
    (hin : IsInertAt D.host.F D.host.E v w) (uS : UnrAt χS w) (uT : UnrAt χT w)
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} {ϖ : w.adicCompletion D.host.E}
    {eS : Gv S v ≃* GU c S.rank} {eT : Gv T v ≃* GU c T.rank} (hU : IsUnramInv ϖ c (qV D.host.F v))
    (heS : IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS) (heT : IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT)
    {f₀ : WO S T → ℂ} (hf₀ : VacFin ψ S T v f₀) (h0 : f₀ ≠ 0) {qu : ℂˣ} (hq : (qu : ℂ) = qV D.host.F v)
    {hS : GU c S.rank → ℂ} (hh : hS ∈ Hecke ℂ (KU c S.rank)) :
    ∃ hT ∈ Hecke ℂ (KU c T.rank),
      (∀ α : Fin (T.rank / 2) → ℂˣ, SatU ϖ (qV D.host.F v) hT (fun i => (α i : ℂ)) =
        SatU ϖ (qV D.host.F v) hS (fun i => (liftPar qu T.rank S.rank α i : ℂ))) ∧
      ∀ f, VacFin ψ S T v f →
        heckeVec ((om.comp (MonoidHom.inl _ _)).comp ((embV S v).comp eS.symm.toMonoidHom)) (KU c S.rank) hS f =
        heckeVec ((om.comp (MonoidHom.inr _ _)).comp ((embV T v).comp eT.symm.toMonoidHom)) (KU c T.rank) hT f := by
  have : CharZero (w.adicCompletion D.host.E) :=
    charZero_of_injective_algebraMap (algebraMap D.host.E (w.adicCompletion D.host.E)).injective
  set RS : Representation ℂ (GU c S.rank) (WO S T → ℂ) := (om.comp (MonoidHom.inl _ _)).comp ((embV S v).comp eS.symm.toMonoidHom)
  set RT : Representation ℂ (GU c T.rank) (WO S T → ℂ) := (om.comp (MonoidHom.inr _ _)).comp ((embV T v).comp eT.symm.toMonoidHom)
  have hcS := (GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hU S.rank).1
  have hcT := (GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hU T.rank).1

  have step : ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ hT ∈ Hecke ℂ (KU c T.rank),
      (∀ α : Fin (T.rank / 2) → ℂˣ, SatU ϖ (qV D.host.F v) hT (fun i => (α i : ℂ)) =
        SatU ϖ (qV D.host.F v) hS (fun i => (liftPar qu T.rank S.rank α i : ℂ))) ∧
      heckeVec RS (KU c S.rank) hS f = heckeVec RT (KU c T.rank) hT f := by
    intro f hf hf0
    obtain ⟨δ, ψ', M, ρ0, ω, s, hstd, hsf, hωom, hcT', hcS'⟩ :=
      GlobalTheory.T.weilDatum_inertPlace_standard_cayley_pair D ψ S T χS χT om hW v w h hin uS uT c ϖ eS eT hU heS heT f hf hf0
    obtain ⟨hT, hhT, e1, e2⟩ := howe_down hH hstd hcT' hcS' hle hq hh
    have m1 := map_heckeVec hcS hh M.subtype (ρ := ω.comp (MonoidHom.inl _ _)) (ρ' := RS)
      (fun g m => by simp only [Submodule.subtype_apply, MonoidHom.comp_apply, MonoidHom.inl_apply, hωom]; simp [RS]) s
    have m2 := map_heckeVec hcT hhT M.subtype (ρ := ω.comp (MonoidHom.inr _ _)) (ρ' := RT)
      (fun g m => by simp only [Submodule.subtype_apply, MonoidHom.comp_apply, MonoidHom.inr_apply, hωom]; simp [RT]) s
    simp only [Submodule.subtype_apply, hsf] at m1 m2
    exact ⟨hT, hhT, e2, by rw [← m1, ← m2, e1]⟩
  obtain ⟨hT, hhT, e2, -⟩ := step f₀ hf₀ h0
  refine ⟨hT, hhT, e2, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · subst hf0; rw [heckeVec_zero, heckeVec_zero]
  obtain ⟨hT', hhT', e2', e3⟩ := step f hf hf0
  have : hT = hT' := sub_eq_zero.1 (GlobalTheory.LFun.SatCompare.eq_zero_of_satU hU (sub_mem hhT hhT') fun α => by
    rw [satU_sub hU hhT hhT', e2, e2', sub_self])
  rw [this, e3]

end Place

section Place2

variable {D : D7}

theorem map_piRep_proj {G U : Type} [Group G] [AddCommGroup U] [Module ℂ U] {ι : Type} (π : Representation ℂ G U)
    {K : Subgroup G} (hK : Formalism.UG.IsCommensurated K) {φ : G → ℂ} (hφ : φ ∈ Hecke ℂ K) (F : ι → U) (j : ι) :
    heckeVec (piRep ι π) K φ F j = heckeVec π K φ (F j) :=
  map_heckeVec hK hφ (LinearMap.proj j) (fun _ _ => rfl) F

set_option maxHeartbeats 1000000 in

theorem param_down (hH : GlobalTheory.Hk3.HoweUnram) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hle : T.rank ≤ S.rank)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = v)
    (hin : IsInertAt D.host.F D.host.E v w) (uS : UnrAt χS w) (uT : UnrAt χT w)
    (U : Submodule ℂ (WO S T → ℂ)) (hUs : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U)
    {ι : Type} [Fintype ι] (f : ι → U) (hf : ∀ j, VacFin ψ S T v (f j))
    {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv S v) X) (x : ι → X) (B : Multiset ℂˣ)
    (hx : ∀ j, x j = 0 ∨ IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ (x j) B)
    {X' : Type} [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (Gv T v) X') (b : U →ₗ[ℂ] X →ₗ[ℂ] X')
    (hb : ∀ a a' (u : U) y, b ⟨om (embV S v a, embV T v a') u, hUs a a' u u.2⟩ (ρ a y) = ρ' a' (b u y))
    (B' : Multiset ℂˣ) (hz : IsParamVec D.sp.cm.sig T.gram (frameLat T) h ρ' (∑ j, b (f j) (x j)) B')
    {qu : ℂˣ} (hq : (qu : ℂ) = qV D.host.F v) :
    B.map (fun y => ((-1 : ℂˣ) ^ T.rank)⁻¹ * y) =
      B'.map (fun y => ((-1 : ℂˣ) ^ S.rank)⁻¹ * y) + GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str qu ((S.rank : ℤ) - T.rank) := by
  have hz0 := hz.ne_zero
  rcases hz with ⟨hs, -⟩ | ⟨-, c, ϖ, eT, α', hUI, heT, hα', rfl⟩
  · exact absurd hs (not_isSplit_of_isInertAt hin)
  have hH' := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 S
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat S
  obtain ⟨eS, heS, -⟩ := (((exists_isInertChart _ (isCMExt_host D) v).2 w h hin).2.2.2.2 c heT.1).2 S.rank S.gram
    (frameLat S) hH' hL.fg hL.span_eq_top (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D S v)

  obtain ⟨j0, hj0⟩ : ∃ j, b (f j) (x j) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz0 (Finset.sum_eq_zero fun j _ => hc j)
  have hx0 : x j0 ≠ 0 := fun e => hj0 (by rw [e, map_zero])
  have hf0 : (f j0 : WO S T → ℂ) ≠ 0 := fun e => hj0 (by rw [show f j0 = 0 from Subtype.ext e, map_zero, LinearMap.zero_apply])
  obtain ⟨-, -, -, -, α, -, -, -, rfl⟩ := ((hx j0).resolve_left hx0).resolve_left
    (fun h' => not_isSplit_of_isInertAt hin h'.1)
  set ρS := ρ.comp eS.symm.toMonoidHom
  set ρT := ρ'.comp eT.symm.toMonoidHom

  have hxj : ∀ j, x j ∈ fixed ρS (KU c S.rank) ∧ ∀ φ ∈ Hecke ℂ (KU c S.rank),
      heckeVec ρS (KU c S.rank) φ (x j) = SatU ϖ (qV D.host.F v) φ (fun i => (α i : ℂ)) • x j := by
    intro j
    rcases hx j with e | hp
    · rw [e]; exact ⟨zero_mem _, fun φ _ => by rw [heckeVec_zero, smul_zero]⟩
    obtain ⟨-, c2, ϖ2, e2, α2, hU2, he2, hα2, hB⟩ := hp.resolve_left (fun h' => not_isSplit_of_isInertAt hin h'.1)
    have ec := heS.1.unique he2.1
    subst ec
    have h3 := (IsSatVecU.of_chart he2 heS hα2).of_unif hU2 hUI
    refine ⟨h3.2.1, fun φ hφ => ?_⟩
    rw [h3.2.2 φ hφ, GlobalTheory.SatBc.satU_eq_of_bcParam_eq _ ϖ c _ _ hUI α2 α hB.symm φ hφ]
  set RS : Representation ℂ (GU c S.rank) (WO S T → ℂ) := (om.comp (MonoidHom.inl _ _)).comp ((embV S v).comp eS.symm.toMonoidHom)
  set RT : Representation ℂ (GU c T.rank) (WO S T → ℂ) := (om.comp (MonoidHom.inr _ _)).comp ((embV T v).comp eT.symm.toMonoidHom)
  have e0S : embV S v 1 = 1 := map_one _
  have e0T : embV T v 1 = 1 := map_one _
  let πS : Representation ℂ (GU c S.rank) U := GlobalTheory.PRep.sub RS U fun g u hu => by
    show om (embV S v (eS.symm g), 1) u ∈ U; rw [← e0T]; exact hUs _ _ u hu
  let πT : Representation ℂ (GU c T.rank) U := GlobalTheory.PRep.sub RT U fun g u hu => by
    show om (1, embV T v (eT.symm g)) u ∈ U; rw [← e0S]; exact hUs _ _ u hu
  have hπS : ∀ g (u : U), ((πS g u : U) : WO S T → ℂ) = RS g u := fun _ _ => rfl
  have hπT : ∀ g (u : U), ((πT g u : U) : WO S T → ℂ) = RT g u := fun _ _ => rfl
  have hcS := GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hUI S.rank
  have hcT := GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hUI T.rank
  have hρ1 : ∀ y, ρ 1 y = y := fun y => by rw [map_one]; rfl
  have hbT : ∀ g (u : U) y, b (πT g u) y = ρT g (b u y) := fun g u y => by
    have e2 := hb 1 (eT.symm g) u y
    have e : πT g u = ⟨om (embV S v 1, embV T v (eT.symm g)) u, hUs _ _ u u.2⟩ :=
      Subtype.ext ((hπT g u).trans (congrArg (fun z => om (z, embV T v (eT.symm g)) (u : WO S T → ℂ)) e0S.symm))
    rw [hρ1] at e2
    rw [e, e2]; rfl
  have hbS : ∀ g (u : U) y, b (πS g u) (ρS g y) = b u y := fun g u y => by
    have e2 := hb (eS.symm g) 1 u y
    have e : πS g u = ⟨om (embV S v (eS.symm g), embV T v 1) u, hUs _ _ u u.2⟩ :=
      Subtype.ext ((hπS g u).trans (congrArg (fun z => om (embV S v (eS.symm g), z) (u : WO S T → ℂ)) e0T.symm))
    rw [map_one ρ', Module.End.one_apply] at e2
    rw [e]; exact e2

  have hfixS : ∀ j, f j ∈ fixed πS (KU c S.rank) := fun j => by
    by_cases h0 : (f j : WO S T → ℂ) = 0
    · rw [show f j = 0 from Subtype.ext h0]; exact zero_mem _
    obtain ⟨δ, ψ', M, ρ0, ω, s, hstd, hsf, hωom, -, -⟩ :=
      GlobalTheory.T.weilDatum_inertPlace_standard_cayley_pair D ψ S T χS χT om hW v w h hin uS uT c ϖ eS eT hUI heS heT (f j) (hf j) h0
    refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_
    have a4 := hstd.1.fix k 1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2 (one_mem _) s hstd.2.2.1
    have e3 := hωom k 1 s
    rw [hπS]
    show om (embV S v (eS.symm k), 1) (f j : WO S T → ℂ) = f j
    rw [← hsf, show (1 : GA D T) = embV T v (eT.symm 1) by simp]
    exact e3.symm.trans (congrArg Subtype.val a4)
  have hev : ∀ φ ∈ Hecke ℂ (KU c S.rank), (fun g => φ g⁻¹) = φ := fun φ hφ => funext fun g => hcS.2.2 φ hφ g

  have key : ∀ φ ∈ Hecke ℂ (KU c S.rank), SatU ϖ (qV D.host.F v) φ (fun i => (α i : ℂ)) =
      SatU ϖ (qV D.host.F v) φ (fun i => (liftPar qu T.rank S.rank α' i : ℂ)) := by
    intro φ hφ
    obtain ⟨φ', hφ', e2, e3⟩ := hecke_down hH hW hle h hin uS uT hUI heS heT (hf j0) hf0 hq hφ
    have hT1 : ∀ j, heckeVec πT (KU c T.rank) φ' (f j) = heckeVec πS (KU c S.rank) φ (f j) := fun j => by
      apply Subtype.ext
      have m1 := map_heckeVec hcT.1 hφ' U.subtype (ρ := πT) (ρ' := RT) (fun g u => hπT g u) (f j)
      have m2 := map_heckeVec hcS.1 hφ U.subtype (ρ := πS) (ρ' := RS) (fun g u => hπS g u) (f j)
      simp only [Submodule.subtype_apply] at m1 m2
      rw [m1, m2, e3 _ (hf j)]
    let Φ : (ι → U) →ₗ[ℂ] X' :=
      { toFun := fun F => ∑ j, b (F j) (x j)
        map_add' := fun F G => by simp [Finset.sum_add_distrib]
        map_smul' := fun a F => by simp [Finset.smul_sum] }
    have hΦ : ∀ g F, Φ (piRep ι πT g F) = ρT g (Φ F) := fun g F => by
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
      exact Finset.sum_congr rfl fun j _ => hbT g (F j) (x j)
    have m := map_heckeVec hcT.1 hφ' Φ hΦ f
    have lhs : Φ (heckeVec (piRep ι πT) (KU c T.rank) φ' f) =
        SatU ϖ (qV D.host.F v) φ (fun i => (α i : ℂ)) • ∑ j, b (f j) (x j) := by
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_piRep_proj πT hcT.1 hφ', hT1 j,
        (GlobalTheory.ChainOnto.heckeVec_move _ _ hcS.1 hcS.2.1 U X X' πS ρS b hbS (f j) (hfixS j) (x j) (hxj j).1 φ hφ).2,
        hev φ hφ, (hxj j).2 φ hφ, map_smul]
    have rhs : heckeVec ρT (KU c T.rank) φ' (Φ f) =
        SatU ϖ (qV D.host.F v) φ (fun i => (liftPar qu T.rank S.rank α' i : ℂ)) • ∑ j, b (f j) (x j) := by
      rw [← e2]; exact hα'.2.2 φ' hφ'
    exact smul_left_injective ℂ hz0 (lhs.symm.trans (m.trans rhs))
  have hB : bcParam S.rank α = bcParam S.rank (liftPar qu T.rank S.rank α') :=
    GlobalTheory.LGrp.bcParam_of_weylConj (weylConj_of_dosetInd hUI fun d t _ _ => key _ (Formalism.UG.Final.DosetIndMem _ _ ℂ t))
  rw [hB, ← GlobalTheory.T.baseChange_thetaLiftSatakeParameter_eq_add_segment qu T.rank S.rank hle α']

end Place2

section Dict

variable {D : D7}

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext x
  simp [heisO, symplOH, symplO, hO]

theorem vacFin_of_isVacAt {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.DivisionValues.conjPl w = w) {ψ : AddChar (AF D.host.F) ℂ}
    {S T : HSp D} {f : WO S T → ℂ} (hf : GlobalTheory.Hk3.IsVacAt ψ S T w f) : VacFin ψ S T (w.under (𝓞 D.host.F)) f := by
  obtain ⟨ε, hε, hns, -, hpi⟩ := GlobalTheory.VacFixInert.inert_data hw
  obtain ⟨e0, f0, h0⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S).2.1 w
  have he0 := (hpi e0 f0 h0).1
  have hL : ∀ {u : WO S T}, (u ∈ latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
      fun x => x = w.under (𝓞 D.host.F)) → u ∈ latO S T (L0c D S) (L0c D T) fun _ => True := fun hu => by
    rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    exact GlobalTheory.PlaceModel.latO_le_top _ hu
  refine ⟨hf.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have h2 : 2 • u ∈ latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
        fun x => x = w.under (𝓞 D.host.F) := AddSubgroup.nsmul_mem _ hu 2
    exact hf.2 e0 f0 h0 _ (hL h2) (Or.inl (by rw [he0]; exact GlobalTheory.VacFixInert.isHalf_of_mem' hε h2))
  · have hz : u = 0 := by
      have h1 := GlobalTheory.VacFixInert.isHalf_of_mem' hε hu
      have h2 := GlobalTheory.VacFixInert.split_mul_eq_zero hε hns e he
      ext i j
      rw [← hh i j, ← h1 i j, ← mul_assoc, h2, zero_mul, Matrix.zero_apply]
    rw [hz, heisO_zero']

theorem unrAt_of_unrPl {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.DivisionValues.conjPl w = w) {χ : (AE D)ˣ →* Circle}
    (h : GlobalTheory.Hk3.UnrPl w χ) : UnrAt χ w := by
  intro x hx
  obtain ⟨e0, f0, h0⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (D.sp.V 0)).2.1 w
  obtain ⟨ε, -, -, -, hpi⟩ := GlobalTheory.VacFixInert.inert_data hw
  obtain ⟨he0, hf0⟩ := hpi e0 f0 h0
  have hΦ : GlobalTheory.IdemSupport.Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hd := (GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h0).1
  have hg := GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd (GlobalTheory.LFun.EulerTie.finComp_locIdele_self (F := D.host.F) w x)
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w x).1 hx
  have k := h e0 f0 h0 (locIdele D.host.F w x) (by
      rw [hf0, ← he0]
      linear_combination hg)
    ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w x).2 h1) (by rw [← map_inv]; exact (GlobalTheory.LFun.EulerTie.locIdele_int_iff w x⁻¹).2 h2)
  show Circle.toUnits (χ (locIdele D.host.F w x)) = 1
  rw [k, map_one]

end Dict

section Glob

variable {D : D7}

theorem isUnram_host' (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := by
  have hu : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := GlobalTheory.InertOfConj.unram D
  rw [GlobalTheory.LFun.isUnram_iff]
  intro P hP
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 hu ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have hv : P.asIdeal.under (𝓞 D.host.F) = v.asIdeal := by rw [← hP]; rfl
  have : P.asIdeal.LiesOver v.asIdeal := ⟨hv.symm⟩
  rw [hv] at h1
  rwa [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal _ v.ne_bot] at h1

theorem isInertAt_of_conj {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.DivisionValues.conjPl w = w) :
    IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w := by
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → Q = w := fun Q hQ =>
    (GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hQ).elim id fun e => e.trans hw
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (isUnram_host' D (w.under (𝓞 D.host.F))) with
    ⟨P, Q, hne, hP, hQ⟩ | ⟨w', hw'⟩
  · exact absurd ((key P (HeightOneSpectrum.ext hP)).trans (key Q (HeightOneSpectrum.ext hQ)).symm) hne
  · obtain rfl := (GlobalTheory.LFun.InertChart.under_eq_iff hw' w).1 rfl
    exact hw'

def contAut (S : HSp D) : Submodule ℂ (GA D S → ℂ) where
  carrier := {z | Continuous z ∧ ∀ γ ∈ GQ S, ∀ g, z (γ * g) = z g}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, fun γ hγ g => by simp [ha.2 γ hγ, hb.2 γ hγ]⟩
  smul_mem' := fun c _ ha => ⟨ha.1.const_smul c, fun γ hγ g => by simp [ha.2 γ hγ]⟩

theorem thetaKO_smul {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D S) (g : GA D T)
    (c : ℂ) (u : WO S T → ℂ) : thetaKO om h g (c • u) = c * thetaKO om h g u := by
  simp [thetaKO]

theorem integrable_contAut {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    (hpos : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) {u : WO S T → ℂ} (hu : IsThetaFunO ψ S T u) {z : GA D S → ℂ}
    (hz : z ∈ contAut S) (g : GA D T) : IntegrableOn (fun h => thetaKO om h g u * z h) 𝓕 ν := by
  have := GlobalTheory.WeilParts.integrableOn_theta_definite D ψ hW.std S T χS χT om hW hpos ℂ (LinearMap.toSpanSingleton ℂ _ u)
    (fun x => (GlobalTheory.FinWeilO.thetaSub ψ S T).smul_mem x (show u ∈ GlobalTheory.FinWeilO.thetaSub ψ S T from hu)) z hz.1 hz.2 ν 𝓕 hν h𝓕 g
  refine this.congr_fun_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [LinearMap.toSpanSingleton_apply, thetaKO_smul, mul_comm]

end Glob

section Coord

variable {D : D7}

open GlobalTheory.DownLift.Params in
set_option maxHeartbeats 1000000 in

theorem paramFun_definite {V : HSp D} (c : CoefA V) (hc : c.Is)
    {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP.under (𝓞 D.host.F) ∈ S) {f : Formalism.IndefR.Bridge.Gf V → c.W}
    (hf : f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) (s : GlobalTheory.DownLift.Sys D)
    (he : ∀ P d, P.under (𝓞 D.host.F) ∉ S → GlobalTheory.Hk3.IsLab V P d → GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) f = s P d • f)
    (B : GlobalTheory.LFun.Fam D.host.E) (hB : GlobalTheory.LFun.IsSysParamD D S V.rank s B)
    (ℓ : c.W →ₗ[ℂ] ℂ) (hℓ : (fun h => ℓ (c.ext f h)) ≠ 0) :
    GlobalTheory.LFun.IsParamFunV V S (fun h => ℓ (c.ext f h)) B := by
  obtain ⟨n, hB'⟩ := hβ
  rw [one_pow] at hB'
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D V β Λ (flag1L L) S hB' hS).1
  have hlev : ∀ k ∈ (levG V β (flag1L L) : Set (GA D V)), ∀ g,
      (fun h => ℓ (c.ext f h)) (g * k) = levChi V β (flag1L L) k * (fun h => ℓ (c.ext f h)) g := fun k hk g =>
    (congrArg ℓ (ext_level c hc hf hk g)).trans (map_smul _ _ _)
  have heig : ∀ w d R, Hecke₂ V (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) S w d R →
      heckeLin V R (fun h => ℓ (c.ext f h)) = s w d • fun h => ℓ (c.ext f h) := fun w d R hR => by
    have hw : w.under (𝓞 D.host.F) ∉ S := by
      obtain ⟨_, _, _, _, h, -⟩ := hR
      exact (GlobalTheory.GoodPrimes.offS_iff S w).1 h
    have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := GlobalTheory.DefLiftHecke.one_pow_notMem w 0
    obtain ⟨hk, hop, -⟩ := GlobalTheory.LevOp.level_operators V β Λ 1 (flag1L L) hB' w h1 fun PP hPP =>
      ⟨fun e => hw (e ▸ hS PP hPP), fun e => hw (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e ▸ hS PP hPP)⟩
    have hR' : GlobalTheory.Hk3.SphOp V w d R := ((hop S d R).1 hR).2
    have h2 := ((GlobalTheory.SphLabelOps.label_operators V w).1 d R hR').2 _ (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ)
      (fun h => ℓ (c.ext f h)) fun k hkk => funext fun g => by
        have := hlev k (hk k hkk).1 g
        rwa [(hk k hkk).2, one_mul] at this
    funext g
    have h3 := congrFun h2 g
    have h4 := GlobalTheory.DefLiftHecke.ext_hkF c hc w (Finsupp.single d 1) f g
    rw [he w d hw ⟨R, hR'⟩, map_smul, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_smul] at h4
    rw [GlobalTheory.Hk3.opOf, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, Finset.sum_apply, LinearMap.sum_apply,
      Finset.sum_apply] at h3
    have h5 := congrArg ℓ h4
    rw [map_sum, Pi.smul_apply, map_smul] at h5
    exact h3.trans h5.symm
  exact (GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph hℓ hlev heig B).2 hB

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open GlobalTheory.DownLift.Params in

theorem paramV_coord (R : RealDat D A Ks) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (h)
    (hh : GlobalTheory.Hk3.IsOpsV R i t h) (s : GlobalTheory.DownLift.Sys D) (y : (R.HV i t).H) (hy : GlobalTheory.DownLift.IsEigV R i t h s y)
    (B : GlobalTheory.LFun.Fam D.host.E) (hB : GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B)
    (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) (hℓ : (fun g => ℓ (R.extV i t y g)) ≠ 0) :
    GlobalTheory.LFun.IsParamFunV (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (fun g => ℓ (R.extV i t y g)) B :=
  paramFun_definite (R.cV i) (hC.models.cV i) (hC.lev.βV i) (L := R.datVt i t)
    (fun _ hPP => under_mem_badPl R t hPP) ((hC.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)) s
    (fun P d hP hd => (hh P ((good_iff R t P).2 hP) _ y).symm.trans
      ((congrArg (R.HV i t).e (hy P d ((good_iff R t P).2 hP) hd)).trans (map_smul _ _ _))) B hB ℓ hℓ

end Coord

section Main

variable {D : D7}

theorem seg_coe {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w x t).map (fun a : ℂˣ => (a : ℂ)) = GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) (x : ℂ) t := by
  simp only [GlobalTheory.LFun.seg, GlobalTheory.DownLift.str, Multiset.map_map, Finset.range_val]
  exact Multiset.map_congr rfl fun k _ => by simp [GlobalTheory.LFun.npow]

theorem thetaKO_sum {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D S) (g : GA D T)
    {ι : Type} (s : Finset ι) (u : ι → WO S T → ℂ) :
    thetaKO om h g (∑ k ∈ s, u k) = ∑ k ∈ s, thetaKO om h g (u k) := by
  simp [thetaKO, map_sum, Finset.sum_apply]

open GlobalTheory.DownLift.Params in
set_option maxHeartbeats 4000000 in

theorem unrCorr_inert : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP →
    ∀ i t, GlobalTheory.DownLift.UnrCorr R i t (fun w => Formalism.IndefR.Lev.IsConjPl w w) := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hFull i t h hh s c y hy hth hpart B B' hB hB' w hgood hcw
  have hC := hG.core
  have hW := (hFull i t).datum
  have hw : Formalism.DivisionValues.conjPl w = w := by
    rw [GlobalTheory.SphConj.conjPl_eq_cP]; exact ((GlobalTheory.IdemSupport.isConjPl_iff w w).1 hcw).symm
  have hin := isInertAt_of_conj hw
  have hv : w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := (good_iff R t w).1 hgood
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hU := GlobalTheory.UnrOffLevels.unrPl_of_good R F hC.lev t w hgood
  have u1 : GlobalTheory.Hk3.UnrPl w (R.toLevCh.mu t ((i : ℕ) + 1)) := hU.2 _ (by omega) i.2
  have uS : UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 w := unrAt_of_unrPl hw u1
  have uT : UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w :=
    unrAt_of_unrPl hw (GlobalTheory.VacFixInert.unrPl_mul_inv' u1 hU.1)

  obtain ⟨v0, hv0⟩ : ∃ v0 : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, R.thF i t y (fun ρ => v0 ρ) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hth (GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ _ R.θ hC.models.inf (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _
      (hC.thP.thF_mem i t y) hc)

  obtain ⟨nW, hβW⟩ := hC.lev.βW i
  rw [one_pow] at hβW
  have hsphW := (GlobalTheory.FinZeta.LevelOff.level_offS D _ (R.βW i) _ (R.datWp i R.triv) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) hβW
    fun PP hPP => under_mem_badPl R t (hPP.imp_right fun h => absurd h (Finset.notMem_empty _))).1
  have hB'' : GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Wc D i).rank c B' := by rw [rW]; exact hB'
  have hz := (GlobalTheory.LFun.isParamFunV_iff_of_mem_partFull hsphW hpart hv0 B').2 hB'' _ hv w rfl

  let b0 := Module.finBasis ℂ (R.cV i).W
  let L0 : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
    (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t)) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ v0)
  have hL0 : ∀ x, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v0) x) = L0 x := fun _ => rfl
  have hvac : ∀ x, GlobalTheory.Hk3.IsVacAt R.ψ (Vc D i) (Wc D i) w (L0 x) := fun x =>
    (GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels R F hC t w hgood).2.2 i _
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have hs : (Vc D i).SigOK := D.sp.V_sig _
    have := hs (tauE D τ)
    rw [hC.models.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hν := hC.models.νV i t
  have hf := (hC.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hxk : ∀ k, (fun g => b0.coord k (R.extV i t y g)) ∈ contAut (Vc D i) := fun k =>
    ⟨(b0.coord k).continuous_of_finiteDimensional.comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hC.models.cV i) (R.βV i) (R.datVt i t) hf),
      fun γ hγ g => congrArg (b0.coord k) (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hf γ hγ g)⟩
  have hexp : ∀ g, R.thF i t y (fun ρ => v0 ρ) g = ∑ k, ∫ h in R.fdV i t,
      thetaKO (R.ωP i t) h g (L0 (b0 k)) * b0.coord k (R.extV i t y h) ∂(R.νV i t) := by
    intro g
    rw [GlobalTheory.DefLiftHecke.thF_eq_integral hC.thP i t y v0 g]
    have e1 : ∀ h, thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v0) ((R.cV i).ext ((R.HV i t).e y) h))) =
        ∑ k, thetaKO (R.ωP i t) h g (L0 (b0 k)) * b0.coord k (R.extV i t y h) := fun h => by
      rw [hL0]
      conv_lhs => rw [← b0.sum_repr ((R.cV i).ext ((R.HV i t).e y) h)]
      rw [map_sum, thetaKO_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, thetaKO_smul, mul_comm]
      rfl
    simp_rw [e1]
    exact integral_finset_sum _ fun k _ => integrable_contAut hW hpos hν.1.1 hν.2 (hvac _).1 (hxk k) g

  have : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  let X := contAut (Vc D i)
  let ρ0 : Representation ℂ (Gv (Vc D i) (w.under (𝓞 D.host.F))) (GA D (Vc D i) → ℂ) :=
    (GlobalTheory.PRep.rightReg ℂ (GA D (Vc D i)) ℂ).comp (embV (Vc D i) (w.under (𝓞 D.host.F)))
  have hρ0 : ∀ a (z : GA D (Vc D i) → ℂ) g, ρ0 a z g = z (g * embV (Vc D i) (w.under (𝓞 D.host.F)) a) :=
    fun _ _ _ => rfl
  have hXs : ∀ a, ∀ z ∈ X, ρ0 a z ∈ X := fun a z hz =>
    ⟨hz.1.comp (continuous_mul_right _), fun γ hγ g => by rw [hρ0, hρ0, mul_assoc, hz.2 γ hγ]⟩
  let ρX : Representation ℂ (Gv (Vc D i) (w.under (𝓞 D.host.F))) X := GlobalTheory.PRep.sub ρ0 X hXs
  let U := GlobalTheory.FinWeilO.thetaSub R.ψ (Vc D i) (Wc D i)
  have hint : ∀ (u : U) (z : X) x, IntegrableOn (fun h => thetaKO (R.ωP i t) h x (u : WO (Vc D i) (Wc D i) → ℂ) *
      (z : GA D (Vc D i) → ℂ) h) (R.fdV i t) (R.νV i t) := fun u z x =>
    integrable_contAut hW hpos hν.1.1 hν.2 u.2 z.2 x
  let bf : U → X → GA D (Wc D i) → ℂ := fun u z x =>
    ∫ h in R.fdV i t, thetaKO (R.ωP i t) h x (u : WO (Vc D i) (Wc D i) → ℂ) * (z : GA D (Vc D i) → ℂ) h ∂(R.νV i t)
  let b : U →ₗ[ℂ] X →ₗ[ℂ] (GA D (Wc D i) → ℂ) := LinearMap.mk₂ ℂ bf
    (fun u u' z => by
      funext x
      show _ = bf u z x + bf u' z x
      simp only [bf, ← integral_add (hint u z x) (hint u' z x)]
      congr 1; funext g
      simp [thetaKO, add_mul])
    (fun a u z => by
      funext x
      show _ = a * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [thetaKO, mul_assoc])
    (fun u z z' => by
      funext x
      show _ = bf u z x + bf u z' x
      simp only [bf, ← integral_add (hint u z x) (hint u z' x)]
      congr 1; funext g
      simp [mul_add])
    (fun a u z => by
      funext x
      show _ = a * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [mul_left_comm])
  have hUs : ∀ a a', ∀ u ∈ U, (R.ωP i t) (embV (Vc D i) (w.under (𝓞 D.host.F)) a,
      embV (Wc D i) (w.under (𝓞 D.host.F)) a') u ∈ U := fun a a' u hu => hW.om_pres _ u hu
  have hb : ∀ a a' (u : U) (z : X), b ⟨(R.ωP i t) (embV (Vc D i) (w.under (𝓞 D.host.F)) a,
      embV (Wc D i) (w.under (𝓞 D.host.F)) a') u, hUs a a' u u.2⟩ (ρX a z) =
      ((GlobalTheory.PRep.rightReg ℂ (GA D (Wc D i)) ℂ).comp (embV (Wc D i) (w.under (𝓞 D.host.F)))) a' (b u z) := by
    intro a a' u z
    funext x
    show ∫ g in R.fdV i t, thetaKO (R.ωP i t) g x ((R.ωP i t) (embV _ _ a, embV _ _ a') u) *
        (z : GA D (Vc D i) → ℂ) (g * embV _ _ a) ∂(R.νV i t) =
      ∫ g in R.fdV i t, thetaKO (R.ωP i t) g (x * embV _ _ a') (u : WO (Vc D i) (Wc D i) → ℂ) *
        (z : GA D (Vc D i) → ℂ) g ∂(R.νV i t)
    simp_rw [GlobalTheory.ChainOnto.thetaKO_om_apply]
    exact GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant D (Vc D i) _ _ hν.1.1 hν.2
      (fun g => thetaKO (R.ωP i t) g (x * embV _ _ a') (u : WO (Vc D i) (Wc D i) → ℂ) * (z : GA D (Vc D i) → ℂ) g)
      (fun γ hγ g => by simp only [GlobalTheory.ChainOnto.thetaKO_left hW u.2 γ hγ, z.2.2 γ hγ]) _

  let fk : Fin (Module.finrank ℂ (R.cV i).W) → U := fun k => ⟨L0 (b0 k), (hvac _).1⟩
  have hfk : ∀ k, VacFin R.ψ (Vc D i) (Wc D i) (w.under (𝓞 D.host.F)) (fk k) := fun k => vacFin_of_isVacAt hw (hvac _)
  let xk : Fin (Module.finrank ℂ (R.cV i).W) → X := fun k => ⟨_, hxk k⟩
  have hxB : ∀ k, xk k = 0 ∨ IsParamVec D.sp.cm.sig (Vc D i).gram (frameLat (Vc D i)) (rfl : w.under (𝓞 D.host.F) = _) ρX
      (xk k) (B w) := by
    intro k
    by_cases h0 : (fun g => b0.coord k (R.extV i t y g)) = 0
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (GlobalTheory.ChainOnto.isParamVec_of_injective_equivariant X.subtype (fun _ _ => rfl) Subtype.val_injective
        (paramV_coord R hC i t h hh s y hy B hB (b0.coord k) h0 _ hv w rfl))
  have hzsum : (∑ k, b (fk k) (xk k)) = R.thF i t y (fun ρ => v0 ρ) := by
    funext g
    rw [hexp g, Finset.sum_apply]
    rfl
  have hq0 : ((qV D.host.F (w.under (𝓞 D.host.F)) : ℕ) : ℂ) ≠ 0 := by
    obtain ⟨-, ⟨c0, hc0, -⟩, -, -, hch⟩ := (exists_isInertChart _ (isCMExt_host D) _).2 w rfl hin
    obtain ⟨ϖ0, hU0⟩ := (hch c0 hc0).1
    have := hU0.2.2.2.2.2.1
    exact_mod_cast (by omega : qV D.host.F (w.under (𝓞 D.host.F)) ≠ 0)
  have E1 := param_down hH hW (by omega) rfl hin uS uT U hUs fk hfk ρX xk (B w) hxB
    ((GlobalTheory.PRep.rightReg ℂ (GA D (Wc D i)) ℂ).comp (embV (Wc D i) (w.under (𝓞 D.host.F)))) b hb (B' w)
    (by rw [hzsum]; exact hz) (qu := Units.mk0 _ hq0) rfl

  obtain ⟨hvS, -⟩ := GlobalTheory.ChainOnto.val_seg_of_isInertAt D _ _ hW.hecS hW.resS _ w rfl hin uS
  obtain ⟨hvT, hseg⟩ := GlobalTheory.ChainOnto.val_seg_of_isInertAt D _ _ hW.hecT hW.resT _ w rfl hin uT
  have ht : ((Vc D i).rank : ℤ) - (Wc D i).rank = (D.R.t : ℤ) := by rw [rV, rW]; push_cast; ring
  rw [ht] at E1
  have hstr : GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) ((((-1 : ℂˣ) ^ (Wc D i).rank : ℂˣ)) : ℂ) D.R.t =
      ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str (Units.mk0 _ hq0) D.R.t).map (((-1 : ℂˣ) ^ (Wc D i).rank) * ·)).map (fun a : ℂˣ => (a : ℂ)) := by
    rw [← hseg (Units.mk0 _ hq0) _ D.R.t rfl]
    exact (seg_coe w _ D.R.t).symm
  show (B w).map (fun a : ℂˣ => (a : ℂ)) = (B' w).map (fun a : ℂˣ =>
    ((a * GlobalTheory.LFun.val (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w *
      (GlobalTheory.LFun.val (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 w)⁻¹ : ℂˣ) : ℂ)) +
    GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal)
      (GlobalTheory.LFun.val (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w : ℂ) D.R.t
  rw [hvS, hvT, hstr]
  have E2 := congrArg (fun M : Multiset ℂˣ => (M.map (((-1 : ℂˣ) ^ (Wc D i).rank) * ·)).map (fun a : ℂˣ => (a : ℂ))) E1
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def] at E2
  rw [Multiset.map_map]
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (E2.trans (congrArg₂ _ (Multiset.map_congr rfl fun a _ => ?_) rfl))
  · simp only [mul_inv_cancel_left]
  · congr 1
    rw [mul_comm _ a, mul_left_comm, ← mul_assoc]

end Main

end GlobalTheory.DownInert
