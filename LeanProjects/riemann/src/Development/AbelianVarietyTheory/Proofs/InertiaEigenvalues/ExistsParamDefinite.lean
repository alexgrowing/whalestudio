import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunctionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Hk3

namespace GlobalTheory.DownLift.Params

variable {D : D7}

theorem mem_bddAut_of_posDef {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {f : GA D V → ℂ} (hc : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : f ∈ GlobalTheory.FinZeta.bddAut V := by
  have hpos : ∀ τ, (gramAt D V τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact V hpos
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨hc, hl, b, fun g => ?_⟩
  obtain ⟨γ, hγ, c, hcC, rfl⟩ := hcov g
  rw [hl γ hγ]
  exact hb c hcC

theorem level_abs {Γ Gf W : Type} [Group Γ] [Group Gf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gf}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gf} {χ : J →* ℂˣ} {f : Gf → W} (hf : f ∈ Bridge.AdForms ι ρ J χ)
    {k : Gf} (hk : k ∈ J) (h : Gf) : f (h * k) = ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) • f h := by
  have h3 := hf 1 h ⟨k, hk⟩
  rw [map_one, map_one, one_mul] at h3
  exact h3

theorem ext_level {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ)
    {k : GA D V} (hk : k ∈ levG V β (flag1L L)) (h : GA D V) :
    c.ext f (h * k) = levChi V β (flag1L L) k • c.ext f h := by
  have hJ : (finHom V).rangeRestrict k ∈ (levEnv V β L).J := hk.2
  exact (GlobalTheory.DefLiftHecke.ext_mul c hc f hk.1 h).trans ((congrArg (c.ρ h⁻¹) (level_abs hf hJ _)).trans (map_smul _ _ _))

theorem exists_coord_ne {V : HSp D} (c : CoefA V) {f : Bridge.Gf V → c.W} (h0 : f ≠ 0) :
    ∃ ℓ : c.W →ₗ[ℂ] ℂ, (fun h => ℓ (c.ext f h)) ≠ 0 := by
  obtain ⟨u, hu⟩ := Function.ne_iff.1 h0
  obtain ⟨g, rfl⟩ := (finHom V).rangeRestrict_surjective u
  have h1 : c.ext f g ≠ 0 := fun e => hu (by
    have e' : c.ρ g⁻¹ (f ((finHom V).rangeRestrict g)) = 0 := e
    have := congrArg (c.ρ g) e'
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at this)
  refine ⟨innerₛₗ ℂ (c.ext f g), Function.ne_iff.2 ⟨g, fun e => h1 ?_⟩⟩
  exact inner_self_eq_zero.1 e

set_option maxHeartbeats 1000000 in

theorem exists_param_definite {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) (c : CoefA V) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP.under (𝓞 D.host.F) ∈ S) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) (h0 : f ≠ 0) (s : Sys D)
    (he : ∀ P d, P.under (𝓞 D.host.F) ∉ S → IsLab V P d → hkF V P (Finsupp.single d 1) f = s P d • f) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D S V.rank s B := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  obtain ⟨ℓ, hℓ⟩ := exists_coord_ne c h0
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D V β Λ (flag1L L) S hB hS).1
  have hbd : (fun h => ℓ (c.ext f h)) ∈ GlobalTheory.FinZeta.bddAut V :=
    mem_bddAut_of_posDef hs hp (ℓ.continuous_of_finiteDimensional.comp (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf))
      fun γ hγ g => congrArg ℓ (GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ g)
  have hlev : ∀ k ∈ (levG V β (flag1L L) : Set (GA D V)), ∀ g,
      (fun h => ℓ (c.ext f h)) (g * k) = levChi V β (flag1L L) k * (fun h => ℓ (c.ext f h)) g := fun k hk g =>
    (congrArg ℓ (ext_level c hc hf hk g)).trans (map_smul _ _ _)
  have heig : ∀ w d R, Hecke₂ V (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) S w d R →
      heckeLin V R (fun h => ℓ (c.ext f h)) = s w d • fun h => ℓ (c.ext f h) := fun w d R hR => by
    have hw : w.under (𝓞 D.host.F) ∉ S := by
      obtain ⟨_, _, _, _, h, -⟩ := hR
      exact (GlobalTheory.GoodPrimes.offS_iff S w).1 h
    have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := GlobalTheory.DefLiftHecke.one_pow_notMem w 0
    obtain ⟨hk, hop, -⟩ := GlobalTheory.LevOp.level_operators V β Λ 1 (flag1L L) hB w h1 fun PP hPP =>
      ⟨fun e => hw (e ▸ hS PP hPP), fun e => hw (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e ▸ hS PP hPP)⟩
    have hR' : SphOp V w d R := ((hop S d R).1 hR).2
    have h2 := ((GlobalTheory.SphLabelOps.label_operators V w).1 d R hR').2 _ (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ)
      (fun h => ℓ (c.ext f h)) fun k hkk => funext fun g => by
        have := hlev k (hk k hkk).1 g
        rwa [(hk k hkk).2, one_mul] at this
    funext g
    have h3 := congrFun h2 g
    have h4 := GlobalTheory.DefLiftHecke.ext_hkF c hc w (Finsupp.single d 1) f g
    rw [he w d hw ⟨R, hR'⟩, map_smul, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_smul] at h4
    rw [opOf, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, Finset.sum_apply, LinearMap.sum_apply,
      Finset.sum_apply] at h3
    have h5 := congrArg ℓ h4
    rw [map_sum, Pi.smul_apply, map_smul] at h5
    exact h3.trans h5.symm
  obtain ⟨B, hB', -⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D V _ _ S hsph _ hbd hℓ hlev s heig
  exact ⟨B, (GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph hℓ hlev heig B).1 hB'⟩

theorem exists_param_part (hP : GlobalTheory.Published.CuspRapidDecay) {V : HSp D} {Sp : D.what₂.Tau → SPar} {θ : InfFam D}
    (hθ : IsInfFam θ) {M : DSModel V Sp}
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP.under (𝓞 D.host.F) ∈ S) {s : Sys D}
    (h : partFull θ M (levS V β L) (levChi V β L) S s ≠ ⊥) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D S V.rank s B ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ S →
      ∀ a ∈ B w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D V β Λ L S hB hS).1
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨v, hv⟩ : ∃ v, U v ≠ 0 := by
    by_contra h
    push Not at h
    exact hU0 (MultilinearMap.ext h)
  obtain ⟨h1, h2⟩ := (mem_partFull θ M _ _ S s U).1 hU
  have h3 := (GlobalTheory.MultMem.mem_mult_iff ..).1 h1
  obtain ⟨B, hB', hb⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D V _ _ S hsph (U v)
    ⟨(h3.aut v).cont, (h3.aut v).left, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h3.aut v) (h3.cusp v)⟩ hv (h3.lev v) s
    fun P d R hR => h2 P d R hR v
  exact ⟨B, (GlobalTheory.LFun.isParamFunV_iff_of_mem_partFull hsph hU hv B).1 hB', fun w hw => (hb w hw).2⟩

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem under_mem_badPl (t : T) {PP : Pl D.host.E} (h : PP ∈ R.Pg ∨ PP ∈ R.Q t) :
    PP.under (𝓞 D.host.F) ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  exact Finset.mem_image.2 ⟨PP, Finset.mem_union.2 h, rfl⟩

theorem good_iff (t : T) (P : Pl D.host.E) : Good R t P ↔ P.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  constructor
  · intro h hm
    obtain ⟨PP, hPP, e⟩ := Finset.mem_image.1 hm
    obtain ⟨h1, h2⟩ := h PP (Finset.mem_union.1 hPP)
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h3 | h3
    · exact h1 h3.symm
    · exact h2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h3)
  · intro hw PP hPP
    exact ⟨fun e => hw (e ▸ under_mem_badPl R t hPP),
      fun e => hw (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e ▸ under_mem_badPl R t hPP)⟩

theorem paramsV {F : Face D A} (hC : Core R F) (i : Fin D.R.m) (t : T) (h) (hh : IsOpsV R i t h) (s y)
    (hy : IsEigV R i t h s y) (h0 : y ≠ 0) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B :=
  exists_param_definite (D.sp.V_sig _) (hC.models.vpos i) (R.cV i) (hC.models.cV i) (hC.lev.βV i) (L := R.datVt i t)
    (fun _ hPP => under_mem_badPl R t hPP) ((hC.models.HV i t).2.1.le (LinearMap.mem_range_self _ y))
    (fun e => h0 ((hC.models.HV i t).1 (e.trans (map_zero _).symm))) s fun P d hP hd =>
      (hh P ((good_iff R t P).2 hP) _ y).symm.trans
        ((congrArg (R.HV i t).e (hy P d ((good_iff R t P).2 hP) hd)).trans (map_smul _ _ _))

theorem paramsW (hP : GlobalTheory.Published.CuspRapidDecay) {F : Face D A} (hC : Core R F) (i : Fin D.R.m) (t : T) (c : Sys D)
    (hc : partW R i t c ≠ ⊥) : ∃ B', GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B' ∧
    ∀ w, Good R t w → ∀ a ∈ B' w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  obtain ⟨B, h1, h2⟩ := exists_param_part hP hC.models.inf (hC.lev.βW i) (L := R.datWp i R.triv)
    (fun PP hPP => under_mem_badPl R t (hPP.imp_right fun h => absurd h (Finset.notMem_empty _))) hc
  rw [rW] at h1 h2
  exact ⟨B, h1, fun w hw => h2 w ((good_iff R t w).1 hw)⟩

theorem paramsEx : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, ParamsEx R i t :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ R _ hG _ i t => ⟨paramsV R hG.core i t, paramsW R hP hG.core i t⟩

end GlobalTheory.DownLift.Params

end
