import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicSideEmptyLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NbcOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeSideStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerTailStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DaAutRepSphAt
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end GlobalTheory.AutQuot
namespace GlobalTheory.AutQuot
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
theorem locOf_eq_alt {π : NG.AutRep D.host.E D.R.nV} {w : PlE D.host} {x} (hx : LocAt π w x) :
    _root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep w = (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x) := by
  have hex : ∃ x, LocAt (clsA π).rep w x := by
    obtain ⟨s, σ, hs, -, -⟩ := hx
    subst hs
    exact locAt_of_split _ s
  unfold _root_.GlobalTheory.AutQuot.locOf_alt
  rw [dif_pos hex, locAt_unique (rep_iso π) hex.choose_spec hx]
end
end GlobalTheory.AutQuot
namespace GlobalTheory.AutQuot
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
theorem f_sph_alt (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : NG.OverPl w v) : (∃ v', NG.OverPl w v' ∧ (clsA π).rep.SphericalAtPlace v') ↔ π.SphericalAtPlace v := by
  constructor
  · rintro ⟨v', hv', hs⟩
    rw [overPl_unique hv hv']
    exact _root_.UpperTheory.One.M.New.sphAt_iso (rep_iso π) hs
  · intro hs
    exact ⟨v, hv, _root_.UpperTheory.One.M.New.sphAt_iso (autIso_symm (rep_iso π)) hs⟩
theorem unr_locOf_of_sphAt (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (hs : π.SphericalAtPlace s.v) :
    D.naut.unr (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep s.w) := by
  obtain ⟨x, hx⟩ := locAt_of_split π s
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T hx, T.unr, Equiv.apply_symm_apply]
  exact _root_.GlobalTheory.T.locRecT_unr_of_sphAt hL D π s x hx hs
theorem f_locPol_alt (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ)
    (J : Subgroup (GAf D.host.E D.R.nV)) (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV))
    (f : GAf D.host.E D.R.nV → π.W) (hf : f ∈ π.S) (hf0 : f ≠ 0)
    (hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) (c : ℕ → ℂ)
    (hc' : ∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) :
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep w) ((1 - (D.R.nV : ℝ)) / 2)) := by
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_localComponent_conj_splitPlace D π s w hc
  obtain ⟨hun, hpol⟩ := _root_.GlobalTheory.T.spherical_vector_fixed_local_alt hL D π s w ϖ hc hu J hJ f hf hf0 hfix c hc' x hx
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T hx]
  have hu2 : D.naut.unr (D.naut.lpTw ((T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x))
      ((1 - (D.R.nV : ℝ)) / 2)) := by
    rw [T.unr, T.tw, Equiv.apply_symm_apply]; exact hun
  unfold galPol
  rw [T.frobEig _ _ hu2, T.tw, Equiv.apply_symm_apply]
  exact hpol
theorem e_locOf_eq_locRecT_of_isLocS (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E))) (hσ : IsLocS π.S s σ) :
    T.e s.w (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep s.w) =
      _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls σ) := by
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T ⟨s, σ, rfl, hσ, HEq.rfl⟩, Equiv.apply_symm_apply]
set_option maxHeartbeats 1000000 in
theorem exists_nbc_auSide_true_of_empty (hE : IsEmpty D.nd.Loc) :
    ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A :=
  ⟨{ _root_.GlobalTheory.AutQuot.boundaryConditionOfNoLocal hL D T hE with
      sphAU := fun _ X w => ∃ v, NG.OverPl w v ∧ (AUq.rep X).SphericalAtPlace v
      embAV_sph := fun i => isEmptyElim i },
    { cls := fun _ _ _ π => clsA π
      surj := fun _ _ _ X => ⟨X.rep, AUq.cls_rep X⟩
      iso := fun _ _ _ π π' => clsA_eq_iff π π'
      mult := fun _ _ _ π => GlobalTheory.T.automorphic_multiplicity_eq_of_iso _ _ _ _ (rep_iso π)
      sph := fun _ _ _ π w v _ hv => _root_.GlobalTheory.AutQuot.f_sph_alt D π w v hv
      sat := fun _ _ _ π v w hv Dv hα => f_sat D π v w hv Dv hα
      clsWt := fun _ _ _ a => clsW a
      surjWt := fun _ _ _ Y => ⟨Y.rep, WtQ.cls_rep Y⟩
      isoWt := fun _ _ _ a b => clsW_eq_iff a b
      wt := fun _ _ _ π a hd => f_wt D π a hd
      infW := fun _ _ _ a τ lam hl => f_infW D a τ lam hl
      locUnr := fun _ _ _ π s hs => _root_.GlobalTheory.AutQuot.unr_locOf_of_sphAt hL D T π s hs
      locPol := fun _ _ _ π s w ϖ hc hu J hJ f hf hf0 hfix c hc' => _root_.GlobalTheory.AutQuot.f_locPol_alt hL D T π s w ϖ hc hu J hJ f hf hf0 hfix c hc' },
    fun _ _ _ π s σ hσ => _root_.GlobalTheory.AutQuot.e_locOf_eq_locRecT_of_isLocS hL D T π s σ hσ⟩
end
end GlobalTheory.AutQuot
open Formalism.BasicNotions GlobalTheory.HeightCounting in
theorem GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), IsEmpty D.nd.Loc →
    ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A :=
  fun hL D hE T => _root_.GlobalTheory.AutQuot.exists_nbc_auSide_true_of_empty hL D T hE
end
end
