import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGLStatement
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.compUnit :
    UpperTheory.Gal.TP.Loc.CompUnit := by
  intro E _ _ _ n U hU w hw τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨B, hh, hp, hd, hi⟩ := GlobalTheory.DefU.Petersson.exists_invariant_pos_form E n
  obtain ⟨hirr, f, h0, hf, h2⟩ := hτ
  have key : ∀ g, ∃ x : GlobalTheory.UnitaryBC.UA E n, ∀ v, f (τ.ρ g v) = GlobalTheory.UnitaryBC.RU E n x (f v) := fun g =>
    ⟨(e.symm g).1, fun v => by
      have h3 := h2 (e.symm g) v
      have hy : ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU n w).subtype) (e.symm g) = g := by
        have := he (e.symm g)
        rw [e.apply_symm_apply] at this
        exact this.symm
      rw [hy] at h3
      exact h3⟩
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    have hst : ∀ g, ∀ v ∈ LinearMap.ker f, τ.ρ g v ∈ LinearMap.ker f := fun g v hv => by
      obtain ⟨x, hx⟩ := key g
      rw [LinearMap.mem_ker, hx, LinearMap.mem_ker.1 hv, map_zero]
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr).2 (LinearMap.ker f) hst with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0
  let f' : τ.V →ₗ[ℂ] GlobalTheory.DefU.autU E n := f.codRestrict _ (fun v => hU.aut _ (hf v))
  have hf' : ∀ v, f' v = 0 → v = 0 := fun v h =>
    hinj ((congrArg Subtype.val h).trans (map_zero f).symm)
  have heq : ∀ g, ∃ x, ∀ v, f' (τ.ρ g v) = GlobalTheory.DefU.autRep E n x (f' v) := fun g => by
    obtain ⟨x, hx⟩ := key g
    exact ⟨x, fun v => Subtype.ext (hx v)⟩
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v u => B (f' u) (f' v))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp), ?_, ?_, ?_⟩
  · intro v u
    simpa using (hh (f' u) (f' v)).symm
  · intro v hv
    have hne : B (f' v) (f' v) ≠ 0 := fun h => hv (hf' v (hd _ h))
    have him : (B (f' v) (f' v)).im = 0 := by
      have := congrArg Complex.im (hh (f' v) (f' v))
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    have hre : (B (f' v) (f' v)).re ≠ 0 := fun h => hne (Complex.ext h him)
    exact lt_of_le_of_ne (hp _) (Ne.symm (by simpa using hre))
  · intro g v u
    obtain ⟨x, hx⟩ := heq g
    simp only [LinearMap.mk₂'ₛₗ_apply, hx]
    exact hi x _ _
