import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.satConj_of :
    LocIso → SatConj := by
  intro hL E _ _ _ a U hU w hw ⟨B, σ, ⟨hirr, f, hf0, hfU, hfe⟩, hB⟩
  obtain ⟨hloc, β, hβ, hK, -⟩ := hL E a w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hpe : ∀ g, cLoc w ((e.symm g : locU a w) : UA E a) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hker : LinearMap.ker f = ⊥ := ((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 hirr).2 _ (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 := hfe (e.symm g) v
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, hpe] at h1
    rw [h1, hv, map_zero]) |>.resolve_right fun h => hf0 (LinearMap.ker_eq_top.1 h)
  have h0 : f x ≠ 0 := (map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hker)).2 hx.1
  obtain ⟨hne, hund, -⟩ := GlobalTheory.SplitPts.over_split hw
  have hs : IsSplitAt (cpl w) := ⟨w, hne.symm, hund.symm⟩
  have hfix : ∀ y ∈ locU a (cpl w), cLoc (cpl w) y ∈ GlobalTheory.LFun.KGL (cpl w) a → RU E a y (f x) = f x := by
    intro y hy hk
    have hy' : y ∈ locU a w := hloc ▸ hy
    have hk' : cLoc w y ∈ GlobalTheory.LFun.KGL w a := by
      rw [← hβ y]
      exact hK _ hk
    have h2 := GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ hk'
    have h1 := hfe ⟨y, hy'⟩ x
    change f (σ.ρ (cLoc w y) x) = RU E a y (f x) at h1
    rw [h2] at h1
    exact h1.symm
  obtain ⟨σ', S, hc, hS, -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU (cpl w) hs (f x) (hfU x) h0 hfix
  exact ⟨S, σ', hc, hS⟩
