import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

namespace UpperTheory.Gal.Int.Div

theorem algGen_of : AlgGen := by
  intro a q B hq hB
  have hz : ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) ^ (((a : ℝ) - 1) / 2) := Real.rpow_pos_of_pos (by positivity) _
    exact_mod_cast this.ne'
  have := UpperTheory.Gal.crystallineComparison.genScale_of B _ hz hB
  convert this using 1
  simp [algSat, Multiset.bind_def, Multiset.pure_def]

theorem detFrob_of : DetFrob := by
  intro E Ω _ _ _ _ _ _ l _ ι a U ψ hψ w hw hl B hB A hA
  obtain ⟨J, hJ, -⟩ := hψ.2 w hw B hB
  obtain ⟨h1, h2⟩ := hJ hl A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have := congrArg (fun g : GL (Fin 1) (Qbar l) => g.val 0 0) (h1 s hs)
    exact Units.ext (by simpa [rk1] using this)
  · have := congrArg (fun p : ℂ[X] => p.coeff 0) (h2 σ hσ)
    simpa [rk1, Matrix.charpoly, Matrix.det_fin_one] using this

theorem frobSeed_of (h1 : InFacts) (h2 : GenPin) (h3 : AlgGen) (h4 : DetFrob) : FrobeniusCondition := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ψ hψ r ρ hin hdet w hw hl B hB hg he A hA
  obtain ⟨-, i1, i2⟩ := h1 _ _ a dd r ρ hin
  obtain ⟨e1, e2⟩ := he A hA
  refine ⟨fun s hs => i1 s (e1 s hs), fun σ hσ => ?_⟩
  have hc : B.card = a := hB.choose_spec.2.card
  refine h2 l ι a _ _ (by simp [algSat, hc]) (h3 a _ B (GlobalTheory.LFun.qV_ne_zero w) hg) (i2 σ⁻¹ _ (e2 σ hσ)) ?_
  rw [hdet]
  exact (h4 E Ω l ι a U ψ hψ w hw hl B hB A hA).2 σ hσ

theorem centU_of (h1 : ZetaEx) (h2 : ZetaLoc) (h3 : SchurU) (h4 : CharOfZeta) (h5 : AlgOfFix) (h6 : SatCent) : CentU := by
  intro E _ _ _ a ha U hU
  obtain ⟨ζ, z1, z2, z3, z4, z5⟩ := h1 E a
  obtain ⟨χ, hχ⟩ := h4 E a U hU ζ z2 z3 z4 fun z => h3 E a U hU _ (z3 z)
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 hU.ne_bot
  obtain ⟨n, hn⟩ := h5 E χ fun z hz => by
    have := hχ z φ hφ
    rw [z5 z hz, map_one] at this
    refine Units.ext (smul_left_injective ℂ hφ0 ?_)
    simpa using this.symm
  refine ⟨χ, n, hn, fun w hw B hB => ?_⟩
  obtain ⟨σ, ⟨hirr, f, hf0, hfU, hfe⟩, hS⟩ := hB
  obtain ⟨x, hx0, hx1, hx2⟩ := h6 E a w σ B hS
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hker : LinearMap.ker f = ⊥ := ((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 hirr).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have h1 := hfe (e.symm g) v
      rw [MonoidHom.comp_apply, Subgroup.subtype_apply, ← he, e.apply_symm_apply] at h1
      rw [h1, hv, map_zero]) |>.resolve_right fun h => hf0 (LinearMap.ker_eq_top.1 h)
  have hfx : f x ≠ 0 := (map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hker)).2 hx0
  have key : ∀ u : (w.adicCompletion E)ˣ, f (σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin a) u) x) =
      ((χ.loc w u : ℂˣ) : ℂ) • f x := fun u => by
    obtain ⟨m1, m2⟩ := h2 E a ζ z1 w hw u
    have := hfe ⟨_, m1⟩ x
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, m2] at this
    exact this.trans (hχ _ _ (hfU x))
  refine ⟨fun u hu => ?_, ?_⟩
  · have := key u
    rw [hx1 u hu] at this
    refine Units.ext (smul_left_injective ℂ hfx ?_)
    simpa using this.symm
  · have := key (atFin w (unif w))
    rw [hx2 _ (unif_spec w), map_smul] at this
    exact Units.ext (smul_left_injective ℂ hfx this.symm)

end UpperTheory.Gal.Int.Div
