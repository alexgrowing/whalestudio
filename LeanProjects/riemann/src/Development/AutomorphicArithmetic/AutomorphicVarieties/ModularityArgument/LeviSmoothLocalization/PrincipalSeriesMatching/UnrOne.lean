import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchIndX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem unr_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    IsUnram (1 : kˣ →* ℂˣ) := by
  unfold IsUnram
  simp

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.indX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.IndX := by
  intro K M _ _ _ _ _ _ _ h2 P π hI v s s' hs hs' ξ hξ
  have hM := matchIndX K M h2 P π hI v s s' hs hs' ξ⁻¹ (IsSmoothChar.inv hξ.1)
  have hK := (polFacts (v.adicCompletion K)).2.2.2
  have e : ξ * ξ⁻¹ = 1 := mul_inv_cancel ξ
  have h1 : eval 1 (pol s ξ⁻¹) = 0 :=
    ((hK s _).2.2.1 1).2 ⟨ξ, hξ, by rw [e]; exact unr_one, by rw [e]; simp⟩
  have h0 := congrArg (Polynomial.eval 1) hM
  rw [h1, eval_prod, eq_comm, Finset.prod_eq_zero_iff] at h0
  obtain ⟨w, -, hw⟩ := h0
  rw [eval_comp, eval_pow, eval_X, one_pow] at hw
  have hL := polFacts (w.1.adicCompletion M)
  obtain ⟨ζ, hζ, hu, hval⟩ := ((hL.2.2.2 (s' w) _).2.2.1 1).1 hw
  refine ⟨w, ?_⟩
  have : ζ = ξ.comp (nm w) := by
    refine hL.2.1 _ _ hu ?_
    rw [mul_one, Units.val_eq_one] at hval
    exact mul_inv_eq_one.1 hval
  exact this ▸ hζ
