import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem index_eq_of_marked_isometry {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (hr : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H Dw.p Dw.q ty) (k k' : Fin F.n) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La)
    (hEF : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b)
    (hM : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F.t k' a + l.M • x)
    (hA : ∀ a, ∃ x, gam (F.t k a) = F.t k' a + l.A • x) : k = k' := by
  obtain ⟨-, P', hP'⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di k') g ty
    (by rw [(F.sig k').1, (F.sig k').2]; exact hty)
  have hP := GlobalTheory.ClassUniq.isPeriod_comp_isometry gam hEF hP'
  set P := P'.comp gam.toLinearMap.toAddMonoidHom with hPdef
  refine F.disj k k' P P' hP hP' ?_
  exact (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g ty
    hr hσ hty (F.Di k) (F.Di k')
    (F.t k) (F.t k') P P' (F.u k P) (F.u k' P') (F.ex k P) (F.ex k' P')
    ⟨F.over_σ k P hP, hP, ⟨F.ex_add k P hP, F.ex_onto k P hP, GlobalTheory.ClassUniq.isHolTo_ex F k P hP,
      (F.ex_diff k P hP).1, (F.ex_diff k P hP).2⟩, F.ex_ker k P hP, F.ex_lin k P hP, F.ex_weil k P hP,
      F.ex_eta k P hP, F.ex_etaA k P hP⟩
    ⟨F.over_σ k' P' hP', hP', ⟨F.ex_add k' P' hP', F.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F k' P' hP',
      (F.ex_diff k' P' hP').1, (F.ex_diff k' P' hP').2⟩, F.ex_ker k' P' hP', F.ex_lin k' P' hP',
      F.ex_weil k' P' hP', F.ex_eta k' P' hP', F.ex_etaA k' P' hP'⟩).2
    ⟨gam, LinearEquiv.refl ℂ _, hEF, hM, hA, fun a => rfl⟩

theorem UW.ik_injective {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (W : UW U) :
    Function.Injective W.ik := by
  obtain ⟨hr, hX, -, hfib, -⟩ := hU
  obtain ⟨g, e, F, ik, φ, hEF, hP⟩ := W
  intro k k' hk
  change ik k = ik k' at hk
  obtain ⟨x, hx⟩ := CompInj.dom_nonempty (U.X k)
  obtain ⟨x₀, hx₀⟩ := CompInj.dom_nonempty (U.X k')
  obtain ⟨P, -, hper, hpt, hder, -⟩ := hP k ⟨x, hx⟩
  obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
  have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2.1⟩ : _ ∧ _ ∧ _)
  have hEF' := hEF k'
  generalize φ k' = ψ at hP₀ hP' hEF'
  clear hP hEF φ
  generalize ik k' = n at *
  subst hk
  obtain ⟨x', hx', hPx⟩ := CompInj.exists_frame hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1 (F.sig _).2
    ψ hEF' x₀ hx₀ P₀ hP₀ hper₀ P hper
  obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
  obtain rfl : P = P' := by
    ext a j
    rw [hPx, hP']
  have hbor := CompInj.frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
    ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
  obtain ⟨ga, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
  exact (congrArg Sigma.fst h).symm

theorem comp_eq_of_matched : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (W : UW U) (k k' : U.Comp), SameSp (U.X k) (U.X k') → ∀ ga : GL (Fin r) E, IsUn (U.X k) ga → mapL ga (U.X k).Λ = (U.X k').Λ → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ (U.X k').Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ W.mark k a = W.mark k' a + l.M • u) → k = k' := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h1 hA W k k' hS ga hun hΛ hm
  apply W.ik_injective hσ hU h1
  have hinj : Function.Injective
      ((Matrix.toLin' (ga : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)) := by
    intro u v huv
    have h : (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = (ga : Matrix (Fin r) (Fin r) E) *ᵥ v := huv
    have h2 := congrArg (fun w => ((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) h
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using h2
  let ψ : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ :=
    (Submodule.equivMapOfInjective _ hinj (U.X k).Λ).trans (LinearEquiv.ofEq _ _ hΛ)
  let gam : (W.F.Di (W.ik k)).La ≃ₗ[𝓞 E] (W.F.Di (W.ik k')).La := (W.φ k).trans (ψ.trans (W.φ k').symm)
  have hgam : ∀ a, (W.φ k' (gam a) : Fin r → E) = (ga : Matrix (Fin r) (Fin r) E) *ᵥ (W.φ k a : Fin r → E) := by
    intro a
    change (W.φ k' ((W.φ k').symm (ψ (W.φ k a))) : Fin r → E) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  refine index_eq_of_marked_isometry W.F (hU.1 ▸ h1) hσ
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw W.g W.e) _ _ gam (fun a b => ?_) (fun a ha => ?_) fun a => ?_
  · have h := W.isom k' (gam a) (gam b)
    rw [hgam, hgam, ← hS.gm, ← hS.xi, hun, ← W.isom k a b] at h
    exact_mod_cast h
  · obtain ⟨w, hw, h⟩ := hm a ha
    refine ⟨(W.φ k').symm ⟨w, hw⟩, (W.φ k').injective (Subtype.ext ?_)⟩
    rw [hgam, map_add, map_nsmul, LinearEquiv.apply_symm_apply]
    exact h
  · exact ⟨gam (W.F.t _ a) - W.F.t _ a, by rw [hA, one_smul, add_sub_cancel]⟩

end GlobalTheory.Dict
