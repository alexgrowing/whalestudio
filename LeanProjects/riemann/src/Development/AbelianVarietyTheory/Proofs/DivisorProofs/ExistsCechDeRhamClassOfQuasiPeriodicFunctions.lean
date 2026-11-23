import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRestrictionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedAlgebraicFormFderivUniformisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerOneFormEqZeroOfUniformisedValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer

theorem exists_isPer_of_quasiPeriodic : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ U, DifferentiableOn ℂ (k U) (pre u.ex U.1)) → (∀ U V : A.left.affineOpens, V ≤ U → IsReg u.ex V.1 (k V - k U)) → (∀ U a, IsReg u.ex U.1 fun z => fderiv ℂ (k U) z (Pi.single a 1)) → (∀ U (l : u.Λ), ∀ z ∈ pre u.ex U.1, k U (z + l) = k U z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  intro A _ g L u hA k q hk hreg hder hper
  obtain ⟨hopen, hdiff, -, -, -, hmono, -, -, hres, hev, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  have hf : ∀ (U V : A.left.affineOpens) (_ : Opposite.op U ⟶ Opposite.op V), ∃ b : Sec (str A) V.1,
      ∀ z ∈ pre u.ex V.1, (k V - k U) z = val u.ex V.1 b z :=
    fun U V a => hreg U V (leOfHom a.unop)
  choose f hf using hf
  have hω : ∀ U : A.left.affineOpens, ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧
      ∀ z ∈ pre u.ex U.1, fderiv ℂ (k U) z = evForm u.ex U.1 z ξ :=
    fun U => GlobalTheory.T.exists_closed_algebraic_form_fderiv_uniformised A g L u hA U (k U) (hk U) (hder U)
  choose ω hωc hωe using hω
  have hsub : ∀ (U : A.left.Opens) (b b' : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (b - b') z = val u.ex U b z - val u.ex U b' z := by
    intro U b b' z hz
    obtain ⟨e, he⟩ := hev U z hz
    exact (he _).trans ((map_sub e b b').trans (congrArg₂ (· - ·) (he b).symm (he b').symm))
  have hadd : ∀ (U : A.left.Opens) (b b' : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (b + b') z = val u.ex U b z + val u.ex U b' z := by
    intro U b b' z hz
    obtain ⟨e, he⟩ := hev U z hz
    exact (he _).trans ((map_add e b b').trans (congrArg₂ (· + ·) (he b).symm (he b').symm))
  have hfun : ∀ (U V W : A.left.affineOpens) (φ : Opposite.op U ⟶ Opposite.op V) (ψ : Opposite.op V ⟶ Opposite.op W),
      f U W (φ ≫ ψ) = Sec.res (str A) (show W.1 ≤ V.1 from leOfHom ψ.unop) (f U V φ) + f V W ψ := by
    intro U V W φ ψ
    have hle : W.1 ≤ V.1 := leOfHom ψ.unop
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA W.1
      (f U W (φ ≫ ψ) - (Sec.res (str A) hle (f U V φ) + f V W ψ) : Sec (str A) W.1) fun z hz => ?_)
    have e1 := hsub W.1 (f U W (φ ≫ ψ)) (Sec.res (str A) hle (f U V φ) + f V W ψ) z hz
    have e2 := hadd W.1 (Sec.res (str A) hle (f U V φ)) (f V W ψ) z hz
    have e3 := hres V.1 W.1 hle (f U V φ) z hz
    have e4 := hf U W (φ ≫ ψ) z hz
    have e5 := hf U V φ z (hmono _ _ hle hz)
    have e6 := hf V W ψ z hz
    simp only [Pi.sub_apply] at e4 e5 e6
    linear_combination e1 - e2 - e3 - e4 + e5 + e6
  have hform : ∀ (U V : A.left.affineOpens) (φ : Opposite.op U ⟶ Opposite.op V),
      ω V = p1 (OAff (str A)) φ (ω U) + KaehlerDifferential.D ℂ (Sec (str A) V.1) (f U V φ) := by
    intro U V φ
    refine sub_eq_zero.1 (GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values A g L u hA V _ fun z hz => ?_)
    have hle : V.1 ≤ U.1 := leOfHom φ.unop
    have hz' : z ∈ pre u.ex U.1 := hmono _ _ hle hz
    have e1 := GlobalTheory.T.evForm_restriction_eq A g L u U V φ (ω U) z hz
    have e2 := (GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u V.1 z hz).2.2 (f U V φ)
    have heq : k V =ᶠ[nhds z] k U + val u.ex V.1 (f U V φ) := by
      filter_upwards [(hopen _).mem_nhds hz] with w hw
      have := hf U V φ w hw
      simp only [Pi.sub_apply] at this
      simp only [Pi.add_apply]
      linear_combination this
    have e3 : fderiv ℂ (k V) z = fderiv ℂ (k U) z + fderiv ℂ (val u.ex V.1 (f U V φ)) z :=
      heq.fderiv_eq.trans (fderiv_add ((hk _).differentiableAt ((hopen _).mem_nhds hz'))
        ((hdiff _ _).differentiableAt ((hopen _).mem_nhds hz)))
    refine (map_sub (evForm u.ex V.1 z) _ _).trans (sub_eq_zero.2 ?_)
    refine Eq.trans ?_ (map_add (evForm u.ex V.1 z) _ _).symm
    exact (hωe V z hz).symm.trans (e3.trans (congrArg₂ (· + ·) ((hωe U z hz').trans e1.symm) e2.symm))
  let c0 : Tot1 (OAff (str A)) := (fun U V a => f U.unop V.unop a, fun U => ω U.unop)
  have hc : c0 ∈ cechDeRhamTotalCocyclesOne (OAff (str A)) :=
    mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨fun T T' T'' φ ψ => hfun T.unop T'.unop T''.unop φ ψ, fun T T' φ => hform T.unop T'.unop φ,
      fun T => hωc T.unop⟩
  refine ⟨Hyp1.mk _ ⟨c0, hc⟩, ⟨c0, hc⟩, k, rfl, ⟨hk, fun U V a z hz => ?_, fun U z hz => hωe U z hz⟩, hper⟩
  have := hf U V a z hz
  simp only [Pi.sub_apply] at this
  change k V z = k U z + val u.ex V.1 (f U V a) z
  linear_combination this

end GlobalTheory.CechPer
