import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_prim_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q,
    IsPer u.ex u.Λ x q → ∀ c, Hyp1.mk _ c = x → ∃ h, IsPrim u.ex c h ∧
      ∀ (U : A.left.affineOpens) (l : u.Λ), ∀ z ∈ pre u.ex U.1, h U (z + l) = h U z + q l := by
  intro A _ g L u x q hx c hc
  obtain ⟨hOpen, hDiff, -, hPer, -, -, -, -, hRes, hHom, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  obtain ⟨c₀, h₀, hc₀, ⟨p1, p2, p3⟩, hp⟩ := hx
  obtain ⟨b, hb⟩ := Hyp1.mk_eq_mk.1 (hc.trans hc₀.symm)
  have hval_add : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s + t) z = val u.ex U s z + val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_add]
  have hval_sub : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s - t) z = val u.ex U s z - val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_sub]
  have hcf : ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V),
      c.1.1 (Opposite.op U) (Opposite.op V) a = c₀.1.1 (Opposite.op U) (Opposite.op V) a +
        (b (Opposite.op V) - Sec.res (str A) (leOfHom a.unop) (b (Opposite.op U))) := by
    intro U V a
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.1 (Opposite.op U) (Opposite.op V) a) hb
    simp only [dTot0_f] at this
    exact (eq_add_of_sub_eq' this.symm :)
  have hcω : ∀ U : A.left.affineOpens, c.1.2 (Opposite.op U) =
      c₀.1.2 (Opposite.op U) + KaehlerDifferential.D ℂ _ (b (Opposite.op U)) := by
    intro U
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.2 (Opposite.op U)) hb
    simp only [dTot0_ω] at this
    change _ = (c.1 - c₀.1).2 _ at this
    rw [this]
    change c.1.2 _ = c₀.1.2 _ + (c.1.2 _ - c₀.1.2 _)
    abel
  refine ⟨fun U z ↦ h₀ U z + val u.ex U.1 (b (Opposite.op U)) z, ⟨fun U ↦ ?_, fun U V a z hz ↦ ?_, fun U z hz ↦ ?_⟩,
    fun U l z hz ↦ ?_⟩
  · exact (p1 U).add (hDiff U.1 _)
  · have hle : V.1 ≤ U.1 := leOfHom a.unop
    have hr : val u.ex V.1 (Sec.res (str A) hle (b (Opposite.op U))) z = val u.ex U.1 (b (Opposite.op U)) z :=
      hRes U.1 V.1 hle _ z hz
    simp only
    rw [p2 U V a z hz, hcf U V a, hval_add _ _ _ z hz, hval_sub _ _ _ z hz, hr]
    ring
  · have hd₀ : DifferentiableAt ℂ (h₀ U) z := ((p1 U) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    have hd₁ : DifferentiableAt ℂ (val u.ex U.1 (b (Opposite.op U))) z :=
      ((hDiff U.1 _) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    obtain ⟨-, -, hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz
    change fderiv ℂ (h₀ U + val u.ex U.1 (b (Opposite.op U))) z = _
    rw [fderiv_add hd₀ hd₁, p3 U z hz, hcω U, map_add, hD]
  · simp only
    rw [hp U l z hz]
    erw [hPer]
    ring

end GlobalTheory.CechPer
