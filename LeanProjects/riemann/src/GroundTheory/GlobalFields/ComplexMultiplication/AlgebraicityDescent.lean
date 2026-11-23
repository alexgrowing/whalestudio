import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IntermediateField Polynomial

noncomputable section

namespace GroundTheory.Global

section Descent

variable {L : Type} [Field L] [CharZero L] [Algebra L ℂ] {W W' : WeierstrassCurve L} [W.IsElliptic]
  [W'.IsElliptic]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_map_eq_of_forall_conj_eq
    (ψ : Isogeny (W.baseChange ℂ) (W'.baseChange ℂ)) (h : ∀ g : ℂ ≃ₐ[L] ℂ, ψ.conj g = ψ) :
    ∃ φ : Isogeny W W', φ.map (algebraMap L ℂ) = ψ := by
  classical
  have hxfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.x = ψ.x := fun g ↦ by rw [← Isogeny.conj_alt_bis, h g]
  have hyfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.y = ψ.y := fun g ↦ by rw [← Isogeny.conj_y, h g]
  obtain ⟨r, hr⟩ := ψ.exists_ratEmb_eq_x
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_add_mul_genY (W.baseChange ℂ) ψ.y
  have ha' := ha
  have hb' := hb
  rw [← fieldRange_ratEmb] at ha' hb'
  obtain ⟨r₂, hr₂⟩ := ha'
  obtain ⟨r₃, hr₃⟩ := hb'
  change ratEmb (W.baseChange ℂ) r₂ = a at hr₂
  change ratEmb (W.baseChange ℂ) r₃ = b at hr₃
  have hab_fix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g a = a ∧ galFF W g b = b := by
    intro g
    have e := hyfix g
    rw [hab, map_add, map_mul, galFF_genY] at e
    exact eq_of_add_mul_genY_eq (galFF_mem_adjoin_genX W _ ha) (galFF_mem_adjoin_genX W _ hb)
      ha hb e
  have hlift : ∀ s : RatFunc ℂ, (∀ g : ℂ ≃ₐ[L] ℂ,
      galFF W g (ratEmb (W.baseChange ℂ) s) = ratEmb (W.baseChange ℂ) s) →
      (∃ p : L[X], p.map (algebraMap L ℂ) = s.num) ∧
        ∃ q : L[X], q.map (algebraMap L ℂ) = s.denom := by
    intro s hs
    have hc : ∀ c ∈ s.num.coeffs ∪ s.denom.coeffs, c ∈ Set.range (algebraMap L ℂ) := by
      intro c hc
      have hbot : c ∈ (⊥ : IntermediateField L ℂ) := by
        refine (mem_bot_iff_forall_algEquiv_apply_eq (F := L)).2 fun g ↦ ?_
        obtain ⟨h1, h2⟩ := map_eq_of_galFF_ratEmb W g (hs g)
        rcases Finset.mem_union.mp hc with hc | hc
        · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
          have := congrArg (coeff · n) h1
          simpa using this
        · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
          have := congrArg (coeff · n) h2
          simpa using this
      exact IntermediateField.mem_bot.1 hbot
    constructor
    · rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : s.num.coeff n = 0
      · exact ⟨0, by rw [hn, map_zero]⟩
      · exact hc _ (Finset.mem_union_left _ (coeff_mem_coeffs hn))
    · rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : s.denom.coeff n = 0
      · exact ⟨0, by rw [hn, map_zero]⟩
      · exact hc _ (Finset.mem_union_right _ (coeff_mem_coeffs hn))
  obtain ⟨⟨n₁, hn₁⟩, ⟨d₁, hd₁⟩⟩ := hlift r (fun g ↦ by rw [hr]; exact hxfix g)
  obtain ⟨⟨n₂, hn₂⟩, ⟨d₂, hd₂⟩⟩ := hlift r₂ (fun g ↦ by rw [hr₂]; exact (hab_fix g).1)
  obtain ⟨⟨n₃, hn₃⟩, ⟨d₃, hd₃⟩⟩ := hlift r₃ (fun g ↦ by rw [hr₃]; exact (hab_fix g).2)
  set X₁ := genX W
  set x₁ : W.toAffine.FunctionField := aeval X₁ n₁ / aeval X₁ d₁
  set y₁ : W.toAffine.FunctionField :=
    aeval X₁ n₂ / aeval X₁ d₂ + aeval X₁ n₃ / aeval X₁ d₃ * genY W
  have hrat : ∀ (s : RatFunc ℂ) (p q : L[X]), p.map (algebraMap L ℂ) = s.num →
      q.map (algebraMap L ℂ) = s.denom →
      ffMap (algebraMap L ℂ) W (aeval X₁ p / aeval X₁ q) = ratEmb (W.baseChange ℂ) s := by
    intro s p q hp hq
    conv_rhs => rw [← RatFunc.num_div_denom s]
    rw [ratEmb_div, map_div₀, ffMap_aeval, ffMap_aeval, ffMap_genX, hp, hq]
    rfl
  have hx₁ : ffMap (algebraMap L ℂ) W x₁ = ψ.x := by
    rw [← hr]
    exact hrat r n₁ d₁ hn₁ hd₁
  have hy₁ : ffMap (algebraMap L ℂ) W y₁ = ψ.y := by
    rw [hab, map_add, map_mul, ← hr₂, ← hr₃, hrat r₂ n₂ d₂ hn₂ hd₂, hrat r₃ n₃ d₃ hn₃ hd₃,
      ffMap_genY]
    rfl
  exact ⟨Isogeny.ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁,
    Isogeny.map_ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁⟩

omit [CharZero L] [W.IsElliptic] [W'.IsElliptic] in
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.invConst_congr {F : Type} [Field F]
    {C D C' D' : WeierstrassCurve F} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
    [D'.IsElliptic] (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    invConst (φ.congr hC hC') = invConst φ := by
  subst hC hC'
  rw [Isogeny.congr_rfl]

omit [CharZero L] in

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.invConst_conj (g : ℂ ≃ₐ[L] ℂ)
    (ψ : Isogeny (W.baseChange ℂ) (W'.baseChange ℂ)) : invConst (ψ.conj g) = g (invConst ψ) := by
  rw [Isogeny.conj, Isogeny.mapOf, Isogeny.invConst_congr, invConst_map]
  rfl

end Descent

namespace Elliptic

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]
include hK

theorem exists_isogeny_map_eq_of_cm (L : IntermediateField K ℂ) (W : WeierstrassCurve L)
    [W.IsElliptic] (hW : Nonempty (isogEnd (W.baseChange ℂ) ≃+* 𝓞 K))
    (ψ : Isogeny (W.baseChange ℂ) (W.baseChange ℂ)) :
    ∃ φ : Isogeny W W, φ.map (algebraMap L ℂ) = ψ := by
  refine ψ.exists_map_eq_of_forall_conj_eq fun g ↦ ?_
  obtain ⟨Λ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve (W.baseChange ℂ)
  have hΛ : latticeEnd Λ = cmRing (algebraMap K ℂ) := latticeEnd_eq_cmRing_of_ringEquiv
    (algebraMap K ℂ) hK Λ ((latticeEndEquiv Λ).trans ((vcEndEquiv C hC).symm.trans hW.some))
  have hmem : endConst (W.baseChange ℂ) ψ.toHom ∈ cmRing (algebraMap K ℂ) := by
    rw [← hΛ, ← range_endConst hC]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := (mem_cmRing (algebraMap K ℂ)).1 hmem
  have hfix : g (endConst (W.baseChange ℂ) ψ.toHom) = endConst (W.baseChange ℂ) ψ.toHom := by
    rw [← ha, IsScalarTower.algebraMap_apply K L ℂ]
    exact g.commutes _
  have hc : invConst (ψ.conj g) = invConst ψ := by
    rw [Isogeny.invConst_conj]
    rw [endConst_apply, homConst_toHom] at hfix
    exact hfix
  have e : endConst (W.baseChange ℂ) (ψ.conj g).toHom = endConst (W.baseChange ℂ) ψ.toHom := by
    rw [endConst_apply, endConst_apply, homConst_toHom, homConst_toHom, hc]
  have e' := congrArg Subtype.val (endConst_injective e)
  exact Isogeny.ext' e'

theorem CMCurve.exists_model_endomorphisms_defined (E : CMCurve K) :
    ∃ (W : WeierstrassCurve K⟮E.curve.j⟯) (_ : W.IsElliptic) (C : VariableChange ℂ),
      C • W.baseChange ℂ = E.curve ∧
        ∀ ψ : Isogeny (W.baseChange ℂ) (W.baseChange ℂ),
          ∃ φ : Isogeny W W, φ.map (algebraMap K⟮E.curve.j⟯ ℂ) = ψ := by
  classical
  set W := WeierstrassCurve.ofJ (⟨E.curve.j, mem_adjoin_simple_self K _⟩ : K⟮E.curve.j⟯)
  have hj : (W.baseChange ℂ).j = E.curve.j := by
    show (W.map (algebraMap K⟮E.curve.j⟯ ℂ)).j = _
    rw [map_j, ofJ_j]
    rfl
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq _ _ hj
  refine ⟨W, inferInstance, C, hC, fun ψ ↦ ?_⟩
  exact exists_isogeny_map_eq_of_cm hK K⟮E.curve.j⟯ W ⟨(vcEndEquiv C hC).trans E.endIso.some⟩ ψ

end Elliptic

end GroundTheory.Global
