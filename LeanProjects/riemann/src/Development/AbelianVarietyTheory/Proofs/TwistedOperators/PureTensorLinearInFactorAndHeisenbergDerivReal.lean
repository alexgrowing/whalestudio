import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergMatrixCoeffRealLineSkewStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAwayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlaceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PureLinear

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finite_of_eq_off {ι : Type} {a b : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite)
    (h : ∀ p, p ≠ q → b p = a p) : (Function.mulSupport b).Finite := by
  refine (ha.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    rw [Function.mem_mulSupport] at hp ⊢
    rwa [h p hpq] at hp

theorem exists_cofactor {ι : Type} {a : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite) :
    ∃ C : ℂ, ∀ b : ι → ℂ, (∀ p, p ≠ q → b p = a p) → ∏ᶠ p, b p = b q * C := by
  refine ⟨∏ᶠ (p) (_ : p ≠ q), a p, fun b hb => ?_⟩
  rw [← mul_finprod_cond_ne q (finite_of_eq_off q ha hb)]
  congr 1
  exact finprod_congr fun p => finprod_congr fun hp => hb p hp

private theorem lineAt_fin_eq_zero_and_inf_other_eq_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) (i : Fin m) (j : Fin n) :
    finPart D (lineAt θ τ z t i j) = 0 ∧ ∀ ρ, ρ ≠ τ → θ ρ (infPart D (lineAt θ τ z t i j)) = 0 := by
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  refine ⟨by simpa using congrFun (congrFun (hfin t) i) j, fun ρ hρ => ?_⟩
  have h := congrFun (congrFun (hcomp t ρ) i) j
  simp only [hρ, if_false] at h
  simpa [compAt] using h

private theorem ae_eq_zero_of_fin_zero_of_theta_inf_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (a : AE D) (h1 : finPart D a = 0)
    (h2 : ∀ ρ, θ ρ (infPart D a) = 0) : a = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  exact hσ.ext a h1 h2

variable {D : D7}

theorem wAt_lineAt_self {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) : wAt (.inr τ) (lineAt θ τ z t) = lineAt θ τ z t := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  simp only [wAt]
  rw [← sub_eq_zero]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_sub, map_mul, hf]
  · intro ρ
    rw [map_sub, map_sub, map_mul, map_mul]
    by_cases hρ : ρ = τ
    · subst hρ
      rw [(hid.2.2.2.2.2.2 θ hθ ρ).1, one_mul, sub_self]
    · rw [hr ρ hρ, mul_zero, sub_zero]

theorem wAt_lineAt_ne {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) {p : Place D} (hp : p ≠ .inr τ) : wAt p (lineAt θ τ z t) = 0 := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  simp only [wAt, Matrix.zero_apply, Pi.zero_apply]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_mul, hf]
  · intro ρ
    rw [map_mul, map_mul]
    rcases p with v | τ'
    · rw [(hid.2.2.2.1 v).1, map_zero, zero_mul]
    · have hτ' : τ' ≠ τ := fun h => hp (by rw [h])
      by_cases hρ : ρ = τ'
      · subst hρ
        rw [hr ρ hτ', mul_zero]
      · rw [(hid.2.2.2.2.2.2 θ hθ ρ).2 τ' (Ne.symm hρ), zero_mul]

theorem finite_ne_of_eq_off {ι X : Type} {x y : ι → X} {f₀ : X} (q : ι) (hx : {p | x p ≠ f₀}.Finite)
    (h : ∀ p, p ≠ q → y p = x p) : {p | y p ≠ f₀}.Finite := by
  refine (hx.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    simp only [Set.mem_setOf_eq] at hp ⊢
    rwa [h p hpq] at hp

theorem isPure_linear_and_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → (∀ (x y z : Place D → WO S T → ℂ) (f g : WO S T → ℂ) (q : Place D) (c : ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → y p = x p) → (∀ p, p ≠ q → z p = x p) → z q = c • x q + y q → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • f + g)) ∧ ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → (∀ p, p ≠ .inr τ → x' p = x p) → x' (.inr τ) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ)) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hthH : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  refine ⟨fun x y z f g q c hx hy hyx hzx hzq => ?_, fun x x' f τ z hx hx' hxτ => ?_⟩
  · unfold IsPure IsRestricted at hx hy ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx
    obtain ⟨⟨hyl, -⟩, hgθ, hyw⟩ := hy
    have hzl : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (z p) := by
      intro p
      by_cases hp : p = q
      · rw [hp, hzq]
        exact ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x q) (hxl q).1).2 q (hxl q)).2.1 c (y q) (hyl q)
      · rw [hzx p hp]
        exact hxl p
    refine ⟨⟨hzl, finite_ne_of_eq_off q hxfin hzx⟩,
      GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul c hfθ) hgθ, fun w => ?_⟩
    obtain ⟨hxs, hxe⟩ := hxw w
    obtain ⟨-, hye⟩ := hyw w
    obtain ⟨C, hC⟩ := exists_cofactor q hxs
    have ha := hC (fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) (fun _ _ => rfl)
    have hb := hC (fun p => ipO μ 𝓕 (y p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hyx p hp])
    have hd := hC (fun p => ipO μ 𝓕 (z p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hzx p hp])
    beta_reduce at ha hb hd
    refine ⟨finite_of_eq_off q hxs (fun p hp => by simp only [hzx p hp]), ?_⟩
    have hG := hthH w f₀ hf₀
    have hGq := hthH (wAt q w) f₀ hf₀
    have e1 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (c • f) (heisO ψ S T w f₀) (GlobalTheory.WeilVacMove.isTheta_smul c hfθ) hG
    have e2 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w f₀) hfθ hG
    have e3 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (c • x q) (heisO ψ S T (wAt q w) f₀)
      (GlobalTheory.WeilVacMove.isTheta_smul c (hxl q).1) hGq
    have e4 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x q) (heisO ψ S T (wAt q w) f₀) (hxl q).1 hGq
    rw [hd, hzq, (e3.2.2.2.1 (y q) (hyl q).1).1, (e4.2.2.1 c).1, (e1.2.2.2.1 g hgθ).1, (e2.2.2.1 c).1,
      hxe, hye, ha, hb]
    ring
  · have hx1 := hx
    unfold IsPure IsRestricted at hx1 ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx1
    have hx'l : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (x' p) := by
      intro p
      by_cases hp : p = .inr τ
      · rw [hp, hxτ]
        exact ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x (.inr τ)) (hxl _).1).2 (.inr τ) (hxl _)).2.2 τ rfl z
      · rw [hx' p hp]
        exact hxl p
    refine ⟨⟨hx'l, finite_ne_of_eq_off (.inr τ) hxfin hx'⟩,
      GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hfθ, fun w => ?_⟩
    obtain ⟨hxs, -⟩ := hxw w
    obtain ⟨C, hC⟩ := exists_cofactor (.inr τ) hxs
    have key : ∀ t : ℝ, ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀) =
        ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C := by
      intro t
      have hP := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx (lineAt θ τ z t)
      unfold IsPure at hP
      have e := hC (fun p => ipO μ 𝓕 (heisO ψ S T (wAt p (lineAt θ τ z t)) (x p)) (heisO ψ S T (wAt p w) f₀))
        (fun p hp => by simp only [wAt_lineAt_ne hθ τ z t hp, GlobalTheory.WeilVacMove.heisO_zero])
      beta_reduce at e
      rw [(hP.2.2 w).2, e, wAt_lineAt_self hθ τ z t]
    have hG := hthH w f₀ hf₀
    have h1 := (GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ f (heisO ψ S T w f₀) hfθ hG τ z).1
    have h2 := ((GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ (x (.inr τ)) (heisO ψ S T (wAt (.inr τ) w) f₀)
      (hxl _).1 (hthH _ _ hf₀) τ z).1).mul_const C
    have h3 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀))
        (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C) 0 := by
      simpa only [key] using h2
    have hd := hC (fun p => ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hx' p hp])
    beta_reduce at hd
    refine ⟨finite_of_eq_off (.inr τ) hxs (fun p hp => by simp only [hx' p hp]), ?_⟩
    rw [hd, hxτ, h1.unique h3]

end GlobalTheory.PureLinear

end
