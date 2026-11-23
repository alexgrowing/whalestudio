import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.SelfDualIsom

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {M₁ M₂ V : Type}
    [AddCommGroup M₁] [Module (𝓞 E) M₁] [Module.Finite (𝓞 E) M₁]
    [AddCommGroup M₂] [Module (𝓞 E) M₂] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (φ₁ : M₁ →ₗ[𝓞 E] V) (φ₂ : M₂ →ₗ[𝓞 E] V)
    (hspan : Submodule.span E (Set.range φ₂) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, (N : 𝓞 E) • φ₁ x ∈ LinearMap.range φ₂ := by
  classical
  have h1 : ∀ v : V, ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ LinearMap.range φ₂ := by
    intro v
    have hv : v ∈ Submodule.span E (Set.range φ₂) := by rw [hspan]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
    rw [← LinearMap.coe_range, Submodule.span_eq] at ht
    have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero t.2
    have hm := Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)})
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ht0
    · rw [← hc, mul_smul]
      exact Submodule.smul_mem _ _ ht
  choose n hn hmem using h1
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M₁)
  refine ⟨∏ x ∈ s, n (φ₁ x), Finset.prod_pos fun x _ => hn _, fun x => ?_⟩
  have hx : x ∈ Submodule.span (𝓞 E) (s : Set M₁) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ₁ x)) (Finset.mem_coe.1 hy)
    rw [hk, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hmem _)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ _ ha

theorem exists_scaled_isometry : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D₁ D₂ : Datum H), D₁.p = D₂.p → D₁.q = D₂.q → ∃ (N : ℕ) (f : D₁.La →ₗ[𝓞 E] D₂.La), 0 < N ∧ Function.Injective f ∧ ∀ x y, D₂.EF (f x) (f y) = (N : ℤ) ^ 2 * D₁.EF x y := by
  intro hH E _ _ _ H D₁ D₂ hp hq
  have hL := GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt hH
  have hξ := GlobalTheory.OneSpace.cc_rt H
  obtain ⟨Gm, φ₂, hM₂⟩ := GlobalTheory.exists_herm_coord_of_datum E H D₂ (H.rt : E) hξ (GlobalTheory.OneSpace.rt_ne H) _ rfl
  obtain ⟨φ₁, hinj₁, -, -, -, hEF₁⟩ :=
    GlobalTheory.model_in_same_space hL hH E H D₂ D₁ _ (H.rt : E) Gm φ₂ hp hq hξ hM₂
  obtain ⟨hinj₂, hspan₂, -, -, hEF₂⟩ := hM₂
  have := D₁.fin
  obtain ⟨N, hN, hmem⟩ := exists_nat_smul_mem φ₁ φ₂ hspan₂
  let g : D₁.La →ₗ[𝓞 E] LinearMap.range φ₂ := ((N : 𝓞 E) • φ₁).codRestrict _ hmem
  let f : D₁.La →ₗ[𝓞 E] D₂.La := (LinearEquiv.ofInjective φ₂ hinj₂).symm.toLinearMap ∘ₗ g
  have hf : ∀ x, φ₂ (f x) = (N : E) • φ₁ x := by
    intro x
    have h1 : φ₂ (f x) = (N : 𝓞 E) • φ₁ x :=
      LinearEquiv.ofInjective_symm_apply φ₂ (h := hinj₂) (g x)
    rw [h1, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨N, f, hN, fun x y hxy => hinj₁ ?_, fun x y => ?_⟩
  · have := congrArg φ₂ hxy
    rw [hf, hf] at this
    exact smul_right_injective _ hN0 this
  · have h2 := hEF₂ (f x) (f y)
    rw [hf, hf, GlobalTheory.HermModel.herm_smul_left, GlobalTheory.HermModel.herm_smul_right] at h2
    have hc : FD.cc (N : E) = N := by simp [FD.cc]
    have h3 : (H.rt : E) * ((N : E) * (FD.herm Gm (φ₁ x) (φ₁ y) * FD.cc (N : E))) =
        ((N : ℚ) ^ 2) • ((H.rt : E) * FD.herm Gm (φ₁ x) (φ₁ y)) := by
      rw [hc, Algebra.smul_def]
      simp only [map_pow, map_natCast]
      ring
    rw [h3, map_smul, ← hEF₁, smul_eq_mul] at h2
    exact_mod_cast h2

end GlobalTheory.SelfDualIsom
