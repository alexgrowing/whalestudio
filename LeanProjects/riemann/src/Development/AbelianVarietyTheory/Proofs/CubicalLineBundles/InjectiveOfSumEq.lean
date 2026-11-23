import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignatureStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ISupRangeDifferentialEqTopOfJointlyOntoStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Indep

section Linear

variable {K V J : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype J]

theorem finrank_le_sum {N : J → Submodule K V} (h : ⨆ i, N i = ⊤) :
    Module.finrank K V ≤ ∑ i, Module.finrank K (N i) := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  rw [← Module.finrank_directSum]
  exact LinearMap.finrank_le_finrank_of_surjective hs

theorem iSupIndep_of_sum_le {N : J → Submodule K V} (h : ⨆ i, N i = ⊤)
    (hd : ∑ i, Module.finrank K (N i) ≤ Module.finrank K V) : iSupIndep N := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  have he : Module.finrank K (DirectSum J fun i => N i) = Module.finrank K V := by
    rw [Module.finrank_directSum]
    exact le_antisymm hd (finrank_le_sum h)
  exact DirectSum.IsInternal.submodule_iSupIndep
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).2 hs, hs⟩

theorem sum_finrank_eq {N : J → Submodule K V} (hi : iSupIndep N) (h : ⨆ i, N i = ⊤) :
    ∑ i, Module.finrank K (N i) = Module.finrank K V := by
  classical
  rw [← Module.finrank_directSum]
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap N)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi h)).finrank_eq

theorem injective_of_sum_eq {W : J → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)] {M : ∀ i, W i →ₗ[K] V} (h : ⨆ i, LinearMap.range (M i) = ⊤)
    (hd : ∑ i, Module.finrank K (W i) = Module.finrank K V) (j : J) : Function.Injective (M j) := by
  have hle : ∀ i ∈ (Finset.univ : Finset J), Module.finrank K (LinearMap.range (M i)) ≤ Module.finrank K (W i) :=
    fun i _ => LinearMap.finrank_range_le _
  have he := (Finset.sum_eq_sum_iff_of_le hle).1
    (le_antisymm (Finset.sum_le_sum hle) (hd ▸ finrank_le_sum h)) j (Finset.mem_univ _)
  have := LinearMap.finrank_range_add_finrank_ker (M j)
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega

end Linear

open IntCoord in

theorem map_eigLat_le {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} {f : P.A ⟶ P'.A}
    (hf : ∀ x, a.act x ≫ f = f ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : F.IsDiffOf F' f M) (τ : O →+* 𝓞 K) :
    (F.eigLat a τ).map (M.restrictScalars (𝓞 K)) ≤ F'.eigLat a' τ := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨u, hu, he⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.2 O a τ c).1 hc
  refine Submodule.subset_span ⟨u ≫ f, hM u c hu, fun x => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (he x),
    Category.assoc]

theorem letters_independent : ThetaUnifAV → Out.Laws → IndSt := by
  intro hU hL E _ _ _ H K _ _ ρ σ₁ p q X FA FB M hM N
  classical
  haveI : Finite (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (X.split ▸ Module.finrank_pos)).2
  haveI := Fintype.ofFinite (𝓞 E →+* 𝓞 K)
  have hρ : ρ ≠ 0 := fun h => by
    have := X.ρ_sq
    rw [h] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hsq : ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = -ρ ↔ ¬ τ H.rt = ρ := fun τ => by
    have e : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, X.ρ_sq]; simp
    refine ⟨fun h h' => hρ ?_, fun h => (sq_eq_sq_iff_eq_or_eq_neg.1 e).resolve_left h⟩
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination h - h'
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have hA : ∀ b : Bool, (∀ τ : 𝓞 E →+* 𝓞 K, latRank K ((FA b).eigLat (X.A b).t.act τ) =
        if τ H.rt = (if b then ρ else -ρ) then 1 else 0) ∧
      iSupIndep (fun τ : 𝓞 E →+* 𝓞 K =>
        Submodule.span K ((FA b).eigLat (X.A b).t.act τ : Set (Fin (FA b).P₀.g → K))) ∧
      ⨆ τ : 𝓞 E →+* 𝓞 K, Submodule.span K ((FA b).eigLat (X.A b).t.act τ : Set (Fin (FA b).P₀.g → K)) = ⊤ ∧
      (FA b).P₀.g = Module.finrank ℚ E / 2 := by
    rintro (_ | _)
    · obtain ⟨a, b, c, d, -⟩ := GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A false) (FA false) 0 1 X.split X.typeM X.ρ_sq
      refine ⟨fun τ => ?_, b, c, by rw [(FA false).fib.1]; simpa using d⟩
      rw [a]
      by_cases h : τ H.rt = ρ
      · rw [if_pos h, if_neg (by simpa [hsq] using h)]
      · rw [if_neg h, if_pos (by simpa [hsq] using h)]
    · obtain ⟨a, b, c, d, -⟩ := GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A true) (FA true) 1 0 X.split X.typeP X.ρ_sq
      refine ⟨fun τ => ?_, b, c, by rw [(FA true).fib.1]; simpa using d⟩
      rw [a]
      simp
  have hB : FB.P₀.g = Module.finrank ℚ E / 2 * (p + q) := by
    rw [FB.fib.1]
    exact (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ X.B FB p q X.split X.typeB X.ρ_sq).2.2.2.1
  have hsur : ⨆ j, LinearMap.range (M j) = ⊤ :=
    GlobalTheory.T.iSup_range_differential_eq_top_of_jointly_onto hU hL K X.B.pol FB σ₁ (Fin p ⊕ Fin q) (fun j => (X.A j.isLeft).pol) (fun j => FA j.isLeft) X.φ M
      inferInstance (fun j => (X.lin j).1) hM fun y => by
        obtain ⟨x, hx⟩ := X.onto y
        exact ⟨p + q, finSumFinEquiv.symm, fun m => x _, hx⟩
  have hdim : ∑ j : Fin p ⊕ Fin q, Module.finrank K (Fin (FA j.isLeft).P₀.g → K) =
      Module.finrank K (Fin FB.P₀.g → K) := by
    simp [(hA _).2.2.2, hB, mul_comm]
  have hinj := injective_of_sum_eq hsur hdim
  have hspan : ∀ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) =
      (Submodule.span K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2 : Set _)).map (M x.1) := fun x => by
    rw [Submodule.map_span]
    rfl
  have hrk : ∀ x, latRank K (N x) = latRank K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2) := fun x => by
    rw [latRank, hspan]
    exact (Submodule.equivMapOfInjective _ (hinj x.1) _).finrank_eq.symm
  have htop : ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤ := by
    rw [iSup_prod, ← hsur]
    refine iSup_congr fun j => ?_
    rw [← Submodule.map_top, ← (hA j.isLeft).2.2.1, Submodule.map_iSup]
    exact iSup_congr fun τ => hspan (j, τ)
  refine ⟨fun x => map_eigLat_le (X.lin x.1).2 (hM x.1) x.2, fun x => ?_, hinj, iSupIndep_of_sum_le htop ?_, htop⟩
  · rw [hrk, (hA _).1]
  · rw [← hdim, Fintype.sum_prod_type]
    refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [← sum_finrank_eq (hA j.isLeft).2.1 (hA j.isLeft).2.2.1]
    exact Finset.sum_congr rfl fun τ _ => hrk (j, τ)

end GlobalTheory.CM.Indep
end
