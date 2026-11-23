import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HomLinear

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

omit [GrpObj A] [GrpObj A'] in

theorem valAt'_comp_left (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (f : A ⟶ A') (U : A'.left.Opens) (s : Γ(A'.left, U)) :
    valAt' (x ≫ f).left U s = valAt' x.left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) :=
  (valAt'_comp x.left f.left U s).symm

omit [GrpObj A'] in

theorem isHolTo_ex_comp (u : HolUnif A L g) (f : A ⟶ A') :
    IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (u.ex z ≫ f).left) := by
  intro U s
  have hset : {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (u.ex w ≫ f).left ⁻¹ᵁ U} =
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (f.left ⁻¹ᵁ U)} := by
    ext w
    simp
  have hfun : (fun w => valAt' (u.ex w ≫ f).left U s) =
      fun w => valAt' (u.ex w).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) :=
    funext fun w => valAt'_comp_left _ f U s
  rw [hset, hfun]
  exact u.hol _ _

theorem isTangent_comp {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f]
    {v : epsR R ⟶ G} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem top_le_ex_zero (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) (U : A.left.Opens)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
  have h0 : u.ex 0 = η[A] := by
    rw [(u.ker 0).mpr u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  rw [h0, ← hv]
  intro a _
  exact h (Set.mem_univ _)

theorem isDiff_comp (u : HolUnif A L g) (u' : HolUnif A' L' g') (f : A ⟶ A') [IsMonHom f]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u'.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff : DifferentiableAt ℂ (fun z => valAt' (u'.ex z).left U s) 0 :=
    (u'.hol U s).2.differentiableAt ((u'.hol U s).1.mem_nhds (top_le_ex_zero u' (isTangent_comp f hv) U h))
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u'.ex z).left U s) ∘ LinearMap.toContinuousLinearMap F := by
    funext z
    rw [← valAt'_comp_left, ← hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := LinearMap.toContinuousLinearMap F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) (LinearMap.toContinuousLinearMap F).hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1

theorem exists_linear_of_isMonHom :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' →
  ∀ (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g'),
  (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u'.IsDiff w v) →
  ∀ f : A ⟶ A', IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), (∀ z, u'.ex (F z) = u.ex z ≫ f) ∧
    (∀ l ∈ u.Λ, F l ∈ u'.Λ) ∧ (∀ w v, IsTangent v → u.IsDiff w v → IsTangent (v ≫ f) ∧ u'.IsDiff (F w) (v ≫ f)) ∧
    ∀ f' : A ⟶ A', (∀ z, u'.ex (F z) = u.ex z ≫ f') → f' = f := by
  intro A A' _ _ hA hA' L L' g g' u u' h1 h2 f hf
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.existsUnique_linearLift_of_holomorphic_abelianVariety A' hA' L' g' g u' h1 h2 (fun z => u.ex z ≫ f)
    (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) (isHolTo_ex_comp u f)
  refine ⟨F, hF, fun l hl => ?_, fun w v hv hd => ⟨isTangent_comp f hv, isDiff_comp u u' f F hF hv hd⟩,
    fun f' hf' => ?_⟩
  · rw [← u'.ker, hF, (u.ker l).mpr hl]
    exact MonObj.one_comp f
  · have hs : Smooth A.hom := hA.smooth
    have hp : IsProper A'.hom := hA'.proper
    have hr : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hs
    refine ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨z, rfl⟩ := u.ex_onto x
    rw [← hf', hF]

end GlobalTheory.HomLinear
