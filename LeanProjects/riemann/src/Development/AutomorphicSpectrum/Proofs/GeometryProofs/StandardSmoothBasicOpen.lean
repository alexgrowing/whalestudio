import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem hom_to_spQ_ext {X : Scheme.{0}} (a b : X ⟶ Sp ℚ) : a = b := by
  haveI : IsAffine (Sp ℚ) := inferInstanceAs (IsAffine (Spec (CommRingCat.of ℚ)))
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv).mp
  apply CommRingCat.hom_ext
  exact RingHom.ext_rat _ _

theorem smoothOfRelativeDimension_spMap (B : Type) [CommRing B] [Algebra ℚ B] (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ B] :
    SmoothOfRelativeDimension e (spMap (algebraMap ℚ B)) := by
  show SmoothOfRelativeDimension e (Spec.map (CommRingCat.ofHom (algebraMap ℚ B)))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension e)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap e).mpr inferInstance)

def valEquiv {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z]
    (W : Z.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) :
    Γ(Z, W) ≃+* A :=
  RingEquiv.ofBijective
    ((valMap ζ W h).hom.codRestrict A.toSubring (fun x => by
      have : (valMap ζ W h).hom x ∈ (A : Set Ω) := hA ▸ Set.mem_range_self x
      exact this))
    ⟨fun x y hxy => valMap_injective ζ h (congrArg Subtype.val hxy), fun y => by
      have : (y : Ω) ∈ Set.range (valMap ζ W h).hom := hA ▸ y.2
      obtain ⟨x, hx⟩ := this
      exact ⟨x, Subtype.ext hx⟩⟩

theorem smoothOfRelativeDimension_basicOpen_of_away : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (W : Z.Opens) (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)], SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) := by
  intro Ω _ _ Z ζ _ _ g e W hW h A hA σ g₀ hg _
  haveI := hW.isLocalization_basicOpen σ
  have hE : valEquiv ζ W h A hA σ = g₀ := by
    apply Subtype.ext
    rw [hg]
    show (valMap ζ W h).hom σ = valR ζ W σ
    simp only [valR, valMap, dif_pos h]
    rfl
  let ψ : Γ(Z, Z.basicOpen σ) ≃+* Localization.Away g₀ :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers σ) (T := Submonoid.powers g₀) _ _ (valEquiv ζ W h A hA)
      (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hE)
  have hiso : IsIso (CommRingCat.ofHom (ψ.symm : Localization.Away g₀ →+* Γ(Z, Z.basicOpen σ))) :=
    ⟨⟨CommRingCat.ofHom (ψ : Γ(Z, Z.basicOpen σ) →+* Localization.Away g₀),
      by ext x; simp, by ext x; simp⟩⟩
  let f2 : Spec Γ(Z, Z.basicOpen σ) ⟶ Sp (Localization.Away g₀) :=
    Spec.map (CommRingCat.ofHom (ψ.symm : Localization.Away g₀ →+* Γ(Z, Z.basicOpen σ)))
  haveI : IsIso f2 := by dsimp only [f2]; infer_instance
  have key : (Z.basicOpen σ).ι ≫ g =
      ((hW.basicOpen σ).isoSpec.hom ≫ f2) ≫ spMap (algebraMap ℚ (Localization.Away g₀)) :=
    hom_to_spQ_ext _ _
  rw [key]
  haveI := smoothOfRelativeDimension_spMap (Localization.Away g₀) e
  have := smoothOfRelativeDimension_comp 0 e ((hW.basicOpen σ).isoSpec.hom ≫ f2)
    (spMap (algebraMap ℚ (Localization.Away g₀)))
  rwa [zero_add] at this

end GlobalTheory.CompanionTheory.Ar.SncRes
