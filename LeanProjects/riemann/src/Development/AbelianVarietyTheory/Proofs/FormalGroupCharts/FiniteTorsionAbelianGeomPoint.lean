import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusExtTorsion

theorem finite_torsion_abelian_geomPoint {S : Scheme.{0}} (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S) (n : ℕ)
    (hn : 1 ≤ n) : Finite {x : Over.mk t ⟶ B // x ^ n = 1} := by
  have hA : IsAbelianScheme ((Over.pullback t).obj B) :=
    { comm := by have := hB.comm; infer_instance
      smooth := by have := hB.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hB.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hB.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have h := abelian_torsion_finite_and_mulN_surjective.1 Ω ((Over.pullback t).obj B) hA n hn
  have hp := isGrpPullback_pullback B t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp Ω)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst B.hom t = y.left ≫ pullback.fst B.hom t :=
        congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp Ω))).hom (Over.w y))
        (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Finite {x : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t) ⟶ B // x ^ n = 1} := by
    refine Finite.of_equiv _ (e.toEquiv.subtypeEquiv (p := fun x => x ^ n = 1) fun x => ?_)
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp Ω))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

theorem finite_torsion_geomPoint : ∀ (S : Scheme.{0}) (G B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → IsPullback i (toUnit _) q η[B] → IsAbelianScheme B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S) (N : ℕ), 1 ≤ N → Finite {x : Over.mk t ⟶ G // x ^ N = 1} := by
  intro S G B _ _ _ X _ _ _ q i hq hi hk hB Ω _ _ t n hn
  refine SemiAbTorsion.finite_pow_eq_one_of_extension (IsMonHom.monoidHom i (Over.mk t))
    (IsMonHom.monoidHom q (Over.mk t)) ?_ ?_ n ?_
    (finite_torsion_abelian_geomPoint B hB Ω t n hn)
  · intro a b h
    exact hk.hom_ext h (toUnit_unique _ _)
  · intro x hx
    have hx' : x ≫ q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · haveI : IsDomain Γ((Over.mk t).left, ⊤) := inferInstanceAs (IsDomain Γ(Sp Ω, ⊤))
    haveI := SemiAbTorsion.finite_chars_pow_eq_one X Γ((Over.mk t).left, ⊤) hn
    let e := splitTorusPointsEquiv S X (Over.mk t)
    refine Finite.of_injective (fun s => (⟨e s.1, by rw [← map_pow, s.2, map_one]⟩ :
      {s : Multiplicative X →* Γ((Over.mk t).left, ⊤)ˣ // s ^ n = 1})) ?_
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))

end GlobalTheory.TorusExtTorsion
