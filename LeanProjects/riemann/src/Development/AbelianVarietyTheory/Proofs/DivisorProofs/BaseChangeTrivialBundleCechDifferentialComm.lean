import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_restrict {X X' : Scheme.{0}} {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    {V W : X'.Opens} (h : W ≤ V) (x : GlobalTheory.AbLaw.SecOnR s' ((LB.triv X).pull φ) V) :
    trivCoord φ s' W (GlobalTheory.AbLaw.SecOnR.restrict s' _ h x) = Sec.res s' h (trivCoord φ s' V x) := by
  simp only [trivCoord, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.AbLaw.SecOnR.coord_restrict]
  change (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _ = (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _
  rw [← Functor.map_comp, ← Functor.map_comp]; rfl

theorem Φ_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R}
    {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (q : ℕ)
    (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X q)
    (t : {s : Finset κ // s.card = q + 1}) :
    Φ w D hD' q x t = trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (q + 1) x t) :=
  rfl

theorem trivCoord_d {R' : Type} [CommRing R'] {X X' : Scheme.{0}} {s' : X' ⟶ Sp R'} (φ : X' ⟶ X) {κ : Type}
    [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i))
    (p : ℕ) (y : GlobalTheory.Cube.Term (GlobalTheory.AbLaw.secCube s' ((LB.triv X).pull φ) fun i => φ ⁻¹ᵁ D i) (p + 1))
    (t : {s : Finset κ // s.card = p + 1 + 1}) :
    trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.Cube.d _ (p + 1) y t) =
      δ (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p (fun u => trivCoord φ s' (⨅ i ∈ u.1, φ ⁻¹ᵁ D i) (y u)) t := by
  refine (congrArg (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) (GlobalTheory.Cube.d_apply _ (p + 1) y t)).trans ?_
  refine ((map_sum (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _)).trans ?_
  refine Eq.trans ?_ (δ_apply (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p _ t).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (map_zsmul (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _).trans ?_
  congr 1
  exact trivCoord_restrict φ s' _ _

theorem Φ_dB : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD' p x
  have e1 : dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x =
      (GlobalTheory.Cube.d (GlobalTheory.AbLaw.secCube s (LB.triv X) D) (p + 1)).baseChange R' x := by
    simp only [dB, GlobalTheory.AbLaw.cechLB_d]; rfl
  have e2 := GlobalTheory.AbLaw.d_secTermBaseChange (LB.triv X) D w (p + 1) x
  funext t
  refine (Φ_apply w D hD' (p + 1) _ t).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)
    (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (p + 1 + 1) z t)) e1).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (z t)) e2.symm).trans ?_
  exact trivCoord_d φ D hD' p _ t

end GlobalTheory.CechPoset
