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

theorem trivCoord_pull_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {g' : R →+* R'} {g'' : R →+* R''}
    {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X}
    (w' : φ ≫ s = s' ≫ spMap g') (w'' : φ' ≫ s = s'' ≫ spMap g'') (ψ : X'' ⟶ X') (h : ψ ≫ φ = φ')
    (V : X.Opens) (V' : X'.Opens) (V'' : X''.Opens) (e' : V' ≤ φ ⁻¹ᵁ V) (e'' : V'' ≤ φ' ⁻¹ᵁ V) (e : V'' ≤ ψ ⁻¹ᵁ V')
    (x : GlobalTheory.AbLaw.SecOnR s (LB.triv X) V) :
    trivCoord φ' s'' V'' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w'' V V'' e'' x) =
      (ψ.appLE V' V'' e).hom (trivCoord φ s' V' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w' V V' e' x)) := by
  subst h
  have k : ∀ {Y : Scheme.{0}} {S : Type} [CommRing S] {g : R →+* S} (t : Y ⟶ Sp S) (π : Y ⟶ X)
      (w : π ≫ s = t ≫ spMap g) (O : Y.Opens) (eO : O ≤ π ⁻¹ᵁ V) (e2 : O ≤ π ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit)),
      trivCoord π t O (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w V O eO x) =
        (π.appLE _ O e2).hom (x.coord PUnit.unit) := by
    intro Y S _ g t π w O eO e2
    have := GlobalTheory.AbLaw.SecOn.coord_pullLE π eO ((GlobalTheory.AbLaw.SecOnR.of s (LB.triv X) V).symm x) (i0 π)
    refine (congrArg (Sec.res t (le_inf le_rfl (by rw [triv_pull_U]; exact le_top))) this).trans ?_
    exact GlobalTheory.LB.resG_appLE π _ _ _
  have e2 : V' ≤ φ ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit) := fun y hy => ⟨e' hy, trivial⟩
  rw [k s' φ w' V' e' e2, k s'' (ψ ≫ φ) w'' V'' e'' (fun y hy => e2 (e hy))]
  exact (congrArg (fun q => q.hom (x.coord PUnit.unit)) (Scheme.Hom.appLE_comp_appLE ψ φ _ V' V'' e2 e)).symm

theorem Φ_ext_eq_pullCoef : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := by
  intro R R' R'' _ _ _ _ _ X X' X'' s s' s'' φ φ' w' w'' α ψ wψ h κ _ D hD' hD'' hle p z t
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact (map_zero ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)))).symm
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    exact (congrArg₂ (· + ·) hx hy).trans (map_add ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) _ _).symm
  | tmul r x =>
    have a1 : Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ (r ⊗ₜ x)) t = trivCoord φ' s'' _ (α r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w'' t.1 (x t)) := rfl
    have a2 : Φ w' D hD' p (r ⊗ₜ x) t = trivCoord φ s' _ (r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w' t.1 (x t)) := rfl
    refine a1.trans (Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) a2).symm)
    refine ((trivCoord φ' s'' _).map_smul _ _).trans ?_
    refine Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) ((trivCoord φ s' _).map_smul _ _)).symm
    refine Eq.trans ?_ ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).smul (ne t.1 (card_nonempty t)) r _).symm
    exact congrArg (α r • ·) (trivCoord_pull_comp w' w'' ψ h _ _ _ _ _ (pr _ hD' _ hD'' hle (ne t.1 (card_nonempty t)).unop).2 (x t))

end GlobalTheory.CechPoset
