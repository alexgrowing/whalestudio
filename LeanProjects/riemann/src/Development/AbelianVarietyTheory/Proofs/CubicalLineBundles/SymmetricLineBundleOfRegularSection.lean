import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsoLineBundleOfRegularPullbacksSameZeroSchemeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SymOfZeroDivisor

theorem appLE_mem_nonZeroDivisors {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (a : Γ(X, W))
    (ha : ∀ (V : X.Opens) (h : V ≤ W), resG X h a ∈ nonZeroDivisors Γ(X, V))
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) : (f.appLE W V h).hom a ∈ nonZeroDivisors Γ(Y, V) := by
  have h' : f ''ᵁ V ≤ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact h hy
  have e : (f.appLE W V h).hom a = (f.appIso V).hom.hom (resG X h' a) := by
    rw [Scheme.Hom.appIso_hom']
    change _ = (X.presheaf.map (homOfLE h').op ≫ f.appLE _ _ _).hom a
    rw [Scheme.Hom.map_appLE]
  rw [e]
  rw [← MulEquivClass.map_nonZeroDivisors (f.appIso V).commRingCatIsoToRingEquiv]
  exact Submonoid.mem_map_of_mem _ (ha _ h')

theorem inv_eq_zero_iff {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Scheme.{0}} (t : T ⟶ A.left) :
    t ≫ (GrpObj.inv : A ⟶ A).left = (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ eSec A ↔
      t = t ≫ A.hom ≫ eSec A := by
  have h1 : (GrpObj.inv : A ⟶ A).left ≫ A.hom = A.hom := Over.w _
  have h2 : eSec A ≫ (GrpObj.inv : A ⟶ A).left = eSec A := by
    unfold eSec
    rw [← Over.comp_left, GrpObj.one_inv]
  have h3 : (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ eSec A =
      (t ≫ A.hom ≫ eSec A) ≫ (GrpObj.inv : A ⟶ A).left := by
    rw [Category.assoc, reassoc_of% h1]
    simp only [Category.assoc]
    exact congrArg (fun u => t ≫ A.hom ≫ u) h2.symm
  rw [h3]
  exact cancel_mono _

theorem sym_of_regular_section : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (i : L.ι) (V : Scheme.Opens A.left) (h : V ≤ L.U i), resG A.left h (θ.f i) ∈ nonZeroDivisors Γ(A.left, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → Out.Sym A L := by
  intro S A _ L θ hL hreg hz s
  refine ⟨⊤, trivial, ?_⟩
  haveI : IsIso (GrpObj.inv : A ⟶ A).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (GrpObj.inv : A ⟶ A)))
  refine GlobalTheory.T.isoLineBundle_of_regularPullbacks_sameZeroScheme A.left _ L θ _ _ hL
    (fun i V h => appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h)
    (fun i V h => appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h) ?_
  intro T t i j h h'
  rw [hz, hz, ← Category.assoc t]
  exact inv_eq_zero_iff A _

end GlobalTheory.SymOfZeroDivisor
