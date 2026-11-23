import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem rosatiAdj_mul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (c : CubicalStr A L) (f g f' g' : A ⟶ A), RosatiAdj A L.L f g → RosatiAdj A L.L f' g' → RosatiAdj A L.L (f * f') (g * g') := by
  intro S A _ _ L c f g f' g' h h' s
  obtain ⟨U, hs, t, ht⟩ := h s
  obtain ⟨U', hs', t', ht'⟩ := h' s
  refine ⟨U ⊓ U', ⟨hs, hs'⟩, ?_⟩
  let W : (A ⊗ A).left.Opens := (A ⊗ A).hom ⁻¹ᵁ (U ⊓ U')
  have l : W ≤ (A ⊗ A).hom ⁻¹ᵁ U := fun _ hy => hy.1
  have l' : W ≤ (A ⊗ A).hom ⁻¹ᵁ U' := fun _ hy => hy.2
  let T : Over S := Over.mk (W.ι ≫ (A ⊗ A).hom)
  let ρ : T ⟶ A ⊗ A := Over.homMk W.ι rfl
  obtain ⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι :=
    ⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩
  have pr : ∀ (a b : A ⟶ A) (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V) (Y : Scheme.{0})
      (m : T.left ⟶ Y) (n : Y ⟶ (A ⊗ A).left), m ≫ n = W.ι →
      ∏ i, k (m ≫ n ≫ rosatiφ A a b i) ^ rosatiε i =
      k ((x ≫ a) * y).left * (k (x ≫ a).left)⁻¹ * (k y.left)⁻¹ * (k (x * (y ≫ b)).left)⁻¹ * k x.left *
        k (y ≫ b).left := fun a b V _ k Y m n e =>
    (Finset.prod_congr rfl fun i _ => by rw [← Category.assoc, e, hxy]).trans (prod_ros a b x y k)
  obtain ⟨u, hu, -⟩ := exists_gen L.isLB (φ' := fun i => W.ι ≫ rosatiφ A (f * f') (g * g') i) (ε' := rosatiε)
    (fun V _ k => by
      refine (DVR.prod_sum₂ (K := Fin 6 ⊕ Fin 6) (K' := thK ⊕ thK) (U := V) _
        (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
          (pr f g V k _ _ _ (Scheme.homOfLE_ι _ l)) (pr f' g' V k _ _ _ (Scheme.homOfLE_ι _ l')))
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x ≫ f) (x ≫ f') y k)
          (DVR.prod_neg _ _ (prod_cub x (y ≫ g) (y ≫ g') k)))).trans ?_
      refine Eq.trans ?_ ((pr (f * f') (g * g') V k _ (𝟙 _) W.ι (Category.id_comp _)).symm.trans
        (Finset.prod_congr rfl fun i _ => by rw [Category.id_comp]))
      rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L.L _ _ _ _
      (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ t ((A ⊗ A).left.homOfLE l))
        (LB.pullGen L.L _ _ t' ((A ⊗ A).left.homOfLE l')))
      (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (x ≫ f) (lift (x ≫ f') y)).left)
        (LB.invGen L.L _ _ (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x (lift (y ≫ g) (y ≫ g'))).left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht' _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _))))
  exact ⟨u, hu⟩

end GlobalTheory
