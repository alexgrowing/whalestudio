import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPicardGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.RosLam

theorem form_rosati {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (f g : G ⟶ G)
    {V : Type} [CommGroup V] (k : ((G ⊗ G).left ⟶ G.left) → V) :
    (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G ≫ f, snd G G] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) /
      (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G, snd G G ≫ g] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) =
      ∏ i, k (Out.rosatiφ G f g i) ^ Out.rosatiε i := by
  have p := prod_ros f g (fst G G) (snd G G) k
  rw [lift_fst_snd] at p
  simp only [Over.id_left, Category.id_comp] at p
  rw [p, GlobalTheory.NormRos.prod_square, GlobalTheory.NormRos.prod_square]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem lbIso_of_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (f g : G ⟶ G) (t : LB.Gen (LB.LinComb L (Out.rosatiφ G f g) Out.rosatiε)) (ht : t.IsGen) :
    LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) := by
  obtain ⟨Pic, _, cl, pl, h₁, h₂, -, -, h₅, -⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  obtain ⟨a, a'⟩ := h₅ _ _ L hL _ (Out.rosatiφ G f g) Out.rosatiε
  obtain ⟨b, b'⟩ : (cubeLB G ![fst G G ≫ f, snd G G] L).IsLB ∧ cl (cubeLB G ![fst G G ≫ f, snd G G] L) = _ :=
    h₅ _ _ L hL _ _ _
  obtain ⟨c, c'⟩ : (cubeLB G ![fst G G, snd G G ≫ g] L).IsLB ∧ cl (cubeLB G ![fst G G, snd G G ≫ g] L) = _ :=
    h₅ _ _ L hL _ _ _
  refine (h₁ _ _ _ b c).1 ?_
  have e := ((h₂ _ _ a).2 ⟨t, ht⟩).symm.trans a'
  rw [b', c', ← div_eq_one, e]
  have key := form_rosati f g (V := Multiplicative (FreeAbelianGroup ((G ⊗ G).left ⟶ G.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have k := congrArg (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift fun ψ : (G ⊗ G).left ⟶ G.left => Additive.ofMul (pl ψ (cl L)))) key
  simpa only [map_div, map_prod, map_zpow, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, toAdd_ofAdd,
    FreeAbelianGroup.lift_apply_of, toMul_ofMul] using k

theorem rosatiAdj_iff_lamEq : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (f g : P.A ⟶ P.A), IsMonHom f → IsMonHom g → (Out.RosatiAdj P.A P.L f g ↔ LamEq P.L f (𝟙 P.A) P.L (𝟙 P.A) g) := by
  intro hG S P f g hf hg
  have := P.isAb.comm
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  constructor
  · intro h
    obtain ⟨u, hu, -⟩ := exists_ros hG P.isAb P.isLB f g h
    exact lbIso_of_gen P.isLB f g u hu
  · intro h s
    obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati P.isLB f g h
    exact ⟨⊤, trivial, LB.pullGen P.L _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩

end GlobalTheory.RosLam
