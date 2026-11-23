import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosGen

private theorem lbIso_of_local {O : Type} [CommRing O] [IsLocalRing O] {A : Over (Geo.Tor.Sp O)} [GrpObj A]
    [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (f g : A ⟶ A) (h : Out.RosatiAdj A L f g) :
    Geo.Tor.LBIso (cubeLB A ![fst A A ≫ f, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ g] L) := by
  obtain ⟨U, hs, t, ht⟩ := h (IsLocalRing.closedPoint O)
  have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hs
  obtain ⟨n, hn⟩ : ∃ n : (A ⊗ A).left ⟶ ((A ⊗ A).hom ⁻¹ᵁ U).toScheme,
      n ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift ((A ⊗ A).hom ⁻¹ᵁ U).ι (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι, hU]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_gen hL (φ' := Out.rosatiφ A f g) (ε' := Out.rosatiε)
    (fun V _ k => Finset.prod_congr rfl fun i _ => by
      show k (n ≫ _ ≫ _) ^ _ = k _ ^ _
      rw [← Category.assoc, hn, Category.id_comp])
    (LB.pullGen L _ _ t n) (DVR.pullGen_isGen _ _ _ _ ht n)
  exact GlobalTheory.RosLam.lbIso_of_gen hL f g u hu

private theorem prod_two {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (x y : T ⟶ G)
    {U : Type 1} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  have key := GlobalTheory.NormRos.prod_square x y (U := Multiplicative (FreeAbelianGroup (T.left ⟶ G.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have k := congrArg (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift fun ψ : T.left ⟶ G.left => Additive.ofMul (h ψ))) key
  simpa only [map_mul, map_inv, map_prod, map_zpow, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply,
    toAdd_ofAdd, FreeAbelianGroup.lift_apply_of, toMul_ofMul] using k

theorem exists_gen_of_rosatiAdj : ∀ (O : Type) [CommRing O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)) (Z : Scheme.{0}) (Q : LB Z) (ψ₂ : (P.A ⊗ P.A).left ⟶ Z), Q.IsLB → Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) → ∀ f f' : P.A ⟶ P.A, IsMonHom f → IsMonHom f' → Out.RosatiAdj P.A P.L f f' → ∃ t : LB.Gen (LB.LinComb Q (K := Fin 2) ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]), t.IsGen := by
  intro O _ _ P Z Q ψ₂ hQ hI f f' _ _ h
  have := P.isAb.comm
  have H := lbIso_of_local P.isLB f f' h
  obtain ⟨Pic, _, cl, pl, h₁, h₂, -, h₄, h₅, -⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  obtain ⟨a, a'⟩ : (abelian₂ P.A P.L).IsLB ∧ cl (abelian₂ P.A P.L) = _ := h₅ _ _ P.L P.isLB _ _ _
  obtain ⟨q, q'⟩ : (Q.pull ψ₂).IsLB ∧ cl (Q.pull ψ₂) = _ := h₅ _ _ Q hQ _ _ _
  have e₀ : pl ψ₂ (cl Q) = cl (abelian₂ P.A P.L) := by
    rw [(h₁ _ _ _ a q).2 hI, q']; simp
  have key : ∀ x y : P.A ⊗ P.A ⟶ P.A, (cubeLB P.A ![x, y] P.L).IsLB ∧
      pl ((lift x y).left ≫ ψ₂) (cl Q) = cl (cubeLB P.A ![x, y] P.L) := fun x y => by
    obtain ⟨b, b'⟩ : (cubeLB P.A ![x, y] P.L).IsLB ∧ cl (cubeLB P.A ![x, y] P.L) = _ := h₅ _ _ P.L P.isLB _ _ _
    refine ⟨b, ?_⟩
    rw [h₄, e₀, a', b']
    have p₁ := prod_two x y (fun φ => pl φ (cl P.L))
    have p₂ := prod_two (fst P.A P.A) (snd P.A P.A) (fun φ => pl φ (cl P.L))
    refine Eq.trans (congrArg (pl (lift x y).left) p₂) (Eq.trans ?_ p₁.symm)
    simp only [map_mul, map_inv, ← h₄, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd]
  obtain ⟨c, c'⟩ := h₅ _ _ Q hQ (Fin 2)
    ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]
  refine (h₂ _ _ c).1 ?_
  rw [c', Fin.prod_univ_two]
  show pl ((lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂) (cl Q) ^ (1 : ℤ) *
    pl ((lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂) (cl Q) ^ (-1 : ℤ) = 1
  rw [(key _ _).2, (key _ _).2, (h₁ _ _ _ (key _ _).1 (key _ _).1).2 H]
  simp

end GlobalTheory.RosGen
