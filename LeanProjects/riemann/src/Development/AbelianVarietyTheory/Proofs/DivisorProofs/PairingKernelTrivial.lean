import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiStarMulKillsPointOfTrivialPairingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.pairing_kernel_trivial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)] := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi κ₀ hκ T x hx
  have h1 := GlobalTheory.T.pull_generator_factor_pairing_generic_mumfordBundle R D D' F A' G' U' oA oG hlin G inc hinc κ₀ hκ T x hx
  have hra : (U'.gen.inv ≫ (Over.pullback (jK R)).map pr) ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) = oA.act F.e := by
    have e1 := hlin.ext F.e
    rw [← hpi, CategoryTheory.Functor.map_comp] at e1
    rw [Category.assoc, ← Category.assoc ((Over.pullback (jK R)).map pr), e1, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h2 := GlobalTheory.T.rosati_star_mul_kills_point_of_trivial_pairing (FractionRing R) A' F.O oA F.e F.f ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) (U'.gen.inv ≫ (Over.pullback (jK R)).map pr) hra T (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom) h1
  have hip' : (Over.pullback (jK R)).map inc ≫ (Over.pullback (jK R)).map pr = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  have he : (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.e = x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom := by
    rw [← hra]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc ((Over.pullback (jK R)).map inc) ((Over.pullback (jK R)).map pr), hip', Category.id_comp]
  obtain ⟨-, hsym, g, hg⟩ := hF
  set y := x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom with hy
  have hu : y ≫ oA.act (Star.star F.e * F.f * F.e) = toUnit T ≫ η[A'.A] := by
    rw [hsym, oA.map_mul, ← Category.assoc, he, h2]
  have h3 : y = toUnit T ≫ η[A'.A] := by
    have : IsMonHom (oA.act g) := oA.hom g
    rw [← he, ← hg, oA.map_mul, ← Category.assoc, hu, Category.assoc, IsMonHom.one_hom]
  have hx' : x = y ≫ U'.gen.inv ≫ (Over.pullback (jK R)).map pr := by
    rw [hy]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hip', Category.comp_id]
  rw [hx', h3]
  have hη : η[A'.A] ≫ U'.gen.inv = η[(Over.pullback (jK R)).obj G'] := by
    have : IsMonHom U'.gen.hom := U'.gen_hom
    rw [← IsMonHom.one_hom U'.gen.hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsMonHom ((Over.pullback (jK R)).map pr) := inferInstance
  rw [Category.assoc, ← Category.assoc η[A'.A], hη, IsMonHom.one_hom]
