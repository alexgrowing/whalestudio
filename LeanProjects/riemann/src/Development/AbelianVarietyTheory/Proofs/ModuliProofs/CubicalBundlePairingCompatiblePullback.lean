import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNRatioTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem cubV_of_pmaps {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f) {L : RigLB G} {L' : RigLB G'}
    {c : CubicalStr G L} {c' : CubicalStr G' L'} {w : LB.Iso L'.L (L.L.pull m.F)}
    (H : PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t m.F3) {T : Over S'} {z : T.left} {J J'}
    (hJ : Good L.L z J) (hJ' : Good L'.L z J') (a b d : T ⟶ G') :
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := Over.mk (T.hom ≫ f)) z J (Out.toBase hw a) (Out.toBase hw b)
      (Out.toBase hw d)) =
      (∏ I : thK.{0}, (fun q => gw w q z (J (q ≫ m.F)) (J' q)) ((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ^ thε I) *
        cubV c' z J' a b d := by
  have co : ∀ i : Fin 3, m.F3 ≫ (x3 G i).left = (x3 G' i).left ≫ m.F := fun i => by
    have h := m.psum_comm {i}
    rw [psum_single, psum_single] at h
    exact h.symm
  have q : (lift a (lift b d)).left ≫ m.F3 =
      (lift (Out.toBase hw a) (lift (Out.toBase hw b) (Out.toBase hw d))).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, co, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  have e := H _ (lift a (lift b d)).left z (fun I => J (((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ≫ m.F))
    (fun I => J' ((lift a (lift b d)).left ≫ thφ G' (x3 G') I)) (fun I => hJ _) (fun I => hJ' _)
  refine Eq.trans ?_ e
  refine (congrArg (fun r => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t r z J) q.symm).trans ?_
  refine val_of _ _ _ _ _ fun I => congrArg J ?_
  rw [Category.assoc, Category.assoc]
  exact congrArg _ (m.psum_comm I.down).symm

theorem cubWeil_of_isPullCubical : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y) → ∀ (L : RigLB G) (L' : RigLB G') (c : CubicalStr G L) (c' : CubicalStr G' L'), m.IsPullCubical c' c → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil c' N x y ζ → CubWeil c N (Out.toBase hw x) (Out.toBase hw y) ζ := by
  intro S S' f G _ _ G' _ _ m hw mul L L' c c' h N T x y ζ hζ
  obtain ⟨w, -, -, H⟩ := (isPullCubical_iff m c c').1 h
  let β := toBaseHom mul T
  refine ⟨(map_pow β x N).symm.trans ((congrArg β hζ.1).trans (map_one β)),
    (map_pow β y N).symm.trans ((congrArg β hζ.2.1).trans (map_one β)), fun z J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_pt L'.isLB (Z := T.left) z
  obtain ⟨W, hW⟩ : ∃ W : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ,
    W = fun q => gw w q z (J (q ≫ m.F)) (J' q) := ⟨_, rfl⟩
  let θ : (Over.mk (T.hom ≫ f) ⟶ G) → (Over.mk (T.hom ≫ f) ⟶ G) → (Over.mk (T.hom ≫ f) ⟶ G) →
    (T.left.presheaf.stalk z)ˣ := cubV c (T := Over.mk (T.hom ≫ f)) z J
  have a' : ∀ a b d : T ⟶ G', θ (β a) (β b) (β d) * W (a * b).left * W (a * d).left * W (b * d).left *
      W (1 : T ⟶ G').left = W (a * b * d).left * W a.left * W b.left * W d.left * cubV c' z J' a b d := by
    intro a b d
    have e := (cubV_of_pmaps m hw H (T := T) (z := z) hJ hJ' a b d).trans (congrArg₂ (· * ·)
      ((congrArg (fun V : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ =>
        ∏ I : thK.{0}, V ((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ^ thε I) hW.symm).trans (prod_cub a b d W)) rfl)
    have e' : θ (β a) (β b) (β d) = _ := e
    rw [e']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact cubN_ratio_twist β (fun x => W x.left) a' hζ.1 hζ.2.1 (hζ.2.2 z J' hJ')

end GlobalTheory.UU
