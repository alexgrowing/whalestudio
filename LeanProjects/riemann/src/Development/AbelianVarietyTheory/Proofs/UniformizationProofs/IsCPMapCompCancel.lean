import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

theorem IsCPMap.cancel {P : CP G} {P' : CP G'} {P'' : CP G''} {f' : S'' ⟶ S'} {F' : G''.left ⟶ G'.left}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    {hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f} {w'' : LB.Iso P''.L.L (P.L.L.pull (F' ≫ F))}
    (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'')
    (mul : ∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y)
    (Tw : Tri w w' w'') : IsCPMap P'' P' f' F' hw' w' := by
  have key : ∀ (T : Over S''), ∃ ρ : Over.mk (T.hom ≫ f' ≫ f) ⟶ Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f),
      ρ.left = 𝟙 T.left ∧ ∀ x : T ⟶ G'', toBase hw'' x = ρ ≫ toBase hw (toBase hw' x) := fun T =>
    ⟨Over.homMk (𝟙 T.left) (by simp), rfl, fun x => Over.OverMorphism.ext
      ((Category.assoc _ _ _).symm.trans (Category.id_comp _).symm)⟩
  refine ⟨mul, (isGen_iff _).2 (Tw.pgen_cancel P.L.isLB ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)),
    fun T z J'' J' hJ'' hJ' B hB => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
  obtain ⟨ρ, hρ, e⟩ := key T
  obtain ⟨a₁, a₂, a₃⟩ := h.vals (Over.mk (T.hom ≫ f')) z J' J hJ' hJ _ (fun _ => rfl)
  let β := toBaseHom mul T
  let A : (Over.mk (T.hom ≫ f') ⟶ G') → (T.left.presheaf.stalk z)ˣ :=
    fun x => gw w x.left z (J (x.left ≫ F)) (J' x.left)
  have hAB : ∀ x : T ⟶ G'', A (β x) * B x = gw w'' x.left z (J (x.left ≫ F' ≫ F)) (J'' x.left) := fun x => by
    rw [hB, ← Category.assoc]
    exact (Tw _ x.left z _ _ _ (hJ ((x.left ≫ F') ≫ F)) (hJ' (x.left ≫ F')) (hJ'' x.left)).symm
  obtain ⟨b₁, b₂, b₃⟩ := h''.vals T z J'' J hJ'' hJ (fun x => A (β x) * B x) hAB
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rw [map_one, ← Category.assoc, _root_.mul_assoc] at b₁
    exact mul_left_cancel (a := A 1) (a₁.symm.trans b₁)
  · have a : val P.sym ((x.left ≫ F') ≫ F) z J * A (β x) = A (β x)⁻¹ * val P'.sym (x.left ≫ F') z J' := a₂ (β x)
    have b := b₂ x
    rw [map_inv, ← Category.assoc, ← _root_.mul_assoc, a, _root_.mul_assoc, _root_.mul_assoc] at b
    exact mul_left_cancel b
  · have c : @_root_.id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ f' ≫ f)) z J (toBase hw'' x)
        (toBase hw'' y) (toBase hw'' u)) = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := by
      have e' : (lift (toBase hw'' x) (lift (toBase hw'' y) (toBase hw'' u))).left =
          (lift (toBase hw (β x)) (lift (toBase hw (β y)) (toBase hw (β u)))).left := by
        rw [e, e, e, ← comp_lift, ← comp_lift, Over.comp_left, hρ]; exact Category.id_comp _
      exact congrArg (fun r => val (L := P.L.L) (φ := thφ G (x3 G)) (ε := thε) P.c.t r z J) e'
    obtain ⟨C, hC⟩ : ∃ C : (T.left.presheaf.stalk z)ˣ, C = cubV P.c (T := Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f)) z J
        (toBase hw (β x)) (toBase hw (β y)) (toBase hw (β u)) := ⟨_, rfl⟩
    obtain ⟨C', hC'⟩ : ∃ C' : (T.left.presheaf.stalk z)ˣ, C' = cubV P'.c (T := Over.mk (T.hom ≫ f')) z J'
        (β x) (β y) (β u) := ⟨_, rfl⟩
    have a : C * A (β x * β y) * A (β x * β u) * A (β y * β u) * A 1 =
        A (β x * β y * β u) * A (β x) * A (β y) * A (β u) * C' := by
      rw [hC, hC']; exact a₃ (β x) (β y) (β u)
    have b := b₃ x y u
    rw [c.trans hC.symm] at b
    simp only [map_mul, map_one] at b
    have g : C' * B (x * y) * B (x * u) * B (y * u) * B 1 =
        B (x * y * u) * B x * B y * B u * cubV P''.c z J'' x y u := by
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul] at a' b' ⊢
      linear_combination (norm := abel) b' - a'
    rw [hC'] at g
    exact g

theorem isCPMap_comp_cancel :
    (∀ (S S' S'' : Scheme.{0}) (f : S' ⟶ S) (f' : S'' ⟶ S') (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (G'' : Over S'') [GrpObj G''] [IsCommMonObj G''] (P : CP G) (P' : CP G') (P'' : CP G'') (F : G'.left ⟶ G.left) (hw) (w) (F' : G''.left ⟶ G'.left) (hw' : F' ≫ G'.hom = G''.hom ≫ f') (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f), IsCPMap P' P f F hw w → (∀ w', IsCPMap P'' P' f' F' hw' w' → ∃ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' ∧ Tri w w' w'') ∧ ((∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y) → ∀ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' → ∃ w', IsCPMap P'' P' f' F' hw' w' ∧ Tri w w' w'')) := by
  intro S S' S'' f f' G _ _ G' _ _ G'' _ _ P P' P'' F hw w F' hw' hw'' h
  refine ⟨fun w' h' => ?_, fun mul w'' h'' => ?_⟩
  · obtain ⟨w'', Tw, H⟩ := h.exists_comp h' hw''
    exact ⟨w'', H, Tw⟩
  · obtain ⟨w', Tw⟩ := Geo.Tor.exists_cancel P.L.isLB w w'' ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h''.gen)
      P'.L.isLB P''.L.isLB
    exact ⟨w', h.cancel h'' mul Tw, Tw⟩

end GlobalTheory.UU
end
