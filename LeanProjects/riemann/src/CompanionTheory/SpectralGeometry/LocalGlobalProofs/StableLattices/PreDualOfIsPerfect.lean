import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIsPerfectOfAdditive
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.DualScheme

theorem preDual_of_isPerfect {S : Scheme.{0}} [IsLocallyNoetherian S] {A B : Over S} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (h : IsPerfect A B P) :
    PreDual A B P where
  isLB := h.isLB
  add₁ := CubeNoeth.isAdditive_of_triv_axes hA hB h.isLB h.zero_left h.zero_right
  add₂ := CubeNoeth.isAdditive_swap_of_triv_axes hA hB h.isLB h.zero_left h.zero_right
  right := h.ker_right
  left k _ _ t := (Set.finite_singleton (1 : Over.mk t ⟶ A)).subset fun x hx ↦ h.ker_left _ x hx

theorem pull_lam_of_left {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (c : Pic G.left) (u : T'.left ⟶ T.left)
    {a b : T ⟶ G} {a' b' : T' ⟶ G} (ha : u ≫ a.left = a'.left) (hb : u ≫ b.left = b'.left) :
    CechPic.pull u (lam c a b) = lam c a' b' := by
  have hT : u ≫ T.hom = T'.hom := by
    rw [← Over.w a, ← Category.assoc, ha, Over.w a']
  have hab : u ≫ (a * b).left = (a' * b').left := by
    rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, GlobalTheory.AbDual.lift_left_fst, GlobalTheory.AbDual.lift_left_fst, ha]
    · rw [Category.assoc, GlobalTheory.AbDual.lift_left_snd, GlobalTheory.AbDual.lift_left_snd, hb]
  have hu : ∀ X : Over S, (toUnit X).left = X.hom := fun X => by
    simpa using Over.w (toUnit X)
  have h1 : u ≫ (1 : T ⟶ G).left = (1 : T' ⟶ G).left := by
    rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, ← Category.assoc, hu, hu, hT]
  simp only [GlobalTheory.CechPic.lam, map_add, map_sub, ← GlobalTheory.CechPic.pull_comp, hab, h1, ha, hb]

theorem pull_lam_sq {S S' : Scheme.{0}} {b : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G b φ) (c : Pic G.left) {l : (G' ⊗ G').left ⟶ (G ⊗ G).left}
    (l₁ : l ≫ (fst G G).left = (fst G' G').left ≫ φ) (l₂ : l ≫ (snd G G).left = (snd G' G').left ≫ φ) :
    CechPic.pull l (lam c (fst G G) (snd G G)) = lam (CechPic.pull φ c) (fst G' G') (snd G' G') := by
  rw [GlobalTheory.CechPic.lam_pull_of_isGrpPullback hp c (fst G' G') (snd G' G')]
  exact pull_lam_of_left (T := G ⊗ G) (T' := Over.mk ((G' ⊗ G').hom ≫ b)) (a := fst G G)
    (b := snd G G) (a' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp _ (fst G' G'))
    (b' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp _ (snd G' G')) c l (by rw [l₁]; rfl) (by rw [l₂]; rfl)

theorem ktrivDual : KTrivModel → FinDual → KTrivDual := by
  intro hM hF R _ A _ g hA hg L hL hK
  obtain ⟨R₀, _, σ, A₀, _, φ, L₀, _, hA₀, hg₀, hp, hL₀, hK₀, hiso⟩ := hM R A g hA hg L hL hK
  haveI := hA₀.comm
  have hperf : IsPerfect A₀ A₀ (abelian₂ A₀ L₀) := isPerfect_lam hL₀ hK₀
  have hd : IsDual A₀ A₀ (abelian₂ A₀ L₀) :=
    hF R₀ A₀ A₀ g hA₀ hA₀ hg₀ hg₀ _ (preDual_of_isPerfect hA₀ hA₀ hperf)
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine IsDual.baseChange hp hp l₁ l₂ hP ?_ hd
  refine (cls_eq_iff (pull_isLB hperf.isLB l) hP).1 ?_
  rw [cls_pull hperf.isLB,
    show cls _ hperf.isLB = lam (cls L₀ hL₀) (fst A₀ A₀) (snd A₀ A₀) from cls_cube_two hL₀ _ _ hperf.isLB,
    show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP,
    (cls_eq_iff hL (pull_isLB hL₀ φ)).2 hiso, cls_pull hL₀]
  exact pull_lam_sq hp _ l₁ l₂

end GlobalTheory.CompanionTheory.DualScheme
