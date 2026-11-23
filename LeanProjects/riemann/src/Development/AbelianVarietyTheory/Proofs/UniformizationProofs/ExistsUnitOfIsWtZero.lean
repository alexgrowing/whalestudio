import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem unit_ext_of_flat {Y Z : Scheme.{0}} (π : Y ⟶ Z) [Flat π] [Surjective π] {V : Z.Opens} {a b : Γ(Z, V)ˣ}
    (h : ∀ y, π y ∈ V → gm π y V a = gm π y V b) : a = b := by
  have e : pullU π V a = pullU π V b := Geo.Tor.unit_ext fun y hy => by
    have k := h y hy
    rw [← Category.id_comp π] at k
    exact (gm_pull (𝟙 Y) π y V hy a).trans (k.trans (gm_pull (𝟙 Y) π y V hy b).symm)
  exact Units.ext (FunDescent.app_injective π V (congrArg Units.val e))

theorem TQ.exists_unit_of_isWt_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (V : Q.B.left.Opens) (f : Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ) (hf : IsWt Q.i _ f.val 0) :
    ∃ a : Γ(Q.B.left, V)ˣ, pullU Q.q.left V a = f := by
  have := Q.q_affine
  obtain ⟨-, h₂, h₃⟩ := invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj inferInstance
    Q.isKernel V
  obtain ⟨a, ha⟩ := h₃ f.val fun Z t g k₁ k₂ => by
    rw [hf Z t g k₁ k₂, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]
  obtain ⟨b, rfl⟩ := h₂ a (ha ▸ f.isUnit)
  exact ⟨b, Units.ext ha⟩

theorem lbIso_of_genWt : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] (Q : TQ G X) (N N' : LB Q.B.left) (u : LB.Gen (N.pull Q.q.left)) (u' : LB.Gen (N'.pull Q.q.left)) (χ : X), N.IsLB → N'.IsLB → Q.GenWt N u χ → Q.GenWt N' u' χ → LBIso N N' := by
  intro S X _ G _ Q N N' u u' χ _ _ hu hu'
  have := Q.q_flat
  have := Q.q_surj
  have key : ∀ (k : N'.ι) (j : N.ι), ∃ a : Γ(Q.B.left, N'.U k ⊓ N.U j)ˣ, ∀ y, Q.q.left y ∈ N'.U k ⊓ N.U j →
      gm Q.q.left y _ a = gm (𝟙 _) y _ (u'.s fun _ => k) * (gm (𝟙 _) y _ (u.s fun _ => j))⁻¹ := by
    intro k j
    have l₁ : Q.q.left ⁻¹ᵁ (N'.U k ⊓ N.U j) ≤ (N'.pull Q.q.left).U fun _ => k := fun _ hx => mem_pull.2 hx.1
    have l₂ : Q.q.left ⁻¹ᵁ (N'.U k ⊓ N.U j) ≤ (N.pull Q.q.left).U fun _ => j := fun _ hx => mem_pull.2 hx.2
    have w := ((hu'.2 fun _ => k).res l₁).mul ((hu.2 fun _ => j).inv.res l₂)
    rw [add_neg_cancel] at w
    obtain ⟨a, ha⟩ := Q.exists_unit_of_isWt_zero _ (res l₁ (u'.s _) * res l₂ (u.s _)⁻¹) w
    refine ⟨a, fun y hy => ?_⟩
    have e := gm_pull (𝟙 _) Q.q.left y _ hy a
    rw [Category.id_comp] at e
    rw [← e, ha, map_mul, gm_res (𝟙 _) y l₁ hy, gm_res (𝟙 _) y l₂ hy, map_inv]
  choose a ha using key
  have tr : ∀ (M : LB Q.B.left) (t : LB.Gen (M.pull Q.q.left)), t.IsGen → ∀ (i i' : M.ι) (y : G.left),
      Q.q.left y ∈ M.U i → Q.q.left y ∈ M.U i' →
      gm (𝟙 _) y _ (t.s fun _ => i) = gm Q.q.left y _ (M.g i i') * gm (𝟙 _) y _ (t.s fun _ => i') := by
    intro M t ht i i' y hi hi'
    have hm : y ∈ (M.pull Q.q.left).U (fun _ => i) ⊓ (M.pull Q.q.left).U (fun _ => i') :=
      ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
    have e := congrArg (gm (𝟙 _) y _) (ht (fun _ => i) (fun _ => i'))
    rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g M Q.q.left (𝟙 _) y _ _ hm.1 hm.2, Category.id_comp] at e
    exact e
  refine ⟨⟨fun p => a p.1 p.2⟩, fun p p' => unit_ext_of_flat Q.q.left fun y hy => ?_⟩
  have e₁ := (gm_res Q.q.left y inf_le_left hy (a p.1 p.2)).trans (ha _ _ y hy.1)
  have e₂ := (gm_res Q.q.left y inf_le_right hy (a p'.1 p'.2)).trans (ha _ _ y hy.2)
  have e₃ : gm Q.q.left y _ ((LB.div N' N).g p p') =
      gm Q.q.left y _ (N'.g p.1 p'.1) * (gm Q.q.left y _ (N.g p.2 p'.2))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) ((map_inv _ _).trans (congrArg _ (gm_res _ y _ hy _))))
  refine e₁.trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) e₃ e₂)).symm)
  rw [tr N' u' hu'.1 p.1 p'.1 y hy.1.1 hy.2.1, tr N u hu.1 p.2 p'.2 y hy.1.2 hy.2.2,
    mul_inv, _root_.mul_mul_mul_comm]

end GlobalTheory.UU
