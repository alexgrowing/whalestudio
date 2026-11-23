import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.TrivTwist

variable {X Y : Scheme.{0}}

theorem gm_pull_g (A : LB X) (f : Y ⟶ X) (y : Y) (i j : A.ι) (hi : f y ∈ A.U i) (hj : f y ∈ A.U j) :
    gm (𝟙 Y) y ((A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j)) ((A.pull f).g (fun _ => i) (fun _ => j)) =
      gm f y (A.U i ⊓ A.U j) (A.g i j) := by
  have hp : (𝟙 Y : Y ⟶ Y) y ∈ (A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (A.g i j))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hp _).trans ((gm_pull (𝟙 Y) f y (A.U i ⊓ A.U j) ⟨hi, hj⟩ _).trans (by rw [Category.id_comp]))

theorem isGen_pull_iff (A : LB X) (f : Y ⟶ X) (t : LB.Gen (A.pull f)) :
    t.IsGen ↔ ∀ (i j : A.ι) (y : Y), f y ∈ A.U i → f y ∈ A.U j →
      gm (𝟙 Y) y ((A.pull f).U (fun _ => i)) (t.s (fun _ => i)) =
        gm f y (A.U i ⊓ A.U j) (A.g i j) * gm (𝟙 Y) y ((A.pull f).U (fun _ => j)) (t.s (fun _ => j)) := by
  constructor
  · intro h i j y hi hj
    have hp : (𝟙 Y : Y ⟶ Y) y ∈ (A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j) :=
      ⟨mem_pull.2 hi, mem_pull.2 hj⟩
    have := congrArg (gm (𝟙 Y) y ((A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j))) (h (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res _ y _ hp, gm_res _ y _ hp, gm_pull_g A f y i j hi hj] at this
    exact this
  · intro h I J
    refine unit_ext fun y hy => ?_
    have hi := mem_pull.1 hy.1
    have hj := mem_pull.1 hy.2
    have := h (I PUnit.unit) (J PUnit.unit) y hi hj
    rw [← gm_pull_g A f y _ _ hi hj] at this
    exact (gm_res _ y _ hy _).trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ y _ hy _))).symm)

theorem gm_div_g_one (M N : LB X) (hN : ∀ i j, N.g i j = 1) (f : Y ⟶ X) (y : Y) (p q : M.ι × N.ι)
    (hp : f y ∈ (LB.div M N).U p) (hq : f y ∈ (LB.div M N).U q) :
    gm f y ((LB.div M N).U p ⊓ (LB.div M N).U q) ((LB.div M N).g p q) = gm f y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) := by
  show gm f y _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  have hm : f y ∈ (LB.div M N).U p ⊓ (LB.div M N).U q := ⟨hp, hq⟩
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res f y _ hm _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y _ hm _)))).trans ?_)
  rw [hN, map_one, inv_one, _root_.mul_one]

theorem triv_pull_div_iff (M N : LB X) (hc : ∀ x : X, ∃ k, x ∈ N.U k) (hN : ∀ i j, N.g i j = 1) (f : Y ⟶ X) :
    Triv (M.pull f) ↔ Triv ((LB.div M N).pull f) := by
  have hle : ∀ p : M.ι × N.ι, ((LB.div M N).pull f).U (fun _ => p) ≤ (M.pull f).U (fun _ => p.1) :=
    fun p y hy => mem_pull.2 (mem_pull.1 hy).1
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨⟨fun P => res (hle (P PUnit.unit)) (t.s (fun _ => (P PUnit.unit).1))⟩, (isGen_pull_iff _ f _).2 ?_⟩
    intro p q y hp hq
    rw [gm_div_g_one M N hN f y p q hp hq]
    exact (gm_res (𝟙 Y) y (hle p) (mem_pull.2 hp) _).trans (((isGen_pull_iff M f t).1 ht p.1 q.1 y hp.1 hq.1).trans
      (congrArg _ (gm_res (𝟙 Y) y (hle q) (mem_pull.2 hq) _).symm))
  · rintro ⟨c, hc'⟩
    have H : ∀ (p q : M.ι × N.ι) (y : Y), f y ∈ (LB.div M N).U p → f y ∈ (LB.div M N).U q →
        gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => p)) (c.s (fun _ => p)) =
          gm f y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
            gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => q)) (c.s (fun _ => q)) := fun p q y hp hq => by
      rw [← gm_div_g_one M N hN f y p q hp hq]
      exact (isGen_pull_iff _ f c).1 hc' p q y hp hq
    have glue : ∀ i : M.ι, ∃ s : Γ(Y, (M.pull f).U (fun _ => i))ˣ, ∀ k : N.ι,
        res (hle (i, k)) s = c.s (fun _ => (i, k)) := fun i =>
      glue_unit _ (fun k => ((LB.div M N).pull f).U (fun _ => (i, k))) (fun k => hle (i, k))
        (fun y hy => by
          obtain ⟨k, hk⟩ := hc (f y)
          exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.2 ⟨mem_pull.1 hy, hk⟩⟩)
        (fun k => c.s (fun _ => (i, k))) (fun k k' y hy => by
          have h₁ := mem_pull.1 hy.1
          have h₂ := mem_pull.1 hy.2
          have e := mul_eq_right.1 (H (i, k) (i, k) y h₁ h₁).symm
          have e' := H (i, k) (i, k') y h₁ h₂
          exact e'.trans ((congrArg (· * _) e).trans (_root_.one_mul _)))
    choose s hs using glue
    refine ⟨⟨fun I => s (I PUnit.unit)⟩, (isGen_pull_iff M f _).2 fun i j y hi hj => ?_⟩
    obtain ⟨k, hk⟩ := hc (f y)
    have v : ∀ a, f y ∈ M.U a → gm (𝟙 Y) y ((M.pull f).U (fun _ => a)) (s a) =
        gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => (a, k))) (c.s (fun _ => (a, k))) := fun a ha =>
      (gm_res (𝟙 Y) y (hle (a, k)) (mem_pull.2 ⟨ha, hk⟩) _).symm.trans (congrArg _ (hs a k))
    exact (v i hi).trans ((H (i, k) (j, k) y ⟨hi, hk⟩ ⟨hj, hk⟩).trans (congrArg _ (v j hj).symm))

theorem linComb_pw_zero_g (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j : K → L.ι) :
    (LB.LinComb (pw L 0) φ ε).g i j = 1 := by
  refine Finset.prod_eq_one fun k _ => ?_
  have e : (pw L 0).g (i k) (j k) = 1 := zpow_zero _
  exact (congrArg (· ^ ε k) ((congrArg _ ((congrArg _ e).trans (map_one _))).trans (map_one _))).trans (one_zpow _)

theorem inK_iff_trivial_twist : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → (pw L 0).IsLB ∧ (∃ u : LB.Gen (abelian₂ B (pw L 0)), u.IsGen) ∧ ∀ (O : LB B.left), O = pw L 0 → ∀ (T : Over S) (x : T ⟶ B), InK B L x ↔ (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) := by
  intro S B _ L hL
  refine ⟨isLB_pw hL 0, ⟨⟨fun _ => 1⟩, fun i j => ?_⟩, ?_⟩
  · exact (map_one _).trans
      ((congrArg₂ (· * ·) (linComb_pw_zero_g L _ _ i j) (map_one _)).trans (_root_.one_mul _)).symm
  · rintro O rfl T x
    refine forall_congr' fun p => exists_congr fun U => and_congr Iff.rfl ?_
    refine triv_pull_div_iff _ _ (fun y => ?_) (fun i j => linComb_pw_zero_g L _ _ i j) _
    obtain ⟨k, hk⟩ := exists_chart (isLB_pw hL 0) ((snd T B).left y)
    exact ⟨fun _ => k, mem_pull.2 hk⟩

end GlobalTheory.UU.TrivTwist
end
