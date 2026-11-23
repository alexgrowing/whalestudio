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

namespace GlobalTheory.Unif.RigidifyIso

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_ratio {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (f : Y' ⟶ Y) (hφ : ∀ k, φ' k ≫ F = f ≫ φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ c : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm (r ≫ f) z (LB.wchart L φ p) (t.s p) =
        gm r z ⊤ c * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q)) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have le : ∀ p, LB.wchart L (fun k => φ' k ≫ F) p ≤ f ⁻¹ᵁ LB.wchart L φ p := fun p y hy =>
    Set.mem_iInter.2 fun k => (congrArg (fun g : Y' ⟶ X => g y ∈ L.U (p k)) (hφ k)).mp (Set.mem_iInter.1 hy k)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      gm r z _ (res (inf_le_left.trans (le p)) (pullU f _ (t.s p)) * (u p q * res inf_le_right (a.s q))⁻¹) =
        gm (r ≫ f) z (LB.wchart L φ p) (t.s p) * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q))⁻¹ :=
    fun Z r z p q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ hz _).trans (gm_pull r f z _ (le p hz.1) _))
      ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (hu p q Z r z hz) (gm_res r z _ hz _))))))
  obtain ⟨c, hc⟩ := glue_unit (⊤ : Y'.Opens)
    (fun i : (K → L.ι) × (K → L'.ι) => LB.wchart L (fun k => φ' k ≫ F) i.1 ⊓ LB.wchart L' φ' i.2) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      choose q hq using fun k => exists_chart hL' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩)
    (fun i => res (inf_le_left.trans (le i.1)) (pullU f _ (t.s i.1)) * (u i.1 i.2 * res inf_le_right (a.s i.2))⁻¹)
    (fun i i' y hy => by
      have e : trF φ ε (𝟙 Y' ≫ f) y i.1 i'.1 = trF (fun k => φ' k ≫ F) ε (𝟙 Y') y i.1 i'.1 := by
        simp only [trF, hφ, Category.assoc]
      rw [hv _ _ y _ _ hy.1, hv _ _ y _ _ hy.2, pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.2.2,
        gen_trans ha (𝟙 Y') y hy.1.2 hy.2.2, gen_trans ht (𝟙 Y' ≫ f) y (le _ hy.1.1) (le _ hy.2.1), e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨c, fun Z r z p q h₁ h₂ => ?_⟩
  have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
  have e := (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (p, q))).trans (hv Z r z p q hz))
  rw [e, inv_mul_cancel_right]

theorem exists_scaled {X X' B : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (π : X' ⟶ B) (c : Γ(B, ⊤)ˣ) : ∃ w' : LB.Iso L' (L.pull F), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
      (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k → gw w' r z j k = gm (r ≫ π) z ⊤ c * gw w r z j k := by
  refine ⟨⟨fun i => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s i⟩, fun Z r z j k hj hk => ?_⟩
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r π z ⊤ trivial c)) rfl)

theorem exists_rigidified_iso : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (he : eSec G' ≫ Ψ = f ≫ eSec G) (L : RigLB G) (L' : RigLB G'), (∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen) → ∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) := by
  rintro S S' f G _ _ G' _ _ Ψ he L L' ⟨w, hw⟩
  have hw := (isGen_iff w).1 hw
  obtain ⟨c, hc⟩ := exists_ratio (K := PUnit) (φ' := fun _ => eSec G') (φ := fun _ => eSec G) (ε := fun _ => 1)
    hw L.isLB L'.isLB f (fun _ => he) L'.rig L'.rigGen L.rig L.rigGen
  obtain ⟨w', hw'⟩ := exists_scaled (B := (𝟙_ (Over S')).left) w G'.hom c
  have hs : eSec G' ≫ (show G'.left ⟶ (𝟙_ (Over S')).left from G'.hom) = 𝟙 _ := Over.w η[G']
  refine ⟨w', (isGen_iff w').2 fun Y r y j j' k k' hj hj' hk hk' => ?_,
    (maps_iff w' _ (fun _ => eSec G) _ L'.rig L.rig f _ (rigPull_le Ψ f he L.L) (fun _ => rfl)).2
      fun Z r z p q hp hq => ?_⟩
  · rw [hw' Y r y j k hj hk, hw' Y r y j' k' hj' hk', hw Y r y j j' k k' hj hj' hk hk', mul_left_comm]
  · refine (hc Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)).trans ?_
    rw [← _root_.mul_assoc]
    refine congrArg₂ (· * ·) ?_ rfl
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one,
      hw' Z (r ≫ eSec G') z _ _ (hp _) (hq _), Category.assoc]
    exact congrArg (fun g => gm g z ⊤ c * _) ((congrArg (r ≫ ·) hs).trans (Category.comp_id r)).symm

end GlobalTheory.Unif.RigidifyIso
