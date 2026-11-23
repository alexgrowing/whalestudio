import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TwistPair
variable {X W W₁ : Scheme.{0}}

theorem firstCohomologyVanishes_of_refines {M N : LB X} (c : M.ι → N.ι) (le : ∀ k, M.U k ≤ N.U (c k))
    (hg : ∀ k l, M.g k l = res (inf_le_inf (le k) (le l)) (N.g (c k) (c l))) (h : FirstCohomologyVanishes N) :
    FirstCohomologyVanishes M := by
  intro I V d hV hc φ hφ
  have e : ∀ (a b : I) {U : X.Opens} (h₁ : U ≤ M.U (d a) ⊓ M.U (d b)),
      rs X h₁ (M.g (d a) (d b)).val =
        rs X (h₁.trans (inf_le_inf (le _) (le _))) (N.g (c (d a)) (c (d b))).val := fun a b U h₁ => by
    rw [hg]
    exact rs_rs _ _ _
  obtain ⟨ψ, hψ⟩ := h I V (fun a => c (d a)) (fun a => (hV a).trans (le _)) hc φ (fun a b b' => by
    have := hφ a b b'
    rw [e] at this
    exact this)
  refine ⟨ψ, fun a b => ?_⟩
  rw [e]
  exact hψ a b

def secRefine {M N : LB X} (c : M.ι → N.ι) (le : ∀ k, M.U k ≤ N.U (c k))
    (hg : ∀ k l, M.g k l = res (inf_le_inf (le k) (le l)) (N.g (c k) (c l))) (s : LB.Sec N) :
    LB.Sec M where
  f := fun k => rs X (le k) (s.f (c k))
  compat := fun k l => by
    have h := congrArg (rs X (inf_le_inf (le k) (le l))) (s.compat (c k) (c l))
    rw [hg]
    rw [map_mul] at h
    refine (rs_rs _ _ _).trans (((rs_rs _ _ _).symm.trans h).trans ?_)
    exact congrArg₂ (· * ·) rfl ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)

theorem nonzeroLocus_le_secRefine {M N : LB X} (c : M.ι → N.ι) (le : ∀ k, M.U k ≤ N.U (c k))
    (hg : ∀ k l, M.g k l = res (inf_le_inf (le k) (le l)) (N.g (c k) (c l))) (hM : M.IsLB)
    (s : LB.Sec N) : nonzeroLocus s ≤ nonzeroLocus (secRefine c le hg s) := by
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := exists_chart hM x
  refine Opens.mem_iSup.2 ⟨k, ?_⟩
  have h₁ : x ∈ X.basicOpen (rs X (inf_le_left : N.U i ⊓ N.U (c k) ≤ N.U i) (s.f i)) := by
    have := Scheme.basicOpen_res X (s.f i) (homOfLE (inf_le_left : N.U i ⊓ N.U (c k) ≤ N.U i)).op
    exact this.ge ⟨⟨X.basicOpen_le _ hi, le k hk⟩, hi⟩
  have h₂ : x ∈ X.basicOpen (rs X (inf_le_right : N.U i ⊓ N.U (c k) ≤ N.U (c k)) (s.f (c k))) := by
    have := (congrArg X.basicOpen (s.compat i (c k))).le h₁
    rw [Scheme.basicOpen_mul] at this
    exact this.2
  have h₃ := (Scheme.basicOpen_res X (s.f (c k))
    (homOfLE (inf_le_right : N.U i ⊓ N.U (c k) ≤ N.U (c k))).op).le h₂
  exact (Scheme.basicOpen_res X (s.f (c k)) (homOfLE (le k)).op).ge ⟨hk, h₃.2⟩

theorem gm_tw (H : LB X) (a b : W ⟶ X) (t : ℤ) (y : W) (i j i' j' : H.ι)
    (hi : a y ∈ H.U i) (hj : b y ∈ H.U j) (hi' : a y ∈ H.U i') (hj' : b y ∈ H.U j') :
    gm (𝟙 W) y _ ((tw (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (H.pull a) t).g
      (fun _ => j, fun _ => i) (fun _ => j', fun _ => i')) =
      gm a y _ (H.g i i') ^ t * gm b y _ (H.g j j') ^ (-1 : ℤ) := by
  have m : ∀ (e : W ⟶ X) (k : H.ι), e y ∈ H.U k → (𝟙 W : W ⟶ W) y ∈ LB.wchart H (K := PUnit) (fun _ => e) (fun _ => k) :=
    fun e k h => Set.mem_iInter.2 fun _ => h
  refine (gm_div (pw (H.pull a) (-t)) (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (𝟙 W) y
    (fun _ => j, fun _ => i) (fun _ => j', fun _ => i') ⟨⟨m b j hj, m a i hi⟩, m b j' hj', m a i' hi'⟩).trans ?_
  have e₁ := gm_linComb H (K := PUnit) (fun _ => b) (fun _ => -1) (𝟙 W) y (fun _ => j) (fun _ => j')
    (m b j hj) (m b j' hj')
  have e₂ := gm_pull_g H a (𝟙 W) y (fun _ => i) (fun _ => i') (m a i hi) (m a i' hi')
  rw [Fintype.prod_unique, Category.id_comp] at e₁
  rw [Category.id_comp] at e₂
  refine (congrArg₂ (fun u v => u * v⁻¹) e₁ ((map_zpow _ _ _).trans (congrArg (· ^ (-t)) e₂))).trans ?_
  simp only [zpow_neg, inv_inv]
  exact mul_comm _ _

theorem gm_pair (H : LB X) (a b : W₁ ⟶ X) (t : ℤ) (σ : W ⟶ W₁) (y : W) (j j' : Fin 2 → H.ι)
    (hj : σ y ∈ LB.wchart H ![a, b] j) (hj' : σ y ∈ LB.wchart H ![a, b] j') :
    gm σ y _ ((LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]).g j j') =
      gm (σ ≫ a) y _ (H.g (j 0) (j' 0)) ^ t * gm (σ ≫ b) y _ (H.g (j 1) (j' 1)) ^ (-1 : ℤ) :=
  (gm_linComb H ![a, b] ![t, -1] σ y j j' hj hj').trans (Fin.prod_univ_two _)

theorem twist_pair : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (W X : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of S)) (H : LB X) (a b : W ⟶ X) (n : ℕ) (s : Fin (n + 1) → LB.Sec (H.pull a)), H.IsLB → VeryAmpleBy f (H.pull a) s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → (∀ (W₁ : Scheme.{0}) (σ : W ⟶ W₁) (a₁ b₁ : W₁ ⟶ X), σ ≫ a₁ = a → σ ≫ b₁ = b → FirstCohomologyVanishes ((LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ)) ∧ ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1])), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro S _ _ W X f H a b n s hH hs
  have hM : (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)).IsLB := LB.isLB_linComb hH _ _
  have hA : (H.pull a).IsLB := LB.isLB_pull hH a
  obtain ⟨t₁, h₁⟩ := GlobalTheory.T.serre_vanishing_very_ample.1 S W f _ n s hA hs _ hM
  obtain ⟨t₂, h₂⟩ := GlobalTheory.TwistGen.twist_generated S W f _ n s hA hs _ hM
  refine ⟨max t₁ t₂, fun t ht => ⟨?_, ?_⟩⟩
  · rintro W₁ σ a₁ b₁ rfl rfl
    have le : ∀ J : PUnit → Fin 2 → H.ι, ((LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ).U J ≤
        (tw (LB.LinComb H (K := PUnit) (fun _ => σ ≫ b₁) (fun _ => -1)) (H.pull (σ ≫ a₁)) t).U
          (fun _ => J PUnit.unit 1, fun _ => J PUnit.unit 0) := fun J y hy =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (mem_pull.1 hy) 1,
        Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (mem_pull.1 hy) 0⟩
    refine firstCohomologyVanishes_of_refines (M := (LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ) _ le
      (fun J J' => unit_ext fun y hy => ?_) (h₁ t (le_of_max_le_left ht))
    have p := mem_pull.1 hy.1
    have p' := mem_pull.1 hy.2
    refine (gm_pull_g _ σ (𝟙 W) y J J' hy.1 hy.2).trans (Eq.trans ?_ (gm_res (𝟙 W) y _ hy _).symm)
    rw [Category.id_comp]
    exact (gm_pair H a₁ b₁ t σ y _ _ p p').trans (gm_tw H (σ ≫ a₁) (σ ≫ b₁) t y _ _ _ _
      (Set.mem_iInter.1 p 0) (Set.mem_iInter.1 p 1) (Set.mem_iInter.1 p' 0) (Set.mem_iInter.1 p' 1)).symm
  · obtain ⟨m, u, hu⟩ := h₂ t (le_of_max_le_right ht)
    have le : ∀ J : Fin 2 → H.ι, (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]).U J ≤
        (tw (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (H.pull a) t).U
          (fun _ => J 1, fun _ => J 0) := fun J y hy =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1,
        Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0⟩
    have hg : ∀ J J' : Fin 2 → H.ι, (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]).g J J' =
        res (inf_le_inf (le J) (le J'))
          ((tw (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (H.pull a) t).g
            (fun _ => J 1, fun _ => J 0) (fun _ => J' 1, fun _ => J' 0)) := fun J J' =>
      unit_ext fun y hy => by
        refine (gm_pair H a b t (𝟙 W) y _ _ hy.1 hy.2).trans (Eq.trans ?_ (gm_res (𝟙 W) y _ hy _).symm)
        rw [Category.id_comp, Category.id_comp]
        exact (gm_tw H a b t y _ _ _ _ (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.1 1)
          (Set.mem_iInter.1 hy.2 0) (Set.mem_iInter.1 hy.2 1)).symm
    refine ⟨m, fun i => secRefine (M := LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]) _ le hg (u i),
      top_unique ?_⟩
    rw [← hu]
    exact iSup_mono fun i => nonzeroLocus_le_secRefine _ le hg (LB.isLB_linComb hH _ _) (u i)

end GlobalTheory.TwistPair
