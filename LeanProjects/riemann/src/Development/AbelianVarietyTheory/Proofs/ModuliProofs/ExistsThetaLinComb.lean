import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingComb

open CommutatorPairing

theorem exists_gen_linComb {X X' Y' : Scheme.{0}} {D : LB X} {I K : Type} [Fintype I] [Fintype K]
    (F : I → (X' ⟶ X)) (e : I → ℤ) (ψ : K → (Y' ⟶ X')) (ε : K → ℤ) {Y : I → Scheme.{0}} (h : ∀ i, Y' ⟶ Y i)
    (φ : ∀ i, K → (Y i ⟶ X)) (hc : ∀ i k, ψ k ≫ F i = h i ≫ φ i k)
    (t : ∀ i, LB.Gen (LB.LinComb D (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb D F e) ψ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J₀ : (Z ⟶ X) → D.ι), Good D z J₀ →
        val u r z (fun χ i => J₀ (χ ≫ F i)) = ∏ i, val (t i) (r ≫ h i) z J₀ ^ e i := by
  have le : ∀ (jj : K → I → D.ι) (i : I), LB.wchart (LB.LinComb D F e) ψ jj ≤
      h i ⁻¹ᵁ LB.wchart D (φ i) (fun k => jj k i) := fun jj i y hy => Set.mem_iInter.2 fun k => by
    have h₁ : (ψ k ≫ F i) y ∈ D.U (jj k i) := Set.mem_iInter.1 (Set.mem_iInter.1 hy k) i
    rw [hc] at h₁
    exact h₁
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jj : K → I → D.ι), r z ∈ LB.wchart (LB.LinComb D F e) ψ jj →
      gm r z (LB.wchart (LB.LinComb D F e) ψ jj) (∏ i, res (le jj i) (pullU (h i) _ ((t i).s fun k => jj k i)) ^ e i) =
        ∏ i, gm (r ≫ h i) z (LB.wchart D (φ i) fun k => jj k i) ((t i).s fun k => jj k i) ^ e i := by
    intro Z r z jj hz
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, gm_res r z _ hz]
    exact congrArg (· ^ e i) (gm_pull r (h i) z _ (le jj i hz) _)
  refine ⟨⟨fun jj => ∏ i, res (le jj i) (pullU (h i) _ ((t i).s fun k => jj k i)) ^ e i⟩,
    (CechPic.isGen_iff_germ _).2 fun y j j' hj hj' => ?_, fun Z r z J₀ hJ => ?_⟩
  · refine (v _ (𝟙 Y') y j hj).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_linComb (LB.LinComb D F e) ψ ε (𝟙 Y') y j j' hj hj') (v _ (𝟙 Y') y j' hj')).symm)
    have a : ∀ i, gm (𝟙 Y' ≫ h i) y (LB.wchart D (φ i) fun k => j k i) ((t i).s fun k => j k i) = _ := fun i =>
      gen_trans (ht i) (𝟙 Y' ≫ h i) y (le j i hj) (le j' i hj')
    have b : ∀ k, _ := fun k => gm_linComb D F e (𝟙 Y' ≫ ψ k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
      (Set.mem_iInter.1 hj' k)
    simp only [a, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    refine Eq.trans ?_ (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (b k)).symm
    simp only [trF, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, hc]
    rw [Finset.prod_comm]
    simp only [mul_comm]
  · have hz : r z ∈ LB.wchart (LB.LinComb D F e) ψ (fun k i => J₀ ((r ≫ ψ k) ≫ F i)) :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => hJ ((r ≫ ψ k) ≫ F i)
    refine (v Z r z _ hz).trans (Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) ?_)
    exact (val_of (t i) (r ≫ h i) z J₀ _ fun k => by rw [Category.assoc, Category.assoc, hc]).symm

variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A] {D : LB A.left} {I : Type} [Fintype I]

theorem exists_theta_linComb (φ : I → (G ⟶ A)) (hφ : ∀ i, IsMonHom (φ i)) (e : I → ℤ) {n : ℤ} {T : Over S}
    {T' : I → Over S} (m : ∀ i, T ⟶ T' i) (x : T ⟶ G) (θ₀ : ∀ i, ThetaGrp A D n (T' i))
    (hx : ∀ i, m i ≫ (θ₀ i).pt = x ≫ φ i) :
    ∃ θ : ThetaGrp G (LB.LinComb D (fun i => (φ i).left) e) n T, θ.pt = x ∧
      ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ G) (z : Z.left) (J₀), Good D z J₀ →
        thetaVal θ t a z (fun χ i => J₀ (χ ≫ (φ i).left)) = ∏ i, thetaVal (θ₀ i) (t ≫ m i) (a ≫ φ i) z J₀ ^ e i := by
  have hc : ∀ i (k : Fin 2), ![(snd T G).left, (translPt G x).left] k ≫ (φ i).left =
      (lift (fst T G ≫ m i) (snd T G ≫ φ i)).left ≫ ![(snd (T' i) A).left, (translPt A (θ₀ i).pt).left] k := by
    intro i k
    have := hφ i
    fin_cases k
    · exact congrArg CommaMorphism.left (lift_snd (fst T G ≫ m i) (snd T G ≫ φ i)).symm
    · refine congrArg CommaMorphism.left (?_ : translPt G x ≫ φ i = _ ≫ translPt A (θ₀ i).pt)
      rw [lift_translPt, Category.assoc, hx]
      show ((fst T G ≫ x) * snd T G) ≫ φ i = _
      rw [MonObj.mul_comp, Category.assoc]
  obtain ⟨u, hu, hv⟩ := exists_gen_linComb (fun i => (φ i).left) e _ ![n, -n] _ _ hc (fun i => (θ₀ i).φ)
    (fun i => (θ₀ i).isGen)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J₀ hJ => (hv _ (lift t a).left z J₀ hJ).trans ?_⟩
  refine Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) ?_
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  rfl

theorem weilIs_linComb (hG : GlobalFnsSt) (hA : IsAbelianScheme G) (hD : D.IsLB) (φ : I → (G ⟶ A))
    (hφ : ∀ i, IsMonHom (φ i)) (e : I → ℤ) {n : ℤ} {T : Over S} {x y : T ⟶ G} (c : I → Γ(T.left, ⊤)ˣ)
    (h : ∀ i, WeilIs A D n (x ≫ φ i) (y ≫ φ i) (c i)) :
    WeilIs G (LB.LinComb D (fun i => (φ i).left) e) n x y (∏ i, c i ^ e i) := by
  have hL := LB.isLB_linComb hD (fun i => (φ i).left) e
  refine WeilIsogeny.weilIs_of_local hG hA hL fun p => ?_
  choose V hV H using fun i => h i p
  choose θx₀ θy₀ ex ey using fun i => (H i).1
  let V₀ : T.left.Opens := ⟨⋂ i, (V i : Set T.left), isOpen_iInter_of_finite fun i => (V i).isOpen⟩
  have le : ∀ i, V₀ ≤ V i := fun i _ hz => Set.mem_iInter.1 hz i
  obtain ⟨θx, fx, vx⟩ := exists_theta_linComb φ hφ e (fun i => overLE (le i)) (overResι V₀ ≫ x) θx₀
    (fun i => by rw [ex, ← Category.assoc, overLE_ι, Category.assoc])
  obtain ⟨θy, fy, vy⟩ := exists_theta_linComb φ hφ e (fun i => overLE (le i)) (overResι V₀ ≫ y) θy₀
    (fun i => by rw [ey, ← Category.assoc, overLE_ι, Category.assoc])
  obtain ⟨c', hc'⟩ := exists_commIsOf hG hA hL θx θy
  refine ⟨V₀, Set.mem_iInter.2 hV, θx, θy, fx, fy, ?_⟩
  obtain rfl : c' = unitRes V₀ (∏ i, c i ^ e i) := by
    refine unit_ext fun z _ => ?_
    choose J₀ hJ₀ using fun χ : (overRes V₀).left ⟶ A.left => exists_chart hD (χ z)
    have e₁ := (commIsOf_iff hL _ _ _).1 hc' _ (𝟙 _) 1 z (fun χ i => J₀ (χ ≫ (φ i).left))
      (fun χ => Set.mem_iInter.2 fun i => hJ₀ (χ ≫ (φ i).left))
    have e₂ : ∀ i, _ := fun i => (commIsOf_iff hD _ _ _).1 ((H i).2 (θx₀ i) (θy₀ i) (ex i) (ey i)) _
      (𝟙 _ ≫ overLE (le i)) (1 ≫ φ i) z J₀ hJ₀
    have gx : ∀ i, ((𝟙 _ ≫ overLE (le i)) ≫ (θx₀ i).pt) * (1 ≫ φ i) = ((𝟙 _ ≫ θx.pt) * 1) ≫ φ i := fun i => by
      have := hφ i
      rw [MonObj.mul_comp, ex, fx, Category.assoc, ← Category.assoc (overLE _), overLE_ι]
      simp only [Category.assoc]
    have gy : ∀ i, ((𝟙 _ ≫ overLE (le i)) ≫ (θy₀ i).pt) * (1 ≫ φ i) = ((𝟙 _ ≫ θy.pt) * 1) ≫ φ i := fun i => by
      have := hφ i
      rw [MonObj.mul_comp, ey, fy, Category.assoc, ← Category.assoc (overLE _), overLE_ι]
      simp only [Category.assoc]
    have e₃ : ∀ i, gm (𝟙 _ ≫ overLE (le i)).left z ⊤ (unitRes (V i) (c i)) = gm (𝟙 _ ≫ V₀.ι) z ⊤ (c i) := fun i => by
      refine (gm_unitRes (V i) (c i) _ z).trans ?_
      exact congrArg (fun q => gm q z ⊤ (c i)) (congrArg CommaMorphism.left
        ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) (overLE_ι (le i)))))
    refine e₁.symm.trans (Eq.trans ?_ (gm_unitRes V₀ _ (𝟙 _) z).symm)
    unfold commVal
    rw [vx _ _ _ _ _ hJ₀, vx _ _ _ _ _ hJ₀, vy _ _ _ _ _ hJ₀, vy _ _ _ _ _ hJ₀, map_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, ← e₃, ← e₂, commVal, gx, gy]
    simp only [mul_zpow, inv_zpow]
  exact hc'

end GlobalTheory.PairingComb
