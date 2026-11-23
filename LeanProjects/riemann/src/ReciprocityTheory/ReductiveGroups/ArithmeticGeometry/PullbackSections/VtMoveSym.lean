import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

section Transl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}

theorem translPt_one' : translPt A (1 : T ⟶ A) = snd T A := by
  rw [translPt_eq, MonObj.comp_one, _root_.one_mul]

theorem transl_translPt (y x : T ⟶ A) :
    (translT A y).left ≫ (translPt A x).left = (translPt A (y * x)).left := by
  rw [← Over.comp_left]
  congr 1
  simp only [translPt_eq, translT, MonObj.comp_mul, lift_snd, lift_fst_assoc]
  rw [_root_.mul_left_comm, ← _root_.mul_assoc]

theorem transl_pow_succ (x : T ⟶ A) (j : ℕ) :
    (translT A (x ^ j)).left ≫ (translPt A x).left = (translPt A (x ^ (j + 1))).left := by
  rw [transl_translPt, pow_succ]

theorem transl_inv_translPt (x : T ⟶ A) : (translT A x⁻¹).left ≫ (translPt A x).left = (snd T A).left := by
  rw [transl_translPt, inv_mul_cancel, translPt_one']

theorem negT_snd' : (negT A T).left ≫ (snd T A).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, negT, lift_snd]

theorem negT_translPt (x : T ⟶ A) :
    (negT A T).left ≫ (translPt A x).left = (translT A x⁻¹).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  have e1 : negT A T ≫ translPt A x = (fst T A ≫ x) * (snd T A)⁻¹ := by
    rw [translPt_eq, MonObj.comp_mul, negT, lift_fst_assoc, lift_snd]
    rfl
  have e2 : translT A x⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) = (fst T A ≫ x) * (snd T A)⁻¹ := by
    rw [← Category.assoc, translT, lift_snd, translPt_eq]
    show ((fst T A ≫ x⁻¹) * snd T A)⁻¹ = _
    rw [mul_inv, GrpObj.comp_inv, inv_inv]
  rw [e1, e2]

end Transl

section Move

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

include hp hτ in
theorem inv_rel {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : x.left ≫ φ = τ ≫ x₀.left) :
    (x⁻¹).left ≫ φ = τ ≫ (x₀⁻¹).left := by
  show (x ≫ GrpObj.inv).left ≫ φ = τ ≫ (x₀ ≫ GrpObj.inv).left
  rw [push_inv hp x, push_eq hp τ hτ hx]
  try rfl

theorem symLift_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) {k : ℤ} {n : ℕ}
    {x₀ : T₀ ⟶ G} {θ₀ : ThetaGrp G L₀ k T₀} (h₀ : SymLift G L₀ k n x₀ θ₀) (hn : x₀ ^ n = 1) {x : T ⟶ A}
    (hx : x.left ≫ φ = τ ≫ x₀.left) :
    ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left := by
  obtain rfl := h₀.pt_eq
  obtain ⟨θ, rfl, hm⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx.symm
  have hxn : θ.pt ^ n = 1 := pow_eq_one hp τ hτ hx hn
  have hc : ∀ i, (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) i ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, (translPt G θ₀.pt).left] : Fin 2 → _) i := fun i => by
    fin_cases i
    · exact (psi_snd hp τ hτ).symm
    · exact (psi_tr hp τ hτ θ.pt θ₀.pt hx.symm).symm
  obtain ⟨nu₀, gnu₀, cnu₀⟩ := h₀.sym
  have hcn : ∀ i, (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) i ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, (snd T₀ G ≫ (GrpObj.inv : G ⟶ G)).left] : Fin 2 → _) i := fun i => by
    fin_cases i
    · exact (psi_snd hp τ hτ).symm
    · exact snd_inv_push hp τ hτ
  obtain ⟨nu, gnu, hmn⟩ := exists_gen_move hL₀ hL₁ w ((isGen_iff w).1 hw) _ _ ![k, -k] (psiO hp τ hτ).left hcn nu₀ gnu₀
  refine ⟨θ, ⟨rfl, ?_, nu, gnu, ?_⟩, hm⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
    have hG : Good L₀ y J₀ := hJ₀
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ((T ⊗ A).left.presheaf.stalk y)ˣ, ∀ j, g j =
        gw w (translPt A (θ.pt ^ j)).left y (J₀ ((translPt A (θ.pt ^ j)).left ≫ φ)) (J (translPt A (θ.pt ^ j)).left) ^ k :=
      ⟨_, fun _ => rfl⟩
    have key : ∀ j : ℕ, val θ₀.φ ((psiO hp τ hτ).left ≫ (translT G (θ₀.pt ^ j)).left) y J₀ =
        g j / g (j + 1) * val θ.φ (𝟙 _ ≫ (translT A (θ.pt ^ j)).left) y J := fun j => by
      rw [← psi_transl hp τ hτ _ _ (pow_rel hp τ hτ hx j).symm, val_pmaps w hc hm _ y J₀ J hG hJ, Category.id_comp]
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [transl_snd, transl_pow_succ, zpow_neg, div_eq_mul_inv, hg, hg]
    have c := val_corr hG h₀.pow_eq (psiO hp τ hτ).left
    rw [val_powGenT θ₀ n _ y hG, val_one] at c
    rw [val_powGenT θ n _ y hJ, val_one]
    rw [Fin.prod_univ_eq_prod_range (fun j => val θ₀.φ ((psiO hp τ hτ).left ≫ (translT G (θ₀.pt ^ j)).left) y J₀)] at c
    rw [Fin.prod_univ_eq_prod_range (fun j => val θ.φ (𝟙 _ ≫ (translT A (θ.pt ^ j)).left) y J)]
    simp only [key, Finset.prod_mul_distrib, Finset.prod_range_div'] at c
    have gn : g n = g 0 := by rw [hg, hg, hxn, pow_zero]
    rwa [gn, div_self', _root_.one_mul] at c
  · refine corr_of_val hL₁ fun y J hJ => ?_
    choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
    have hG : Good L₀ y J₀ := hJ₀
    have c := val_corr hG cnu₀ (psiO hp τ hτ).left
    rw [val_symGen θ₀ nu₀ _ y hG, val_one] at c
    rw [val_symGen θ nu _ y hJ, val_one]
    have v1 := val_pmaps w hc hm (translT A θ.pt⁻¹).left y J₀ J hG hJ
    have v2 := val_pmaps w hcn hmn (𝟙 _) y J₀ J hG hJ
    have v3 := val_pmaps w hc hm (negT A T).left y J₀ J hG hJ
    have v4 := val_pmaps w hcn hmn (translT A θ.pt⁻¹).left y J₀ J hG hJ
    simp only [Category.id_comp] at v2 ⊢
    rw [← psi_transl hp τ hτ θ.pt⁻¹ θ₀.pt⁻¹ (inv_rel hp τ hτ hx).symm, ← negT_push hp τ hτ, v1, v2, v3, v4] at c
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at c
    rw [transl_inv_translPt, negT_snd', negT_translPt] at c
    apply Additive.ofMul.injective
    have b := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, zpow_neg] at b ⊢
    linear_combination (norm := abel) b

end Move

end ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove
