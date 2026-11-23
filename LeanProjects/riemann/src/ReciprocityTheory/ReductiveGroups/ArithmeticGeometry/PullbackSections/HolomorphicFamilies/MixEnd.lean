import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RigPMaps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section Pmaps

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem val_pmaps' (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hm : PMaps w φ' φ ε a t h) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z)
    (J₀ : (Z ⟶ X) → L.ι) (J : (Z ⟶ X') → L'.ι) (hJ₀ : Good L z J₀) (hJ : Good L' z J) :
    val t (r ≫ h) z J₀ =
      (∏ k, gw w (r ≫ φ' k) z (J₀ ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  have hp : ∀ k, (r ≫ h) ≫ φ k = (r ≫ φ' k) ≫ F := fun k => by
    rw [Category.assoc, Category.assoc, hc]
  have h1 : ∀ k, F (φ' k (r z)) ∈ L.U (J₀ ((r ≫ h) ≫ φ k)) := by
    intro k
    convert hJ₀ ((r ≫ h) ≫ φ k) using 2
    rw [hp]
    first | rfl | simp
  have h2 : ∀ k, φ' k (r z) ∈ L'.U (J (r ≫ φ' k)) := fun k => hJ (r ≫ φ' k)
  have key := hm Z r z (fun k => J₀ ((r ≫ h) ≫ φ k)) (fun k => J (r ≫ φ' k)) h1 h2
  unfold val
  refine key.trans ?_
  simp only [hp]

end Pmaps

theorem val_rigPow {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    val (rigPow A L rig k) r z J = (val (L := L) (K := PUnit) (φ := fun _ => eSec A) (ε := fun _ => 1) rig r z J) ^ k := by
  unfold val
  simp only [rigPow]
  exact map_zpow _ _ _

theorem eSec_mon {S : Scheme.{0}} {A : Over S} [GrpObj A] (φ : A ⟶ A) (hφ : IsMonHom φ) :
    eSec A ≫ φ.left = eSec A := by
  show η[A].left ≫ φ.left = η[A].left
  rw [← Over.comp_left, IsMonHom.one_hom]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
  {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

theorem sndAct_push (π : 𝓞 E) :
    (snd T t'.G ≫ t'.act.act π).left ≫ m.φ = (psiO m.cart τ hτ).left ≫ (snd T₀ t.G ≫ t.act.act π).left := by
  have h : psiO m.cart τ hτ ≫ snd T₀ t.G = pushPt m.cart.1.w (snd T t'.G) := by
    unfold psiO
    exact lift_snd _ _
  calc (snd T t'.G ≫ t'.act.act π).left ≫ m.φ
      = (snd T t'.G).left ≫ ((t'.act.act π).left ≫ m.cm.F) := by
        rw [Over.comp_left, Category.assoc]
        try rfl
    _ = ((snd T t'.G).left ≫ m.cm.F) ≫ (t.act.act π).left := by
        rw [m.act π, Category.assoc]
    _ = (pushPt m.cart.1.w (snd T t'.G)).left ≫ (t.act.act π).left := rfl
    _ = (psiO m.cart τ hτ).left ≫ (snd T₀ t.G ≫ t.act.act π).left := by
        rw [← h, Over.comp_left, Over.comp_left, Category.assoc]

theorem hom_ext₀' {Y : Scheme.{0}} {a b : Y ⟶ (T₀ ⊗ t.G).left} (h1 : a ≫ (fst T₀ t.G).left = b ≫ (fst T₀ t.G).left)
    (h2 : a ≫ (snd T₀ t.G).left = b ≫ (snd T₀ t.G).left) : a = b := pullback.hom_ext h1 h2

theorem endT_push (π : 𝓞 E) :
    (endT t'.G T (t'.act.act π)).left ≫ (psiO m.cart τ hτ).left =
      (psiO m.cart τ hτ).left ≫ (endT t.G T₀ (t.act.act π)).left := by
  have hf : (psiO m.cart τ hτ).left ≫ (fst T₀ t.G).left = (fst T t'.G).left ≫ τ := by
    rw [← Over.comp_left]
    unfold psiO
    rw [lift_fst]
    rfl
  have hs : (psiO m.cart τ hτ).left ≫ (snd T₀ t.G).left = (snd T t'.G).left ≫ m.cm.F := by
    rw [← Over.comp_left]
    unfold psiO
    rw [lift_snd]
    rfl
  have he' : (endT t'.G T (t'.act.act π)).left ≫ (fst T t'.G).left = (fst T t'.G).left := by
    rw [← Over.comp_left, lift_fst]
  have he₀ : (endT t.G T₀ (t.act.act π)).left ≫ (fst T₀ t.G).left = (fst T₀ t.G).left := by
    rw [← Over.comp_left, lift_fst]
  have hes' : (endT t'.G T (t'.act.act π)).left ≫ (snd T t'.G).left = (snd T t'.G ≫ t'.act.act π).left := by
    rw [← Over.comp_left, lift_snd]
  have hes₀ : (endT t.G T₀ (t.act.act π)).left ≫ (snd T₀ t.G).left = (snd T₀ t.G ≫ t.act.act π).left := by
    rw [← Over.comp_left, lift_snd]
  apply hom_ext₀'
  · simp only [Category.assoc]
    rw [he₀, hf, ← Category.assoc, he']
  · simp only [Category.assoc]
    rw [hes₀, ← sndAct_push m τ hτ π, hs, ← Category.assoc, hes']

theorem endGen_move (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (hw : RigIso m w) (π : 𝓞 E) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![𝟙 t.G.left, (t.act.act π).left] ![a, -b])) (hα : α₀.IsGen)
    (hN : IsNormEnd t.G t.PP (t.act.act π) a b α₀) :
    ∃ α₀' : LB.Gen (LB.LinComb t'.PP.L (K := Fin 2) ![𝟙 t'.G.left, (t'.act.act π).left] ![a, -b]),
      α₀'.IsGen ∧
      PMaps w ![𝟙 t'.G.left, (t'.act.act π).left] ![𝟙 t.G.left, (t.act.act π).left] ![a, -b] α₀' α₀ m.φ ∧
      IsNormEnd t'.G t'.PP (t'.act.act π) a b α₀' := by
  have hc : ∀ k, (![𝟙 t'.G.left, (t'.act.act π).left] : Fin 2 → _) k ≫ m.φ =
      m.φ ≫ (![𝟙 t.G.left, (t.act.act π).left] : Fin 2 → _) k := by
    intro k; fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Category.id_comp, Category.comp_id]
    · exact m.act π
  obtain ⟨α₀', g', hm⟩ := exists_gen_move t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw.1) _ _ ![a, -b] m.φ hc α₀ hα
  refine ⟨α₀', g', hm, ?_⟩
  have hr := rig_pmaps m w hw
  have hce : ∀ k : PUnit.{1}, (fun _ => eSec t'.G) k ≫ m.φ = m.cm.e ≫ (fun _ => eSec t.G) k :=
    fun _ => m.cm.e_comm
  have hact : eSec t'.G ≫ (t'.act.act π).left = eSec t'.G := eSec_mon _ (t'.act.hom π)
  unfold IsNormEnd
  refine corr_of_val t'.PP.isLB fun y J hJ => ?_
  choose J₀ hJ₀ using fun χ : (𝟙_ (Over S')).left ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  have hJ₀' : Good t.PP.L y J₀ := hJ₀
  have c0 := val_corr hJ₀' hN m.cm.e
  rw [val_pull hJ₀', val_mul hJ₀', val_rigPow, val_rigPow] at c0
  have p1 := val_pmaps' w hc hm (eSec t'.G) y J₀ J hJ₀' hJ
  have p2 := val_pmaps' w hce hr (𝟙 _) y J₀ J hJ₀' hJ
  rw [show eSec t'.G ≫ m.φ = m.cm.e ≫ eSec t.G from m.cm.e_comm, c0] at p1
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Category.comp_id, hact] at p1
  simp only [Finset.univ_unique, Finset.prod_singleton, Category.id_comp, zpow_one] at p2
  rw [val_pull hJ, val_mul hJ, val_rigPow, val_rigPow, Category.id_comp]
  rw [p2, mul_zpow, mul_zpow] at p1
  exact mul_left_cancel (p1.symm.trans (mul_mul_mul_comm _ _ _ _))

section Snd

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

theorem genSnd_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : PGen w)
    (eA : A.left ⟶ A.left) (eG : G.left ⟶ G.left) (hce : eA ≫ φ = φ ≫ eG) (ε : Fin 2 → ℤ)
    (α₀' : LB.Gen (LB.LinComb L₁ ![𝟙 A.left, eA] ε)) (α₀ : LB.Gen (LB.LinComb L₀ ![𝟙 G.left, eG] ε))
    (hPM : PMaps w ![𝟙 A.left, eA] ![𝟙 G.left, eG] ε α₀' α₀ φ)
    (mA : T ⊗ A ⟶ A) (mG : T₀ ⊗ G ⟶ G) (hmA : mA.left = (snd T A).left ≫ eA)
    (hmG : mG.left = (snd T₀ G).left ≫ eG)
    (α : LB.Gen (LB.LinComb L₀ ![(snd T₀ G).left, mG.left] ε)) (hα : α.IsGen)
    (hαc : LB.Gen.Corr L₀ _ _ _ _ α (LB.pullGen L₀ _ _ α₀ (snd T₀ G).left)) :
    ∃ α' : LB.Gen (LB.LinComb L₁ ![(snd T A).left, mA.left] ε), α'.IsGen ∧
      PMaps w ![(snd T A).left, mA.left] ![(snd T₀ G).left, mG.left] ε α' α (psiO hp τ hτ).left ∧
      LB.Gen.Corr L₁ _ _ _ _ α' (LB.pullGen L₁ _ _ α₀' (snd T A).left) := by
  have hc1 : ∀ k, (![(snd T A).left, mA.left] : Fin 2 → _) k ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, mG.left] : Fin 2 → _) k := by
    intro k; fin_cases k
    · exact (psi_snd hp τ hτ).symm
    · show mA.left ≫ φ = (psiO hp τ hτ).left ≫ mG.left
      rw [hmA, hmG, Category.assoc, hce, ← Category.assoc, ← psi_snd hp τ hτ, Category.assoc]
  have hc2 : ∀ k, (![𝟙 A.left, eA] : Fin 2 → _) k ≫ φ = φ ≫ (![𝟙 G.left, eG] : Fin 2 → _) k := by
    intro k; fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Category.id_comp, Category.comp_id]
    · exact hce
  obtain ⟨α', g', hm⟩ := exists_gen_move hL₀ hL₁ w hw _ _ ε (psiO hp τ hτ).left hc1 α hα
  refine ⟨α', g', hm, corr_of_val hL₁ fun y J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hJ₀' : Good L₀ y J₀ := hJ₀
  have p1 := val_pmaps' w hc1 hm (𝟙 _) y J₀ J hJ₀' hJ
  have p2 := val_pmaps' w hc2 hPM (snd T A).left y J₀ J hJ₀' hJ
  have c := val_corr hJ₀' hαc (psiO hp τ hτ).left
  rw [val_pull hJ₀', psi_snd hp τ hτ] at c
  rw [Category.id_comp, c, p2] at p1
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
    Category.id_comp, hmA] at p1
  rw [val_pull hJ, Category.id_comp]
  exact (mul_left_cancel p1).symm

end Snd

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd
