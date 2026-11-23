import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem lam_eq_ros_mul_cmp : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) [IsMonHom inc] [IsMonHom pr] (ea fa ea' : D'.P.A ⟶ D'.P.A) [IsMonHom ea] [IsMonHom fa] [IsMonHom ea'], pr ≫ inc = ea → ∀ (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa) : G2 D₀.P.A ⟶ G2 D'.P.A).left)), w.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι) (J' : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D'.P.L z J → Good D₀.P.L z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ D₀.P.A) y).left z J J' = 1) → ∀ (ur : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A ea ea') rosatiε)), ur.IsGen → (∀ (T : Over (Sp R)) (y : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val ur (lift (1 : T ⟶ D'.P.A) y).left z J = 1) → ∀ (χ' : D'.X) (χ : D₀.X) (q : 𝟙_ (Over (Sp R)) ⟶ D'.P.A), D₀.c χ ≫ inc ≫ fa = q → D'.c χ' = q ≫ ea' → ∀ (u : LB.Gen (CmpLB D' D₀ pr χ' χ)), Nrm u → ∀ (T : Over (Sp R)) (x : T ⟶ D'.P.A) (z : T.left) (J : (T.left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → GlobalTheory.PolDeg.lamVal w (lift (x ≫ pr) (toUnit T ≫ D₀.c χ)).left z (rl J) (rr J) = val ur (lift x (toUnit T ≫ q)).left z (rl J) * val u x.left z J := by
  intro R _ _ D₀ D' inc pr _ _ ea fa ea' _ _ _ hea w hw hw1 ur hur hur1 χ' χ q hq hq' u hu T x z J hJ
  have hN : (JN D' D₀).IsLB := jn_isLB D' D₀
  have h₁ := isPart_inl D'.P.L D₀.P.L
  have h₂ := isPart_inr D'.P.L D₀.P.L
  obtain ⟨t, ht, htv⟩ := exists_gen_of_iso h₁ h₂ w hw
  let m : D'.P.A.left ⟶ (G2 D₀.P.A).left := (lift pr (toUnit _ ≫ D₀.c χ)).left
  let n : D'.P.A.left ⟶ (G2 D'.P.A).left := (lift (𝟙 _) (toUnit _ ≫ q)).left
  let t₁ := LB.pullGen _ _ _ t m
  let t₂ := LB.mulGen _ _ _ _ _ (h₁.gen (LB.pullGen _ _ _ ur n)) u
  have hG := GlobalTheory.globalFns_holds
  have key := gen_unique' hN (u := t₁) (u' := t₂) ?fe D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ ht m) (DVR.mulGen_isGen _ _ _ _ _ _ _ (h₁.gen_isGen (DVR.pullGen_isGen _ _ _ _ hur n)) hu.1)
    ?ev T.left x.left z J hJ
  · have e₁ : x.left ≫ m = (lift (x ≫ pr) (toUnit T ≫ D₀.c χ)).left := by
      rw [← Over.comp_left, comp_lift, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
    have e₂ : x.left ≫ n = (lift x (toUnit T ≫ q)).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
    rw [val_pull hJ, htv _ _ z J hJ, val_mul hJ, h₁.val_gen _ _ z hJ, val_pull (h₁.good hJ), e₁, e₂] at key
    exact key
  case fe =>
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have mβ : m ≫ (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa)).left =
        (lift ea (toUnit _ ≫ q)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, hea, Category.assoc, hq]
    have A1 : ∏ a₁ : ULift (Finset (Fin 2)), h (m ≫ (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ fa)).left ≫
        (psum D'.P.A (x2 D'.P.A) a₁.down).left ≫ coprod.inl) ^ ((-1 : ℤ) ^ (2 - a₁.down.card)) =
        h ((ea * (toUnit _ ≫ q)).left ≫ coprod.inl) * (h (ea.left ≫ coprod.inl))⁻¹ *
          (h ((toUnit _ ≫ q).left ≫ coprod.inl))⁻¹ * h ((1 : D'.P.A ⟶ D'.P.A).left ≫ coprod.inl) := by
      refine (Finset.prod_congr rfl fun k _ => ?_).trans
        (GlobalTheory.PrimCocycle.prod_lam ea (toUnit _ ≫ q) (fun g => h (g ≫ coprod.inl)))
      rw [← Category.assoc, ← Category.assoc, mβ]
    have A2 : ∏ a₂ : ULift (Finset (Fin 2)), h (m ≫ (psum D₀.P.A (x2 D₀.P.A) a₂.down).left ≫ coprod.inr) ^
        (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((pr * (toUnit _ ≫ D₀.c χ)).left ≫ coprod.inr) * (h (pr.left ≫ coprod.inr))⁻¹ *
          (h ((toUnit _ ≫ D₀.c χ).left ≫ coprod.inr))⁻¹ * h ((1 : D'.P.A ⟶ D₀.P.A).left ≫ coprod.inr))⁻¹ := by
      rw [← GlobalTheory.PrimCocycle.prod_lam pr (toUnit _ ≫ D₀.c χ) (fun g => h (g ≫ coprod.inr)), ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    have A3 := prod_ros ea ea' (𝟙 D'.P.A) (toUnit _ ≫ q) (fun g => h (g ≫ coprod.inl))
    beta_reduce at A3
    rw [A1, A2, A3, Fin.prod_univ_four, Fin.prod_univ_four]
    clear * - h hq'
    have pm : ∀ {X Y : Over (Sp R)} [GrpObj Y] (a b : X ⟶ Y), padd Y a b = a * b := fun _ _ => rfl
    simp only [DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pm, ← Hom.one_def, hq', Category.id_comp,
      Category.assoc]
    simp only [zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  case ev =>
    intro y I hI
    have o₀ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have o' : (1 : 𝟙_ (Over (Sp R)) ⟶ D'.P.A) = η[D'.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have e₁ : eSec D'.P.A ≫ m = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (toUnit _ ≫ D₀.c χ)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, IsMonHom.one_hom, ← Category.assoc,
        toUnit_unique (η[D'.P.A] ≫ toUnit _) (toUnit _), o₀]
    have e₂ : eSec D'.P.A ≫ n = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D'.P.A) (toUnit _ ≫ q)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D'.P.A] ≫ toUnit _) (toUnit _), o']
    rw [val_pull hI, htv _ _ y I hI, val_mul hI, h₁.val_gen _ _ y hI, val_pull (h₁.good hI), e₁, e₂]
    have a := hw1 (𝟙_ _) (toUnit _ ≫ D₀.c χ) y (rl I) (rr I) (h₁.good hI) (h₂.good hI)
    have b := hur1 (𝟙_ _) (toUnit _ ≫ q) y (rl I) (h₁.good hI)
    have c := hu.2 _ (𝟙 _) y I hI
    rw [Category.id_comp] at c
    rw [show isoVal w (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (toUnit _ ≫ D₀.c χ)).left y (rl I) (rr I) = 1 from a, b, c,
      _root_.one_mul]

end GlobalTheory.Mum.Two
