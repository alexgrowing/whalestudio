import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FourfoldProductExt
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLam

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.Z2

variable {S : Scheme.{0}}

section Points

variable {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

def ceLiftPt (G : Over S) {Y : Over (Sp Ω)} (v : Over.mk (Y.hom ≫ s) ⟶ G) : Y ⟶ (Over.pullback s).obj G :=
  Over.homMk (pullback.lift v.left Y.hom (Over.w v)) (pullback.lift_snd _ _ _)

theorem ceToBase_liftPt (G : Over S) {Y : Over (Sp Ω)} (v : Over.mk (Y.hom ≫ s) ⟶ G) :
    toBase G s (ceLiftPt s G v) = v :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

private theorem lam_pull_eq_lam_comp_of_hom {X0 : Scheme} {G G' T : Over X0} [GrpObj G] [GrpObj G'] (ψ : G' ⟶ G)
    (hmul : ∀ x y : T ⟶ G', (x * y) ≫ ψ = (x ≫ ψ) * (y ≫ ψ)) (hone : (1 : T ⟶ G') ≫ ψ = 1)
    (c : Pic G.left) (x y : T ⟶ G') : lam (pull ψ.left c) x y = lam c (x ≫ ψ) (y ≫ ψ) := by
  unfold lam
  simp only [← pull_comp, ← Over.comp_left, hmul, hone]

theorem ceLift_sqToBase (G : Over S) {Y : Over (Sp Ω)} (a u : Y ⟶ (Over.pullback s).obj G) :
    (lift a u).left ≫ sqToBase G s = (lift (toBase G s a) (toBase G s u)).left := by
  have key : (Over.homMk (lift a u).left (by simp only [Over.mk_hom]; rw [← Category.assoc, Over.w]) :
      Over.mk (Y.hom ≫ s) ⟶ Over.mk (((Over.pullback s).obj G ⊗ (Over.pullback s).obj G).hom ≫ s)) ≫
        lift (toBase G s (fst _ _)) (toBase G s (snd _ _)) = lift (toBase G s a) (toBase G s u) := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simp only [Category.assoc, lift_fst, toBase, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · ext
      simp only [Category.assoc, lift_snd, toBase, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  exact congrArg (fun f => f.left) key

end Points

variable {A B : Over S} [GrpObj A] [GrpObj B]

section Fibre

variable {Ω : Type} [Field Ω]

private theorem lam_eq_evc_toBase_of_LBIso [IsCommMonObj A] {P : LB (A ⊗ B).left} (hP : P.IsLB) (l : A ⟶ B)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {Y : Over (Sp Ω)} (X X' : Y ⟶ (Over.pullback s).obj A) :
    lam (cls L hL) X X' = evc hP (toBase A s X) (toBase A s X' ≫ l) := by
  have h1 : (lift (toBase A s X) (toBase A s X')).left = (lift X X').left ≫ sqToBase A s :=
    (ceLift_sqToBase s A X X').symm
  have h2 : lift (toBase A s X) (toBase A s X' ≫ l) =
      lift (toBase A s X) (toBase A s X') ≫ lift (fst A A) (snd A A ≫ l) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hP' := LB.isLB_pull hP (lift (fst A A) (snd A A ≫ l)).left
  have hM := LB.isLB_pull hP' (sqToBase A s)
  have hLam : (abelian₂ ((Over.pullback s).obj A) L).IsLB := GlobalTheory.TripleExt.isLB_cube _ hL
  have h3 := (cls_eq_iff hM hLam).2 e
  rw [cls_pull hP' _ hM, cls_pull hP _ hP'] at h3
  have h4 : cls (abelian₂ ((Over.pullback s).obj A) L) hLam =
      lam (cls L hL) (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)) (snd _ _) :=
    cls_cube_two hL _ _ hLam
  unfold evc
  rw [h2, Over.comp_left, h1, Category.assoc, pull_comp, pull_comp, h3, h4, pull_lam, lift_fst, lift_snd]

set_option maxHeartbeats 800000 in

theorem ceLam_zb_pt (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {Y : Over (Sp Ω)} (a u : Y ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) :
    lam (cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL)) a u =
      zcPair hD.isLB l mu α (toBase _ s a) (toBase _ s u) := by
  haveI := hA.comm
  haveI := hB.comm
  have hl1 : ∀ {T : Over S} (b : T ⟶ B), evc hD.isLB (1 : T ⟶ A) b = 0 := by
    intro T b
    have h := evc_mul_left hD (1 : T ⟶ A) 1 b
    rw [_root_.mul_one] at h
    simpa using h
  have hr1 : ∀ {T : Over S} (x : T ⟶ A), evc hD.isLB x (1 : T ⟶ B) = 0 := by
    intro T x
    have h := evc_mul_right hD hD' x (1 : T ⟶ B) 1
    rw [_root_.mul_one] at h
    simpa using h
  have hlinv : ∀ {T : Over S} (x : T ⟶ A) (b : T ⟶ B), evc hD.isLB x⁻¹ b = -evc hD.isLB x b := by
    intro T x b
    have h := evc_mul_left hD x⁻¹ x b
    rw [inv_mul_cancel, hl1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hrinv : ∀ {T : Over S} (x : T ⟶ A) (b : T ⟶ B), evc hD.isLB x b⁻¹ = -evc hD.isLB x b := by
    intro T x b
    have h := evc_mul_right hD hD' x b⁻¹ b
    rw [inv_mul_cancel, hr1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hL1 := LB.isLB_linComb hL (phiL mu s) (fun _ => (1 : ℤ))
  have hP1 := LB.isLB_linComb hD.isLB (phiP (A := A) (B := B) s) (fun ij : Fin 4 × Fin 4 => α ij.1 ij.2)
  have hcls : cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL) =
      ∑ k, (1 : ℤ) • pull (phiL mu s k) (cls L hL) +
        ∑ ij : Fin 4 × Fin 4, α ij.1 ij.2 • pull (phiP s ij) (cls P hD.isLB) := by
    rw [← cls_linComb hL _ _ hL1, ← cls_linComb hD.isLB _ _ hP1]
    exact cls_tens hL1 hP1 _
  let Λ : Pic ((Over.pullback s).obj (G4 (A ⊗ B))).left →+ Pic Y.left :=
    AddMonoidHom.mk' (fun c => lam c a u) (fun c c' => by
      unfold lam
      simp only [map_add]
      abel)
  have hΛ : ∀ c, lam c a u = Λ c := fun _ => rfl
  have hΛ' : ∀ c, Λ c = lam c a u := fun _ => rfl
  have hφP : ∀ (x : Y ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) (ij : Fin 4 × Fin 4),
      x.left ≫ phiP s ij =
        (lift (toBase _ s x ≫ prj _ ij.1 ≫ fst A B) (toBase _ s x ≫ prj _ ij.2 ≫ snd A B)).left := by
    intro x ij
    have h := toBase_comp s (G4 (A ⊗ B)) x (𝟙 _)
    rw [Category.comp_id] at h
    rw [h, ← comp_lift]
    simp only [phiP, Over.comp_left, Over.homMk_left, Category.assoc]
  have hP : ∀ ij : Fin 4 × Fin 4, lam (pull (phiP s ij) (cls P hD.isLB)) a u =
      evc hD.isLB (toBase _ s a ≫ prj _ ij.1 ≫ fst A B) (toBase _ s u ≫ prj _ ij.2 ≫ snd A B) +
        evc hD.isLB (toBase _ s u ≫ prj _ ij.1 ≫ fst A B) (toBase _ s a ≫ prj _ ij.2 ≫ snd A B) := by
    intro ij
    unfold lam
    simp only [← pull_comp, hφP]
    change evc hD.isLB _ _ - evc hD.isLB _ _ - evc hD.isLB _ _ + evc hD.isLB _ _ = _
    simp only [toBase_mul, toBase_one, MonObj.mul_comp, MonObj.one_comp, evc_mul_left hD,
      evc_mul_right hD hD', hl1, hr1]
    abel
  have hA0 : ∀ i, lam (pull (pA (B := B) s i).left (cls L hL)) a u =
      evc hD.isLB (toBase _ s a ≫ prj _ i ≫ fst A B) (toBase _ s u ≫ prj _ i ≫ fst A B ≫ l) := by
    intro i
    rw [show pA (B := B) s i = (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B) from rfl, lam_pull,
      lam_eq_evc_toBase_of_LBIso hD.isLB l s L hL e]
    simp only [toBase_map, Category.assoc]
  have hA1 : ∀ i, lam (pull ((pA (B := B) s i)⁻¹).left (cls L hL)) a u =
      evc hD.isLB (toBase _ s a ≫ prj _ i ≫ fst A B) (toBase _ s u ≫ prj _ i ≫ fst A B ≫ l) := by
    intro i
    rw [show pA (B := B) s i = (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B) from rfl]
    rw [lam_pull_eq_lam_comp_of_hom _ (fun x y => by simp only [GrpObj.comp_inv, MonObj.mul_comp, mul_inv])
      (by simp only [GrpObj.comp_inv, MonObj.one_comp, inv_one]), lam_eq_evc_toBase_of_LBIso hD.isLB l s L hL e]
    simp only [GrpObj.comp_inv, toBase_inv, toBase_map, GrpObj.inv_comp, hlinv, hrinv, neg_neg,
      Category.assoc]
  have hM0 : ∀ i, lam (pull (pM mu s i).left (cls L hL)) a u =
      evc hD.isLB (toBase _ s a ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
    intro i
    rw [show pM mu s i = (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu) from rfl, lam_pull,
      lam_eq_evc_toBase_of_LBIso hD.isLB l s L hL e]
    simp only [toBase_map, Category.assoc]
  have hM1 : ∀ i, lam (pull ((pM mu s i)⁻¹).left (cls L hL)) a u =
      evc hD.isLB (toBase _ s a ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
    intro i
    rw [show pM mu s i = (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu) from rfl]
    rw [lam_pull_eq_lam_comp_of_hom _ (fun x y => by simp only [GrpObj.comp_inv, MonObj.mul_comp, mul_inv])
      (by simp only [GrpObj.comp_inv, MonObj.one_comp, inv_one]), lam_eq_evc_toBase_of_LBIso hD.isLB l s L hL e]
    simp only [GrpObj.comp_inv, toBase_inv, toBase_map, GrpObj.inv_comp, hlinv, hrinv, neg_neg,
      Category.assoc]
  have hφ0 : ∀ i, phiL mu s (0, i) = (pA (B := B) s i).left := fun _ => rfl
  have hφ1 : ∀ i, phiL mu s (1, i) = ((pA (B := B) s i)⁻¹).left := fun _ => rfl
  have hφ2 : ∀ i, phiL mu s (2, i) = (pM mu s i).left := fun _ => rfl
  have hφ3 : ∀ i, phiL mu s (3, i) = ((pM mu s i)⁻¹).left := fun _ => rfl
  rw [hΛ, hcls, map_add, map_sum, map_sum]
  simp only [map_zsmul, one_smul]
  simp only [hΛ']
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_four]
  simp only [hφ0, hφ1, hφ2, hφ3, hA0, hA1, hM0, hM1, hP]
  unfold zcPair
  simp only [Fin.sum_univ_four, smul_add, two_nsmul]
  ac_rfl

private theorem evc_comp_eq_lam_ceLiftPt [IsCommMonObj A] {P : LB (A ⊗ B).left} (hP : P.IsLB) (l : A ⟶ B)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {Y : Over (Sp Ω)} (x y : Over.mk (Y.hom ≫ s) ⟶ A) :
    evc hP x (y ≫ l) = lam (cls L hL) (ceLiftPt s A x) (ceLiftPt s A y) := by
  have h1 : (lift x y).left = (lift (ceLiftPt s A x) (ceLiftPt s A y)).left ≫ sqToBase A s := by
    rw [ceLift_sqToBase, ceToBase_liftPt, ceToBase_liftPt]
  have h2 : lift x (y ≫ l) = lift x y ≫ lift (fst A A) (snd A A ≫ l) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hP' := LB.isLB_pull hP (lift (fst A A) (snd A A ≫ l)).left
  have hM := LB.isLB_pull hP' (sqToBase A s)
  have hLam : (abelian₂ ((Over.pullback s).obj A) L).IsLB := GlobalTheory.TripleExt.isLB_cube _ hL
  have h3 := (cls_eq_iff hM hLam).2 e
  rw [cls_pull hP' _ hM, cls_pull hP _ hP'] at h3
  have h4 : cls (abelian₂ ((Over.pullback s).obj A) L) hLam =
      lam (cls L hL) (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)) (snd _ _) :=
    cls_cube_two hL _ _ hLam
  unfold evc
  rw [h2, Over.comp_left, h1, Category.assoc, pull_comp, pull_comp, h3, h4, pull_lam, lift_fst, lift_snd]

theorem ceEvc_sym (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : P.IsLB) (l : A ⟶ B) (s : Sp Ω ⟶ S)
    (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {Y : Over (Sp Ω)} (x y : Over.mk (Y.hom ≫ s) ⟶ A) :
    evc hP x (y ≫ l) = evc hP y (x ≫ l) := by
  haveI := hA.comm
  rw [evc_comp_eq_lam_ceLiftPt hP l s L hL e, evc_comp_eq_lam_ceLiftPt hP l s L hL e, lam_comm]

end Fibre

variable [IsCommMonObj A] [IsCommMonObj B]

section EMap

theorem ceEMap_fst (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) {Y : Over S}
    (a : Y ⟶ G4 (A ⊗ B)) (i : Fin 4) :
    a ≫ eMap mu α m ≫ prj _ i ≫ fst A B =
      (a ≫ prj _ i ≫ fst A B) * (∏ j, (a ≫ prj _ j ≫ snd A B ≫ mu) ^ (α i j))⁻¹ := by
  simp only [eMap, g4lift_prj'_assoc, lift_fst, MonObj.comp_mul, GrpObj.comp_inv, Fin.prod_univ_four,
    GrpObj.comp_zpow, Category.assoc]

theorem ceEMap_snd (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) {Y : Over S}
    (a : Y ⟶ G4 (A ⊗ B)) (i : Fin 4) :
    a ≫ eMap mu α m ≫ prj _ i ≫ snd A B = (a ≫ prj _ i ≫ snd A B) ^ (2 * m) := by
  simp only [eMap, g4lift_prj'_assoc, lift_snd, MonObj.comp_pow, Category.assoc]

theorem ceEMap_mul (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) {Y : Over S}
    (a b : Y ⟶ G4 (A ⊗ B)) : (a * b) ≫ eMap mu α m = (a ≫ eMap mu α m) * (b ≫ eMap mu α m) := by
  apply fourfold_product_ext
  intro i
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, ceEMap_fst, MonObj.mul_comp, Finset.prod_mul_distrib, mul_zpow, mul_inv]
    ac_rfl
  · simp only [Category.assoc, ceEMap_snd, MonObj.mul_comp, mul_pow]

theorem ceEMap_one (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) {Y : Over S} :
    (1 : Y ⟶ G4 (A ⊗ B)) ≫ eMap mu α m = 1 := by
  apply fourfold_product_ext
  intro i
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, ceEMap_fst, MonObj.one_comp, one_zpow, Finset.prod_const_one, inv_one]
    exact mul_one _
  · simp only [Category.assoc, ceEMap_snd, MonObj.one_comp, one_pow]

theorem ceEMap_inv (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) {Y : Over S}
    (a : Y ⟶ G4 (A ⊗ B)) : a⁻¹ ≫ eMap mu α m = (a ≫ eMap mu α m)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← ceEMap_mul, inv_mul_cancel, ceEMap_one]

end EMap

section Alg

variable {Y : Over S} {P : LB (A ⊗ B).left}

def ceB (hD : IsDual A B P) (hD' : IsDual B A (swap P)) :
    Additive (Y ⟶ A) →+ Additive (Y ⟶ B) →+ Pic Y.left :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun z => evc hD.isLB (Additive.toMul x) (Additive.toMul z))
      (fun z z' => evc_mul_right hD hD' _ _ _))
    (fun x x' => AddMonoidHom.ext fun z => evc_mul_left hD _ _ _)

private theorem ceZc_alg_lemma {GA GB Q : Type*} [AddCommGroup GA] [AddCommGroup GB] [AddCommGroup Q]
    (E : GA →+ GB →+ Q) (lm : GA →+ GB) (mu : GB →+ GA) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hml : ∀ w, lm (mu w) = m • w)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hsym : ∀ u v, E u (lm v) = E v (lm u)) (x x' : Fin 4 → GA) (z z' : Fin 4 → GB) :
    ∑ i, 2 • E (x i - ∑ j, α i j • mu (z j)) (lm (x' i - ∑ j, α i j • mu (z' j))) +
      ∑ i, ∑ j, α i j • (E (x i - ∑ k, α i k • mu (z k)) ((2 * m) • z' j) +
        E (x' i - ∑ k, α i k • mu (z' k)) ((2 * m) • z j)) +
      ∑ i, 2 • E (mu ((2 * m) • z i)) (lm (mu ((2 * m) • z' i))) =
    ∑ i, 2 • E (x i) (lm (x' i)) + ∑ i, 2 • E (mu (z i)) (lm (mu (z' i))) := by
  have hs : ∀ w v, E (mu w) (lm v) = m • E v w := fun w v => by rw [hsym, hml, map_nsmul]
  have hmz : ∀ w w', m • E (mu w') w = m • E (mu w) w' := fun w w' => by
    rw [← map_nsmul, ← hml, hsym, hml, map_nsmul]
  have hc : (((4 * m ^ 2 - 1 : ℕ) : ℤ)) = 4 * (m : ℤ) ^ 2 - 1 := by
    have h1 : 1 ≤ 4 * m ^ 2 := by nlinarith
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hjk : ∀ j k, α 0 j * α 0 k + α 1 j * α 1 k + α 2 j * α 2 k + α 3 j * α 3 k =
      (4 * (m : ℤ) ^ 2 - 1) * (1 : Matrix (Fin 4) (Fin 4) ℤ) j k := by
    intro j k
    have h := congrFun (congrFun hα j) k
    rw [hc] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_four] using h
  have hd : ∀ j, α 0 j * α 0 j + α 1 j * α 1 j + α 2 j * α 2 j + α 3 j * α 3 j =
      4 * (m : ℤ) ^ 2 - 1 := by
    intro j
    simpa using hjk j j
  have ho : ∀ j k, j ≠ k → α 0 j * α 0 k + α 1 j * α 1 k + α 2 j * α 2 k + α 3 j * α 3 k = 0 := by
    intro j k hne
    simpa [Matrix.one_apply, hne] using hjk j k
  simp only [map_sub, map_sum, map_zsmul, map_nsmul, AddMonoidHom.sub_apply, AddMonoidHom.finset_sum_apply,
    AddMonoidHom.smul_apply, hml, hs, Fin.sum_univ_four, map_add, AddMonoidHom.add_apply]
  linear_combination (norm := module)
      ((-2 : ℤ) * (m : ℤ)) • ((hd 0) • E (mu (z' 0)) (z 0)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 0 1 (by decide)) • E (mu (z' 0)) (z 1)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 0 2 (by decide)) • E (mu (z' 0)) (z 2)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 0 3 (by decide)) • E (mu (z' 0)) (z 3)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 1 0 (by decide)) • E (mu (z' 1)) (z 0)) +
      ((-2 : ℤ) * (m : ℤ)) • ((hd 1) • E (mu (z' 1)) (z 1)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 1 2 (by decide)) • E (mu (z' 1)) (z 2)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 1 3 (by decide)) • E (mu (z' 1)) (z 3)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 2 0 (by decide)) • E (mu (z' 2)) (z 0)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 2 1 (by decide)) • E (mu (z' 2)) (z 1)) +
      ((-2 : ℤ) * (m : ℤ)) • ((hd 2) • E (mu (z' 2)) (z 2)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 2 3 (by decide)) • E (mu (z' 2)) (z 3)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 3 0 (by decide)) • E (mu (z' 3)) (z 0)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 3 1 (by decide)) • E (mu (z' 3)) (z 1)) +
      ((-2 : ℤ) * (m : ℤ)) • ((ho 3 2 (by decide)) • E (mu (z' 3)) (z 2)) +
      ((-2 : ℤ) * (m : ℤ)) • ((hd 3) • E (mu (z' 3)) (z 3)) +
      (-2 * (4 * (m : ℤ) ^ 2 - 1)) • (hmz (z 0) (z' 0)) +
      (-2 * (4 * (m : ℤ) ^ 2 - 1)) • (hmz (z 1) (z' 1)) +
      (-2 * (4 * (m : ℤ) ^ 2 - 1)) • (hmz (z 2) (z' 2)) +
      (-2 * (4 * (m : ℤ) ^ 2 - 1)) • (hmz (z 3) (z' 3))

theorem ceZcPair_eMap (hD : IsDual A B P) (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A)
    [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (hm : 1 ≤ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hsym : ∀ x y : Y ⟶ A, evc hD.isLB x (y ≫ l) = evc hD.isLB y (x ≫ l)) (a a' : Y ⟶ G4 (A ⊗ B)) :
    zcPair hD.isLB l mu α (a ≫ eMap mu α m) (a' ≫ eMap mu α m) =
      ∑ i, 2 • evc hD.isLB (a ≫ prj _ i ≫ fst A B) (a' ≫ prj _ i ≫ fst A B ≫ l) +
        ∑ i, 2 • evc hD.isLB (a ≫ prj _ i ≫ snd A B ≫ mu) (a' ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
  let E := ceB (Y := Y) hD hD'
  let lm' : Additive (Y ⟶ A) →+ Additive (Y ⟶ B) :=
    AddMonoidHom.mk' (fun w => Additive.ofMul (Additive.toMul w ≫ l)) (fun w w' => by
      show Additive.ofMul ((Additive.toMul w * Additive.toMul w') ≫ l) = _
      rw [MonObj.mul_comp]
      rfl)
  let mu' : Additive (Y ⟶ B) →+ Additive (Y ⟶ A) :=
    AddMonoidHom.mk' (fun w => Additive.ofMul (Additive.toMul w ≫ mu)) (fun w w' => by
      show Additive.ofMul ((Additive.toMul w * Additive.toMul w') ≫ mu) = _
      rw [MonObj.mul_comp]
      rfl)
  have hml : ∀ w, lm' (mu' w) = m • w := by
    intro w
    show Additive.ofMul ((Additive.toMul w ≫ mu) ≫ l) = m • w
    rw [Category.assoc, h₂, MonObj.comp_pow, Category.comp_id, ofMul_pow]
    rfl
  have hsym' : ∀ u v, E u (lm' v) = E v (lm' u) := fun u v => hsym (Additive.toMul u) (Additive.toMul v)
  have key := ceZc_alg_lemma E lm' mu' α m hm hml hα hsym'
    (fun i => Additive.ofMul (a ≫ prj _ i ≫ fst A B)) (fun i => Additive.ofMul (a' ≫ prj _ i ≫ fst A B))
    (fun i => Additive.ofMul (a ≫ prj _ i ≫ snd A B)) (fun i => Additive.ofMul (a' ≫ prj _ i ≫ snd A B))
  beta_reduce at key
  have hE : ∀ (p : Y ⟶ A) (q : Y ⟶ B), evc hD.isLB p q = E (Additive.ofMul p) (Additive.ofMul q) :=
    fun _ _ => rfl
  have hlg : ∀ p : Y ⟶ A, Additive.ofMul (p ≫ l) = lm' (Additive.ofMul p) := fun _ => rfl
  have hmug : ∀ p : Y ⟶ B, Additive.ofMul (p ≫ mu) = mu' (Additive.ofMul p) := fun _ => rfl
  have hlx : ∀ (b : Y ⟶ G4 (A ⊗ B)) i,
      Additive.ofMul (b ≫ prj _ i ≫ fst A B ≫ l) = lm' (Additive.ofMul (b ≫ prj _ i ≫ fst A B)) := by
    intro b i
    rw [← hlg]
    simp only [Category.assoc]
  have hmuz : ∀ (b : Y ⟶ G4 (A ⊗ B)) i,
      Additive.ofMul (b ≫ prj _ i ≫ snd A B ≫ mu) = mu' (Additive.ofMul (b ≫ prj _ i ≫ snd A B)) := by
    intro b i
    rw [← hmug]
    simp only [Category.assoc]
  have hlmuz : ∀ (b : Y ⟶ G4 (A ⊗ B)) i,
      Additive.ofMul (b ≫ prj _ i ≫ snd A B ≫ mu ≫ l) =
        lm' (mu' (Additive.ofMul (b ≫ prj _ i ≫ snd A B))) := by
    intro b i
    rw [← hmug, ← hlg]
    simp only [Category.assoc]
  have hf0 : ∀ (b : Y ⟶ G4 (A ⊗ B)) i, (b ≫ eMap mu α m) ≫ prj _ i ≫ fst A B =
      (b ≫ prj _ i ≫ fst A B) * (∏ j, (b ≫ prj _ j ≫ snd A B ≫ mu) ^ (α i j))⁻¹ := by
    intro b i
    rw [Category.assoc, ceEMap_fst]
  have hf1 : ∀ (b : Y ⟶ G4 (A ⊗ B)) i, (b ≫ eMap mu α m) ≫ prj _ i ≫ fst A B ≫ l =
      ((b ≫ prj _ i ≫ fst A B) * (∏ j, (b ≫ prj _ j ≫ snd A B ≫ mu) ^ (α i j))⁻¹) ≫ l := by
    intro b i
    rw [← hf0]
    simp only [Category.assoc]
  have hs0 : ∀ (b : Y ⟶ G4 (A ⊗ B)) i, (b ≫ eMap mu α m) ≫ prj _ i ≫ snd A B =
      (b ≫ prj _ i ≫ snd A B) ^ (2 * m) := by
    intro b i
    rw [Category.assoc, ceEMap_snd]
  have hs1 : ∀ (b : Y ⟶ G4 (A ⊗ B)) i, (b ≫ eMap mu α m) ≫ prj _ i ≫ snd A B ≫ mu =
      ((b ≫ prj _ i ≫ snd A B) ^ (2 * m)) ≫ mu := by
    intro b i
    rw [← hs0]
    simp only [Category.assoc]
  have hs2 : ∀ (b : Y ⟶ G4 (A ⊗ B)) i, (b ≫ eMap mu α m) ≫ prj _ i ≫ snd A B ≫ mu ≫ l =
      (((b ≫ prj _ i ≫ snd A B) ^ (2 * m)) ≫ mu) ≫ l := by
    intro b i
    rw [← hs0]
    simp only [Category.assoc]
  unfold zcPair
  simp only [hf0, hf1, hs0, hs1, hs2]
  simp only [hE, hlx, hmuz, hlmuz, hlg, hmug, ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, ofMul_pow,
    ← sub_eq_add_neg]
  exact key

end Alg

set_option maxHeartbeats 800000 in

theorem two_cls_eMap {Ω : Type} [Field Ω] [IsAlgClosed Ω] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (h₁' : ((zb mu α s P L).pull ((Over.pullback s).map (eMap mu α m)).left).IsLB)
    (h₂' : (lPart mu s L).IsLB) :
    2 • cls _ h₁' = 2 • cls _ h₂' := by
  haveI := hA.comm
  haveI := hB.comm
  haveI hpA : ∀ i, IsMonHom (pA (A := A) (B := B) s i) := fun i => by unfold pA; infer_instance
  haveI hpM : ∀ i, IsMonHom (pM mu s i) := fun i => by unfold pM; infer_instance
  have hMmul : ∀ {T : Over (Sp Ω)} (x y : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))), (x * y) ≫ (Over.pullback s).map (eMap mu α m) = (x ≫ (Over.pullback s).map (eMap mu α m)) * (y ≫ (Over.pullback s).map (eMap mu α m)) := by
    intro T x y
    apply toBase_injective s
    rw [toBase_map, toBase_mul, toBase_mul, toBase_map, toBase_map, ceEMap_mul]
  have hMone : ∀ {T : Over (Sp Ω)}, (1 : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) ≫ (Over.pullback s).map (eMap mu α m) = 1 := by
    intro T
    apply toBase_injective s
    rw [toBase_map, toBase_one, ceEMap_one]
  have hL1 := LB.isLB_linComb hL (phiL mu s) (fun _ => (1 : ℤ))
  have hP1 := LB.isLB_linComb hD.isLB (phiP (A := A) (B := B) s) (fun ij : Fin 4 × Fin 4 => α ij.1 ij.2)
  have hLsum : cls (lPart mu s L) h₂' = (∑ k : Fin 4 × Fin 4, (1 : ℤ) • pull (phiL mu s k) (cls L hL)) := cls_linComb hL _ _ h₂'
  have hzb : cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL) = (∑ k : Fin 4 × Fin 4, (1 : ℤ) • pull (phiL mu s k) (cls L hL)) + (∑ ij : Fin 4 × Fin 4, α ij.1 ij.2 • pull (phiP s ij) (cls P hD.isLB)) := by
    rw [← cls_linComb hL _ _ hL1, ← cls_linComb hD.isLB _ _ hP1]
    exact cls_tens hL1 hP1 _
  have hc1 : cls _ h₁' = pull ((Over.pullback s).map (eMap mu α m)).left (cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL)) :=
    cls_pull _ _ h₁'
  have hgen : ∀ c : Pic ((Over.pullback s).obj (G4 (A ⊗ B))).left, pull ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹).left c = c →
      c + c = 2 • pull (1 : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj (G4 (A ⊗ B))).left c - lam c (𝟙 _) (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹ := by
    intro c hc
    unfold lam
    rw [mul_inv_cancel, hc, Over.id_left, pull_id]
    abel
  have hφ0 : ∀ i, phiL mu s (0, i) = (pA (B := B) s i).left := fun _ => rfl
  have hφ1 : ∀ i, phiL mu s (1, i) = ((pA (B := B) s i)⁻¹).left := fun _ => rfl
  have hφ2 : ∀ i, phiL mu s (2, i) = (pM mu s i).left := fun _ => rfl
  have hφ3 : ∀ i, phiL mu s (3, i) = ((pM mu s i)⁻¹).left := fun _ => rfl
  have e0 : ∀ i, ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹).left ≫ phiL mu s (0, i) = phiL mu s (1, i) := fun i => by
    rw [hφ0, hφ1, ← Over.comp_left, GrpObj.inv_comp, Category.id_comp]
  have e1 : ∀ i, ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹).left ≫ phiL mu s (1, i) = phiL mu s (0, i) := fun i => by
    rw [hφ0, hφ1, ← Over.comp_left, GrpObj.comp_inv, GrpObj.inv_comp, Category.id_comp, inv_inv]
  have e2 : ∀ i, ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹).left ≫ phiL mu s (2, i) = phiL mu s (3, i) := fun i => by
    rw [hφ2, hφ3, ← Over.comp_left, GrpObj.inv_comp, Category.id_comp]
  have e3 : ∀ i, ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹).left ≫ phiL mu s (3, i) = phiL mu s (2, i) := fun i => by
    rw [hφ2, hφ3, ← Over.comp_left, GrpObj.comp_inv, GrpObj.inv_comp, Category.id_comp, inv_inv]
  have symL : pull ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹).left (∑ k : Fin 4 × Fin 4, (1 : ℤ) • pull (phiL mu s k) (cls L hL)) = (∑ k : Fin 4 × Fin 4, (1 : ℤ) • pull (phiL mu s k) (cls L hL)) := by
    simp only [map_sum, map_zsmul, ← pull_comp]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_four, e0, e1, e2, e3]
    abel
  have symP : pull ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹).left (∑ ij : Fin 4 × Fin 4, α ij.1 ij.2 • pull (phiP s ij) (cls P hD.isLB)) = (∑ ij : Fin 4 × Fin 4, α ij.1 ij.2 • pull (phiP s ij) (cls P hD.isLB)) := by
    simp only [map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun ij _ => ?_
    congr 1
    have h1 := pull_phiP s hD.isLB (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B)))) ij
    rw [Over.id_left, pull_id] at h1
    rw [pull_phiP, h1, toBase_inv, GrpObj.inv_comp, GrpObj.inv_comp, evc_inv_inv hD hD']
  have oneP : pull (1 : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj (G4 (A ⊗ B))).left (∑ ij : Fin 4 × Fin 4, α ij.1 ij.2 • pull (phiP s ij) (cls P hD.isLB)) = 0 := by
    simp only [map_sum, map_zsmul, pull_phiP, toBase_one, MonObj.one_comp, evc_one_l hD, smul_zero,
      Finset.sum_const_zero]
  have hvM : (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹ ≫ (Over.pullback s).map (eMap mu α m) = (Over.pullback s).map (eMap mu α m) ≫ (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹ := by
    have L1 : toBase _ s ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹ ≫ (Over.pullback s).map (eMap mu α m)) = (toBase _ s (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B)))) ≫ eMap mu α m)⁻¹ := by
      rw [toBase_map, toBase_inv, ceEMap_inv]
    have R1 : toBase _ s ((Over.pullback s).map (eMap mu α m) ≫ (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹) = (toBase _ s (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B)))) ≫ eMap mu α m)⁻¹ := by
      rw [GrpObj.comp_inv, Category.comp_id, toBase_inv, ← toBase_map, Category.id_comp]
    exact toBase_injective s _ (L1.trans R1.symm)
  have symC1 : pull ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹).left (cls _ h₁') = cls _ h₁' := by
    rw [hc1, ← pull_comp, ← Over.comp_left, hvM, Over.comp_left, pull_comp, hzb, map_add, symL, symP]
  have oneEq : pull (1 : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj (G4 (A ⊗ B))).left (cls _ h₁') = pull (1 : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj (G4 (A ⊗ B))).left (cls _ h₂') := by
    rw [hc1, ← pull_comp, ← Over.comp_left, hMone, hzb, map_add, oneP, add_zero, hLsum]
  have lamEq : lam (cls _ h₁') (𝟙 _) (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹ = lam (cls _ h₂') (𝟙 _) (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))⁻¹ := by
    rw [hc1, lam_pull_eq_lam_comp_of_hom _ hMmul hMone, ceLam_zb_pt hA hB hD hD' l mu α s L hL e, toBase_map, toBase_map,
      ceZcPair_eMap hD hD' l mu α m hm h₂ hα (fun x y => ceEvc_sym hA hD.isLB l s L hL e x y), hLsum,
      lam_eq_lamHom]
    simp only [map_sum, map_zsmul, one_smul, ← lam_eq_lamHom]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_four, line_bundle_pairing_zeroth hD l mu s L hL e, line_bundle_pairing_first hD hD' l mu s L hL e,
      line_bundle_pairing_second hD l mu s L hL e, line_bundle_pairing_third hD hD' l mu s L hL e, two_nsmul]
    ac_rfl
  have g1 := hgen _ symC1
  have g2 := hgen (cls _ h₂') (by rw [hLsum]; exact symL)
  rw [two_nsmul, two_nsmul, g1, g2, oneEq, lamEq]

end PositivityTheory.PrwZar.Z2
