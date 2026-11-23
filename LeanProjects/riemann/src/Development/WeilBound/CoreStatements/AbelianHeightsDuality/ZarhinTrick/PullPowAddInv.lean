import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamD

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.Z2

section Gen

variable {S' : Scheme.{0}}

theorem pow_comp_hom {T G G' : Over S'} [MonObj G] [MonObj G'] (f : G ⟶ G') [IsMonHom f] (x : T ⟶ G) (n : ℕ) :
    (x ^ n) ≫ f = (x ≫ f) ^ n := by
  exact map_pow (IsMonHom.monoidHom f T) x n

end Gen

section Helpers

variable {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

theorem toBase_pow (G : Over S) [GrpObj G] {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj G) (n : ℕ) :
    toBase G s (x ^ n) = toBase G s x ^ n := by
  induction n with
  | zero => simpa using toBase_one s G (T := T)
  | succ k ih => rw [pow_succ, pow_succ, toBase_mul, ih]

theorem pull_one_pt {G T : Over (Sp Ω)} [MonObj G] (c : Pic G.left) : pull (1 : T ⟶ G).left c = 0 := by
  rw [Hom.one_def, Over.comp_left, pull_comp]
  rw [show (pull η[G].left) c = 0 from GlobalTheory.PrimitiveOverField.pic_field _]
  exact map_zero _

section Biadd

variable {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
  (hD' : IsDual B A (swap P)) {Y : Over S}

private theorem evc_mul_left' (a a' : Y ⟶ A) (b : Y ⟶ B) :
    evc hD.isLB (a * a') b = evc hD.isLB a b + evc hD.isLB a' b := by
  have hP := hD.isLB
  have hm := hD.additive Y a a' b
  have h1 : (ev P a b).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hP _
  have h2 : (ev P a' b).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hP _
  have h3 : (ev P (a * a') b).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hP _
  change cls (ev P (a * a') b) h3 = cls (ev P a b) h1 + cls (ev P a' b) h2
  rw [← cls_tens h1 h2 (isLB_tens h1 h2)]
  exact (cls_eq_iff _ _).2 hm

include hD in
theorem evc_pow_left (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hD.isLB (a ^ n) b = n • evc hD.isLB a b := by
  induction n with
  | zero => simpa using IsAdditive.evc_one hD.isLB hD.additive b
  | succ k ih => rw [pow_succ, evc_mul_left' hD, ih, succ_nsmul]

include hD hD' in
theorem evc_pow_right (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hD.isLB a (b ^ n) = n • evc hD.isLB a b := by
  rw [← evc_swap hD.isLB hD'.isLB, evc_pow_left hD' b a n, evc_swap hD.isLB hD'.isLB]

end Biadd

section LPart

variable {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
  (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
  (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
  {T : Over (Sp Ω)}

private theorem lam_eq_evc_toBase_of_isDual (e' : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (x y : T ⟶ (Over.pullback s).obj A) :
    lam (cls L hL) x y = evc hD.isLB (toBase A s x) (toBase A s y ≫ l) := by
  have hP : (abelian₂ ((Over.pullback s).obj A) L).IsLB := LB.isLB_linComb hL _ _
  have hM : (ev P (fst A A) (snd A A ≫ l)).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hD.isLB _
  have hM' : ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)).IsLB :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hM _
  have h1 : cls _ hP = cls _ hM' := ((cls_eq_iff hM' hP).2 e').symm
  have hx := toBase_comp s A (lift x y) (fst _ _)
  have hy := toBase_comp s A (lift x y) (snd _ _)
  rw [lift_fst] at hx
  rw [lift_snd] at hy
  have key : (lift x y).left ≫ sqToBase A s = (lift (toBase A s x) (toBase A s y)).left := by
    rw [hx, hy, ← comp_lift, Over.comp_left]
    rfl
  rw [← GlobalTheory.CubeDual.evc_lam hL hP]
  change pull (lift x y).left (cls _ hP) =
    pull (lift (toBase A s x) (toBase A s y ≫ l)).left (cls P hD.isLB)
  rw [h1]
  change pull (lift x y).left (pull (sqToBase A s) (pull (lift (fst A A) (snd A A ≫ l)).left
    (cls P hD.isLB))) = _
  rw [← pull_comp, ← pull_comp, key, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]

private theorem lam_mul_left' (hD0 : IsDual A B P) (e' : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (x x' y : T ⟶ (Over.pullback s).obj A) :
    lam (cls L hL) (x * x') y = lam (cls L hL) x y + lam (cls L hL) x' y := by
  rw [lam_eq_evc_toBase_of_isDual (hD := hD0) (e' := e'), lam_eq_evc_toBase_of_isDual (hD := hD0) (e' := e'),
    lam_eq_evc_toBase_of_isDual (hD := hD0) (e' := e'), toBase_mul, evc_mul_left' hD0]

private theorem lam_mul_right_zarhin_trick (hD0 : IsDual A B P) (hD1 : IsDual B A (swap P)) (e' : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (x y y' : T ⟶ (Over.pullback s).obj A) :
    lam (cls L hL) x (y * y') = lam (cls L hL) x y + lam (cls L hL) x y' := by
  rw [lam_eq_evc_toBase_of_isDual (hD := hD0) (e' := e'), lam_eq_evc_toBase_of_isDual (hD := hD0) (e' := e'),
    lam_eq_evc_toBase_of_isDual (hD := hD0) (e' := e'), toBase_mul]
  have hm : (toBase A s y * toBase A s y') ≫ l = (toBase A s y ≫ l) * (toBase A s y' ≫ l) :=
    map_mul (IsMonHom.monoidHom l _) _ _
  rw [hm, ← evc_swap hD0.isLB hD1.isLB, evc_mul_left' hD1, evc_swap hD0.isLB hD1.isLB,
    evc_swap hD0.isLB hD1.isLB]

private theorem lam_pow_left' (hD0 : IsDual A B P) (e' : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (x y : T ⟶ (Over.pullback s).obj A) (n : ℕ) :
    lam (cls L hL) (x ^ n) y = n • lam (cls L hL) x y := by
  induction n with
  | zero => simpa using lam_one_left (cls L hL) y
  | succ k ih => rw [pow_succ, lam_mul_left' (hD0 := hD0) (e' := e'), ih, succ_nsmul]

private theorem lam_pow_right' (hD0 : IsDual A B P) (hD1 : IsDual B A (swap P)) (e' : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (x y : T ⟶ (Over.pullback s).obj A) (n : ℕ) :
    lam (cls L hL) x (y ^ n) = n • lam (cls L hL) x y := by
  induction n with
  | zero => simpa using lam_one_right (cls L hL) x
  | succ k ih =>
    rw [pow_succ, lam_mul_right_zarhin_trick (hD0 := hD0) (hD1 := hD1) (e' := e'), ih, succ_nsmul]

include e hD hD' in

theorem lam_self_add_inv (q : T ⟶ (Over.pullback s).obj A) :
    lam (cls L hL) q q + lam (cls L hL) q q⁻¹ = 0 := by
  rw [← lam_mul_right_zarhin_trick (hL := hL) (hD0 := hD) (hD1 := hD') (e' := e), mul_inv_cancel, lam_one_right]

include e hD hD' in
theorem pull_add_inv (q : T ⟶ (Over.pullback s).obj A) :
    pull q.left (cls L hL) + pull q⁻¹.left (cls L hL) = lam (cls L hL) q q := by
  have h7 := lam_self_add_inv (hL := hL) (hD := hD) (hD' := hD') (e := e) (q := q)
  have hd : lam (cls L hL) q q⁻¹ = pull (q * q⁻¹).left (cls L hL) - pull q.left (cls L hL) -
      pull q⁻¹.left (cls L hL) + pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL) := rfl
  rw [mul_inv_cancel, pull_one_pt] at hd
  rw [hd] at h7
  rw [eq_comm, ← sub_eq_zero, ← h7]
  abel

include e hD hD' in
theorem pull_pow_add_inv (q : T ⟶ (Over.pullback s).obj A) (n : ℕ) :
    pull (q ^ n).left (cls L hL) + pull (q ^ n)⁻¹.left (cls L hL) = n ^ 2 • lam (cls L hL) q q := by
  rw [pull_add_inv (hL := hL) (hD := hD) (hD' := hD') (e := e) (q := q ^ n),
    lam_pow_left' (hL := hL) (hD0 := hD) (e' := e), lam_pow_right' (hL := hL) (hD0 := hD) (hD1 := hD') (e' := e),
    smul_smul, sq]

end LPart

end Helpers

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

private theorem pull_add_pull_inv_eq_sq_smul_of_comp_eq_pow {P : LB (A ⊗ B).left} (hD : IsDual A B P) (hD' : IsDual B A (swap P))
    (l : A ⟶ B) [IsMonHom l] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L)) {T : Over (Sp Ω)} (M : T ⟶ T) (f : T ⟶ (Over.pullback s).obj A) (n : ℕ)
    (hf : M ≫ f = f ^ n) :
    pull (M.left ≫ f.left) (cls L hL) + pull (M.left ≫ f⁻¹.left) (cls L hL) =
      n ^ 2 • (pull f.left (cls L hL) + pull f⁻¹.left (cls L hL)) := by
  have hfi : M ≫ f⁻¹ = (f ^ n)⁻¹ := by
    rw [Hom.inv_def, Hom.inv_def, ← Category.assoc, hf]
  rw [← Over.comp_left, ← Over.comp_left, hf, hfi,
    pull_pow_add_inv (hL := hL) (hD := hD) (hD' := hD') (e := e) (q := f) (n := n),
    pull_add_inv (hL := hL) (hD := hD) (hD' := hD') (e := e) (q := f)]

private theorem pull_pow_lift_cls_eq_sq_smul {P : LB (A ⊗ B).left} (hD : IsDual A B P) (hD' : IsDual B A (swap P))
    {Y : Over S} (y : Y ⟶ G4 (A ⊗ B)) (i j : Fin 4) (n : ℕ) :
    pull (((y ^ n) ≫ lift (prj (A ⊗ B) i ≫ fst A B) (prj (A ⊗ B) j ≫ snd A B)).left) (cls P hD.isLB) =
      n ^ 2 • pull ((y ≫ lift (prj (A ⊗ B) i ≫ fst A B) (prj (A ⊗ B) j ≫ snd A B)).left) (cls P hD.isLB) := by
  rw [comp_lift, comp_lift, pow_comp_hom, pow_comp_hom]
  change evc hD.isLB _ _ = n ^ 2 • evc hD.isLB _ _
  rw [evc_pow_left hD, evc_pow_right hD hD', smul_smul, sq]

theorem two_cls_pow (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (n : ℕ) (h' : ((zb mu α s P L).pull ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B)))) ^ n).left).IsLB) :
    2 • cls _ h' = (2 * n ^ 2) • cls _ (isLB_zb mu α s hD.isLB hL) := by
  have hP := hD.isLB
  have hLA : (L.LinComb (phiL mu s) fun _ => (1 : ℤ)).IsLB := LB.isLB_linComb hL _ _
  have hPA : (P.LinComb (phiP s) fun ij => α ij.1 ij.2).IsLB := LB.isLB_linComb hP _ _
  have hz := isLB_zb mu α s hP hL
  have hpull : cls _ h' = pull ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B)))) ^ n).left (cls _ hz) := rfl
  have hsplit : cls _ hz = cls _ hLA + cls _ hPA := cls_tens hLA hPA hz
  rw [hpull, hsplit, map_add, cls_linComb hL, cls_linComb hP, map_sum, map_sum]
  simp only [map_zsmul, ← pull_comp, one_smul]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  obtain ⟨N, hN⟩ : ∃ N : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj (G4 (A ⊗ B)), N = (𝟙 _) ^ n := ⟨_, rfl⟩
  rw [← hN]
  have hA : ∀ y : Fin 4, N ≫ pA (A := A) (B := B) s y = (pA (A := A) (B := B) s y) ^ n := by
    intro y
    rw [hN]
    show (𝟙 _ ^ n) ≫ (Over.pullback s).map (prj (A ⊗ B) y ≫ fst A B) =
      ((Over.pullback s).map (prj (A ⊗ B) y ≫ fst A B)) ^ n
    rw [pow_comp_hom, Category.id_comp]
  have hM : ∀ y : Fin 4, N ≫ pM mu s y = (pM mu s y) ^ n := by
    intro y
    rw [hN]
    show (𝟙 _ ^ n) ≫ (Over.pullback s).map (prj (A ⊗ B) y ≫ snd A B ≫ mu) =
      ((Over.pullback s).map (prj (A ⊗ B) y ≫ snd A B ≫ mu)) ^ n
    rw [pow_comp_hom, Category.id_comp]
  have hLsum : (∑ x : Fin 4, ∑ y : Fin 4, pull (N.left ≫ phiL mu s (x, y)) (cls L hL)) =
      n ^ 2 • ∑ x : Fin 4, ∑ y : Fin 4, pull (phiL mu s (x, y)) (cls L hL) := by
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fin.sum_univ_four, Fin.sum_univ_four]
    have h1 := pull_add_pull_inv_eq_sq_smul_of_comp_eq_pow hD hD' l s L hL e N (pA (A := A) (B := B) s y) n (hA y)
    have h2 := pull_add_pull_inv_eq_sq_smul_of_comp_eq_pow hD hD' l s L hL e N (pM mu s y) n (hM y)
    change pull (N.left ≫ (pA (A := A) (B := B) s y).left) (cls L hL) +
        pull (N.left ≫ (pA (A := A) (B := B) s y)⁻¹.left) (cls L hL) +
        pull (N.left ≫ (pM mu s y).left) (cls L hL) + pull (N.left ≫ (pM mu s y)⁻¹.left) (cls L hL) =
      n ^ 2 • (pull (pA (A := A) (B := B) s y).left (cls L hL) +
        pull (pA (A := A) (B := B) s y)⁻¹.left (cls L hL) +
        pull (pM mu s y).left (cls L hL) + pull (pM mu s y)⁻¹.left (cls L hL))
    rw [add_assoc, h1, h2, ← smul_add, ← add_assoc]
  have hPterm : ∀ x y : Fin 4, pull (N.left ≫ phiP s (x, y)) (cls P hP) =
      n ^ 2 • pull (phiP s (x, y)) (cls P hP) := by
    intro x y
    have h0 := toBase_comp s (G4 (A ⊗ B)) N (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))
    rw [Category.comp_id, hN, toBase_pow] at h0
    have h3 : N.left ≫ phiP s (x, y) = (((toBase (G4 (A ⊗ B)) s (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))))) ^ n) ≫
        lift (prj (A ⊗ B) x ≫ fst A B) (prj (A ⊗ B) y ≫ snd A B)).left := by
      rw [hN, h0, Category.assoc, Over.comp_left]
      rfl
    rw [h3, pull_pow_lift_cls_eq_sq_smul hD hD']
    rfl
  have hPsum : (∑ x : Fin 4, ∑ y : Fin 4, α (x, y).1 (x, y).2 • pull (N.left ≫ phiP s (x, y)) (cls P hP)) =
      n ^ 2 • ∑ x : Fin 4, ∑ y : Fin 4, α (x, y).1 (x, y).2 • pull (phiP s (x, y)) (cls P hP) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hPterm x y, smul_comm]
  rw [hLsum, hPsum, ← smul_add, smul_smul]

end PositivityTheory.PrwZar.Z2
