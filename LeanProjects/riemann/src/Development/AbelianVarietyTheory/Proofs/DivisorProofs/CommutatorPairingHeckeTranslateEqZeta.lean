import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HeckeWeilValue

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lbIso_mulA_diag (hA : IsAbelianScheme A) {P : LB (G2 A).left} (hP : P.IsLB)
    (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) (k : ℕ) :
    LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (k ^ 2))
      ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull (Out.mulA A k).left) := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), DiagPairing.pc hP (x * x') y =
      DiagPairing.pc hP x y + DiagPairing.pc hP x' y := fun T x x' y => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), DiagPairing.pc hP x (y * y') =
      DiagPairing.pc hP x y + DiagPairing.pc hP x y' := fun T x y y' => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂ T y y' x).2
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  refine (cls_eq_iff (LB.isLB_linComb hD _ _) (pull_isLB hD _)).1 ?_
  rw [cls_lbPow hD, cls_pull hD, cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have e1 : pull (lift (Out.mulA A k) (Out.mulA A k)).left (cls P hP) =
      DiagPairing.pc hP (Out.mulA A k) (Out.mulA A k) := rfl
  have e2 : pull (lift (𝟙 A) (𝟙 A)).left (cls P hP) = DiagPairing.pc hP (𝟙 A) (𝟙 A) := rfl
  rw [e1, e2, Out.mulA, DiagPairing.pc_pow_left hP hB, DiagPairing.pc_pow_right hP hB', smul_smul, sq]

end GlobalTheory.HeckeWeilValue

open GlobalTheory.HeckeWeilValue in

theorem GlobalTheory.UPel.HT.Hecke.weil_value_translate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k M : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ (I : TateIsoO D κ (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))) (n : ℕ), 0 < n → n.Coprime p → ∀ (u v : D.La) (e : (Γ((Over.mk x).left, ⊤))ˣ), Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) ((n * (k ^ 2 / c) : ℕ) : ℤ) (I.ev (n * k) (g u)) (I.ev (n * k) (g v)) e → e = unitOn (I.ζ n ^ (2 * D.EF u v)) := by
  intro p _ D R _ b g c k M hc hk hEF _ hck S s o κ _ _ x β _ I n hn hnp u v e he
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hk0 : 0 < k := levelPos_of_coprime hk
  have hc0 : 0 < c := levelPos_of_coprime hc
  have hmc : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have hm0 : 0 < k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd (by positivity) hck) hc0
  have hmp : (k ^ 2 / c).Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro c hmc) (Nat.Coprime.pow_left 2 hk)
  set m := k ^ 2 / c with hm
  have hN : 0 < n * (m * k ^ 2) := by positivity
  have hNp : (n * (m * k ^ 2)).Coprime p :=
    Nat.Coprime.mul hnp (Nat.Coprime.mul hmp (Nat.Coprime.pow_left 2 hk))
  have eN : n * (m * k ^ 2) = n * k * (m * k) := by ring
  have hev : ∀ w : D.La, I.ev (n * k) (g w) = I.ev (n * (m * k ^ 2)) (m • g w) ≫ Out.mulA o.A k := fun w => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, ← TateIsoO.ev_nsmul, smul_smul, mul_comm k m,
      TateIsoO.ev_nsmul, eN, I.tower (n * k) (m * k) (by positivity) (by positivity) (by rw [← eN]; exact hNp)]
  haveI := isMonHom_mulA (A := o.A) k
  have hw := lbIso_mulA_diag o.ab o.isLB o.ample o.rig₁ o.rig₂ k
  rw [hev u, hev v] at he
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG o.ab hL hL (Out.mulA o.A k) hw he
  have h2 := I.isom (n * (m * k ^ 2)) hN hNp (m • g u) (m • g v)
  have eZ : ((n * m : ℕ) : ℤ) * ((k ^ 2 : ℕ) : ℤ) = ((n * (m * k ^ 2) : ℕ) : ℤ) := by push_cast; ring
  rw [eZ] at h1
  rw [GlobalTheory.CommutatorPairing.weilIs_unique hG o.ab hL h1 h2]
  congr 1
  have eF : D.EF (m • g u) (m • g v) = ((m * k ^ 2 : ℕ) : ℤ) * D.EF u v := by
    simp only [map_nsmul, LinearMap.smul_apply, hEF, nsmul_eq_mul]
    rw [← hmc]
    push_cast
    ring
  rw [eF, show (2 : ℤ) * (((m * k ^ 2 : ℕ) : ℤ) * D.EF u v) = ((m * k ^ 2 : ℕ) : ℤ) * (2 * D.EF u v) by ring,
    zpow_mul, zpow_natCast, I.ζ_pow n (m * k ^ 2) hn (by positivity) hNp]
