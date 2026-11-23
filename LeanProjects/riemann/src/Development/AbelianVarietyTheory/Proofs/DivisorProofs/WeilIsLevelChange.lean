import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegRel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelChangePairing

open GlobalTheory.CechPic

section Lift

variable {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B]

theorem lift_mul_lift' (x x' : T ⟶ A) (y y' : T ⟶ B) : lift x y * lift x' y' = lift (x * x') (y * y') := by
  ext1 <;> simp only [MonObj.mul_comp, lift_fst, lift_snd]

theorem lift_pow_eq (x : T ⟶ A) (y : T ⟶ B) (m : ℕ) : lift x y ^ m = lift (x ^ m) (y ^ m) := by
  ext1 <;> simp only [MonObj.pow_comp, lift_fst, lift_snd]

theorem lift_one_one : (1 : T ⟶ A ⊗ B) = lift (1 : T ⟶ A) (1 : T ⟶ B) := by
  ext1 <;> simp only [MonObj.one_comp, lift_fst, lift_snd]

end Lift

theorem isMonHom_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (m : ℕ) :
    IsMonHom ((𝟙 A) ^ m : A ⟶ A) := by
  induction m with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem pc_mul_right {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {P : LB (G2 A).left} (hP : P.IsLB)
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (T : Over S) (x y y' : T ⟶ A) :
    DiagPairing.pc hP x (y * y') = DiagPairing.pc hP x y + DiagPairing.pc hP x y' := by
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have z₁ : ∀ z : T ⟶ A, DiagPairing.pc hP 1 z = 0 := fun z => by
    obtain ⟨t, ht⟩ := h₁
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e
    have q : lift (1 : T ⟶ A) z = z ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [q, Over.comp_left, pull_comp, e, map_zero]
  have z₂ : ∀ z : T ⟶ A, DiagPairing.pc hP z 1 = 0 := fun z => by
    obtain ⟨t, ht⟩ := h₂
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e
    have q : lift z (1 : T ⟶ A) = z ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [q, Over.comp_left, pull_comp, e, map_zero]
  have h := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hAA P hP T (lift 1 y) (lift 1 y') (lift x 1)
  have hl := LB.isLB_linComb hP (fun k : Fin 8 ↦ (![lift 1 y * lift 1 y' * lift x 1, lift 1 y * lift 1 y',
    lift 1 y * lift x 1, lift 1 y' * lift x 1, lift 1 y, lift 1 y', lift x 1, 1] k).left) ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (cls_eq_zero_iff hl).2 h
  rw [cls_linComb hP _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  simp only [lift_mul_lift', _root_.mul_one, _root_.one_mul, ← lift_one_one] at e
  have o : (1 : T ⟶ G2 A) = lift (1 : T ⟶ A) 1 := lift_one_one
  rw [o] at e
  have a1 := z₁ (y * y')
  have a2 := z₁ y
  have a3 := z₁ y'
  have a4 := z₂ x
  have a5 := z₁ 1
  unfold DiagPairing.pc at a1 a2 a3 a4 a5 ⊢
  rw [a1, a2, a3, a4, a5] at e
  rw [← sub_eq_zero, ← e]
  abel

theorem weilIs_pow_pos {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hG : Out.GlobalFnsSt)
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L k x y c) {j : ℕ} (hj : 0 < j) :
    Out.WeilIs A L k (x ^ j) y (c ^ j) := by
  induction j with
  | zero => exact absurd hj (lt_irrefl 0)
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · simpa using h
    · rw [pow_succ x j, pow_succ c j]
      exact DiagPairing.weilIs_mul_left hG hA hL (ih hj') h

theorem weilIs_levelChange : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N m : ℕ), 0 < N → 0 < m → ((N * m : ℕ) : κ) ≠ 0 → ∀ (a b : Over.mk y ⟶ A), a ^ (N * m) = 1 → b ^ (N * m) = 1 → ∀ (c : (Γ((Over.mk y).left, ⊤))ˣ), Out.WeilIs (G2 A) P ((N * m : ℕ) : ℤ) (lift a 1) (lift 1 b) c → Out.WeilIs (G2 A) P N (lift (a ^ m) 1) (lift 1 (b ^ m)) (c ^ m) := by
  intro S A _ _ hA P hP h₁ h₂ κ _ _ y N m hN hm hNm a b ha hb c hc
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hB' := pc_mul_right A hA hP h₁ h₂
  haveI := isMonHom_id_pow A m
  let ψ : G2 A ⟶ G2 A := lift (fst A A) (snd A A ≫ (𝟙 A) ^ m)
  have e : ∀ {T : Over S} (u v : T ⟶ A), lift u v ≫ ψ = lift u (v ^ m) := fun u v => by
    simp only [ψ, comp_lift, ← Category.assoc, MonObj.comp_pow, Category.comp_id, lift_fst, lift_snd]
  have hψ' : ψ = lift (fst A A) (snd A A ^ m) := by
    rw [← e (fst A A) (snd A A), lift_fst_snd, Category.id_comp]
  have hL : (lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have hiso : LBIso (lbPow P m) (P.pull ψ.left) := by
    refine (cls_eq_iff hL (pull_isLB hP _)).1 ?_
    rw [cls_lbPow hP, cls_pull hP, hψ']
    have e' := DiagPairing.pc_pow_right hP hB' (fst A A) (snd A A) m
    unfold DiagPairing.pc at e'
    rw [e', lift_fst_snd]
    exact congrArg (m • ·) (pull_id _).symm
  have hNκ : (N : κ) ≠ 0 := by
    rw [Nat.cast_mul] at hNm
    exact left_ne_zero_of_mul hNm
  have hx : (lift (a ^ m) 1 : Over.mk y ⟶ G2 A) ^ N = 1 := by
    rw [lift_pow_eq, ← pow_mul, mul_comm m N, ha, one_pow, lift_one_one]
  have hy : (lift 1 (b ^ m) : Over.mk y ⟶ G2 A) ^ N = 1 := by
    rw [lift_pow_eq, ← pow_mul, mul_comm m N, hb, one_pow, lift_one_one]
  obtain ⟨c₀, h₀⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 A) P hAA hP κ y N hN hNκ _ _ hx hy
  have h₀' : Out.WeilIs (G2 A) P (N : ℤ) (lift (a ^ m) 1 ≫ ψ) (lift 1 b ≫ ψ) c₀ := by
    rw [e, e, one_pow]; exact h₀
  have h₁' : Out.WeilIs (G2 A) P ((N : ℤ) * (m : ℕ)) (lift (a ^ m) 1) (lift 1 b) c₀ :=
    GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hAA hP hP ψ hiso h₀'
  have h₂' : Out.WeilIs (G2 A) P ((N * m : ℕ) : ℤ) (lift (a ^ m) 1) (lift 1 b) (c ^ m) := by
    have := weilIs_pow_pos hG hAA hP hc hm
    rwa [lift_pow_eq, one_pow] at this
  have hc₀ : c₀ = c ^ m :=
    GlobalTheory.CommutatorPairing.weilIs_unique hG hAA hP (by rw [Nat.cast_mul]; exact h₁') h₂'
  rw [← hc₀]
  exact h₀

end GlobalTheory.LevelChangePairing
