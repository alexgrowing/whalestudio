import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsLinearSimilitudeMemKernelPolarisatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeWeilLift

open GlobalTheory.CechPic

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB (A ⊗ A).left} (hL : L.IsLB)

def qc {T : Over S} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls L hL)

theorem pull_eq_qc {T : Over S} (f : T ⟶ A ⊗ A) :
    pull f.left (cls L hL) = qc hL (f ≫ fst A A) (f ≫ snd A A) := by
  unfold qc; rw [lift_comp_fst_snd]

omit [IsCommMonObj A] in
theorem translPt_fst {T : Over S} (x : T ⟶ A ⊗ A) :
    Out.translPt (A ⊗ A) x ≫ fst A A = (fst T (A ⊗ A) ≫ x ≫ fst A A) * (snd T (A ⊗ A) ≫ fst A A) := by
  have e : Out.translPt (A ⊗ A) x = (fst T (A ⊗ A) ≫ x) * snd T (A ⊗ A) := rfl
  rw [e, MonObj.mul_comp, Category.assoc]

omit [IsCommMonObj A] in
theorem translPt_snd {T : Over S} (x : T ⟶ A ⊗ A) :
    Out.translPt (A ⊗ A) x ≫ snd A A = (fst T (A ⊗ A) ≫ x ≫ snd A A) * (snd T (A ⊗ A) ≫ snd A A) := by
  have e : Out.translPt (A ⊗ A) x = (fst T (A ⊗ A) ≫ x) * snd T (A ⊗ A) := rfl
  rw [e, MonObj.mul_comp, Category.assoc]

variable {hL}

include hL in

theorem exists_theta_left
    (hB : ∀ (T : Over S) (x x' y : T ⟶ A), qc hL (x * x') y = qc hL x y + qc hL x' y)
    {T : Over S} (t : T ⟶ 𝟙_ (Over S)) (h : 𝟙_ (Over S) ⟶ A)
    (ht : ∃ u : (L.pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, u.IsGen) :
    ∃ θ : Out.ThetaGrp (A ⊗ A) L 1 T, θ.pt = t ≫ lift h 1 := by
  have z : pull (lift (toUnit A ≫ h) (𝟙 A)).left (cls L hL) = 0 := by
    rw [← cls_pull hL _ (pull_isLB hL _)]; exact (cls_eq_zero_iff _).2 ht
  set b := snd T (A ⊗ A) ≫ snd A A
  have e1 : fst T (A ⊗ A) ≫ (t ≫ lift h 1) ≫ fst A A = b ≫ toUnit A ≫ h := by
    rw [Category.assoc, lift_fst, ← Category.assoc, ← Category.assoc,
      toUnit_unique (fst T (A ⊗ A) ≫ t) (b ≫ toUnit A)]
  have e2 : fst T (A ⊗ A) ≫ (t ≫ lift h 1) ≫ snd A A = 1 := by
    rw [Category.assoc, lift_snd, MonObj.comp_one, MonObj.comp_one]
  have e3 : qc hL (b ≫ toUnit A ≫ h) b = 0 := by
    unfold qc
    rw [show lift (b ≫ toUnit A ≫ h) b = b ≫ lift (toUnit A ≫ h) (𝟙 A) by
      rw [comp_lift, Category.comp_id], Over.comp_left, pull_comp, z, map_zero]
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB (A ⊗ A) L 1 (t ≫ lift h 1)), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T (A ⊗ A)).left _ + (-1 : ℤ) • pull (Out.translPt (A ⊗ A) (t ≫ lift h 1)).left _ = 0
    rw [pull_eq_qc, pull_eq_qc, translPt_fst, translPt_snd, e1, e2, _root_.one_mul, hB, e3]
    simp
  exact ⟨⟨_, u, hu⟩, rfl⟩

include hL in

theorem exists_theta_right
    (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), qc hL x (y * y') = qc hL x y + qc hL x y')
    {T : Over S} (t : T ⟶ 𝟙_ (Over S)) (h : 𝟙_ (Over S) ⟶ A)
    (ht : ∃ u : (L.pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, u.IsGen) :
    ∃ θ : Out.ThetaGrp (A ⊗ A) L 1 T, θ.pt = t ≫ lift 1 h := by
  have z : pull (lift (𝟙 A) (toUnit A ≫ h)).left (cls L hL) = 0 := by
    rw [← cls_pull hL _ (pull_isLB hL _)]; exact (cls_eq_zero_iff _).2 ht
  set a := snd T (A ⊗ A) ≫ fst A A
  have e1 : fst T (A ⊗ A) ≫ (t ≫ lift 1 h) ≫ snd A A = a ≫ toUnit A ≫ h := by
    rw [Category.assoc, lift_snd, ← Category.assoc, ← Category.assoc,
      toUnit_unique (fst T (A ⊗ A) ≫ t) (a ≫ toUnit A)]
  have e2 : fst T (A ⊗ A) ≫ (t ≫ lift 1 h) ≫ fst A A = 1 := by
    rw [Category.assoc, lift_fst, MonObj.comp_one, MonObj.comp_one]
  have e3 : qc hL a (a ≫ toUnit A ≫ h) = 0 := by
    unfold qc
    rw [show lift a (a ≫ toUnit A ≫ h) = a ≫ lift (𝟙 A) (toUnit A ≫ h) by
      rw [comp_lift, Category.comp_id], Over.comp_left, pull_comp, z, map_zero]
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB (A ⊗ A) L 1 (t ≫ lift 1 h)), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T (A ⊗ A)).left _ + (-1 : ℤ) • pull (Out.translPt (A ⊗ A) (t ≫ lift 1 h)).left _ = 0
    rw [pull_eq_qc, pull_eq_qc, translPt_fst, translPt_snd, e1, e2, _root_.one_mul, hB', e3]
    simp
  exact ⟨⟨_, u, hu⟩, rfl⟩

end General

end GlobalTheory.HeckeWeilLift

namespace GlobalTheory.HeckeWeilLift

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem exists_weilIs_hecke : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∃ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u := by
  intro p _ D R _ b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₁ hh₁ h₂ hh₂
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hcls : cls _ hQ = (k ^ 2 / c) • cls o.P o.isLB := by
    refine (cls_linComb o.isLB (K := Fin (k ^ 2 / c)) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have hQB : ∀ (T : Over S) (x x' y : T ⟶ o.A), qc hQ (x * x') y = qc hQ x y + qc hQ x' y :=
    fun T x x' y => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB T x x' y)).trans (smul_add _ _ _)
  have hQB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), qc hQ x (y * y') = qc hQ x y + qc hQ x y' :=
    fun T x y y' => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB' T x y y')).trans (smul_add _ _ _)
  obtain ⟨t₁, -⟩ := GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₁ hh₁
  obtain ⟨-, t₂⟩ := GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₂ hh₂
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  exact CommutatorPairing.exists_weilIs hG hA2 hQ
    (fun _ => ⟨⊤, trivial, exists_theta_left hQB (Out.overResι ⊤) h₁ t₁⟩)
    (fun _ => ⟨⊤, trivial, exists_theta_right hQB' (Out.overResι ⊤) h₂ t₂⟩)

end GlobalTheory.HeckeWeilLift
