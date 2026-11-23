import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Elliptic

abbrev toInt : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv

theorem exists_int (c : (1 : FracId ℚ).elt) : ∃ n : ℤ, (n : ℚ) = c := by
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (𝓞 ℚ)⁰).1 c.2
  exact ⟨toInt a, by rw [Rat.ringOfIntegersEquiv_apply_coe]; exact ha⟩

def eltInt (c : (1 : FracId ℚ).elt) : ℤ := (exists_int c).choose

theorem eltInt_spec (c : (1 : FracId ℚ).elt) : (eltInt c : ℚ) = c := (exists_int c).choose_spec

theorem eltInt_add (c c' : (1 : FracId ℚ).elt) : eltInt (c + c') = eltInt c + eltInt c' := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_add, eltInt_spec, eltInt_spec, eltInt_spec, Submodule.coe_add]

theorem eltInt_smul (a : 𝓞 ℚ) (c : (1 : FracId ℚ).elt) : eltInt (a • c) = toInt a * eltInt c := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, eltInt_spec, eltInt_spec, Submodule.coe_smul, Algebra.smul_def,
    Rat.ringOfIntegersEquiv_apply_coe]

def oneElt : (1 : FracId ℚ).elt := ⟨1, (FractionalIdeal.mem_one_iff (𝓞 ℚ)⁰).2 ⟨1, map_one _⟩⟩

theorem eltInt_one : eltInt oneElt = 1 := by
  apply Int.cast_injective (α := ℚ)
  rw [eltInt_spec, Int.cast_one]
  rfl

section

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

def ratAct : OAct (𝓞 ℚ) A where
  act a := (Serre.intAct A).act (toInt a)
  hom a := (Serre.intAct A).hom _
  one := by rw [map_one]; exact (Serre.intAct A).one
  mul a b := by rw [map_mul]; exact (Serre.intAct A).mul _ _
  add a b := by rw [map_add]; exact (Serre.intAct A).add _ _

variable {A}

theorem comp_ratAct {T : Over S} (x : T ⟶ A) (a : 𝓞 ℚ) : x ≫ (ratAct A).act a = x ^ toInt a := by
  show x ≫ (Serre.intAct A).act (toInt a) = _
  unfold Serre.intAct
  rw [GrpObj.comp_zpow, Category.comp_id]

theorem lam_zpow_left {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen) {T : Over S}
    (x y : T ⟶ A) (n : ℤ) : lam (cls L hL) (x ^ n) y = n • lam (cls L hL) x y := by
  have key : ∀ m : ℕ, lam (cls L hL) (x ^ (m : ℤ)) y = (m : ℤ) • lam (cls L hL) x y := fun m ↦ by
    rw [zpow_natCast, lam_pow_left hL hΘ, natCast_zsmul]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact key m
  · have h := lam_mul_left hL hΘ (x ^ (-(m : ℤ))) (x ^ (m : ℤ)) y
    rw [← zpow_add, neg_add_cancel, zpow_zero, lam_one_left, key] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero, ← h]

theorem lam_zpow_right {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen) {T : Over S}
    (x y : T ⟶ A) (n : ℤ) : lam (cls L hL) x (y ^ n) = n • lam (cls L hL) x y := by
  rw [lam_comm, lam_zpow_left hL hΘ, lam_comm]

def mulLam (L : LB A.left) (n : ℤ) : LB (G2 A).left := cubeLB A ![fst A A, snd A A ^ n] L

theorem isLB_mulLam {L : LB A.left} (hL : L.IsLB) (n : ℤ) : (mulLam L n).IsLB := LB.isLB_linComb hL _ _

theorem cls_mulLam {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen) (n : ℤ) :
    cls _ (isLB_mulLam hL n) = n • lam (cls L hL) (fst A A) (snd A A) :=
  (cls_cube_two hL (fst A A) (snd A A ^ n) (isLB_mulLam hL n)).trans (lam_zpow_right hL hΘ _ _ n)

theorem cls_pull_mulLam {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen) (n : ℤ)
    {T : Over S} (x y : T ⟶ A) :
    cls _ (pull_isLB (isLB_mulLam hL n) (lift x y).left) = n • lam (cls L hL) x y := by
  rw [cls_pull (isLB_mulLam hL n), cls_mulLam hL hΘ, map_zsmul, pull_lam, lift_fst, lift_snd]

theorem cls_pull_lam {L : LB A.left} (hL : L.IsLB) {T : Over S} (x y : T ⟶ A)
    (h : ((abelian₂ A L).pull (lift x y).left).IsLB) : cls _ h = lam (cls L hL) x y := by
  rw [cls_pull (L := abelian₂ A L) (LB.isLB_linComb hL _ _) _ h]
  erw [cls_cube_two hL (fst A A) (snd A A)]
  rw [pull_lam, lift_fst, lift_snd]

end

variable {k : Type} [Field k] [IsAlgClosed k] (Q : Out.PolAV (Sp k)) (hg : Q.g = 1)

def obj : Obj ℚ 1 (Sp k) :=
  haveI := Q.isAb.comm
  haveI := Q.isAb.proper
  have hΘ := exists_gen_theta_of_isAbelianScheme k Q.A Q.isAb Q.L Q.isLB
  have hL := Q.isLB
  { A := Q.A
    ab := Q.isAb
    dim := by rw [Module.finrank_self, ← hg]; exact Q.smoothDim
    rm := ratAct Q.A
    P c := mulLam Q.L (eltInt c)
    isLB c := isLB_mulLam hL _
    rig₁ c := (cls_eq_zero_iff (pull_isLB (isLB_mulLam hL _) _)).1 (by
      rw [cls_pull_mulLam hL hΘ, lam_one_left, smul_zero])
    rig₂ c := (cls_eq_zero_iff (pull_isLB (isLB_mulLam hL _) _)).1 (by
      rw [cls_pull_mulLam hL hΘ, lam_one_right, smul_zero])
    symm c := (cls_eq_iff (isLB_mulLam hL _) (pull_isLB (isLB_mulLam hL _) _)).1 (by
      rw [cls_pull_mulLam hL hΘ, cls_mulLam hL hΘ, lam_comm])
    add c c' := (cls_eq_iff (isLB_mulLam hL _) (LB.isLB_div (isLB_mulLam hL _) (isLB_mulLam hL _))).1 (by
      rw [cls_div (isLB_mulLam hL _) (isLB_mulLam hL _), cls_mulLam hL hΘ, cls_mulLam hL hΘ, cls_mulLam hL hΘ,
        eltInt_add, add_smul, add_sub_cancel_left])
    smul a c := (cls_eq_iff (isLB_mulLam hL _) (pull_isLB (isLB_mulLam hL _) _)).1 (by
      rw [cls_pull_mulLam hL hΘ, cls_mulLam hL hΘ, comp_ratAct, lam_zpow_right hL hΘ, eltInt_smul, smul_smul,
        mul_comm])
    pos c hc := by
      have h0 : 0 < eltInt c := by
        have := hc (Rat.castHom ℝ)
        rw [← eltInt_spec] at this
        simpa using this
      have hD := pull_isLB (L := abelian₂ Q.A Q.L) (LB.isLB_linComb hL _ _) (lift (𝟙 Q.A) (𝟙 Q.A)).left
      refine (GlobalTheory.KeyAtFam.relAmple_iff_of_cls hD (pull_isLB (isLB_mulLam hL _) _) (d := (eltInt c).toNat) (by omega) ?_).2
        (EighthPowerFactor.relAmple_diag_lam Q.isAb hL hΘ Q.ample)
      rw [cls_pull_mulLam hL hΘ, cls_pull_lam hL, ← natCast_zsmul, Int.toNat_of_nonneg h0.le]
    ker c T x hx a ha := by
      have h₁ := (cls_eq_zero_iff (pull_isLB (isLB_mulLam hL _) _)).2 hx
      rw [cls_pull_mulLam hL hΘ, ← lam_zpow_right hL hΘ, lam_comm, ← GrpObj.comp_zpow] at h₁
      have h₂ : x ^ eltInt c = 1 := SiegelOfPolarised.eq_one_of_lam hL Q.ktriv _
        ((cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hL _ _) _)).1 ((cls_pull_lam hL _ _ _).trans h₁))
      obtain ⟨b, hb⟩ := ha oneElt
      have h₃ := congrArg eltInt hb
      rw [eltInt_smul, eltInt_smul, eltInt_one, _root_.mul_one] at h₃
      rw [comp_ratAct, h₃, mul_comm, zpow_mul, h₂, one_zpow] }

end GlobalTheory.RealMult.Elliptic

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]

def Obj.DetGen.ofBasis (X : Obj F 𝔠 (Sp R)) (b : Module.Basis (Fin (Module.finrank ℚ F)) R X.Lie) : X.DetGen :=
  ⟨b.det, eq_top_iff.2 fun f _ ↦ Submodule.mem_span_singleton.2 ⟨f b, (AlternatingMap.eq_smul_basis_det b f).symm⟩⟩

end GlobalTheory.RealMult
