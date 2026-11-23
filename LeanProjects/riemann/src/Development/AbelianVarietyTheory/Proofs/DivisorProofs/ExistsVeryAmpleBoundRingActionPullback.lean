import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroChartOfEffectiveClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassPullbackVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulVeryAmpleSubIsEffectivePicClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeTheoremPicardGroupStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

theorem pull_one (M : GlobalTheory.UU.CP B) : pull (1 : B ⟶ B).left (cls M.L.L M.L.isLB) = 0 := by
  have e : (1 : B ⟶ B).left = (toUnit B).left ≫ eSec B := by
    rw [Hom.one_def]; rfl
  rw [e, pull_comp, ← cls_pull M.L.isLB _ (pull_isLB M.L.isLB _),
    (cls_eq_zero_iff (pull_isLB M.L.isLB _)).2 ⟨M.L.rig, M.L.rigGen⟩, map_zero]

theorem pull_inv (M : GlobalTheory.UU.CP B) (f : B ⟶ B) :
    pull (f⁻¹).left (cls M.L.L M.L.isLB) = pull f.left (cls M.L.L M.L.isLB) := by
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb M.L.isLB _ _)).2 ⟨M.sym, M.sym_gen⟩
  rw [cls_linComb M.L.isLB, Fin.sum_univ_two] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pull_id, one_zsmul,
    neg_one_zsmul] at h0
  have hι : pull (ι[B]).left (cls M.L.L M.L.isLB) = cls M.L.L M.L.isLB := by
    rw [← sub_eq_zero, sub_eq_add_neg]; exact h0
  rw [Hom.inv_def, Over.comp_left, pull_comp, hι]

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_pow (k : Type) [Field k] (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (f : B ⟶ B) (n : ℕ) :
    pull (f ^ n).left (cls M.L.L M.L.isLB) = (n ^ 2) • pull f.left (cls M.L.L M.L.isLB) := by
  have h := GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing k B M n
  have e : pull (𝟙 B ^ n).left (cls M.L.L M.L.isLB) = ((n : ℤ) ^ 2) • cls M.L.L M.L.isLB := by
    rw [← cls_pull M.L.isLB _ (pull_isLB M.L.isLB _),
      ← (cls_eq_iff (isLB_pw M.L.isLB _) (pull_isLB M.L.isLB _)).2 h, cls_pw]
  have e2 : f ^ n = f ≫ 𝟙 B ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  rw [e2, Over.comp_left, pull_comp, e, map_zsmul]
  norm_cast

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem act_zsmul {O : Type} [CommRing O] {S : Scheme.{0}} {B : Over S} [GrpObj B] (act : OAct O B) (a : O) (n : ℤ) :
    act.act (n • a) = act.act a ^ n := by
  have h0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this |>.symm ▸ rfl
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul, zpow_zero, h0]
  | succ k ih => rw [add_zsmul, one_zsmul, act.add, ih, zpow_add_one]
  | pred k ih =>
    rw [sub_zsmul, one_zsmul, zpow_sub_one, ← ih]
    refine eq_mul_inv_of_mul_eq ?_
    rw [← act.add]; congr 1; abel

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_zpow (k : Type) [Field k] (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (f : B ⟶ B) (n : ℤ) :
    pull (f ^ n).left (cls M.L.L M.L.isLB) = (n.natAbs ^ 2) • pull f.left (cls M.L.L M.L.isLB) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast, pull_pow, Int.natAbs_natCast]
  | negSucc m => rw [zpow_negSucc, pull_inv, pull_pow, Int.natAbs_negSucc]

theorem eff_nsmul {X : Scheme.{0}} [IsIntegral X] (hE0 : Eff (0 : Pic X)) {x : Pic X} (hx : Eff x) :
    ∀ n : ℕ, Eff (n • x)
  | 0 => by rw [zero_smul]; exact hE0
  | n + 1 => by rw [succ_nsmul]; exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ (eff_nsmul hE0 hx n) hx

theorem eff_sum {O : Type} [CommRing O] {S : Scheme.{0}} {B : Over S} [GrpObj B] (act : OAct O B)
    {X : Scheme.{0}} [IsIntegral X] (F : (B ⟶ B) → Pic X) (c0 : Pic X) (hE0 : Eff (0 : Pic X))
    (hc0 : Eff c0) (h1 : F 1 = 0) (hpar : ∀ f g, Eff (2 • F f + 2 • F g - F (f * g))) :
    ∀ (l : ℕ) (b : Fin l → O) (t : Fin l → ℕ), (∀ i, Eff (t i • c0 - F (act.act (b i)))) →
      Eff ((2 ^ l * ∑ i, t i) • c0 - F (act.act (∑ i, b i))) := by
  have h0 : act.act 0 = 1 := by rw [← zero_smul ℤ (0 : O), act_zsmul, zpow_zero]
  intro l
  induction l with
  | zero =>
    intro b t _
    rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty, h0, h1, mul_zero, zero_smul, sub_zero]
    exact hE0
  | succ l ih =>
    intro b t ht
    rw [Fin.sum_univ_castSucc (f := b), Fin.sum_univ_castSucc (f := t), act.add]
    have hP := ih (fun i => b i.castSucc) (fun i => t i.castSucc) fun i => ht _
    set P := act.act (∑ i : Fin l, b i.castSucc)
    set g := act.act (b (Fin.last l))
    set T := ∑ i : Fin l, t i.castSucc
    set u := t (Fin.last l)
    have h2 : 2 ≤ 2 ^ (l + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : (2 ^ (l + 1) * (T + u)) • c0 - F (P * g) =
        (2 • F P + 2 • F g - F (P * g)) + 2 • ((2 ^ l * T) • c0 - F P) + 2 • (u • c0 - F g) +
          ((2 ^ (l + 1) - 2) * u) • c0 := by
      simp only [← natCast_zsmul]
      push_cast [Nat.cast_sub h2]
      module
    rw [e]
    exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ (GlobalTheory.T.isEffectivePicClass_add_integral _ _ (GlobalTheory.T.isEffectivePicClass_add_integral _ _ (hpar P g) (eff_nsmul hE0 hP 2)) (eff_nsmul hE0 (ht _) 2))
      (eff_nsmul hE0 hc0 _)

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem exists_effective_bound : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (c : ℕ), H.IsLB ∧ GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ 1 ≤ c ∧ ∀ (n : Fin d → ℤ) (K : ℕ), 1 ≤ K → (∀ i, (n i).natAbs ≤ K) → ∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left))) (j : (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left)).ι), σ.f j ≠ 0 := by
  intro E _ _ k _ _ _ A _ act g hB hg d a
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hproj := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k A hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k A hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec A)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps GlobalTheory.globalFns_holds _ A hB).1 ⟨H, r, hH, hr⟩
    (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety GlobalTheory.globalFns_holds k A hB hproj H hH) hsym
  have hL : M.L.L = H := by rw [hM]
  subst hL
  obtain ⟨c0, hc0⟩ : ∃ c0, cls M.L.L M.L.isLB = c0 := ⟨_, rfl⟩
  have hEF : ∀ φ : A ⟶ A, Eff (pull φ.left c0) := fun φ =>
    hc0 ▸ GlobalTheory.T.isEffectivePicClass_pullback_veryAmple k A.hom M.L.L m s M.L.isLB hs φ.left inferInstance
  have h1 : pull (1 : A ⟶ A).left c0 = 0 := hc0 ▸ pull_one A M
  have hE0 : Eff (0 : Pic A.left) := h1 ▸ hEF 1
  have hEc : Eff c0 := by
    have := hEF (𝟙 A)
    rwa [Over.id_left, pull_id] at this
  have hpar : ∀ f g : A ⟶ A, Eff (2 • pull f.left c0 + 2 • pull g.left c0 - pull (f * g).left c0) := by
    intro f g
    have e := GlobalTheory.T.cube_theorem_picardGroup A M f g g⁻¹
    rw [mul_inv_cancel_right, mul_inv_cancel, pull_one, pull_inv A M g, hc0] at e
    have e' : 2 • pull f.left c0 + 2 • pull g.left c0 - pull (f * g).left c0 = pull (f * g⁻¹).left c0 := by
      rw [← sub_eq_zero, ← sub_eq_zero.2 e]
      abel
    rw [e']
    exact hEF _
  have hc : ∀ i, ∃ ci : ℕ, Eff (ci • c0 - pull (act.act (a i)).left c0) := fun i => by
    obtain ⟨ci, h⟩ := GlobalTheory.T.exists_nsmul_veryAmple_sub_isEffectivePicClass k A.left A.hom M.L.L m s _ M.L.isLB (pull_isLB M.L.isLB (act.act (a i)).left) hs
    rw [cls_pull M.L.isLB, hc0] at h
    exact ⟨ci, h⟩
  choose ci hci using hc
  refine ⟨M.L.L, m, s, 2 ^ d * ∑ i, ci i + 1, M.L.isLB, hs, by omega, fun n K _ hn => ?_⟩
  have hterm : ∀ i, Eff ((K ^ 2 * ci i) • c0 - pull (act.act (n i • a i)).left c0) := by
    intro i
    have hle : (n i).natAbs ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left (hn i) 2
    have e : (K ^ 2 * ci i) • c0 - pull (act.act (n i • a i)).left c0 =
        (n i).natAbs ^ 2 • (ci i • c0 - pull (act.act (a i)).left c0) +
          ((K ^ 2 - (n i).natAbs ^ 2) * ci i) • c0 := by
      rw [act_zsmul, ← hc0, pull_zpow, hc0]
      simp only [← natCast_zsmul]
      push_cast [Nat.cast_sub hle]
      module
    rw [e]
    exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ (eff_nsmul hE0 (hci i) _) (eff_nsmul hE0 hEc _)
  have hsum := eff_sum act (fun φ => pull φ.left c0) c0 hE0 hEc h1 hpar d (fun i => n i • a i)
    (fun i => K ^ 2 * ci i) hterm
  refine GlobalTheory.T.exists_section_nonzero_chart_of_effective_class _ (LB.isLB_div (isLB_pw M.L.isLB _) (pull_isLB M.L.isLB _)) ?_
  rw [cls_div (isLB_pw M.L.isLB _) (pull_isLB M.L.isLB _), cls_pw M.L.isLB, cls_pull M.L.isLB, hc0]
  have e : (((2 ^ d * ∑ i, ci i + 1) * K ^ 2 : ℕ) : ℤ) • c0 - pull (act.act (∑ i, n i • a i)).left c0 =
      ((2 ^ d * ∑ i, K ^ 2 * ci i) • c0 - pull (act.act (∑ i, n i • a i)).left c0) + (K ^ 2) • c0 := by
    simp only [← Finset.mul_sum, ← natCast_zsmul]
    push_cast
    module
  rw [e]
  exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ hsum (eff_nsmul hE0 hEc _)

end GlobalTheory.OEndDegree
