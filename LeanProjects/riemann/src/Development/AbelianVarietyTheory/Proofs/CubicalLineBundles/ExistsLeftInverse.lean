import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplitStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TensorAmple

open GlobalTheory.CechPic GlobalTheory.HermTensorLB

theorem exists_leftInverse {O : Type} [CommRing O] (bar : O →+* O) {M : Type} [AddCommGroup M] [Module O M]
    (h : M → M → O) (hadd : ∀ m m' n, h (m + m') n = h m n + h m' n)
    (hsmul : ∀ (c : O) m n, h (c • m) n = c * h m n) (hsym : ∀ m n, h n m = bar (h m n))
    (hperf : ∀ l : M →ₗ[O] O, ∃! n, ∀ m, l m = h m n) {n k : ℕ} (l : Fin k → (M →ₗ[O] O))
    (hl : ∀ m m', (n : O) * h m m' = ∑ i, l i m * bar (l i m')) :
    ∃ r : (Fin k → O) →ₗ[O] M, ∀ m, r (LinearMap.pi l m) = n • m := by
  choose e he using fun i => (hperf (l i)).exists
  let f : M → (M →ₗ[O] O) := fun y =>
    { toFun := fun x => h x y, map_add' := fun a b => hadd a b y, map_smul' := fun c a => hsmul c a y }
  refine ⟨Fintype.linearCombination O e, fun m => ?_⟩
  refine (hperf (f (n • m))).unique (fun x => ?_) (fun x => rfl)
  change h x (n • m) = h x _
  rw [hsym (n • m), hsym (Fintype.linearCombination O e _), Fintype.linearCombination_apply]
  change bar (f x (n • m)) = bar (f x _)
  rw [map_sum, map_nsmul, map_sum, map_nsmul]
  change n • bar (h m x) = ∑ i, bar (h (l i m • e i) x)
  simp only [hsmul, map_mul, ← hsym, ← he]
  rw [nsmul_eq_mul, hl]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem lam_self (laws : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}
    (x : T ⟶ P.A) : lam (cls P.L P.isLB) x x = 2 • pull x.left (cls P.L P.isLB) := by
  have h₂ := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 (laws.mulPull S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h₂
  have h₀ : pull (eSec P.A) (cls P.L P.isLB) = 0 := (cls_eq_zero_iff (pull_isLB P.isLB _)).2 P.rigid
  have h₁ : pull (1 : T ⟶ P.A).left (cls P.L P.isLB) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    exact (congrArg _ h₀).trans (map_zero _)
  have h₃ := congrArg (pull x.left) h₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_zsmul, ← pull_comp, Category.comp_id,
    ← Over.comp_left, Out.mulA, MonObj.comp_pow, map_zero, pow_two, MonObj.comp_mul] at h₃
  rw [lam, h₁, add_zero, ← sub_eq_zero, ← neg_eq_zero, ← h₃]
  push_cast
  abel

theorem relAmple_tensor : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) [IsCommMonObj P.A] (O : Type) [CommRing O] (bar : O →+* O) (M : Type) [AddCommGroup M] [Module O M] (h : M → M → O) [Module.Finite O M] [Module.Projective O M] (A : Over S) [GrpObj A] [IsCommMonObj A] (a : OAct O P.A) (b : OAct O A) (t : IsTensor A b P.A a M) (w : O) (N N' : LB A.left), N.IsLB → N'.IsLB → (∃ tθ : LB.Gen (Theta A N), tθ.IsGen) → (∀ m n, LBIso (cubeLB A ![fst P.A P.A ≫ t.tmul m, snd P.A P.A ≫ t.tmul n] N) (cubeLB P.A ![fst P.A P.A ≫ a.act (h m n), snd P.A P.A] P.L)) → (∀ c, LBIso (cubeLB P.A ![fst P.A P.A ≫ a.act c, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a.act (bar c)] P.L)) → ((∀ c, bar (bar c) = c) ∧ (∀ m m' n, h (m + m') n = h m n + h m' n) ∧ (∀ (c : O) m n, h (c • m) n = c * h m n) ∧ ∀ m n, h n m = bar (h m n)) → (∀ l : M →ₗ[O] O, ∃! n, ∀ m, l m = h m n) → (∃ (n k : ℕ) (l : Fin k → (M →ₗ[O] O)), 0 < n ∧ ∀ m m', (n : O) * h m m' = ∑ i, l i m * bar (l i m')) → w + bar w = 1 → LBIso N' (cubeLB A ![𝟙 A, b.act w] N) → Out.RelAmple A N' := by
  intro laws S _ P _ O _ bar M _ _ h _ _ A _ _ a b t w N N' hN hN' hT H hadj ⟨hbar, hadd, hsmul, hsym⟩ hperf
    ⟨n, k, l, hn, hl⟩ hw hiso
  have hL := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (laws.cube S P ⟨P.L, rig, hL, hrig⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  let q := Out.powIsPowGrp P.A k
  let ψ := t.mapLeft (IsTensor.pow q a) (LinearMap.pi l)
  let p : Fin k → (A ⟶ P.A) := fun i => ψ ≫ q.pr i
  have pl : ∀ i, IsLinearHom b a (p i) := fun i =>
    (t.isLinearHom_mapLeft _ _).comp (isLinearHom_pr q a i)
  have pm : ∀ i, IsMonHom (p i) := fun i => (pl i).1
  have hp : ∀ m i, t.tmul m ≫ p i = a.act (l i m) := fun m i => by simp [p, ψ]
  have am := a.hom
  have adj : ∀ {T : Over S} (x y : T ⟶ P.A) (c : O),
      lam (cls P.L hL) (x ≫ a.act c) y = lam (cls P.L hL) x (y ≫ a.act (bar c)) := by
    intro T x y c
    have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj c)
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  have base : ∀ {T : Over S} (x y : T ⟶ P.A) (m m' : M),
      lam (cls N hN) (x ≫ t.tmul m) (y ≫ t.tmul m') = lam (cls P.L hL) (x ≫ a.act (h m m')) y := by
    intro T x y m m'
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (H m m')
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  have key : ∀ {T : Over S} (x y : T ⟶ A),
      n • lam (cls N hN) x y = ∑ i, lam (cls P.L hL) (x ≫ p i) (y ≫ p i) := by
    intro T x y
    induction x using t.induction_on with
    | one => simp only [MonObj.one_comp, lam_one_left, smul_zero, Finset.sum_const_zero]
    | mul x x' hx hx' =>
      simp only [MonObj.mul_comp, lam_mul_left hN hT, lam_mul_left hL hΘ, smul_add, hx, hx', Finset.sum_add_distrib]
    | tmul m x =>
      induction y using t.induction_on with
      | one => simp only [MonObj.one_comp, lam_one_right, smul_zero, Finset.sum_const_zero]
      | mul y y' hy hy' =>
        simp only [MonObj.mul_comp, lam_mul_right hN hT, lam_mul_right hL hΘ, smul_add, hy, hy',
          Finset.sum_add_distrib]
      | tmul m' y =>
        let φ : O →+ Pic T.left := AddMonoidHom.mk' (fun c => lam (cls P.L hL) (x ≫ a.act c) y) fun c d => by
          simp only [a.add, MonObj.comp_mul, lam_mul_left hL hΘ]
        have hφ : ∀ c d, lam (cls P.L hL) (x ≫ a.act c) (y ≫ a.act d) = φ (c * bar d) := by
          intro c d
          have := adj (x ≫ a.act c) y (bar d)
          rw [hbar, Category.assoc, ← a.mul] at this
          exact this.symm
        simp only [Category.assoc, hp, hφ, ← map_sum, ← hl, base, ← nsmul_eq_mul, map_nsmul]
        rfl
  have dbl : ∀ x : A ⟶ P.A, 2 • lam (cls P.L hL) x (x ≫ a.act w) = 2 • pull x.left (cls P.L hL) := by
    intro x
    rw [two_nsmul, ← lam_self laws P x]
    nth_rw 2 [lam_comm]
    rw [adj, ← lam_mul_right hL hΘ, ← MonObj.comp_mul, ← a.add, hw, a.one, Category.comp_id]
  have hB : (Out.boxLB P.L q.pr).IsLB := LB.isLB_linComb hL _ _
  have hψB := pull_isLB hB ψ.left
  have final : LBIso (lbPow ((Out.boxLB P.L q.pr).pull ψ.left) 2) (lbPow N' (2 * n)) := by
    refine (cls_eq_iff (LB.isLB_linComb hψB _ _) (LB.isLB_linComb hN' _ _)).1 ?_
    rw [cls_lbPow hψB, cls_lbPow hN', cls_pull hB, cls_linComb hL,
      (cls_eq_iff hN' (LB.isLB_linComb hN _ _)).2 hiso]
    erw [cls_cube_two hN]
    rw [mul_smul, key, map_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Category.id_comp, (pl i).comm, dbl, one_smul, ← pull_comp]
    rfl
  obtain ⟨r, hr⟩ := exists_leftInverse bar h hadd hsmul hsym hperf l hl
  have hfin : IsFinite ψ.left := GlobalTheory.T.tensor_map_finite_of_split laws S P O M A a b t n k _ r hn hr
  have hA : IsAbelianScheme A := t.isAbelianScheme P.isAb
  have hG : IsAbelianScheme (Out.powObj P.A k) := (IsTensor.pow q a).isAbelianScheme P.isAb
  have hid : IsFinite (𝟙 A : A ⟶ A).left := by rw [Over.id_left]; infer_instance
  have a₁ := (relAmple_finite_pow_iso S A _ ψ _ 1 one_pos hA hG hB hfin).1
    (relAmple_boxLB S _ P.A k q P.L hL P.ample)
  have a₂ := (relAmple_finite_pow_iso S A A (𝟙 A) _ 2 two_pos hA hA hψB hid).2.1.2 a₁
  have a₃ := (relAmple_finite_pow_iso S A A (𝟙 A) _ 1 one_pos hA hA (LB.isLB_linComb hψB _ _) hid).2.2.2 _
    (LB.isLB_linComb hN' _ _) final a₂
  exact (relAmple_finite_pow_iso S A A (𝟙 A) N' (2 * n) (by omega) hA hA hN' hid).2.1.1 a₃

end GlobalTheory.TensorAmple
