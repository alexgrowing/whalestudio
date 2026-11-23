import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevF
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataForm

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

theorem subst_prodF (G : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf)
    (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) :
    P.subst G (prodF P F) = prodF P fun v s => rowAct Kf (G v s) (F v s) := by
  unfold prodF
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_prod, map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  have key : (P.subst G).comp ((P.vEmb v).comp (blockEmb Kf s)) =
      ((P.vEmb v).comp (blockEmb Kf s)).comp (rowAct Kf (G v s)) := by
    refine MvPolynomial.algHom_ext fun y => ?_
    simp [Places.subst, rowAct, Places.vEmb, blockEmb, map_sum, aeval_X]
  exact congrArg (fun φ => φ (F v s)) key

def IsZPow (b x : Kf) : Prop := ∃ z : ℤ, x = b ^ z

theorem IsZPow.one (b : Kf) : IsZPow b 1 := ⟨0, by simp⟩
theorem IsZPow.mul {b x y : Kf} (hb : b ≠ 0) (hx : IsZPow b x) (hy : IsZPow b y) : IsZPow b (x * y) := by
  obtain ⟨z, rfl⟩ := hx; obtain ⟨z', rfl⟩ := hy; exact ⟨z + z', by rw [zpow_add₀ hb]⟩
theorem IsZPow.zpow {b x : Kf} (hx : IsZPow b x) (n : ℤ) : IsZPow b (x ^ n) := by
  obtain ⟨z, rfl⟩ := hx; exact ⟨z * n, by rw [zpow_mul]⟩
theorem IsZPow.pow {b x : Kf} (hx : IsZPow b x) (n : ℕ) : IsZPow b (x ^ n) := by
  have := hx.zpow n; rwa [zpow_natCast] at this
theorem IsZPow.prod {b : Kf} (hb : b ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → Kf) (h : ∀ i ∈ s, IsZPow b (f i)) :
    IsZPow b (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsZPow.one b
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul hb (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem IsZPow.inv {b x : Kf} (hx : IsZPow b x) : IsZPow b x⁻¹ := by
  obtain ⟨z, rfl⟩ := hx; exact ⟨-z, by rw [zpow_neg]⟩

def LowT {k : ℕ} {R : Type*} [Zero R] (A : Matrix (Fin k) (Fin k) R) : Prop := ∀ i j, i < j → A i j = 0

theorem gPos_lowT (v : Fin P.nV) (s : Fin (P.n' v)) (A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))
    (hA : LowT A) : LowT (P.gPos v s A) := fun i j hij => by
  show P.ι v ((P.σ v ^ s.val) (A i j)) = 0
  rw [hA i j hij, map_zero, map_zero]

theorem gPos_diag (v : Fin P.nV) (s : Fin (P.n' v)) (A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (a : Fin (P.m + 1)) :
    P.gPos v s A a a = P.ι v ((P.σ v ^ s.val) (A a a)) := rfl

theorem subst_lowT (b : Kf) (hb : b ≠ 0) (A : ∀ v, Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (hA : ∀ v, LowT (A v))
    (hd : ∀ v s a, IsZPow b (P.gPos v s (A v) a a)) :
    ∃ c : Kf, IsZPow b c ∧ P.subst (fun v s => P.gPos v s (A v)) (EV P) = c • EV P := by
  unfold EV
  rw [subst_prodF]
  simp_rw [rowAct_hw Kf le_rfl _ _ (gPos_lowT P _ _ _ (hA _))]
  refine ⟨_, ?_, prodF_smul P _ _⟩
  refine IsZPow.prod hb _ _ fun v _ => IsZPow.prod hb _ _ fun s _ => ?_
  unfold hwScal
  exact IsZPow.prod hb _ _ fun t _ => (IsZPow.prod hb _ _ fun a _ => hd v s _).pow _

theorem det_lowT {k : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin k) (Fin k) R) (hA : LowT A) :
    A.det = ∏ i, A i i :=
  Matrix.det_of_lowerTriangular A fun i j hij => hA i j hij

theorem gPos_inv_det (v : Fin P.nV) (s : Fin (P.n' v)) (A : GL (Fin (P.m + 1)) (P.Qq v)) :
    (P.gPos v s ((A⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det =
      (P.gPos v s (A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det⁻¹ := by
  have h1 : P.gPos v s ((A⁻¹ : GL _ _) : Matrix _ _ _) * P.gPos v s (A : Matrix _ _ _) = 1 := by
    rw [← jd_gPos_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, jd_gPos_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem natAct_inv_lowT (b : Kf) (hb : b ≠ 0) (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v))
    (hA : ∀ v, LowT (A v : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)))
    (hd : ∀ v s a, IsZPow b (P.gPos v s (A v : Matrix _ _ _) a a)) :
    ∃ c : Kf, IsZPow b c ∧ P.natAct A⁻¹ (EV P) = c • EV P := by
  obtain ⟨c, hc, h1⟩ := subst_lowT P b hb (fun v => (A v : Matrix _ _ _)) hA hd
  refine ⟨(∏ v, ∏ s : Fin (P.n' v), (P.gPos v s ((A⁻¹ : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) v :
      Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det ^ (-(lamAt (P.lam0 v) s (Fin.last P.m)))) * c,
    IsZPow.mul hb (IsZPow.prod hb _ _ fun v _ => IsZPow.prod hb _ _ fun s _ => ?_) hc, ?_⟩
  · rw [Pi.inv_apply, gPos_inv_det, det_lowT _ (gPos_lowT P v s _ (hA v))]
    exact ((IsZPow.prod hb _ _ fun a _ => hd v s a).inv).zpow _
  · unfold Places.natAct
    rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    have : (fun v s => P.gPos v s (((A⁻¹ : ∀ v, GL _ _) v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))) =
        fun v s => P.gPos v s (A v : Matrix _ _ _) := by
      funext v s; rw [Pi.inv_apply, inv_inv]
    rw [this, h1, smul_smul]

end Formalism.BasicNotions.Examples₂.NZ
