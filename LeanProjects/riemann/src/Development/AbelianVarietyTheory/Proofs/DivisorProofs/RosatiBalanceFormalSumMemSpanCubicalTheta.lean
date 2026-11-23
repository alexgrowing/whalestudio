import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBal.SpanPf

variable {r : ℕ}

abbrev S (r : ℕ) : Submodule ℤ (Vec r →₀ ℤ) :=
  Submodule.span ℤ (Set.range fun p : Vec r × Vec r × Vec r => theta p.1 p.2.1 p.2.2)

lemma lam_comm (u v : Vec r) : lam u v = lam v u := by
  unfold lam; rw [add_comm u v]; abel

lemma theta_eq (u u' v : Vec r) : theta u u' v = lam (u + u') v - lam u v - lam u' v := by
  unfold lam theta; abel

lemma theta_mem (a b c : Vec r) : theta a b c ∈ S r := Submodule.subset_span ⟨(a, b, c), rfl⟩

def f (u v : Vec r) : (Vec r →₀ ℤ) ⧸ S r := Submodule.Quotient.mk (lam u v)

lemma f_comm (u v : Vec r) : f u v = f v u := by unfold f; rw [lam_comm]

lemma f_add_left (u u' v : Vec r) : f (u + u') v = f u v + f u' v := by
  unfold f
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  have h := theta_mem u u' v
  rw [theta_eq] at h
  convert h using 1; abel

lemma f_add_right (u v v' : Vec r) : f u (v + v') = f u v + f u v' := by
  rw [f_comm, f_add_left, f_comm v, f_comm v']

lemma f_smul_left (c : ℤ) (u v : Vec r) : f (c • u) v = c • f u v :=
  map_zsmul (AddMonoidHom.mk' (fun u => f u v) (fun a b => f_add_left a b v)) c u

lemma f_smul_right (c : ℤ) (u v : Vec r) : f u (c • v) = c • f u v := by
  rw [f_comm, f_smul_left, f_comm]

def B (r : ℕ) : Vec r →ₗ[ℤ] Vec r →ₗ[ℤ] (Vec r →₀ ℤ) ⧸ S r :=
  LinearMap.mk₂ ℤ f f_add_left f_smul_left f_add_right f_smul_right

lemma B_apply (u v : Vec r) : B r u v = Submodule.Quotient.mk (lam u v) := rfl

lemma B_comm (u v : Vec r) : B r u v = B r v u := f_comm u v

lemma axv_eq (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : axv A i = ∑ l, A i l • xv l := by
  funext s
  cases s <;> simp [axv, xv, Finset.sum_apply, Pi.single_apply]

lemma azv_eq (A' : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : azv A' i = ∑ l, A' i l • zv l := by
  funext s
  cases s <;> simp [azv, zv, Finset.sum_apply, Pi.single_apply]

def P (C : Matrix (Fin r) (Fin r) ℤ) : (Vec r →₀ ℤ) ⧸ S r := ∑ l, ∑ m, C l m • B r (xv l) (zv m)

lemma P_add (C D : Matrix (Fin r) (Fin r) ℤ) : P (C + D) = P C + P D := by
  simp [P, add_smul, Finset.sum_add_distrib]

lemma T1 (A V : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, V i j • B r (axv A i) (zv j) = P (A.transpose * V) := by
  simp only [P, axv_eq, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

lemma T3 (A' V : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, V i j • B r (xv i) (azv A' j) = P (V * A') := by
  simp only [P, azv_eq, map_sum, map_zsmul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma swapW (V : Matrix (Fin r) (Fin r) ℤ) (g : Fin r → Fin r → (Vec r →₀ ℤ) ⧸ S r) :
    ∑ i, ∑ j, V i j • g j i = ∑ i, ∑ j, V.transpose i j • g i j := by
  rw [Finset.sum_comm]; rfl

lemma per (A A' : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) :
    ∑ a : Fin 6, rosatiε a • B r (rosVec A A' a i) (rosVec A A' a j) =
      B r (axv A i) (zv j) + B r (zv i) (axv A j) - B r (xv i) (azv A' j) - B r (azv A' i) (xv j) := by
  simp [Fin.sum_univ_six, rosVec, rosatiε, map_add, LinearMap.add_apply]
  abel

theorem main {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (h : A.transpose * (W + W.transpose) = (W + W.transpose) * A') :
    GlobalTheory.TensBal.sig W A A' ∈ Submodule.span ℤ
      (Set.range fun p : GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r =>
        GlobalTheory.TensBal.theta p.1 p.2.1 p.2.2) := by
  rw [← Submodule.Quotient.mk_eq_zero]
  have e : (Submodule.Quotient.mk (sig W A A') : (Vec r →₀ ℤ) ⧸ S r) =
      ∑ i, ∑ j, W i j • ∑ a : Fin 6, rosatiε a • B r (rosVec A A' a i) (rosVec A A' a j) := by
    rw [sig, ← Submodule.mkQ_apply]
    simp only [map_sum, map_zsmul, Submodule.mkQ_apply, ← B_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  show (Submodule.Quotient.mk (sig W A A') : (Vec r →₀ ℤ) ⧸ S r) = 0
  rw [e]
  simp only [per, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, W i j • B r (zv i) (axv A j) = P (A.transpose * W.transpose) := by
    rw [← T1]; simp only [B_comm (zv _)]; exact swapW W (fun a b => B r (axv A a) (zv b))
  have h4 : ∑ i, ∑ j, W i j • B r (azv A' i) (xv j) = P (W.transpose * A') := by
    rw [← T3]; simp only [B_comm (azv A' _)]; exact swapW W (fun a b => B r (xv a) (azv A' b))
  rw [T1, h2, T3, h4, ← P_add, sub_sub, ← P_add, ← Matrix.add_mul, ← Matrix.mul_add, h, sub_self]

end GlobalTheory.TensBal.SpanPf

end
