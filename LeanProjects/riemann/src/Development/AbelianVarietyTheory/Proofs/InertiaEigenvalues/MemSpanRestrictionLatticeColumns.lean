import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.ResR

open Matrix

variable {l : ℕ} [Fact l.Prime] {r : ℕ}

theorem resGL_mul_inv_map (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) :
    (resMat n ω).map f * (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map f = 1 := by
  have h : (resMat n ω) = ((resGL n ω hdet : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := rfl
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Units.mul_inv, map_one]

theorem resGL_inv_mul_map (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) :
    (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map f * (resMat n ω).map f = 1 := by
  have h : (resMat n ω) = ((resGL n ω hdet : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := rfl
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Units.inv_mul, map_one]

theorem resMat_mulVec_apply (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) (v : n × Fin r → S) (i : n) (m : Fin r) :
    ((resMat n ω).map f *ᵥ v) (i, m) = ∑ k, f (fr l m (ω k)) * v (i, k) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, resMat_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

theorem sum_fr_mul_eq_iter (hr : 0 < r) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hω : ∀ k, fr l r (ω k) = ω k)
    (a : n → P.R.B) (ha : ∀ i, P.φB^[r] (a i) = a i) (u : n × Fin r → P.R.B)
    (hu : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ u = fun j => P.φB^[j.2] (a j.1))
    (m : ℕ) (i : n) :
    ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m (ω k)) * u (i, k) = P.φB^[m] (a i) := by
  have h := congrFun hu (i, ⟨m % r, Nat.mod_lt _ hr⟩)
  rw [resMat_mulVec_apply] at h
  simp only [fr_mod (hω _)] at h
  rw [h]
  exact Function.IsPeriodicPt.iterate_mod_apply (ha i) m

theorem phi_fix_of_res (hr : 0 < r) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hω : ∀ k, fr l r (ω k) = ω k)
    (hdet : (frobMat ω).det ≠ 0)
    (a : n → P.R.B) (ha : ∀ i, P.φB^[r] (a i) = a i) (u : n × Fin r → P.R.B)
    (hu : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ u = fun j => P.φB^[j.2] (a j.1))
    (j : n × Fin r) : P.φB (u j) = u j := by
  set d : n × Fin r → P.R.B := fun j => P.φB (u j) - u j with hd
  have hz : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ d = 0 := by
    funext ⟨i, m⟩
    rw [resMat_mulVec_apply]
    have h1 := sum_fr_mul_eq_iter P hr ω hω a ha u hu (m + (r - 1)) i
    have h2 := sum_fr_mul_eq_iter P hr ω hω a ha u hu (m + (r - 1) + 1) i
    have e : m + (r - 1) + 1 = (m : ℕ) + r := by omega
    rw [Function.iterate_succ_apply', ← h1, map_sum] at h2
    simp only [map_mul, phiB_algebraMap, ← fr_one, ← fr_add] at h2
    rw [show 1 + ((m : ℕ) + (r - 1)) = (m : ℕ) + r by omega, e] at h2
    simp only [fr_add, hω] at h2
    simp only [hd, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
    rw [h2, sub_self]
  have : d = 0 := by
    rw [← Matrix.one_mulVec d, ← resGL_inv_mul_map n ω hdet, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  exact sub_eq_zero.1 (congrFun this j)

def tzGL {N : Type} [Fintype N] [DecidableEq N] (e : N → ℤ) : GL N P.R.BdR where
  val := Matrix.diagonal fun j => tz P (e j)
  inv := Matrix.diagonal fun j => tz P (-e j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [← tz_add, tz_zero]
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp [← tz_add, tz_zero]

theorem iota_q_eq (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (U : Fin r → GL n P.R.BdR)
    (e : n × Fin r → ℤ) (A₀ : GL (n × Fin r) P.R.B) (W₀ : GL (n × Fin r) P.R.BdR)
    (hA : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) =
      (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR)) :
    ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.ιB *
      ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
        (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map P.ιB *
      (blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) =
      ((W₀⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
  set G : GL (n × Fin r) P.R.BdR := Units.map ((P.ιB : P.R.B →+* P.R.BdR).mapMatrix).toMonoidHom A₀ with hGdef
  set kp : GL (n × Fin r) P.R.BdR := Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+*
    Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom (resGL n ω hdet) with hkp
  have hG : G = kp⁻¹ * blockGL U * tzGL P e * W₀ := by
    apply Units.ext
    rw [hGdef]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Units.val_mul]
    rw [show (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (P.ιB : P.R.B →+* P.R.BdR) =
      (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) from rfl, hA]
    rfl
  have h1 : ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.ιB =
      ((G⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    rw [hGdef, ← map_inv, Units.coe_map]
    rfl
  have h2 : ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
        (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map P.ιB = ((kp⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    rw [hkp, ← map_inv, Units.coe_map, Matrix.map_map]
    ext i j
    simp [iota_kur]
  have h3 : (blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) =
      ((blockGL U * tzGL P e : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := rfl
  rw [h1, h2, Matrix.mul_assoc, h3, ← Units.val_mul, ← Units.val_mul, hG]
  congr 1
  group

theorem mem_span_colv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ), 0 < r → ∀ (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
    (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n]
    (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B),
    (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) →
    ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ →
    (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) →
    ∀ a : n → P.R.B, LatC P U x y a → a ∈ Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) := by
  intro l _ P r hr ω hω hdet n _ _ U x y A₀ hφ W₀ hW₀ hA a hLat
  obtain ⟨ha, hw⟩ := hLat
  choose w hw0 hwe using hw
  set pB : Matrix (n × Fin r) (n × Fin r) P.R.B := (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hpB
  set pI : Matrix (n × Fin r) (n × Fin r) P.R.B :=
    (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
      (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hpI
  set V : n × Fin r → P.R.B := fun j => P.φB^[j.2] (a j.1) with hV
  set u : n × Fin r → P.R.B := pI *ᵥ V with hu
  have hpu : pB *ᵥ u = V := by
    rw [hu, Matrix.mulVec_mulVec, hpB, hpI, resGL_mul_inv_map, Matrix.one_mulVec]
  set Ai : Matrix (n × Fin r) (n × Fin r) P.R.B := ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B)
    with hAi
  set q : n × Fin r → P.R.B := Ai *ᵥ u with hq

  have hAφ : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.φB = A₀ := Matrix.ext fun i j => hφ i j
  have hAiφ : Ai.map (P.φB : P.R.B →+* P.R.B) = Ai := by
    have h1 : Ai.map (P.φB : P.R.B →+* P.R.B) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) = 1 := by
      conv_lhs => rw [← hAφ]
      rw [show (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.φB =
          ((P.φB : P.R.B →+* P.R.B).mapMatrix (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B)) from rfl,
        show Ai.map (P.φB : P.R.B →+* P.R.B) = (P.φB : P.R.B →+* P.R.B).mapMatrix Ai from rfl, ← map_mul, hAi,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    calc Ai.map (P.φB : P.R.B →+* P.R.B)
        = Ai.map (P.φB : P.R.B →+* P.R.B) * ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) * Ai) := by
          rw [hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = Ai := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have huφ : ∀ j, P.φB (u j) = u j := phi_fix_of_res P hr ω hω hdet a ha u hpu
  have hqφ : ∀ c, P.φB (q c) = q c := by
    intro c
    have := RingHom.map_mulVec (P.φB : P.R.B →+* P.R.B) Ai u c
    rw [hAiφ] at this
    change P.φB (q c) = _ at this
    rw [this, hq]
    congr 1
    funext j
    exact huφ j

  set wt : n × Fin r → P.R.BdR := fun j => w j.2 j.1 with hwt
  have hιV : (fun j => P.ιB (V j)) = ((blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1)))) *ᵥ wt := by
    funext ⟨i, m⟩
    have h := congrFun (hwe m) i
    change P.ιB (P.φB^[m] (a i)) = _
    have hd : ∀ (v w : n × Fin r → P.R.BdR), Matrix.diagonal v *ᵥ w = fun j => v j * w j :=
      fun v w => funext (Matrix.mulVec_diagonal v w)
    have hd' : ∀ (v w : n → P.R.BdR), Matrix.diagonal v *ᵥ w = fun j => v j * w j :=
      fun v w => funext (Matrix.mulVec_diagonal v w)
    rw [show P.ιB (P.φB^[m] (a i)) = ev P m (a i) from rfl, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hd, hd']
    simp only [Matrix.mulVec, dotProduct, blockGL, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, hwt]
    rw [Finset.sum_comm, Finset.sum_eq_single m]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  have hιq : (fun c => P.ιB (q c)) = ((W₀⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *ᵥ wt := by
    funext c
    have e1 := RingHom.map_mulVec (P.ιB : P.R.B →+* P.R.BdR) Ai u c
    have e2 : (fun j => P.ιB (u j)) = (pI.map (P.ιB : P.R.B →+* P.R.BdR)) *ᵥ (fun j => P.ιB (V j)) := by
      funext j
      exact RingHom.map_mulVec (P.ιB : P.R.B →+* P.R.BdR) pI V j
    change P.ιB (q c) = _ at e1
    rw [e1]
    change (Ai.map P.ιB *ᵥ (fun j => P.ιB (u j))) c = _
    rw [e2, hιV, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [← iota_q_eq P ω hdet U (fun j : n × Fin r => eps x y (j.2, j.1)) A₀ W₀ hA]
    simp only [Matrix.mul_assoc]
    rfl
  have hqF : ∀ c, P.ιB (q c) ∈ Fil P 0 := by
    intro c
    rw [show P.ιB (q c) = (fun c => P.ιB (q c)) c from rfl, hιq]
    exact Fil_sum fun j _ => Fil_mul_left (hW₀.2 c j) (hw0 j.2 j.1)
  choose cq hcq using fun c => fund P (hqφ c) (hqF c)

  have hAq : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) *ᵥ q = u := by
    rw [hq, Matrix.mulVec_mulVec, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have haeq : a = ∑ c, cq c • colv P ω A₀ c := by
    funext i
    have h0 := sum_fr_mul_eq_iter P hr ω hω a ha u hpu 0 i
    simp only [fr_zero, Function.iterate_zero, id] at h0
    rw [← h0, ← hAq]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    simp only [Algebra.smul_def, hcq, colv, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [haeq]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))

end GlobalTheory.PMon.ResR
end
