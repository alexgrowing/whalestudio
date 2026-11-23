import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Extract

theorem exists_matrix_of_span {F B n N : Type} [Field F] [CommRing B] [Algebra F B] [Fintype N]
    (u v : N → n → B) (h : Submodule.span F (Set.range u) ≤ Submodule.span F (Set.range v)) :
    ∃ G : Matrix N N F, ∀ (ψ : B →ₐ[F] B) (c : N) (i : n),
      ψ (u c i) = ∑ e, ψ (v e i) * algebraMap F B (G e c) := by
  classical
  have hc : ∀ c, ∃ g : N → F, ∑ e, g e • v e = u c := fun c =>
    (Submodule.mem_span_range_iff_exists_fun F).mp (h (Submodule.subset_span ⟨c, rfl⟩))
  choose g hg using hc
  refine ⟨Matrix.of fun e c => g c e, ?_⟩
  intro ψ c i
  rw [← hg c, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Pi.smul_apply, map_smul, Algebra.smul_def, mul_comm, Matrix.of_apply]

theorem mul_mem_sub {R N : Type} [CommRing R] [Fintype N] (S : Subring R) {X Y : Matrix N N R}
    (hX : ∀ i j, X i j ∈ S) (hY : ∀ i j, Y i j ∈ S) (i j : N) : (X * Y) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem blocks {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {r : ℕ} (S : Subring R)
    (E U : Fin r → GL n R) (d : n × Fin r → R) (hd : ∀ x, IsUnit (d x))
    (W W' : Matrix (n × Fin r) (n × Fin r) R) (hW : ∀ i j, W i j ∈ S) (hW' : ∀ i j, W' i j ∈ S)
    (hWW : W * W' = 1)
    (h : Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) =
      Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d * W) (m : Fin r) :
    ∃ V : GL n R, (∀ i j, (V : Matrix n n R) i j ∈ S) ∧ (∀ i j, ((V⁻¹ : GL n R) : Matrix n n R) i j ∈ S) ∧
      (E m : Matrix n n R) = (U m : Matrix n n R) * Matrix.diagonal (fun j => d (j, m)) * (V : Matrix n n R) := by
  classical
  set M : Fin r → Matrix n n R := fun m => (U m : Matrix n n R) * Matrix.diagonal (fun j => d (j, m)) with hM
  set Mi : Fin r → Matrix n n R := fun m =>
    Matrix.diagonal (fun j => (((hd (j, m)).unit⁻¹ : Rˣ) : R)) * (((U m)⁻¹ : GL n R) : Matrix n n R) with hMi
  have hMiM : ∀ m, Mi m * M m = 1 := by
    intro m
    calc Mi m * M m = Matrix.diagonal (fun j => (((hd (j, m)).unit⁻¹ : Rˣ) : R)) *
          ((((U m)⁻¹ : GL n R) : Matrix n n R) * (U m : Matrix n n R)) * Matrix.diagonal (fun j => d (j, m)) := by
          simp only [hM, hMi, Matrix.mul_assoc]
      _ = 1 := by
          rw [Units.inv_mul, Matrix.mul_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1
          funext j
          exact IsUnit.val_inv_mul _
  have hMMi : ∀ m, M m * Mi m = 1 := by
    intro m
    calc M m * Mi m = (U m : Matrix n n R) * ((Matrix.diagonal (fun j => d (j, m)) *
          Matrix.diagonal (fun j => (((hd (j, m)).unit⁻¹ : Rˣ) : R))) * (((U m)⁻¹ : GL n R) : Matrix n n R)) := by
          simp only [hM, hMi, Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.diagonal_mul_diagonal]
          have : (fun j => d (j, m) * (((hd (j, m)).unit⁻¹ : Rˣ) : R)) = fun _ => (1 : R) := by
            funext j
            exact IsUnit.mul_val_inv _
          rw [this, Matrix.diagonal_one, Matrix.one_mul, Units.mul_inv]
  have hdiag : Matrix.diagonal d = Matrix.blockDiagonal (fun m => Matrix.diagonal fun j => d (j, m)) := by
    rw [Matrix.blockDiagonal_diagonal]
  have h' : Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) = Matrix.blockDiagonal M * W := by
    rw [h, hdiag, Matrix.blockDiagonal_mul]
  set Vm : Fin r → Matrix n n R := fun m => Mi m * (E m : Matrix n n R) with hVm
  set Vm' : Fin r → Matrix n n R := fun m => (((E m)⁻¹ : GL n R) : Matrix n n R) * M m with hVm'
  have hVV : ∀ m, Vm m * Vm' m = 1 := by
    intro m
    simp only [hVm, hVm', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (E m : Matrix n n R), Units.mul_inv, Matrix.one_mul, hMiM]
  have hV'V : ∀ m, Vm' m * Vm m = 1 := by
    intro m
    simp only [hVm, hVm', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M m), hMMi, Matrix.one_mul, Units.inv_mul]
  have hWb : W = Matrix.blockDiagonal Vm := by
    have hone : Matrix.blockDiagonal Mi * Matrix.blockDiagonal M = 1 := by
      rw [← Matrix.blockDiagonal_mul]
      simp only [hMiM]
      exact Matrix.blockDiagonal_one
    calc W = (Matrix.blockDiagonal Mi * Matrix.blockDiagonal M) * W := by rw [hone, Matrix.one_mul]
      _ = Matrix.blockDiagonal Mi * Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) := by
          rw [Matrix.mul_assoc, ← h']
      _ = Matrix.blockDiagonal Vm := by rw [← Matrix.blockDiagonal_mul, hVm]
  have hW'b : W' = Matrix.blockDiagonal Vm' := by
    have hone : Matrix.blockDiagonal Vm' * W = 1 := by
      rw [hWb, ← Matrix.blockDiagonal_mul]
      simp only [hV'V]
      exact Matrix.blockDiagonal_one
    calc W' = (Matrix.blockDiagonal Vm' * W) * W' := by rw [hone, Matrix.one_mul]
      _ = Matrix.blockDiagonal Vm' := by rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  refine ⟨⟨Vm m, Vm' m, hVV m, hV'V m⟩, ?_, ?_, ?_⟩
  · intro i j
    have hij := hW (i, m) (j, m)
    rw [hWb, Matrix.blockDiagonal_apply_eq] at hij
    exact hij
  · intro i j
    have hij := hW' (i, m) (j, m)
    rw [hW'b, Matrix.blockDiagonal_apply_eq] at hij
    exact hij
  · show (E m : Matrix n n R) = (U m : Matrix n n R) * Matrix.diagonal (fun j => d (j, m)) * (Mi m * (E m : Matrix n n R))
    rw [← Matrix.mul_assoc]
    have := hMMi m
    simp only [hM] at this
    rw [this, Matrix.one_mul]

theorem abstract {F B R n : Type} [Field F] [CommRing B] [Algebra F B] [CommRing R] [Fintype n] [DecidableEq n]
    {r : ℕ} (hr : 0 < r) (φ : B →ₐ[F] B) (ι : B →+* R) (S : Subring R) (hS : ∀ q : F, ι (algebraMap F B q) ∈ S)
    (w : Fin r → B) (hw : ∀ k, (φ ^ r) (w k) = w k) (hwu : ∀ k, IsUnit (w k))
    (p q : Matrix (n × Fin r) (n × Fin r) B) (hp : ∀ a b, p a b = if a.1 = b.1 then (φ ^ (a.2 : ℕ)) (w b.2) else 0)
    (hpq : p * q = 1) (hpS : ∀ a b, ι (p a b) ∈ S) (hqS : ∀ a b, ι (q a b) ∈ S)
    (U : Fin r → GL n R) (d : n × Fin r → R) (hd : ∀ x, IsUnit (d x))
    (A₀ : GL (n × Fin r) B)
    (hA₀ : ∀ i j, φ ((A₀ : Matrix (n × Fin r) (n × Fin r) B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) B) i j)
    (W₀ : GL (n × Fin r) R) (hW₀ : ∀ i j, (W₀ : Matrix (n × Fin r) (n × Fin r) R) i j ∈ S)
    (hW₀' : ∀ i j, ((W₀⁻¹ : GL (n × Fin r) R) : Matrix (n × Fin r) (n × Fin r) R) i j ∈ S)
    (hA : (A₀ : Matrix (n × Fin r) (n × Fin r) B).map ι =
      q.map ι * Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d *
        (W₀ : Matrix (n × Fin r) (n × Fin r) R))
    (a : n → n → B)
    (hsp : Submodule.span F (Set.range fun (jk : n × Fin r) (i : n) => w jk.2 * a jk.1 i) =
      Submodule.span F (Set.range fun (c : n × Fin r) (i : n) =>
        ∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) c)) :
    ∃ A : GL n B, (∀ i j, (φ ^ r) ((A : Matrix n n B) i j) = (A : Matrix n n B) i j) ∧
      ∀ m : Fin r, ∃ V : GL n R, (∀ i j, (V : Matrix n n R) i j ∈ S) ∧
        (∀ i j, ((V⁻¹ : GL n R) : Matrix n n R) i j ∈ S) ∧
        (A : Matrix n n B).map (fun b => ι ((φ ^ (m : ℕ)) b)) =
          (U m : Matrix n n R) * Matrix.diagonal (fun j => d (j, m)) * (V : Matrix n n R) := by
  classical
  have hfix : ∀ (m : ℕ) (x : B), φ x = x → (φ ^ m) x = x := by
    intro m x hx
    induction m with
    | zero => simp
    | succ k ih => rw [pow_succ, AlgHom.mul_apply, hx, ih]
  obtain ⟨G, hG⟩ := exists_matrix_of_span (F := F)
    (fun (jk : n × Fin r) (i : n) => w jk.2 * a jk.1 i)
    (fun (c : n × Fin r) (i : n) => ∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) c) hsp.le
  obtain ⟨G', hG'⟩ := exists_matrix_of_span (F := F)
    (fun (c : n × Fin r) (i : n) => ∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) c)
    (fun (jk : n × Fin r) (i : n) => w jk.2 * a jk.1 i) hsp.ge
  set A : Matrix n n B := Matrix.of fun i j => a j i with hAdef
  set Gm : Matrix (n × Fin r) (n × Fin r) B := G.map (algebraMap F B) with hGm
  set G'm : Matrix (n × Fin r) (n × Fin r) B := G'.map (algebraMap F B) with hG'm
  set D : Matrix (n × Fin r) (n × Fin r) B := Matrix.blockDiagonal fun m : Fin r => A.map ⇑(φ ^ (m : ℕ)) with hDdef
  have hY : ∀ (i : n) (m : Fin r) (e : n × Fin r), (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B)) (i, m) e =
      (φ ^ (m : ℕ)) (∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) e) := by
    intro i m e
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hp, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, hfix _ _ (hA₀ _ _)]
  have hZ : ∀ (i : n) (m : Fin r) (c : n × Fin r), (D * p) (i, m) c = (φ ^ (m : ℕ)) (w c.2 * a c.1 i) := by
    intro i m c
    have hinner : ∀ x : n, ∑ k : Fin r, D (i, m) (x, k) * p (x, k) c =
        (φ ^ (m : ℕ)) (a x i) * (if x = c.1 then (φ ^ (m : ℕ)) (w c.2) else 0) := by
      intro x
      rw [Fintype.sum_eq_single m]
      · simp only [hDdef, Matrix.blockDiagonal_apply_eq, Matrix.map_apply, hAdef, Matrix.of_apply, hp]
      · intro k hk
        rw [hDdef, Matrix.blockDiagonal_apply_ne _ _ _ (Ne.symm hk), zero_mul]
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [hinner, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul]
    rw [mul_comm]
  have hZY : D * p = p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm := by
    ext ⟨i, m⟩ c
    rw [hZ, hG (φ ^ (m : ℕ)) c i, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hY]
    rfl
  have hYZ : p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) = D * p * G'm := by
    ext ⟨i, m⟩ c
    rw [hY, hG' (φ ^ (m : ℕ)) c i, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hZ]
    rfl
  have hqp : q * p = 1 := mul_eq_one_comm.mp hpq
  have hL : ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q *
      (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc q, hqp, Matrix.one_mul]
    exact Units.inv_mul A₀
  have hGG : Gm * G'm = 1 := by
    calc Gm * G'm = (((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q *
          (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B))) * (Gm * G'm) := by rw [hL, Matrix.one_mul]
      _ = ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q *
          (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm * G'm) := by simp only [Matrix.mul_assoc]
      _ = ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q *
          (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B)) := by rw [← hZY, ← hYZ]
      _ = 1 := hL
  have hD : D = p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm * q := by
    calc D = D * (p * q) := by rw [hpq, Matrix.mul_one]
      _ = D * p * q := by rw [Matrix.mul_assoc]
      _ = p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm * q := by rw [hZY]
  have hDinv : D * (p * G'm * ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q) = 1 := by
    rw [hD]
    calc p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm * q *
          (p * G'm * ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q) =
        p * ((A₀ : Matrix (n × Fin r) (n × Fin r) B) * ((Gm * (q * p) * G'm) *
          (((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hqp, Matrix.mul_one, hGG, Matrix.one_mul, ← Matrix.mul_assoc (A₀ : Matrix (n × Fin r) (n × Fin r) B),
            Units.mul_inv, Matrix.one_mul, hpq]
  have hdetD : IsUnit D.det := Matrix.isUnit_det_of_right_inverse hDinv
  rw [hDdef, Matrix.det_blockDiagonal] at hdetD
  have hdetA : IsUnit A.det := by
    have h0 := isUnit_of_dvd_unit
      (Finset.dvd_prod_of_mem (fun m : Fin r => (A.map ⇑(φ ^ (m : ℕ))).det) (Finset.mem_univ ⟨0, hr⟩)) hdetD
    have hm0 : A.map ⇑(φ ^ ((⟨0, hr⟩ : Fin r) : ℕ)) = A := by
      ext i j
      simp
    simpa only [hm0] using h0
  refine ⟨Matrix.nonsingInvUnit A hdetA, ?_, ?_⟩
  · intro i j
    change (φ ^ r) (a j i) = a j i
    have hyfix : ∀ e : n × Fin r, (φ ^ r) (∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) e) =
        ∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) e := by
      intro e
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hw k, hfix _ _ (hA₀ _ _)]
    have h1 := hG (φ ^ r) (j, ⟨0, hr⟩) i
    have h2 := hG (AlgHom.id F B) (j, ⟨0, hr⟩) i
    simp only [hyfix, AlgHom.id_apply] at h1 h2
    rw [← h2, map_mul, hw] at h1
    exact (hwu _).mul_left_cancel h1
  · intro m
    set Wm : Matrix (n × Fin r) (n × Fin r) R := (W₀ : Matrix (n × Fin r) (n × Fin r) R) * Gm.map ι * q.map ι with hWm
    set W'm : Matrix (n × Fin r) (n × Fin r) R :=
      p.map ι * G'm.map ι * ((W₀⁻¹ : GL (n × Fin r) R) : Matrix (n × Fin r) (n × Fin r) R) with hW'm
    have hGS : ∀ i j, (Gm.map ι) i j ∈ S := fun i j => hS (G i j)
    have hG'S : ∀ i j, (G'm.map ι) i j ∈ S := fun i j => hS (G' i j)
    have hWS : ∀ i j, Wm i j ∈ S := fun i j =>
      mul_mem_sub S (fun i j => mul_mem_sub S hW₀ hGS i j) hqS i j
    have hW'S : ∀ i j, W'm i j ∈ S := fun i j =>
      mul_mem_sub S (fun i j => mul_mem_sub S hpS hG'S i j) hW₀' i j
    have hWW : Wm * W'm = 1 := by
      calc Wm * W'm = (W₀ : Matrix (n × Fin r) (n × Fin r) R) * ((Gm * (q * p) * G'm).map ι) *
            ((W₀⁻¹ : GL (n × Fin r) R) : Matrix (n × Fin r) (n × Fin r) R) := by
            simp only [hWm, hW'm, Matrix.map_mul, Matrix.mul_assoc]
        _ = 1 := by
            rw [hqp, Matrix.mul_one, hGG, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.mul_one, Units.mul_inv]
    have hpqι : p.map ι * q.map ι = 1 := by
      rw [← Matrix.map_mul, hpq, Matrix.map_one _ (map_zero ι) (map_one ι)]
    let E : Fin r → GL n R := fun m =>
      Units.map (ι.comp ((φ ^ (m : ℕ) : B →ₐ[F] B) : B →+* B)).mapMatrix.toMonoidHom (Matrix.nonsingInvUnit A hdetA)
    have hEm : (E m : Matrix n n R) = (Matrix.nonsingInvUnit A hdetA : Matrix n n B).map
        (fun b => ι ((φ ^ (m : ℕ)) b)) := by
      ext i j
      rfl
    have hblk : Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) =
        Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d * Wm := by
      calc Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) = D.map ι := by
            rw [hDdef, Matrix.blockDiagonal_map _ _ (map_zero ι)]
            rfl
        _ = p.map ι * (A₀ : Matrix (n × Fin r) (n × Fin r) B).map ι * Gm.map ι * q.map ι := by
            rw [hD]
            simp only [Matrix.map_mul]
        _ = p.map ι * (q.map ι * Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d *
            (W₀ : Matrix (n × Fin r) (n × Fin r) R)) * Gm.map ι * q.map ι := by rw [hA]
        _ = (p.map ι * q.map ι) * Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d *
            ((W₀ : Matrix (n × Fin r) (n × Fin r) R) * Gm.map ι * q.map ι) := by simp only [Matrix.mul_assoc]
        _ = Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d * Wm := by
            rw [hpqι, Matrix.one_mul]
    obtain ⟨V, hV1, hV2, hV3⟩ := blocks S E U d hd Wm W'm hWS hW'S hWW hblk m
    exact ⟨V, hV1, hV2, by rw [← hEm]; exact hV3⟩

theorem extract : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n), (∀ m, UnitM P (U m)) → ∀ (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → ∀ a : n → n → P.R.B, Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) → ∃ A : GL n P.R.B, (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) ∧ ∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (eps x y (m, j))) * (W : Matrix n n P.R.BdR) := by
  intro l _ P r ω hω hdet n _ _ U x y hU A₀ hA₀ W₀ hW₀ hA a hsp
  classical
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact ⟨1, fun i j => rfl, fun m => m.elim0⟩
  have hcoe : ∀ (m : ℕ) (b : P.R.B), (P.φB ^ m) b = P.φB^[m] b := by
    intro m
    induction m with
    | zero => intro b; rfl
    | succ k ih => intro b; rw [pow_succ, AlgHom.mul_apply, ih, Function.iterate_succ_apply]
  have hWu := hW₀
  unfold UnitM at hWu
  let ι : P.R.B →+* P.R.BdR := (P.ιB : P.R.B →+* P.R.BdR)
  let pGL : GL (n × Fin r) P.R.B :=
    Units.map ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).mapMatrix :
      Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+* Matrix (n × Fin r) (n × Fin r) P.R.B).toMonoidHom (resGL n ω hdet)
  have hpv : ∀ a b, (pGL : Matrix (n × Fin r) (n × Fin r) P.R.B) a b =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((resGL n ω hdet : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) a b) := fun a b => rfl
  have hqv : ∀ a b, ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B) a b =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) :
        Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) a b) := fun a b => rfl
  have hres : (resGL n ω hdet : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = resMat n ω := rfl
  have hwu : ∀ k, IsUnit (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k)) := by
    intro k
    refine IsUnit.map _ (isUnit_iff_ne_zero.mpr ?_)
    intro h0
    apply hdet
    apply Matrix.det_eq_zero_of_column_eq_zero k
    intro m
    simp [frobMat, h0]
  have hsp' : Submodule.span ℚ_[l] (Set.range fun (jk : n × Fin r) (i : n) =>
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω jk.2) * a jk.1 i) =
      Submodule.span ℚ_[l] (Set.range fun (c : n × Fin r) (i : n) =>
        ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c) := by
    have e4 : (fun (jk : n × Fin r) (i : n) => algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω jk.2) * a jk.1 i) =
        fun jk => ω jk.2 • a jk.1 := by
      funext jk i
      rw [Pi.smul_apply, Algebra.smul_def]
    rw [e4]
    exact hsp
  have hAι : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι =
      ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι *
        Matrix.blockDiagonal (fun m => (U m : Matrix n n P.R.BdR)) *
        Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    have e1 : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι =
        (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) := by
      ext i j
      rfl
    have e3 : ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι =
        ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))).map (kd P) := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, hqv]
      exact iota_kur P _
    have e2 : (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) =
        ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι *
          Matrix.blockDiagonal (fun m => (U m : Matrix n n P.R.BdR)) := by
      rw [e3]
      rfl
    rw [e1, hA, e2]
  obtain ⟨A, hA1, hA2⟩ := abstract (F := ℚ_[l]) (B := P.R.B) (R := P.R.BdR) (n := n) hr P.φB ι (S0 P)
    (fun q => by
      rw [mem_S0_of_sum_eq]
      show P.ιB (algebraMap ℚ_[l] P.R.B q) ∈ Fil P 0
      rw [AlgHom.commutes]
      exact q_mem_Fil P q)
    (fun k => algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k))
    (fun k => by rw [hcoe, phi_iter_kur, hω])
    hwu
    (pGL : Matrix (n × Fin r) (n × Fin r) P.R.B)
    ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B)
    (fun a b => by
      rw [hpv, hres, resMat_apply]
      split_ifs
      · rw [hcoe, phi_iter_kur]
      · exact map_zero _)
    (Units.mul_inv pGL)
    (fun a b => by
      rw [mem_S0_of_sum_eq]
      show P.ιB ((pGL : Matrix (n × Fin r) (n × Fin r) P.R.B) a b) ∈ Fil P 0
      rw [hpv, iota_kur]
      exact kd_mem_Fil P _)
    (fun a b => by
      rw [mem_S0_of_sum_eq]
      show P.ιB (((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B) a b) ∈ Fil P 0
      rw [hqv, iota_kur]
      exact kd_mem_Fil P _)
    U (fun j : n × Fin r => tz P (eps x y (j.2, j.1)))
    (fun j => by
      unfold tz
      exact (Units.isUnit _).map P.ιB)
    A₀ hA₀ W₀ (fun i j => (mem_S0_of_sum_eq P).mpr (hWu.1 i j)) (fun i j => (mem_S0_of_sum_eq P).mpr (hWu.2 i j)) hAι a hsp'
  refine ⟨A, fun i j => by rw [← hcoe]; exact hA1 i j, fun m => ?_⟩
  obtain ⟨V, hV1, hV2, hV3⟩ := hA2 m
  refine ⟨V, by unfold UnitM; exact ⟨fun i j => (mem_S0_of_sum_eq P).mp (hV1 i j), fun i j => (mem_S0_of_sum_eq P).mp (hV2 i j)⟩, ?_⟩
  rw [← hV3]
  ext i j
  show P.ιB (P.φB^[(m : ℕ)] _) = P.ιB ((P.φB ^ (m : ℕ)) _)
  rw [hcoe]

end GlobalTheory.PMon.Extract

end
