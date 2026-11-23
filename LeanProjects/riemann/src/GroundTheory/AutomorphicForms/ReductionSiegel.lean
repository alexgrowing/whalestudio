import Mathlib
import GroundTheory.AutomorphicForms.ReductionCore

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

section Unipotent

variable {R : Type*} [CommRing R] {n : ℕ}

def IsUnitriangular (M : Matrix (Fin n) (Fin n) R) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1

def unitriangular (p : Fin n → Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = j then 1 else if i < j then p i j else 0

theorem isUnitriangular_unitriangular (p : Fin n → Fin n → R) :
    IsUnitriangular (unitriangular p) := by
  refine ⟨fun i j hij => ?_, fun i => by simp [unitriangular]⟩
  have h1 : i ≠ j := fun h => (lt_irrefl j) (h ▸ hij)
  have h2 : ¬ i < j := not_lt.2 hij.le
  simp [unitriangular, h1, h2]

theorem IsUnitriangular.eq_unitriangular {M : Matrix (Fin n) (Fin n) R} (hM : IsUnitriangular M) :
    M = unitriangular fun i j => M i j := by
  ext i j
  simp only [unitriangular, of_apply]
  split_ifs with h1 h2
  · subst h1; exact hM.2 i
  · rfl
  · exact hM.1 (lt_of_le_of_ne (not_lt.1 h2) (Ne.symm h1))

theorem IsUnitriangular.det_eq_one {M : Matrix (Fin n) (Fin n) R} (hM : IsUnitriangular M) :
    M.det = 1 := by
  rw [det_of_isUpperTriangular hM.1]
  simp [hM.2]

theorem IsUnitriangular.mul {M N : Matrix (Fin n) (Fin n) R} (hM : IsUnitriangular M)
    (hN : IsUnitriangular N) : IsUnitriangular (M * N) := by
  refine ⟨hM.1.mul hN.1, fun i => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hM.2, hN.2, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hM.1 h, zero_mul]
    · rw [hN.1 h, mul_zero]
  · simp

end Unipotent

theorem exists_isCompact_add_mem :
    ∃ D : Set 𝔸[K], IsCompact D ∧ ∀ x : 𝔸[K], ∃ k : K, x + algebraMap K 𝔸[K] k ∈ D := by
  obtain ⟨C, hC, hx⟩ := exists_isCompact_forall_exists_sub_mem K
  refine ⟨C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)),
    hC.prod (isCompact_integralFiniteAdeles K), fun x => ?_⟩
  obtain ⟨k, hk⟩ := hx x
  exact ⟨-k, by rwa [map_neg, ← sub_eq_add_neg]⟩

section LastCol

variable {R : Type*} [CommRing R] {m : ℕ}

def lastColMat (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases (v i') (fun j' => A i' j') j) i

@[simp] theorem lastColMat_last_last (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R) :
    lastColMat A v (Fin.last m) (Fin.last m) = 1 := by simp [lastColMat]

@[simp] theorem lastColMat_last_castSucc (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R) (j : Fin m) :
    lastColMat A v (Fin.last m) j.castSucc = 0 := by simp [lastColMat]

@[simp] theorem lastColMat_castSucc_last (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R) (i : Fin m) :
    lastColMat A v i.castSucc (Fin.last m) = v i := by simp [lastColMat]

@[simp] theorem lastColMat_castSucc_castSucc (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R)
    (i j : Fin m) : lastColMat A v i.castSucc j.castSucc = A i j := by simp [lastColMat]

theorem isUnitriangular_lastColMat {A : Matrix (Fin m) (Fin m) R} (hA : IsUnitriangular A)
    (v : Fin m → R) : IsUnitriangular (lastColMat A v) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
      | cast j =>
        rw [lastColMat_castSucc_castSucc]
        exact hA.1 (Fin.castSucc_lt_castSucc_iff.1 hij)
  · induction i using Fin.lastCases with
    | last => simp
    | cast i => rw [lastColMat_castSucc_castSucc]; exact hA.2 i

end LastCol

theorem exists_unitriangular_mul_mem {D : Set 𝔸[K]}
    (hD : ∀ x : 𝔸[K], ∃ k : K, x + algebraMap K 𝔸[K] k ∈ D) :
    ∀ (m : ℕ) (u : Matrix (Fin m) (Fin m) 𝔸[K]), IsUnitriangular u →
      ∃ ν : Matrix (Fin m) (Fin m) K, IsUnitriangular ν ∧
        ∀ i j, i < j → (ν.map (algebraMap K 𝔸[K]) * u) i j ∈ D := by
  classical
  intro m
  induction m with
  | zero => exact fun u _ => ⟨1, ⟨blockTriangular_one, fun i => i.elim0⟩, fun i => i.elim0⟩
  | succ m ih =>
    intro u hu
    set u' : Matrix (Fin m) (Fin m) 𝔸[K] := Matrix.of fun i j => u i.castSucc j.castSucc with hu'
    have hu'u : IsUnitriangular u' := ⟨fun i j hij => hu.1 (Fin.castSucc_lt_castSucc_iff.2 hij),
      fun i => hu.2 i.castSucc⟩
    obtain ⟨ν', hν', hν'D⟩ := ih u' hu'u
    set v : Fin m → 𝔸[K] := fun i => u i.castSucc (Fin.last m) with hv
    choose w hw using fun i => hD ((ν'.map (algebraMap K 𝔸[K]) *ᵥ v) i)
    refine ⟨lastColMat ν' w, isUnitriangular_lastColMat hν' w, fun i j hij => ?_⟩
    have hul : ∀ j : Fin m, u (Fin.last m) j.castSucc = 0 := fun j => hu.1 (Fin.castSucc_lt_last j)
    induction i using Fin.lastCases with
    | last => exact absurd hij (not_lt.2 (Fin.le_last j))
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        have := hw i
        simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.map_apply,
          lastColMat_castSucc_castSucc, lastColMat_castSucc_last, hu.2, mul_one]
        simpa [mulVec, dotProduct, hv] using this
      | cast j =>
        have := hν'D i j (Fin.castSucc_lt_castSucc_iff.1 hij)
        simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.map_apply,
          lastColMat_castSucc_castSucc, lastColMat_castSucc_last, hul, mul_zero, add_zero]
        simpa [Matrix.mul_apply, hu'] using this

section Diag

variable (n : ℕ)

def diagUnits {R : Type*} [CommRing R] : (Fin n → Rˣ) →* GL (Fin n) R where
  toFun d := ⟨diagonal fun i => (d i : R), diagonal fun i => ((d i)⁻¹ : Rˣ),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' d e := Units.ext (by simp [diagonal_mul_diagonal])

@[simp] theorem coe_diagUnits {R : Type*} [CommRing R] (d : Fin n → Rˣ) :
    ((diagUnits n d : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal fun i => (d i : R) := rfl

theorem continuous_diagUnits :
    Continuous (diagUnits n : (Fin n → IdeleGroup K) → AdelicGLn.AdelicGL K n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp (continuous_apply i))
  · change Continuous fun d : Fin n → IdeleGroup K => diagonal fun i => (((d i)⁻¹ : IdeleGroup K) : 𝔸[K])
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp ((continuous_apply i).inv))

theorem diagonal_diagUnits (c : Fin n → Kˣ) :
    AdelicGLn.diagonal K n (diagUnits n c) =
      diagUnits n (fun i => IdeleGroup.diagonal K (c i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [AdelicGLn.diagonal_apply, coe_diagUnits, coe_diagUnits, diagonal_apply, diagonal_apply]
  split_ifs <;> simp [IdeleGroup.coe_diagonal]

theorem diagUnits_mem_adelicBorel (d : Fin n → IdeleGroup K) :
    diagUnits n d ∈ adelicBorel := by
  rw [mem_adelicBorel, coe_diagUnits]
  exact blockTriangular_diagonal _

def unitriangularGL (p : Fin n → Fin n → 𝔸[K]) : AdelicGLn.AdelicGL K n :=
  ⟨unitriangular p, adjugate (unitriangular p),
    by rw [mul_adjugate, (isUnitriangular_unitriangular p).det_eq_one, one_smul],
    by rw [adjugate_mul, (isUnitriangular_unitriangular p).det_eq_one, one_smul]⟩

theorem continuous_unitriangularGL :
    Continuous (unitriangularGL n : (Fin n → Fin n → 𝔸[K]) → AdelicGLn.AdelicGL K n) := by
  have h : Continuous fun p : Fin n → Fin n → 𝔸[K] => unitriangular p := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [unitriangular, of_apply]
    split_ifs
    · exact continuous_const
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const
  exact Units.continuous_iff.2 ⟨h, h.matrix_adjugate⟩

theorem unitriangularGL_mem_adelicBorel (p : Fin n → Fin n → 𝔸[K]) :
    unitriangularGL n p ∈ adelicBorel :=
  (isUnitriangular_unitriangular p).1

end Diag

def siegelTorus (n : ℕ) (t : ℝ) : Set (AdelicGLn.AdelicGL K n) :=
  {a | ∃ (r : Fin n → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧
    a = diagUnits n fun i => posIdele (r i) (hr i)}

def siegelSet (n : ℕ) (ω : Set (AdelicGLn.AdelicGL K n)) (t : ℝ) : Set (AdelicGLn.AdelicGL K n) :=
  {g | ∃ b ∈ ω, ∃ a ∈ siegelTorus n t, ∃ k ∈ maxCompact, g = b * a * k}

open scoped Pointwise in

theorem exists_siegelSet (n : ℕ) :
    ∃ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω ∧
      ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) ∧ ∃ t : ℝ, 0 < t ∧
      ∀ g : AdelicGLn.AdelicGL K n, ∃ γ : GL (Fin n) K,
        AdelicGLn.diagonal K n γ * g ∈ siegelSet n ω t := by
  classical
  obtain ⟨t₀, ht₀, hred⟩ := exists_reduced (K := K)
  obtain ⟨D, hD, hDmem⟩ := exists_isCompact_add_mem (K := K)
  obtain ⟨S, hS, hS1, hSmem⟩ := exists_isCompact_normOneSubgroup K
  set d : ℕ := Module.finrank ℚ K with hd
  have hd0 : 0 < d := Module.finrank_pos
  set FN : Set (AdelicGLn.AdelicGL K n) :=
    unitriangularGL n '' (Set.pi univ fun _ => Set.pi univ fun _ => D) with hFN
  set FT : Set (AdelicGLn.AdelicGL K n) := diagUnits n '' (Set.pi univ fun _ => S) with hFT
  have hFNc : IsCompact FN := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hD).image
    (continuous_unitriangularGL n)
  have hFTc : IsCompact FT := (isCompact_univ_pi fun _ => hS).image (continuous_diagUnits n)
  refine ⟨FN * FT, hFNc.mul hFTc, ?_, t₀ ^ ((d : ℝ)⁻¹), Real.rpow_pos_of_pos ht₀ _, fun g => ?_⟩
  · rintro _ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, -, rfl⟩, rfl⟩
    exact mul_mem (unitriangularGL_mem_adelicBorel n p) (diagUnits_mem_adelicBorel n e)
  obtain ⟨γ, b, hb, k, hk, hγ, hratio⟩ := hred n g
  set B : Matrix (Fin n) (Fin n) 𝔸[K] := (b : Matrix (Fin n) (Fin n) 𝔸[K]) with hB
  set dU : Fin n → IdeleGroup K := fun i => (isUnit_apply_self_of_mem_adelicBorel hb i).unit
    with hdU
  have hdUv : ∀ i, ((dU i : IdeleGroup K) : 𝔸[K]) = B i i := fun i => IsUnit.unit_spec _
  set r : Fin n → ℝ := fun i => (ideleModule K (dU i) : ℝ) ^ ((d : ℝ)⁻¹) with hr
  have hrpos : ∀ i, 0 < r i := fun i => Real.rpow_pos_of_pos (ideleModule K (dU i)).2 _
  have hrd : ∀ i, r i ^ d = ideleModule K (dU i) := fun i =>
    Real.rpow_inv_natCast_pow (ideleModule K (dU i)).2.le hd0.ne'
  have heqmod : ∀ i, ideleModule K (dU i) = ideleModule K (posIdele (r i) (hrpos i)) := fun i =>
    Subtype.ext (by rw [ideleModule_posIdele, ← hd, hrd i])
  have hnorm : ∀ i, dU i * (posIdele (r i) (hrpos i))⁻¹ ∈ normOneSubgroup K := fun i => by
    rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, heqmod i, mul_inv_cancel]
  choose c hc using fun i => hSmem _ (hnorm i)
  set σ : Fin n → IdeleGroup K :=
    fun i => IdeleGroup.diagonal K (c i) * (dU i * (posIdele (r i) (hrpos i))⁻¹) with hσ
  set e : Fin n → IdeleGroup K := fun i => IdeleGroup.diagonal K (c i) with he
  set δA : AdelicGLn.AdelicGL K n := diagUnits n e with hδA
  have hδ : AdelicGLn.diagonal K n (diagUnits n c) = δA := diagonal_diagUnits n c
  set u : AdelicGLn.AdelicGL K n := δA * b * (diagUnits n dU)⁻¹ * δA⁻¹ with hu
  have hu_apply : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝔸[K]) i j =
      (e i : 𝔸[K]) * B i j * (((dU j)⁻¹ : IdeleGroup K) : 𝔸[K]) * (((e j)⁻¹ : IdeleGroup K) : 𝔸[K]) := by
    intro i j
    rw [hu, ← map_inv, ← map_inv]
    simp only [Units.val_mul, hδA, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.inv_apply]
    rfl
  have huu : IsUnitriangular (u : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hu_apply, show B i j = 0 from hb hij]
      simp
    · rw [hu_apply, ← hdUv i]
      calc (e i : 𝔸[K]) * (dU i : 𝔸[K]) * (((dU i)⁻¹ : IdeleGroup K) : 𝔸[K]) *
            (((e i)⁻¹ : IdeleGroup K) : 𝔸[K])
          = ((e i * dU i * (dU i)⁻¹ * (e i)⁻¹ : IdeleGroup K) : 𝔸[K]) := by simp [Units.val_mul]
        _ = 1 := by rw [mul_inv_cancel_right, mul_inv_cancel, Units.val_one]
  obtain ⟨ν, hν, hνD⟩ := exists_unitriangular_mul_mem hDmem n _ huu
  set νGL : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero ν
    (by rw [hν.det_eq_one]; exact one_ne_zero) with hνGL
  set νA : AdelicGLn.AdelicGL K n := AdelicGLn.diagonal K n νGL with hνA
  have hνAmat : (νA : Matrix (Fin n) (Fin n) 𝔸[K]) = ν.map (algebraMap K 𝔸[K]) := rfl
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := let ⟨k₀, hk₀⟩ := hDmem 0; ⟨_, hk₀⟩
  set p : Fin n → Fin n → 𝔸[K] := fun i j =>
    if i < j then ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j else d₀
    with hp
  have hpD : p ∈ Set.pi univ fun _ => Set.pi univ fun _ => D := by
    intro i _ j _
    simp only [hp]
    split_ifs with hij
    · rw [Units.val_mul, hνAmat]
      exact hνD i j hij
    · exact hd₀
  have hνu : νA * u = unitriangularGL n p := by
    refine Units.ext ?_
    have h1 : IsUnitriangular ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
      rw [Units.val_mul, hνAmat]
      exact IsUnitriangular.mul ⟨fun i j hij => by simp [hν.1 hij],
        fun i => by simp [hν.2 i]⟩ huu
    rw [h1.eq_unitriangular]
    change unitriangular _ = unitriangular p
    ext i j
    simp only [unitriangular, of_apply, hp]
    split_ifs <;> rfl

  have hdiag : δA * diagUnits n dU = diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) := by
    rw [hδA, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, hσ, he]
    group
  refine ⟨νGL * diagUnits n c * γ, unitriangularGL n p * diagUnits n σ,
    ⟨_, ⟨p, hpD, rfl⟩, _, ⟨σ, fun i _ => hc i, rfl⟩, rfl⟩,
    diagUnits n (fun i => posIdele (r i) (hrpos i)), ⟨r, hrpos, fun i j hij => ?_, rfl⟩, k, hk, ?_⟩
  ·
    have h := hratio i j hij
    rw [← hdUv j, ← hdUv i, adeleAbs_units, adeleAbs_units, ← hrd i, ← hrd j] at h
    have hrj := (hrpos j).le
    have hri := (hrpos i).le
    have ht : (t₀ ^ ((d : ℝ)⁻¹)) ^ d = t₀ := Real.rpow_inv_natCast_pow ht₀.le hd0.ne'
    have htn : 0 ≤ t₀ ^ ((d : ℝ)⁻¹) := (Real.rpow_pos_of_pos ht₀ _).le
    rw [← pow_le_pow_iff_left₀ (mul_nonneg htn hrj) hri hd0.ne', mul_pow, ht]
    exact h
  · have h1 : δA * b = u * (δA * diagUnits n dU) := by
      rw [hu]; group
    calc AdelicGLn.diagonal K n (νGL * diagUnits n c * γ) * g
        = νA * δA * (AdelicGLn.diagonal K n γ * g) := by
          rw [map_mul, map_mul, hδ, ← hνA]; simp only [mul_assoc]
      _ = νA * (δA * b) * k := by rw [hγ]; simp only [mul_assoc]
      _ = νA * u * (δA * diagUnits n dU) * k := by rw [h1]; simp only [mul_assoc]
      _ = (νA * u) * diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) * k := by
          rw [hdiag]; simp only [mul_assoc]
      _ = _ := by rw [hνu]

open scoped Pointwise in

theorem exists_rationalGL_mul_siegelSet_eq_univ (n : ℕ) :
    ∃ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω ∧
      ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) ∧ ∃ t : ℝ, 0 < t ∧
        (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n)) * siegelSet n ω t = univ := by
  obtain ⟨ω, hω, hωB, t, ht, h⟩ := exists_siegelSet (K := K) n
  refine ⟨ω, hω, hωB, t, ht, Set.eq_univ_of_forall fun g => ?_⟩
  obtain ⟨γ, hγ⟩ := h g
  exact ⟨AdelicGLn.diagonal K n γ⁻¹, ⟨γ⁻¹, rfl⟩, _, hγ, by simp [map_inv]⟩

end Reduction

end

end GroundTheory.Automorphic
