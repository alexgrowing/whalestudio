import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

section Lim

variable {K : Type} [NormedField K] {a : ℕ} {ι κ : Type}

def ulim (s : ℕ → K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => coeff n (s n)

theorem ulim_sub_dvd {s : ℕ → K⟦X⟧} (h : ∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ s (n + 1) - s n) (n : ℕ) :
    (X : K⟦X⟧) ^ (n + 1) ∣ ulim s - s n := by
  have key (m k : ℕ) : (X : K⟦X⟧) ^ (m + 1) ∣ s (m + k) - s m := by
    induction k with
    | zero => simp
    | succ k ih =>
      have := dvd_add ((pow_dvd_pow _ (by omega : m + 1 ≤ m + k + 1)).trans (h (m + k))) ih
      rwa [sub_add_sub_cancel] at this
  rw [X_pow_dvd_iff]
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 hm)
  have := X_pow_dvd_iff.1 (key m k) m (Nat.lt_succ_self m)
  rw [map_sub] at this ⊢
  rw [ulim, coeff_mk, ← neg_sub, this, neg_zero]

variable (K a ι) in

def uPow (m : ℕ) : Submodule K⟦X⟧ (Vec K a ι) where
  carrier := {v | ∀ τ i, (X : K⟦X⟧) ^ m ∣ v τ i}
  add_mem' hv hw τ i := dvd_add (hv τ i) (hw τ i)
  zero_mem' _ _ := dvd_zero _
  smul_mem' c _ hv τ i := (hv τ i).mul_left c

theorem mem_uPow {m : ℕ} {v : Vec K a ι} : v ∈ uPow K a ι m ↔ ∀ τ i, (X : K⟦X⟧) ^ m ∣ v τ i :=
  Iff.rfl

theorem uPow_anti {m n : ℕ} (h : m ≤ n) : uPow K a ι n ≤ uPow K a ι m :=
  fun _ hv τ i => (pow_dvd_pow _ h).trans (hv τ i)

theorem eq_zero_of_mem_uPow {v : Vec K a ι} (h : ∀ m, v ∈ uPow K a ι (m + 1)) : v = 0 := by
  ext τ i n
  simpa using X_pow_dvd_iff.1 (h n τ i) n (Nat.lt_succ_self n)

theorem mem_uPow_one {v : Vec K a ι} : v ∈ uPow K a ι 1 ↔ red v = 0 := by
  simp [mem_uPow, X_dvd_iff, funext_iff]

theorem mem_uPow_iff_exists {m : ℕ} {v : Vec K a ι} :
    v ∈ uPow K a ι m ↔ ∃ w : Vec K a ι, v = (X : K⟦X⟧) ^ m • w := by
  constructor
  · intro h
    choose w hw using h
    exact ⟨w, funext fun τ => funext fun i => hw τ i⟩
  · rintro ⟨w, rfl⟩ τ i
    exact Dvd.intro _ rfl

theorem X_smul_mem_uPow (w : Vec K a ι) : (X : K⟦X⟧) • w ∈ uPow K a ι 1 :=
  mem_uPow_iff_exists.2 ⟨w, by simp⟩

theorem dvd_mulVec [Fintype ι] {c : K⟦X⟧} (Y : Matrix κ ι K⟦X⟧) {v : ι → K⟦X⟧} (hv : ∀ i, c ∣ v i)
    (j : κ) : c ∣ (Y *ᵥ v) j := Finset.dvd_sum fun i _ => (hv i).mul_left _

theorem X_pow_dvd_frob (l : ℕ) [Fact l.Prime] {m : ℕ} {f : K⟦X⟧} (h : (X : K⟦X⟧) ^ (m + 1) ∣ f) :
    (X : K⟦X⟧) ^ (m + 2) ∣ frob K l f := by
  have h1 := map_dvd (frob K l) h
  rw [map_pow, frob_X, ← pow_mul] at h1
  have := (Fact.out : l.Prime).two_le
  exact (pow_dvd_pow _ (by nlinarith)).trans h1

def geom (T : Module.End K (Vec K a ι)) : Module.End K (Vec K a ι) where
  toFun w τ i := ulim fun n => (∑ j ∈ Finset.range (n + 1), T ^ j) w τ i
  map_add' v w := by ext τ i n; simp [ulim, Finset.sum_add_distrib]
  map_smul' c w := by ext τ i n; simp [ulim, Finset.mul_sum]

def Raises (T : Module.End K (Vec K a ι)) : Prop :=
  ∀ m, ∀ v ∈ uPow K a ι (m + 1), T v ∈ uPow K a ι (m + 2)

theorem Raises.pow_mem {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) (n : ℕ) : (T ^ n) w ∈ uPow K a ι (n + 1) := by
  induction n with
  | zero => exact hw
  | succ n ih => rw [pow_succ']; exact hT n _ ih

theorem geom_sub_mem {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) (n : ℕ) :
    geom T w - (∑ j ∈ Finset.range n, T ^ j) w ∈ uPow K a ι (n + 1) := by
  have h : geom T w - (∑ j ∈ Finset.range (n + 1), T ^ j) w ∈ uPow K a ι (n + 1) := fun τ i =>
    ulim_sub_dvd (s := fun n => (∑ j ∈ Finset.range (n + 1), T ^ j) w τ i) (fun n => by
      rw [Finset.sum_range_succ _ (n + 1), LinearMap.add_apply, Pi.add_apply, Pi.add_apply,
        add_sub_cancel_left]
      exact uPow_anti n.succ.le_succ (hT.pow_mem hw (n + 1)) τ i) n
  have := add_mem h (hT.pow_mem hw n)
  rwa [Finset.sum_range_succ, LinearMap.add_apply, ← sub_sub, sub_add_cancel] at this

theorem geom_mem {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) : geom T w ∈ uPow K a ι 1 := by
  simpa using geom_sub_mem hT hw 0

theorem geom_eq {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) : geom T w = w + T (geom T w) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_uPow fun m => uPow_anti (Nat.le_succ _) ?_
  have := sub_mem (geom_sub_mem hT hw (m + 1)) (hT m _ (geom_sub_mem hT hw m))
  convert this using 1
  simp only [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum, LinearMap.add_apply,
    Module.End.mul_apply, map_sub, pow_zero, Module.End.one_apply]
  abel

def cst : (ZMod a → ι → K) →ₗ[K] Vec K a ι where
  toFun d τ i := C (d τ i)
  map_add' d d' := by ext τ i : 2; simp
  map_smul' c d := by ext τ i : 2; simp [smul_eq_C_mul]

@[simp] theorem cst_apply (d : ZMod a → ι → K) (τ : ZMod a) (i : ι) : cst d τ i = C (d τ i) := rfl

@[simp] theorem red_cst (d : ZMod a → ι → K) : red (cst d) = d := by ext τ i; simp

def derV : Module.End K (Vec K a ι) where
  toFun v τ i := PowerSeries.derivative K (v τ i)
  map_add' v w := by ext τ i : 2; simp
  map_smul' c v := by ext τ i : 2; simp

@[simp] theorem derV_apply (v : Vec K a ι) (τ : ZMod a) (i : ι) :
    derV v τ i = PowerSeries.derivative K (v τ i) := rfl

def derTot (f : ZMod a → K⟦X⟧) : ZMod a → K⟦X⟧ := fun τ => PowerSeries.derivative K (f τ)

def NTot (f : ZMod a → K⟦X⟧) : ZMod a → K⟦X⟧ := fun τ => N K (f τ)

def bas [DecidableEq ι] (i : ι) : Vec K a ι := fun _ => Pi.single i 1

theorem eq_sum_bas [Fintype ι] [DecidableEq ι] (v : Vec K a ι) :
    v = ∑ i, (fun τ => v τ i) • (bas i : Vec K a ι) := by
  ext1 τ
  ext1 j
  simp [bas, Finset.sum_apply, Pi.single_apply]

theorem cst_single [DecidableEq ι] (i : ι) :
    cst (fun _ : ZMod a => (Pi.single i 1 : ι → K)) = bas i := by
  ext1 τ
  ext1 j
  simp only [bas, cst_apply, Pi.single_apply]
  split_ifs <;> simp

end Lim

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]

namespace PhiMod

variable (P : PhiMod O K l e a ι)

theorem raises_phi : Raises P.phi := fun _ _ hv τ =>
  dvd_mulVec _ fun i => X_pow_dvd_frob l (hv (τ - 1) i)

theorem raises_smul_phi (c : K) : Raises (c • P.phi) := fun m v hv => by
  have := (uPow K a ι (m + 2)).smul_mem (C c) (P.raises_phi m v hv)
  convert this using 1
  ext τ i : 2
  simp [smul_eq_C_mul]

omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in

theorem _root_.GlobalTheory.BK.Raises.eq_zero {T : Module.End K (Vec K a ι)} (hT : Raises T) {α : Type}
    {σ : α → α} (hσ : Function.Surjective σ) {δ : α → Vec K a ι} (h1 : ∀ x, δ x ∈ uPow K a ι 1)
    (h : ∀ x, δ (σ x) = T (δ x)) (x : α) : δ x = 0 := by
  refine eq_zero_of_mem_uPow fun m => ?_
  induction m generalizing x with
  | zero => exact h1 x
  | succ m ih =>
    obtain ⟨y, rfl⟩ := hσ x
    rw [h]
    exact hT m _ (ih y)

def xiSeq (n : ℕ) : ZMod a → Matrix ι ι K⟦X⟧ :=
  (fun Y τ => P.mx τ * (Y (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C)^[n]
    fun _ => 1

theorem xiSeq_zero (τ : ZMod a) : P.xiSeq 0 τ = 1 := rfl

theorem xiSeq_succ (n : ℕ) (τ : ZMod a) : P.xiSeq (n + 1) τ =
    P.mx τ * (P.xiSeq n (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C := by
  rw [xiSeq, Function.iterate_succ_apply']
  rfl

theorem xiSeq_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 1) ∣ P.xiSeq (n + 1) τ i j - P.xiSeq n τ i j := by
  induction n generalizing τ i j with
  | zero =>
    have h := congrFun (congrFun (P.matrix_mul_inv_const_eq_one τ) i) j
    rw [zero_add, pow_one, X_dvd_iff]
    simp only [xiSeq_succ, xiSeq_zero, Matrix.map_one _ (map_zero (frob K l)) (map_one _), Matrix.mul_one, map_sub]
    rw [Matrix.mul_apply] at h ⊢
    simp only [map_sum, map_mul, Matrix.map_apply, constantCoeff_C, mx0] at h ⊢
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  | succ n ih =>
    rw [← Matrix.sub_apply, xiSeq_succ P (n + 1), xiSeq_succ P n τ, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
    rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun m _ => Dvd.dvd.mul_left ?_ _
    rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub]
    exact X_pow_dvd_frob l (ih (τ - 1) m k)

def xiMat (τ : ZMod a) : Matrix ι ι K⟦X⟧ := Matrix.of fun i j => ulim fun n => P.xiSeq n τ i j

theorem xiMat_sub_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 1) ∣ P.xiMat τ i j - P.xiSeq n τ i j :=
  ulim_sub_dvd (s := fun n => P.xiSeq n τ i j) (fun n => P.xiSeq_dvd n τ i j) n

theorem xiMat_map_constantCoeff (τ : ZMod a) : (P.xiMat τ).map constantCoeff = 1 := by
  ext i j
  have := P.xiMat_sub_dvd 0 τ i j
  rw [zero_add, pow_one, X_dvd_iff, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, xiSeq_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem mx_mul_xiMat (τ : ZMod a) :
    P.mx τ * (P.xiMat (τ - 1)).map (frob K l) = P.xiMat τ * (P.mx0 τ).map C := by
  have h : P.mx τ * (P.xiMat (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C =
      P.xiMat τ := by
    ext i j n
    have h1 : (X : K⟦X⟧) ^ (n + 2) ∣ (P.mx τ * (P.xiMat (τ - 1)).map (frob K l) *
        ((P.mxInv τ).map constantCoeff).map C) i j - P.xiSeq (n + 1) τ i j := by
      rw [← Matrix.sub_apply, xiSeq_succ, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_apply]
      refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
      rw [Matrix.mul_apply]
      refine Finset.dvd_sum fun m _ => Dvd.dvd.mul_left ?_ _
      rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub]
      exact X_pow_dvd_frob l (P.xiMat_sub_dvd n (τ - 1) m k)
    have h2 := X_pow_dvd_iff.1 (dvd_sub h1 (P.xiMat_sub_dvd (n + 1) τ i j)) n (by omega)
    rwa [sub_sub_sub_cancel_right, map_sub, sub_eq_zero] at h2
  rw [← h, Matrix.mul_assoc _ _ ((P.mx0 τ).map C), ← Matrix.map_mul, inv_const_mul_matrix_eq_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

theorem isUnit_det_xiMat (τ : ZMod a) : IsUnit (P.xiMat τ).det := by
  rw [isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, xiMat_map_constantCoeff]
  simp

def xiExt : Vec K a ι ≃ₗ[K] Vec K a ι where
  toFun w τ := P.xiMat τ *ᵥ w τ
  map_add' v w := by ext1; simp [Matrix.mulVec_add]
  map_smul' c v := by ext1; simp [Matrix.mulVec_smul]
  invFun v τ := (P.xiMat τ)⁻¹ *ᵥ v τ
  left_inv w := by ext1 τ; simp [Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ)]
  right_inv w := by ext1 τ; simp [Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)]

theorem xiExt_apply (w : Vec K a ι) (τ : ZMod a) : P.xiExt w τ = P.xiMat τ *ᵥ w τ := rfl

theorem xiExt_smul_tot (f : ZMod a → K⟦X⟧) (w : Vec K a ι) : P.xiExt (f • w) = f • P.xiExt w :=
  funext fun τ => Matrix.mulVec_smul _ (f τ) (w τ)

def xi : P.D →ₗ[K] Vec K a ι := P.xiExt.toLinearMap ∘ₗ cst

theorem xi_apply (d : P.D) : P.xi d = P.xiExt (cst d) := rfl

theorem red_xiExt (w : Vec K a ι) : red (P.xiExt w) = red w := by
  ext1 τ
  rw [red_apply, xiExt_apply, powerSeriesVecReduceModU_mulVec, xiMat_map_constantCoeff, Matrix.one_mulVec, red_apply]

@[simp] theorem red_xi (d : P.D) : red (P.xi d) = d := by rw [xi_apply, red_xiExt, red_cst]

theorem phi_xiExt (w : Vec K a ι) :
    P.phi (P.xiExt w) = P.xiExt fun τ => (P.mx0 τ).map C *ᵥ frobV l (w (τ - 1)) := by
  ext1 τ
  rw [phi_apply, xiExt_apply, xiExt_apply, Matrix.mulVec_mulVec, ← mx_mul_xiMat,
    ← Matrix.mulVec_mulVec]
  congr 1
  ext1 i
  exact RingHom.map_mulVec (frob K l).toRingHom _ _ i

theorem phi_xi (d : P.D) : P.phi (P.xi d) = P.xi (P.phiD d) := by
  rw [xi_apply, phi_xiExt, xi_apply]
  congr 1
  ext τ i : 2
  simp [phiD_apply, Matrix.mulVec, dotProduct]

variable {P} in

theorem map_xi {Q : PhiMod O K l e a κ} {g : Vec K a ι → Vec K a κ}
    (hg : ∀ v, g (P.phi v) = Q.phi (g v)) (d : P.D) : g (P.xi d) = Q.xi (red (g (P.xi d))) := by
  rw [← sub_eq_zero]
  refine Q.raises_phi.eq_zero (σ := P.phiD) P.phiD.surjective
    (δ := fun d => g (P.xi d) - Q.xi (red (g (P.xi d)))) (fun d => ?_) (fun d => ?_) d
  · rw [mem_uPow_one, map_sub, red_xi, sub_self]
  · simp only [← phi_xi, hg, red_phi, map_sub]

theorem xi_unique {s : P.D → Vec K a ι} (h0 : ∀ d, red (s d) = d)
    (h : ∀ d, P.phi (s d) = s (P.phiD d)) (d : P.D) : s d = P.xi d := by
  rw [← sub_eq_zero]
  refine P.raises_phi.eq_zero (σ := P.phiD) P.phiD.surjective
    (δ := fun d => s d - P.xi d) (fun d => ?_) (fun d => ?_) d
  · rw [mem_uPow_one, map_sub, red_xi, h0, sub_self]
  · simp only [← phi_xi, ← h, map_sub]

def nabla : Module.End K (Vec K a ι) := P.xiExt.conj derV

def conn : Module.End K (Vec K a ι) where
  toFun v := (X : K⟦X⟧) • P.nabla v
  map_add' v w := by rw [map_add, smul_add]
  map_smul' c v := by rw [map_smul, smul_comm]; rfl

theorem conn_apply (v : Vec K a ι) : P.conn v = (X : K⟦X⟧) • P.nabla v := rfl

theorem nabla_xiExt (w : Vec K a ι) : P.nabla (P.xiExt w) = P.xiExt (derV w) := by
  simp [nabla, LinearEquiv.conj_apply]

theorem conn_xiExt (w : Vec K a ι) : P.conn (P.xiExt w) = P.xiExt fun τ i => N K (w τ i) := by
  rw [conn_apply, nabla_xiExt]
  exact (P.xiExt_smul_tot (fun _ => X) _).symm

@[simp] theorem nabla_xi (d : P.D) : P.nabla (P.xi d) = 0 := by
  rw [xi_apply, nabla_xiExt, ← map_zero P.xiExt]
  congr 1
  ext τ i : 2
  simp

@[simp] theorem conn_xi (d : P.D) : P.conn (P.xi d) = 0 := by rw [conn_apply, nabla_xi, smul_zero]

theorem nabla_smul_tot (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    P.nabla (f • v) = derTot f • v + f • P.nabla v := by
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [← xiExt_smul_tot, nabla_xiExt, nabla_xiExt, ← xiExt_smul_tot, ← xiExt_smul_tot, ← map_add]
  congr 1
  ext τ i : 2
  simp [derTot, add_comm, mul_comm]

theorem conn_smul_tot (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    P.conn (f • v) = NTot f • v + f • P.conn v := by
  rw [conn_apply, nabla_smul_tot, conn_apply]
  ext τ i : 2
  simp only [derTot, NTot, N_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply', smul_eq_mul]
  ring

theorem conn_smul (f : K⟦X⟧) (v : Vec K a ι) : P.conn (f • v) = N K f • v + f • P.conn v :=
  P.conn_smul_tot (fun _ => f) v

theorem conn_mem_uPow (v : Vec K a ι) : P.conn v ∈ uPow K a ι 1 := X_smul_mem_uPow _

theorem conn_phi (v : Vec K a ι) : P.conn (P.phi v) = (l : K) • P.phi (P.conn v) := by
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [phi_xiExt, conn_xiExt, conn_xiExt, phi_xiExt, ← map_smul]
  congr 1
  ext τ i : 2
  simp only [Matrix.mulVec, dotProduct, map_sum, Pi.smul_apply, Finset.smul_sum, frobV_apply,
    Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul, N_frob, smul_comm, smul_eq_C_mul (a := (l : K)),
    map_natCast]

variable {P} in

theorem map_conn {Q : PhiMod O K l e a κ} (g : Vec K a ι →+ Vec K a κ)
    (σ : (ZMod a → K⟦X⟧) → ZMod a → K⟦X⟧) (hσ : ∀ f, σ (NTot f) = NTot (σ f))
    (hs : ∀ f v, g (f • v) = σ f • g v) (hg : ∀ v, g (P.phi v) = Q.phi (g v)) (v : Vec K a ι) :
    g (P.conn v) = Q.conn (g v) := by
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [eq_sum_bas w]
  simp only [map_sum, xiExt_smul_tot, ← cst_single, ← xi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conn_smul_tot, conn_xi, smul_zero, add_zero, hs, hs, conn_smul_tot, map_xi hg, conn_xi,
    smul_zero, add_zero, hσ]

end PhiMod

namespace PhiMod

variable (P : PhiMod O K l e a ι)

omit [Fact l.Prime] in
theorem bas_mem_M (i : ι) : bas i ∈ P.M := mem_tot.2 fun _ j => by
  simp only [bas, Pi.single_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem phi_bas (i : ι) (τ : ZMod a) : P.phi (bas i) τ = (P.mx τ).col i := by
  have : frobV l (Pi.single i (1 : K⟦X⟧)) = Pi.single i 1 := by
    ext1 j
    rw [frobV_apply, Pi.single_apply]
    split_ifs <;> simp
  simp [phi_apply, bas, this]

theorem eq_sum_phi_bas (v : Vec K a ι) :
    v = ∑ i, (fun τ => (P.mxInv τ *ᵥ v τ) i) • P.phi (bas i) := by
  ext1 τ
  conv_lhs => rw [← Matrix.one_mulVec (v τ), ← P.mx_mul_mxInv τ, ← Matrix.mulVec_mulVec]
  ext1 j
  simp only [Finset.sum_apply, Pi.smul_apply', phi_bas, Pi.smul_apply, Matrix.col_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [Fact l.Prime] in
theorem smul_tot_mem_Mext {B : Subalgebra O K⟦X⟧} {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ B)
    {v : Vec K a ι} (hv : v ∈ P.Mext B) : f • v ∈ P.Mext B :=
  mem_tot.2 fun τ i => B.mul_mem (hf τ) (mem_tot.1 hv τ i)

omit [Fact l.Prime] in
theorem smul_tot_mem_ext {B : Subalgebra O K⟦X⟧} {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ B)
    {v : Vec K a ι} (hv : v ∈ P.ext B) : f • v ∈ P.ext B :=
  mem_tot.2 fun τ => (P.extc B τ).smul_mem ⟨f τ, hf τ⟩ (mem_tot.1 hv τ)

omit [Fact l.Prime] in
theorem Mext_mono {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {v : Vec K a ι} (hv : v ∈ P.Mext B) :
    v ∈ P.Mext B' := mem_tot.2 fun τ i => h (mem_tot.1 hv τ i)

omit [Fact l.Prime] in
theorem ext_mono {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {v : Vec K a ι} (hv : v ∈ P.ext B) :
    v ∈ P.ext B' := mem_tot.2 fun τ => P.mem_extc_iff.2 fun i =>
      h (P.mem_extc_iff.1 (mem_tot.1 hv τ) i)

def lphi : Module.End K (Vec K a ι) := (l : K) • P.phi

theorem lphi_apply (v : Vec K a ι) : P.lphi v = (l : K) • P.phi v := rfl

theorem raises_lphi : Raises P.lphi := P.raises_smul_phi l

def zeta : Module.End K (Vec K a ι) := -(geom P.lphi * P.lphi * P.conn)

theorem lphi_conn_mem (y : Vec K a ι) : P.lphi (P.conn y) ∈ uPow K a ι 1 :=
  uPow_anti one_le_two (P.raises_lphi 0 _ (P.conn_mem_uPow y))

theorem zeta_mem_uPow (y : Vec K a ι) : P.zeta y ∈ uPow K a ι 1 :=
  neg_mem (geom_mem P.raises_lphi (P.lphi_conn_mem y))

theorem zeta_eq (y : Vec K a ι) : P.zeta y = P.lphi (P.zeta y - P.conn y) := by
  have h := geom_eq P.raises_lphi (P.lphi_conn_mem y)
  have h' : P.zeta y = -geom P.lphi (P.lphi (P.conn y)) := rfl
  rw [map_sub, h', map_neg]
  linear_combination (exp := 1) -h

theorem zeta_unique {y z : Vec K a ι} (h1 : z ∈ uPow K a ι 1) (h : z = P.lphi (z - P.conn y)) :
    z = P.zeta y := by
  rw [← sub_eq_zero]
  refine P.raises_lphi.eq_zero (σ := (id : Unit → Unit)) Function.surjective_id
    (δ := fun _ => z - P.zeta y) (fun _ => sub_mem h1 (P.zeta_mem_uPow y)) (fun _ => ?_) ()
  conv_lhs => rw [h, zeta_eq, ← map_sub, sub_sub_sub_cancel_right]

theorem zeta_add_sum_mem (y : Vec K a ι) (m : ℕ) :
    P.zeta y + ∑ n ∈ Finset.range m, (P.lphi ^ (n + 1)) (P.conn y) ∈ uPow K a ι (m + 1) := by
  have h := neg_mem (geom_sub_mem P.raises_lphi (P.lphi_conn_mem y) m)
  rw [neg_sub, sub_eq_neg_add, LinearMap.sum_apply] at h
  exact h

theorem zeta_phi_sub (m : Vec K a ι) : P.zeta (P.phi m - m) = P.conn (P.phi m) :=
  (P.zeta_unique (P.conn_mem_uPow _) (by
    rw [map_sub P.conn, sub_sub_cancel, lphi_apply, conn_phi])).symm

variable {P} in

theorem map_zeta {Q : PhiMod O K l e a κ} (g : Vec K a ι →ₗ[K] Vec K a κ)
    (h1 : ∀ v ∈ uPow K a ι 1, g v ∈ uPow K a κ 1) (hg : ∀ v, g (P.phi v) = Q.phi (g v))
    (hN : ∀ v, g (P.conn v) = Q.conn (g v)) (y : Vec K a ι) : g (P.zeta y) = Q.zeta (g y) :=
  Q.zeta_unique (h1 _ (P.zeta_mem_uPow y)) (by
    conv_lhs => rw [zeta_eq, lphi_apply, map_smul, hg, map_sub, hN]
    rfl)

end PhiMod

namespace Hom

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)

theorem app_smul_tot (f : ZMod a → K⟦X⟧) (v : Vec K a ι) : F.app (f • v) = f • F.app v :=
  funext fun τ => Matrix.mulVec_smul _ (f τ) (v τ)

theorem app_mem_uPow {m : ℕ} {v : Vec K a ι} (hv : v ∈ uPow K a ι m) : F.app v ∈ uPow K a κ m :=
  fun τ => dvd_mulVec _ (hv τ)

theorem app_xi (d : P.D) : F.app (P.xi d) = Q.xi (F.onD d) := by
  rw [PhiMod.map_xi F.app_phi, red_app, PhiMod.red_xi]

theorem app_conn (v : Vec K a ι) : F.app (P.conn v) = Q.conn (F.app v) :=
  PhiMod.map_conn F.app.toAddMonoidHom id (fun _ => rfl) F.app_smul_tot F.app_phi v

theorem app_nabla (v : Vec K a ι) : F.app (P.nabla v) = Q.nabla (F.app v) := by
  have h := F.app_conn v
  rw [PhiMod.conn_apply, PhiMod.conn_apply, map_smul] at h
  exact smul_right_injective _ X_ne_zero h

theorem app_zeta (y : Vec K a ι) : F.app (P.zeta y) = Q.zeta (F.app y) :=
  PhiMod.map_zeta (F.app.restrictScalars K) (fun _ => F.app_mem_uPow) F.app_phi F.app_conn y

end Hom

section Plus

def join (v : Vec K a ι) (f : ZMod a → K⟦X⟧) : Vec K a (ι ⊕ Unit) :=
  fun τ => Sum.elim (v τ) fun _ => f τ

def xVec : Vec K a (ι ⊕ Unit) := join 0 1

namespace PhiMod

variable (P : PhiMod O K l e a ι) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))

omit [Fact l.Prime] in

def plus : PhiMod O K l e a (ι ⊕ Unit) :=
  ofMatrix (fun τ => Matrix.fromBlocks (P.mx τ) (Matrix.replicateCol Unit (y τ)) 0 1)
    (fun τ => Matrix.fromBlocks (P.mxInv τ) (Matrix.replicateCol Unit (-(P.mxInv τ *ᵥ y τ))) 0 1)
    (by
      rintro τ (i | i) (j | j)
      exacts [P.mx_mem τ i j, mem_tot.1 hy τ i, zero_mem _, one_mem _])
    (by
      rintro τ (i | i) (j | j)
      exacts [P.mxInv_mem τ i j, neg_mem (Subalgebra.sum_mem _ fun k _ =>
        mul_mem (P.mxInv_mem τ i k) (mem_tot.1 hy τ k)), zero_mem _, one_mem _])
    fun τ => by
      rw [Matrix.fromBlocks_multiply, ← Matrix.replicateCol_mulVec, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, mx_mul_mxInv]
      simp [← Matrix.replicateCol_add]

theorem plus_phi_join (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (P.plus hy).phi (join v f) = join (P.phi v + frobTot K a l f • y) (frobTot K a l f) := by
  ext1 τ
  rw [phi_apply, plus, mx_ofMatrix]
  ext1 i
  rcases i with i | i <;>
    simp [join, Matrix.mulVec, dotProduct, phi_apply, Fintype.sum_sum_type, mul_comm]

def plusInl : Hom P (P.plus hy) where
  mat _ := Matrix.fromRows 1 0
  mem := by
    rintro τ (i | i) j
    · rw [Matrix.fromRows_apply_inl, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · exact zero_mem _
  comm τ := by
    rw [plus, mx_ofMatrix, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
    simp

theorem plusInl_app (v : Vec K a ι) : (P.plusInl hy).app v = join v 0 := by
  ext1 τ
  rw [Hom.app_apply, plusInl]
  ext1 i
  rcases i with i | i <;> simp [join]

theorem phi_extension_generator_eq_add : (P.plus hy).phi xVec = xVec + (P.plusInl hy).app y := by
  rw [xVec, plus_phi_join, plusInl_app]
  ext1 τ
  ext1 i
  rcases i with i | i <;> simp [join]

theorem conn_phi_extension_generator_eq_zeta : (P.plus hy).conn ((P.plus hy).phi xVec) = (P.plusInl hy).app (P.zeta y) := by
  rw [Hom.app_zeta, ← zeta_phi_sub, phi_extension_generator_eq_add, add_sub_cancel_left]

theorem plus_conn_xVec_eq : (P.plus hy).conn xVec = (P.plusInl hy).app (P.zeta y - P.conn y) := by
  rw [map_sub, ← conn_phi_extension_generator_eq_zeta, phi_extension_generator_eq_add, map_add, Hom.app_conn, add_sub_cancel_right]

variable [NormedAlgebra ℚ_[l] K] [NeZero e]

def plusProj : Hom (P.plus hy) (rankOne O K l e fun _ => 0) where
  mat _ := Matrix.fromCols 0 1
  mem := by
    rintro τ i (j | j)
    exacts [zero_mem _, one_mem _]
  comm τ := by
    have h : (rankOne O K l e fun _ : ZMod a => 0).mx τ = 1 := by
      ext1 i j
      exact (mx_rankOne (n := 0) rfl).trans (pow_zero _)
    rw [h, plus, mx_ofMatrix, Matrix.fromCols_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.fromCols_mul_fromBlocks]
    simp

theorem plusProj_app (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (P.plusProj hy).app (join v f) = fun τ _ => f τ := by
  ext1 τ
  rw [Hom.app_apply, plusProj]
  ext1 i
  simp [join]

end PhiMod

end Plus

end GlobalTheory.BK
