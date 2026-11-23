import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

abbrev Vec (K : Type) (a : ℕ) (ι : Type) : Type := ZMod a → ι → K⟦X⟧

section Vecs

variable {O K : Type} [CommRing O] [NormedField K] [Algebra O K] {a : ℕ} {ι : Type}

variable (ι) in

def vecs (B : Subalgebra O K⟦X⟧) : Submodule B (ι → K⟦X⟧) where
  carrier := {v | ∀ i, v i ∈ B}
  add_mem' hv hw i := B.add_mem (hv i) (hw i)
  zero_mem' _ := B.zero_mem
  smul_mem' c _ hv i := B.mul_mem c.2 (hv i)

theorem mem_vecs {B : Subalgebra O K⟦X⟧} {v : ι → K⟦X⟧} : v ∈ vecs ι B ↔ ∀ i, v i ∈ B := Iff.rfl

def tot {B : Subalgebra O K⟦X⟧} (P : ZMod a → Submodule B (ι → K⟦X⟧)) :
    Submodule B (Vec K a ι) := Submodule.pi Set.univ P

theorem mem_tot {B : Subalgebra O K⟦X⟧} {P : ZMod a → Submodule B (ι → K⟦X⟧)} {v : Vec K a ι} :
    v ∈ tot P ↔ ∀ τ, v τ ∈ P τ := by simp [tot]

def red0 : (ι → K⟦X⟧) →ₗ[K] (ι → K) where
  toFun v i := constantCoeff (v i)
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp

@[simp] theorem powerSeriesVecReduceModU_apply (v : ι → K⟦X⟧) (i : ι) : red0 v i = constantCoeff (v i) := rfl

def red : Vec K a ι →ₗ[K] (ZMod a → ι → K) where
  toFun v τ := red0 (v τ)
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp

@[simp] theorem red_apply (v : Vec K a ι) (τ : ZMod a) : red v τ = red0 (v τ) := rfl

def frobV (l : ℕ) [Fact l.Prime] : (ι → K⟦X⟧) →ₗ[K] (ι → K⟦X⟧) where
  toFun v i := frob K l (v i)
  map_add' v w := by ext1; simp
  map_smul' c v := by ext1; simp

@[simp] theorem frobV_apply (l : ℕ) [Fact l.Prime] (v : ι → K⟦X⟧) (i : ι) :
    frobV l v i = frob K l (v i) := rfl

variable (K a) in

def frobTot (l : ℕ) [Fact l.Prime] : (ZMod a → K⟦X⟧) →ₐ[K] (ZMod a → K⟦X⟧) :=
  AlgHom.pi fun τ => (frob K l).comp (Pi.evalAlgHom K (fun _ : ZMod a => K⟦X⟧) (τ - 1))

@[simp] theorem frobTot_apply (l : ℕ) [Fact l.Prime] (f : ZMod a → K⟦X⟧) (τ : ZMod a) :
    frobTot K a l f τ = frob K l (f (τ - 1)) := rfl

theorem powerSeriesVecReduceModU_mulVec {κ : Type} [Fintype ι] (Y : Matrix κ ι K⟦X⟧) (v : ι → K⟦X⟧) :
    red0 (Y *ᵥ v) = Y.map constantCoeff *ᵥ red0 v := by
  ext i
  exact RingHom.map_mulVec constantCoeff Y v i

end Vecs

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]

structure PhiMod where

  mat : ZMod a → GL ι (invE l e (A O K))

abbrev Mc : Submodule (A O K) (ι → K⟦X⟧) := vecs ι (A O K)

namespace PhiMod

variable {O K l e a ι} (P : PhiMod O K l e a ι)

def mx (τ : ZMod a) : Matrix ι ι K⟦X⟧ :=
  (P.mat τ : Matrix ι ι (invE l e (A O K))).map (invE l e (A O K)).val

def mxInv (τ : ZMod a) : Matrix ι ι K⟦X⟧ :=
  (((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) : Matrix ι ι (invE l e (A O K))).map
    (invE l e (A O K)).val

theorem mx_mem (τ : ZMod a) (i j : ι) : P.mx τ i j ∈ invE l e (A O K) := Subtype.prop _

theorem mxInv_mem (τ : ZMod a) (i j : ι) : P.mxInv τ i j ∈ invE l e (A O K) := Subtype.prop _

theorem mx_mul_mxInv (τ : ZMod a) : P.mx τ * P.mxInv τ = 1 := by
  rw [mx, mxInv, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mxInv_mul_mx (τ : ZMod a) : P.mxInv τ * P.mx τ = 1 := by
  rw [mx, mxInv, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

def ofMatrix (Y Y' : ZMod a → Matrix ι ι K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K))
    (hY' : ∀ τ i j, Y' τ i j ∈ invE l e (A O K)) (h : ∀ τ, Y τ * Y' τ = 1) :
    PhiMod O K l e a ι where
  mat τ :=
    { val := Matrix.of fun i j => ⟨Y τ i j, hY τ i j⟩
      inv := Matrix.of fun i j => ⟨Y' τ i j, hY' τ i j⟩
      val_inv := Matrix.map_injective (f := (invE l e (A O K)).val) Subtype.val_injective (by
        dsimp only
        rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact h τ)
      inv_val := Matrix.map_injective (f := (invE l e (A O K)).val) Subtype.val_injective (by
        dsimp only
        rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact mul_eq_one_comm.1 (h τ)) }

@[simp] theorem mx_ofMatrix (Y Y' : ZMod a → Matrix ι ι K⟦X⟧)
    (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) (hY' : ∀ τ i j, Y' τ i j ∈ invE l e (A O K))
    (h : ∀ τ, Y τ * Y' τ = 1) (τ : ZMod a) : (ofMatrix Y Y' hY hY' h).mx τ = Y τ := rfl

def M (_ : PhiMod O K l e a ι) : Submodule (A O K) (Vec K a ι) := tot fun _ => Mc O K ι

def Mext (_ : PhiMod O K l e a ι) (B : Subalgebra O K⟦X⟧) : Submodule B (Vec K a ι) :=
  tot fun _ => vecs ι B

def extc (B : Subalgebra O K⟦X⟧) (τ : ZMod a) : Submodule B (ι → K⟦X⟧) :=
  Submodule.span B (Set.range (P.mx τ).col)

def ext (B : Subalgebra O K⟦X⟧) : Submodule B (Vec K a ι) := tot (P.extc B)

abbrev Lcomp (τ : ZMod a) : Submodule (A O K) (ι → K⟦X⟧) := P.extc (A O K) τ

abbrev L : Submodule (A O K) (Vec K a ι) := P.ext (A O K)

abbrev MM : Submodule (S O K e) (Vec K a ι) := P.ext (S O K e)

abbrev MMl : Submodule (invL l (S O K e)) (Vec K a ι) := P.ext (invL l (S O K e))

abbrev Lk (k : ℝ) : Submodule (R O K l k) (Vec K a ι) := P.ext (R O K l k)

def FilMM (j : ℕ) : Submodule (S O K e) (Vec K a ι) := Fil O K l e j • P.MM

theorem mem_extc {B : Subalgebra O K⟦X⟧} {τ : ZMod a} {v : ι → K⟦X⟧} :
    v ∈ P.extc B τ ↔ ∃ m ∈ vecs ι B, v = P.mx τ *ᵥ m := by
  rw [extc, Submodule.mem_span_range_iff_exists_fun]
  have key (c : ι → B) : ∑ i, c i • (P.mx τ).col i = P.mx τ *ᵥ fun i => (c i : K⟦X⟧) := by
    ext1 j
    simp [Matrix.mulVec, dotProduct, Subalgebra.smul_def, mul_comm]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, fun i => (c i).2, key c⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨fun i => ⟨m i, hm i⟩, key _⟩

theorem mem_extc_iff {B : Subalgebra O K⟦X⟧} {τ : ZMod a} {v : ι → K⟦X⟧} :
    v ∈ P.extc B τ ↔ P.mxInv τ *ᵥ v ∈ vecs ι B := by
  rw [mem_extc]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rwa [Matrix.mulVec_mulVec, mxInv_mul_mx, Matrix.one_mulVec]
  · intro h
    exact ⟨_, h, by rw [Matrix.mulVec_mulVec, mx_mul_mxInv, Matrix.one_mulVec]⟩

theorem linearIndependent_col (B : Subalgebra O K⟦X⟧) (τ : ZMod a) :
    LinearIndependent B (P.mx τ).col := by
  have h : LinearIndependent K⟦X⟧ (P.mx τ).col :=
    Matrix.linearIndependent_cols_of_det_ne_zero
      (Matrix.isUnit_det_of_right_inverse (P.mx_mul_mxInv τ)).ne_zero
  exact h.restrict_scalars' B

def basisExt (B : Subalgebra O K⟦X⟧) (τ : ZMod a) : Module.Basis ι B (P.extc B τ) :=
  Module.Basis.span (P.linearIndependent_col B τ)

@[simp] theorem coe_basisExt (B : Subalgebra O K⟦X⟧) (τ : ZMod a) (i : ι) :
    (P.basisExt B τ i : ι → K⟦X⟧) = (P.mx τ).col i :=
  congrArg Subtype.val (Module.Basis.span_apply _ i)

theorem extc_eq_span {B : Subalgebra O K⟦X⟧} (h : A O K ≤ B) (τ : ZMod a) :
    P.extc B τ = Submodule.span B (P.Lcomp τ : Set (ι → K⟦X⟧)) := by
  refine le_antisymm (Submodule.span_mono Submodule.subset_span) (Submodule.span_le.2 fun v hv => ?_)
  obtain ⟨m, hm, rfl⟩ := P.mem_extc.1 hv
  exact P.mem_extc.2 ⟨m, fun i => h (hm i), rfl⟩

theorem exists_exponents [NeZero a] : ∃ α β : ℕ, (∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) ∧
    ∀ v ∈ P.M, E K l e ^ β • v ∈ P.L := by
  have key (Y : ZMod a → Matrix ι ι K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) :
      ∃ n : ℕ, ∀ τ, ∀ m ∈ vecs ι (A O K), E K l e ^ n • (Y τ *ᵥ m) ∈ vecs ι (A O K) := by
    choose n hn using fun p : ZMod a × ι × ι => hY p.1 p.2.1 p.2.2
    refine ⟨Finset.univ.sup n, fun τ m hm i => ?_⟩
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
    rw [hc, pow_add, mul_assoc, ← mul_assoc (E K l e ^ n _)]
    exact mul_mem (pow_mem (E_mem l e _) c) (mul_mem (hn (τ, i, j)) (hm j))
  obtain ⟨α, hα⟩ := key P.mx P.mx_mem
  obtain ⟨β, hβ⟩ := key P.mxInv P.mxInv_mem
  refine ⟨α, β, fun v hv => mem_tot.2 fun τ => ?_, fun v hv => mem_tot.2 fun τ => ?_⟩
  · obtain ⟨m, hm, h⟩ := P.mem_extc.1 (mem_tot.1 hv τ)
    rw [Pi.smul_apply, h]
    exact hα τ m hm
  · rw [mem_extc_iff, Pi.smul_apply, Matrix.mulVec_smul]
    exact hβ τ _ (mem_tot.1 hv τ)

abbrev D (_ : PhiMod O K l e a ι) : Type := ZMod a → ι → K

def uL (τ : ZMod a) : Submodule (A O K) (P.Lcomp τ) := Ideal.span {uIn (A O K)} • ⊤

theorem mem_uL_iff {τ : ZMod a} {v : P.Lcomp τ} : v ∈ P.uL τ ↔ red0 (v : ι → K⟦X⟧) = 0 := by
  rw [uL, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, -, rfl⟩
    ext i
    simp [Subalgebra.smul_def]
  · intro h
    have hm := P.mem_extc_iff.1 v.2
    have h0 : red0 (P.mxInv τ *ᵥ v) = 0 := by rw [powerSeriesVecReduceModU_mulVec, h, Matrix.mulVec_zero]
    have h1 (i : ι) : X * PowerSeries.mk (fun n => coeff (n + 1) ((P.mxInv τ *ᵥ v) i)) =
        (P.mxInv τ *ᵥ v) i := by
      have := PowerSeries.eq_X_mul_shift_add_const ((P.mxInv τ *ᵥ v) i)
      rw [show constantCoeff ((P.mxInv τ *ᵥ v) i) = 0 from congrFun h0 i, map_zero,
        add_zero] at this
      exact this.symm
    refine ⟨⟨P.mx τ *ᵥ fun i => PowerSeries.mk fun n => coeff (n + 1) ((P.mxInv τ *ᵥ v) i),
      P.mem_extc.2 ⟨_, fun i n => by rw [coeff_mk]; exact hm i _, rfl⟩⟩, trivial, Subtype.ext ?_⟩
    change (X : K⟦X⟧) • (P.mx τ *ᵥ _) = _
    rw [← Matrix.mulVec_smul]
    have : ((X : K⟦X⟧) • fun i => PowerSeries.mk fun n => coeff (n + 1) ((P.mxInv τ *ᵥ v) i)) =
        P.mxInv τ *ᵥ v := funext h1
    rw [this, Matrix.mulVec_mulVec, mx_mul_mxInv, Matrix.one_mulVec]

def redQ (τ : ZMod a) : (P.Lcomp τ ⧸ (P.uL τ).restrictScalars O) →ₗ[O] (ι → K) :=
  Submodule.liftQ _ ((red0.restrictScalars O).comp ((P.Lcomp τ).subtype.restrictScalars O))
    fun _ hv => P.mem_uL_iff.1 hv

theorem redQ_injective (τ : ZMod a) : Function.Injective (P.redQ τ) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ fun _ hv => P.mem_uL_iff.2 hv)

def mx0 (τ : ZMod a) : Matrix ι ι K := (P.mx τ).map constantCoeff

theorem matrix_mul_inv_const_eq_one (τ : ZMod a) : P.mx0 τ * (P.mxInv τ).map constantCoeff = 1 := by
  rw [mx0, ← Matrix.map_mul, mx_mul_mxInv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inv_const_mul_matrix_eq_one (τ : ZMod a) : (P.mxInv τ).map constantCoeff * P.mx0 τ = 1 :=
  mul_eq_one_comm.1 (P.matrix_mul_inv_const_eq_one τ)

def phiD : P.D ≃ₗ[K] P.D where
  toFun d τ := P.mx0 τ *ᵥ d (τ - 1)
  map_add' d d' := by ext1; simp [Matrix.mulVec_add]
  map_smul' c d := by ext1; simp [Matrix.mulVec_smul]
  invFun d τ := (P.mxInv (τ + 1)).map constantCoeff *ᵥ d (τ + 1)
  left_inv d := by ext1; simp [inv_const_mul_matrix_eq_one]
  right_inv d := by ext1; simp [matrix_mul_inv_const_eq_one]

theorem phiD_apply (d : P.D) (τ : ZMod a) : P.phiD d τ = P.mx0 τ *ᵥ d (τ - 1) := rfl

variable [Fact l.Prime]

def phi : Vec K a ι →ₗ[K] Vec K a ι where
  toFun v τ := P.mx τ *ᵥ frobV l (v (τ - 1))
  map_add' v w := by ext1; simp [Matrix.mulVec_add]
  map_smul' c v := by ext1; simp [Matrix.mulVec_smul]

theorem phi_apply (v : Vec K a ι) (τ : ZMod a) :
    P.phi v τ = P.mx τ *ᵥ frobV l (v (τ - 1)) := rfl

theorem phi_smul_tot (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    P.phi (f • v) = frobTot K a l f • P.phi v := by
  ext1 τ
  rw [Pi.smul_apply', phi_apply, phi_apply, ← Matrix.mulVec_smul]
  congr 1
  ext1 i
  simp

theorem phi_smul (f : K⟦X⟧) (v : Vec K a ι) : P.phi (f • v) = frob K l f • P.phi v :=
  P.phi_smul_tot (fun _ => f) v

theorem phi_injective : Function.Injective P.phi := fun v w h => by
  ext1 τ
  ext1 i
  have := congrArg (fun x => (P.mxInv (τ + 1) *ᵥ x (τ + 1)) i) h
  simp only [phi_apply, Matrix.mulVec_mulVec, mxInv_mul_mx, Matrix.one_mulVec, add_sub_cancel_right,
    frobV_apply] at this
  exact frob_injective l this

theorem phi_mem_ext {B : Subalgebra O K⟦X⟧} (hB : ∀ f ∈ B, frob K l f ∈ B) {v : Vec K a ι}
    (hv : v ∈ P.Mext B) : P.phi v ∈ P.ext B :=
  mem_tot.2 fun τ => P.mem_extc.2 ⟨_, fun i => hB _ (mem_tot.1 hv (τ - 1) i), rfl⟩

theorem phi_mem_L {v : Vec K a ι} (hv : v ∈ P.M) : P.phi v ∈ P.L :=
  P.phi_mem_ext (fun _ => frob_mem_A l) hv

theorem L_eq_span [NeZero a] : P.L = Submodule.span (A O K) (P.phi '' P.M) := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.2 ?_)
  · rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun τ _ => ?_
    have : P.Lcomp τ ≤ (Submodule.span (A O K) (P.phi '' P.M)).comap
        (LinearMap.single (A O K) (fun _ : ZMod a => ι → K⟦X⟧) τ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span ⟨Pi.single (τ - 1) (Pi.single j 1), mem_tot.2 fun σ i => ?_, ?_⟩
      · simp only [Pi.single_apply]
        split_ifs
        · rw [Pi.single_apply]
          split_ifs
          exacts [one_mem _, zero_mem _]
        · exact zero_mem _
      · ext1 σ
        rw [phi_apply]
        by_cases h : σ = τ
        · subst h
          have : frobV l (Pi.single j (1 : K⟦X⟧)) = Pi.single j 1 := by
            ext1 i
            rw [frobV_apply, Pi.single_apply]
            split_ifs <;> simp
          simp [this]
        · simp [h]
    exact this (mem_tot.1 hv τ)
  · rintro _ ⟨v, hv, rfl⟩
    exact P.phi_mem_L hv

theorem red_phi (v : Vec K a ι) : red (P.phi v) = P.phiD (red v) := by
  ext1 τ
  rw [red_apply, phi_apply, powerSeriesVecReduceModU_mulVec, phiD_apply]
  congr 1
  ext i
  simp

variable [NormedAlgebra ℚ_[l] K]

theorem isLocalizedModule_redQ (τ : ZMod a) :
    IsLocalizedModule (Submonoid.powers (l : O)) (P.redQ τ) where
  map_units := by
    rintro ⟨_, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hl : (l : K) ^ n ≠ 0 := pow_ne_zero _ (l_ne_zero l)
    have : ⇑(algebraMap O (Module.End O (ι → K)) ((l : O) ^ n)) = fun y => (l : K) ^ n • y := by
      ext y i
      rw [Module.algebraMap_end_apply]
      simp [Algebra.smul_def]
    rw [this]
    exact (MulAction.toPerm (Units.mk0 _ hl)).bijective
  surj y := by
    choose n b hb using fun i =>
      exists_pow_mul_mem (O := O) l (((P.mxInv τ).map constantCoeff *ᵥ y) i)
    let m := Finset.univ.sup n
    refine ⟨⟨Submodule.Quotient.mk ⟨P.mx τ *ᵥ fun i =>
      C ((l : K) ^ m * ((P.mxInv τ).map constantCoeff *ᵥ y) i), P.mem_extc.2 ⟨_, fun i => ?_, rfl⟩⟩,
      ⟨_, m, rfl⟩⟩, ?_⟩
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ i))
      have : (l : K) ^ m * ((P.mxInv τ).map constantCoeff *ᵥ y) i =
          algebraMap O K ((l : O) ^ c * b i) := by
        rw [map_mul, ← hb, show m = c + n i from hc, pow_add]
        simp [mul_assoc]
      rw [this, ← algebraMap_eq_C]
      exact Subalgebra.algebraMap_mem _ _
    · change ((l : O) ^ m) • y = red0 (P.mx τ *ᵥ _)
      have : (red0 fun i => C ((l : K) ^ m * ((P.mxInv τ).map constantCoeff *ᵥ y) i)) =
          (l : K) ^ m • ((P.mxInv τ).map constantCoeff *ᵥ y) := by
        ext i; simp
      rw [powerSeriesVecReduceModU_mulVec, this, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      erw [P.matrix_mul_inv_const_eq_one τ]
      ext i
      simp [Algebra.smul_def]
  exists_of_eq h := ⟨1, by rw [P.redQ_injective τ h]⟩

end PhiMod

section Hom

variable {O K l e a ι} [Fact l.Prime] {κ μ : Type} [Fintype κ] [DecidableEq κ] [Fintype μ]
  [DecidableEq μ]

structure Hom (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) where

  mat : ZMod a → Matrix κ ι K⟦X⟧
  mem : ∀ τ i j, mat τ i j ∈ A O K
  comm : ∀ τ, mat τ * P.mx τ = Q.mx τ * (mat (τ - 1)).map (frob K l)

namespace Hom

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

def app (F : Hom P Q) : Vec K a ι →ₗ[K⟦X⟧] Vec K a κ where
  toFun v τ := F.mat τ *ᵥ v τ
  map_add' v w := by ext1; simp [Matrix.mulVec_add]
  map_smul' c v := by ext1; simp [Matrix.mulVec_smul]

theorem app_apply (F : Hom P Q) (v : Vec K a ι) (τ : ZMod a) : F.app v τ = F.mat τ *ᵥ v τ := rfl

def onD (F : Hom P Q) : P.D →ₗ[K] Q.D where
  toFun d τ := (F.mat τ).map constantCoeff *ᵥ d τ
  map_add' v w := by ext1; simp [Matrix.mulVec_add]
  map_smul' c v := by ext1; simp [Matrix.mulVec_smul]

theorem red_app (F : Hom P Q) (v : Vec K a ι) : red (F.app v) = F.onD (red v) :=
  funext fun τ => powerSeriesVecReduceModU_mulVec (F.mat τ) (v τ)

theorem app_phi (F : Hom P Q) (v : Vec K a ι) : F.app (P.phi v) = Q.phi (F.app v) := by
  ext1 τ
  rw [app_apply, P.phi_apply, Q.phi_apply, app_apply, Matrix.mulVec_mulVec, F.comm,
    ← Matrix.mulVec_mulVec]
  congr 1
  ext1 i
  exact (RingHom.map_mulVec (frob K l).toRingHom _ _ i).symm

theorem app_mem_Mext (F : Hom P Q) {B : Subalgebra O K⟦X⟧} (hB : A O K ≤ B) {v : Vec K a ι}
    (hv : v ∈ P.Mext B) : F.app v ∈ Q.Mext B :=
  mem_tot.2 fun τ i => Subalgebra.sum_mem _ fun j _ =>
    mul_mem (hB (F.mem τ i j)) (mem_tot.1 hv τ j)

theorem app_mem_M (F : Hom P Q) {v : Vec K a ι} (hv : v ∈ P.M) : F.app v ∈ Q.M :=
  F.app_mem_Mext le_rfl hv

theorem app_mem_ext (F : Hom P Q) {B : Subalgebra O K⟦X⟧} (hB : A O K ≤ B) {v : Vec K a ι}
    (hv : v ∈ P.ext B) : F.app v ∈ Q.ext B := by
  refine mem_tot.2 fun τ => ?_
  obtain ⟨m, hm, h⟩ := P.mem_extc.1 (mem_tot.1 hv τ)
  rw [app_apply, h, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec]
  exact Q.mem_extc.2 ⟨_, fun i => Subalgebra.sum_mem _ fun j _ =>
    mul_mem (hB (frob_mem_A l (F.mem _ i j))) (hm j), rfl⟩

variable (P) in

def scalar (c : O) : Hom P P where
  mat _ := algebraMap O K⟦X⟧ c • (1 : Matrix ι ι K⟦X⟧)
  mem τ i j := by
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · simp
    · simp
  comm τ := by
    have : (algebraMap O K⟦X⟧ c • (1 : Matrix ι ι K⟦X⟧)).map (frob K l) =
        algebraMap O K⟦X⟧ c • (1 : Matrix ι ι K⟦X⟧) := by
      ext1 i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, algebraMap_eq_C]
      split_ifs <;> simp
    rw [this]
    simp

theorem app_scalar (c : O) (v : Vec K a ι) : (scalar P c).app v = algebraMap O K⟦X⟧ c • v := by
  ext1 τ
  simp only [app_apply, scalar, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply]

def comp (G : Hom Q T) (F : Hom P Q) : Hom P T where
  mat τ := G.mat τ * F.mat τ
  mem τ i j := Subalgebra.sum_mem _ fun k _ => mul_mem (G.mem τ i k) (F.mem τ k j)
  comm τ := by
    rw [Matrix.mul_assoc, F.comm, ← Matrix.mul_assoc, G.comm, Matrix.mul_assoc, Matrix.map_mul]

theorem app_comp (G : Hom Q T) (F : Hom P Q) (v : Vec K a ι) :
    (G.comp F).app v = G.app (F.app v) := by
  ext1 τ
  simp only [app_apply, comp, Matrix.mulVec_mulVec]

end Hom

end Hom

section Hat

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]

variable {K} in
open Classical in

def hat (f : K⟦X⟧) : AhatE O K l e :=
  if h : f ∈ RpiE O K l e then toHatE O K l e ⟨f, h⟩ else 0

variable {O K}

theorem hat_of_mem {f : K⟦X⟧} (h : f ∈ RpiE O K l e) : hat O l e f = toHatE O K l e ⟨f, h⟩ :=
  dif_pos h

@[simp] theorem hat_coe (f : RpiE O K l e) : hat O l e (f : K⟦X⟧) = toHatE O K l e f :=
  dif_pos f.2

theorem hat_coe_Rpi (f : Rpi O K l e) :
    hat O l e (f : K⟦X⟧) = algebraMap _ _ (toHat O K l e f) := by
  rw [hat_of_mem l e (le_away _ _ f.2)]
  exact toHatE_eq l e rfl

theorem hat_coe_A (f : A O K) : hat O l e (f : K⟦X⟧) = algebraMap _ _ (ofA O K l e f) := by
  rw [show (f : K⟦X⟧) = (⟨f, A_le_Rpi l e f.2⟩ : Rpi O K l e) from rfl, hat_coe_Rpi]
  exact congrArg _ (toHat_eq_ofAl l e rfl)

theorem hat_add {f g : K⟦X⟧} (hf : f ∈ RpiE O K l e) (hg : g ∈ RpiE O K l e) :
    hat O l e (f + g) = hat O l e f + hat O l e g := by
  rw [hat_of_mem l e hf, hat_of_mem l e hg, ← map_add, ← hat_coe]
  rfl

theorem hat_mul {f g : K⟦X⟧} (hf : f ∈ RpiE O K l e) (hg : g ∈ RpiE O K l e) :
    hat O l e (f * g) = hat O l e f * hat O l e g := by
  rw [hat_of_mem l e hf, hat_of_mem l e hg, ← map_mul, ← hat_coe]
  rfl

theorem hat_E : hat O l e (E K l e) = algebraMap _ _ (Ehat O K l e) :=
  (hat_coe_Rpi l e (EIn l e _)).trans (congrArg _ (toHat_E O K l e))

theorem invE_A_le_RpiE : invE l e (A O K) ≤ RpiE O K l e := invE_le_RpiE l e (A_le_Rpi l e)

theorem invE_invL_S_le_RpiE : invE l e (invL l (S O K e)) ≤ RpiE O K l e :=
  invE_le_RpiE l e (invL_S_le_Rpi l e)

variable {ι}

variable (O) in

def hatV (v : ι → K⟦X⟧) : ι → AhatE O K l e := fun i => hat O l e (v i)

variable (O) in

def hatSpan (N : Set (ι → K⟦X⟧)) : Submodule (Ahat O K l e) (ι → AhatE O K l e) :=
  Submodule.span _ (hatV O l e '' (N ∩ vecs ι (RpiE O K l e)))

variable (O K ι) in

def Mhatc : Submodule (Ahat O K l e) (ι → AhatE O K l e) := hatSpan O l e (Mc O K ι)

theorem mem_Mhatc {w : ι → AhatE O K l e} :
    w ∈ Mhatc O K l e ι ↔ ∀ i, ∃ x : Ahat O K l e, algebraMap _ _ x = w i := by
  constructor
  · intro hw
    have : Mhatc O K l e ι ≤ Submodule.pi Set.univ fun _ => 1 := Submodule.span_le.2 <| by
      rintro _ ⟨v, ⟨hv, -⟩, rfl⟩ i -
      exact Submodule.mem_one.2 ⟨_, (hat_coe_A l e ⟨v i, hv i⟩).symm⟩
    exact fun i => Submodule.mem_one.1 (this hw i trivial)
  · intro hw
    choose x hx using hw
    have h1 : w = ∑ i, x i • hatV O l e (Pi.single i (1 : K⟦X⟧)) := by
      ext j
      have h0 : hat O l e (0 : K⟦X⟧) = 0 := (hat_coe l e 0).trans (map_zero _)
      have h1 : hat O l e (1 : K⟦X⟧) = 1 := (hat_coe l e 1).trans (map_one _)
      simp [hatV, Pi.single_apply, apply_ite (hat O l e), h0, h1, Algebra.smul_def, hx]
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, ⟨fun j => ?_, fun j => ?_⟩, rfl⟩) <;> rw [Pi.single_apply] <;> split_ifs <;> simp

namespace PhiMod

variable {l e a} (P : PhiMod O K l e a ι)

def Mhat (_ : PhiMod O K l e a ι) : Submodule (Ahat O K l e) (ZMod a → ι → AhatE O K l e) :=
  Submodule.pi Set.univ fun _ => Mhatc O K l e ι

def Lhatc (τ : ZMod a) : Submodule (Ahat O K l e) (ι → AhatE O K l e) :=
  hatSpan O l e (P.Lcomp τ)

def Lhat : Submodule (Ahat O K l e) (ZMod a → ι → AhatE O K l e) := Submodule.pi Set.univ P.Lhatc

def hatTot (_ : PhiMod O K l e a ι) (v : Vec K a ι) : ZMod a → ι → AhatE O K l e :=
  fun τ => hatV O l e (v τ)

theorem hatSpan_extc {B : Subalgebra O K⟦X⟧} (hB : B ≤ Rpi O K l e) (τ : ZMod a) :
    hatSpan O l e (P.extc B τ) =
      Submodule.span _ (Set.range fun j => hatV O l e ((P.mx τ).col j)) := by
  have hX (i j : ι) : P.mx τ i j ∈ RpiE O K l e := invE_A_le_RpiE l e (P.mx_mem τ i j)
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨v, ⟨hv, -⟩, rfl⟩
    obtain ⟨m, hm, rfl⟩ := P.mem_extc.1 hv
    refine (Submodule.mem_span_range_iff_exists_fun _).2
      ⟨fun j => toHat O K l e ⟨m j, hB (hm j)⟩, funext fun i => ?_⟩
    have : (P.mx τ *ᵥ m) i = ((∑ j, ⟨m j, le_away _ _ (hB (hm j))⟩ * ⟨P.mx τ i j, hX i j⟩ :
        RpiE O K l e) : K⟦X⟧) := by
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [hatV, this, hat_coe, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Pi.smul_apply, Algebra.smul_def, hatV, Matrix.col_apply, hat_of_mem l e (hX i j),
      toHatE_eq l e (f := ⟨m j, le_away _ _ (hB (hm j))⟩) (g := ⟨m j, hB (hm j)⟩) rfl]
  · rintro _ ⟨j, rfl⟩
    exact ⟨_, ⟨Submodule.subset_span ⟨j, rfl⟩, fun i => hX i j⟩, rfl⟩

end PhiMod

end Hat

section RankOne

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

def Eunit : (invE l e (A O K))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := invE l e (A O K)) (EIn l e (A O K))).unit

@[simp] theorem coe_Eunit : ((Eunit O K l e : invE l e (A O K)) : K⟦X⟧) = E K l e := rfl

variable {a} in

def rankOne (j : ZMod a → ℤ) : PhiMod O K l e a Unit where
  mat τ := Units.map (Matrix.scalar Unit).toMonoidHom (Eunit O K l e ^ j τ)

variable {O K l e a}

theorem mx_rankOne {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = n) :
    (rankOne O K l e j).mx τ () () = E K l e ^ n := by
  simp [PhiMod.mx, rankOne, h, Matrix.diagonal_pow]

theorem mxInv_rankOne {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = -n) :
    (rankOne O K l e j).mxInv τ () () = E K l e ^ n := by
  simp [PhiMod.mxInv, rankOne, h, ← map_inv, Matrix.diagonal_pow]

theorem mem_Lcomp_rankOne {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = n)
    {v : Unit → K⟦X⟧} :
    v ∈ (rankOne O K l e j).Lcomp τ ↔ ∃ m ∈ A O K, v () = E K l e ^ n * m := by
  rw [PhiMod.mem_extc]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m (), hm (), by simp [Matrix.mulVec, dotProduct, mx_rankOne h]⟩
  · rintro ⟨m, hm, hv⟩
    exact ⟨fun _ => m, fun _ => hm, funext fun _ => by
      simp [Matrix.mulVec, dotProduct, mx_rankOne h, hv]⟩

theorem phiD_rankOne {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = n)
    (d : (rankOne O K l e j).D) : (rankOne O K l e j).phiD d τ () = (l : K) ^ n * d (τ - 1) () := by
  simp [PhiMod.phiD_apply, PhiMod.mx0, Matrix.mulVec, dotProduct, mx_rankOne h, constantCoeff_E]

theorem one_notMem_Lcomp_rankOne (τ : ZMod a) :
    (fun _ => 1) ∉ (rankOne O K l e fun _ : ZMod a => 1).Lcomp τ := by
  rw [mem_Lcomp_rankOne (n := 1) rfl]
  rintro ⟨m, hm, h⟩
  have h1 := congrArg (fun f => ‖constantCoeff f‖) h
  simp only [map_one, norm_one, pow_one, map_mul, constantCoeff_E, norm_mul] at h1
  have h2 := hm 0
  rw [coeff_zero_eq_constantCoeff] at h2
  have := norm_l_lt_one (K := K) l
  nlinarith [norm_nonneg (l : K)]

end RankOne

example [Fact (Nat.Prime 3)] : PhiMod ℤ_[3] ℚ_[3] 3 8 2 Unit := rankOne _ _ _ _ fun _ => 5

example [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] :
    monomial (e * l) ((l.factorial : K)⁻¹) ∈ S O K e ∧
      monomial (e * l) ((l.factorial : K)⁻¹) ∉ A O K := by
  have h0 : ‖(l.factorial : K)‖ ≠ 0 := norm_ne_zero_iff.2 (natCast_ne_zero' l l.factorial_ne_zero)
  refine ⟨monomial_mem_S ?_, fun h => ?_⟩
  · rw [wS, Nat.mul_div_cancel_left _ (NeZero.pos e), norm_inv, inv_mul_cancel₀ h0]
  · have h1 := h (e * l)
    rw [coeff_monomial_same, norm_inv] at h1
    have h2 := norm_factorial_le (K := K) l l
    rw [Nat.div_self (Fact.out : l.Prime).pos, pow_one] at h2
    have h3 := h2.trans_lt (norm_l_lt_one l)
    exact absurd ((inv_le_one₀ (lt_of_le_of_ne (norm_nonneg _) h0.symm)).1 h1) (not_le.2 h3)

theorem nontrivial_Ahat [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] :
    Nontrivial (Ahat O K l e) := by
  have h : idE O K l e ^ 1 ≠ ⊤ := by
    rw [pow_one, Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : E K l e * g = 1 := congrArg Subtype.val hg
    have : (g : K⟦X⟧) = 0 := eq_zero_of_E_mul l e (invL_A_le_Rpi l e g.2) fun n => by
      rw [hg', coeff_one, if_neg (by have := NeZero.pos e; omega)]
    simp [this] at hg'
  have := Ideal.Quotient.nontrivial_iff.2 h
  exact (AdicCompletion.evalₐ (idE O K l e) 1).toRingHom.domain_nontrivial

end GlobalTheory.BK
