import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqMulAddOfIsAdicComplete

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

structure BKDat (η H : ℕ) extends PhiMod O K l e a ι where

  desc : Descent toPhiMod
  nabla_mem : ∀ m ∈ toPhiMod.MM, toPhiMod.nabla m ∈ toPhiMod.MM
  EN_mem : ∀ m ∈ toPhiMod.M, toPhiMod.EN m ∈ toPhiMod.Man
  lower : ∀ m ∈ toPhiMod.M, E K l e ^ H • m ∈ toPhiMod.L
  upper : ∀ m ∈ toPhiMod.L, E K l e ^ η • m ∈ toPhiMod.M

section RankOne

variable {O K l e a}

omit [NeZero a] [TameDescentExponentData K l e a] in
theorem Ezpow_mem_A {i : ℤ} (hi : 0 ≤ i) : Ezpow K l e i ∈ A O K := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [Ezpow_natCast]
  exact pow_mem (E_mem l e _) n

def rankOneDesc (j : ℤ) (χ : TameGal K l e a →* O) :
    Descent (rankOne O K l e fun _ : ZMod a => j) :=
  Descent.ofMatrix _ (fun g _ => Matrix.of fun _ _ => C (algebraMap O K (χ g)))
    (fun g _ _ _ => by
      rw [Matrix.of_apply, ← algebraMap_eq_C]
      exact Subalgebra.algebraMap_mem _ _)
    (fun _ => by ext1 i k; simp [Subsingleton.elim i k])
    (fun g h τ => by
      ext1 i k
      have := congrFun ((ringAct g).commutes (algebraMap O K (χ h))) τ
      simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.of_apply, Matrix.map_apply, map_mul]
      exact congrArg _ this.symm)
    fun g τ => by
      ext1 i k
      simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.of_apply, Matrix.map_apply,
        mx_rankOne_eq, frob_C]
      rw [map_Ezpow l e _ (congrFun (ringAct_E g) τ), mul_comm]

theorem rankOneDesc_act (j : ℤ) (χ : TameGal K l e a →* O) (g : TameGal K l e a)
    (v : Vec K a Unit) (τ : ZMod a) : (rankOneDesc j χ).act g v τ () =
      C (algebraMap O K (χ g)) * rescale (g.root τ) (v (τ - g.shift) ()) := by
  change Descent.matAct g _ v τ () = _
  simp [Descent.matAct_apply, Matrix.mulVec, dotProduct]

variable [CompleteSpace K]

omit [NeZero a] [TameDescentExponentData K l e a] in
theorem exists_EN_bas_rankOne (j : ℤ) : ∃ γ ∈ S O K e,
    (rankOne O K l e fun _ : ZMod a => j).EN (bas ()) =
      (E K l e * γ - (j : K⟦X⟧) * N K (E K l e)) • bas () := by
  obtain ⟨γ, hγ, h⟩ := exists_nabla_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
  refine ⟨X * γ, mul_mem HasU.X_mem hγ, smul_right_injective _ (r := Ezpow K l e j)
    (Units.ne_zero _) ?_⟩
  have h1 := congrArg (fun v => E K l e • (X : K⟦X⟧) • v) h
  simp only [← PhiMod.conn_apply, PhiMod.conn_smul, smul_add, smul_smul, E_mul_N_Ezpow] at h1
  simp only [PhiMod.EN_apply, smul_smul]
  rw [mul_comm, eq_sub_of_add_eq' h1, ← sub_smul]
  congr 1
  ring

variable (O K l e a) in

def rankOneDat (η H : ℕ) (j : ℤ) (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H) (χ : TameGal K l e a →* O) :
    BKDat O K l e a Unit η H where
  toPhiMod := rankOne O K l e fun _ => j
  desc := rankOneDesc j χ
  nabla_mem _ := by
    have h (i : Unit) := PhiMod.ext_mono _ (A_le_S l e)
      (PhiMod.phi_mem_L _ ((rankOne O K l e fun _ : ZMod a => j).bas_mem_M i))
    refine PhiMod.nabla_mem_MM_of_basis _ (fun i => ?_) h
    obtain ⟨γ, hγ, h'⟩ := exists_nabla_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
    rw [phi_bas_rankOne, h', ← phi_bas_rankOne (O := O)]
    exact Submodule.smul_mem _ (⟨γ, hγ⟩ : S O K e) (h ())
  EN_mem _ hm := PhiMod.EN_mem_Man_of_basis _ (fun i => by
    obtain ⟨γ, hγ, h⟩ := exists_EN_bas_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
    rw [h]
    exact PhiMod.smul_mem_Man _ (sub_mem (mul_mem (E_mem l e _) (S_le_R l e hγ))
      (mul_mem (intCast_mem _ j) (N_mem (derivative_mem_R l (E_mem l e _)))))
      (PhiMod.M_le_Man _ (PhiMod.bas_mem_M _ _))) (PhiMod.M_le_Man _ hm)
  lower m hm := (mem_ext_rankOne j).2 fun τ => by
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Ezpow_natCast, ← Ezpow_add]
    exact mul_mem (Ezpow_mem_A (by omega)) (mem_tot.1 hm τ ())
  upper m hm := mem_tot.2 fun τ i => by
    have := mul_mem (Ezpow_mem_A (l := l) (e := e) (i := η + j) (by omega))
      ((mem_ext_rankOne j).1 hm τ)
    rwa [← mul_assoc, ← Ezpow_add, add_neg_cancel_right, Ezpow_natCast] at this

end RankOne

variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}

abbrev BKHom (D : BKDat O K l e a ι η H) (D' : BKDat O K l e a κ η' H') : Type :=
  Descent.Hom D.desc D'.desc

namespace BKDat

variable (D : BKDat O K l e a ι η H)

abbrev Y : Submodule O (Vec K a ι) := D.desc.Y η

abbrev Y' : Submodule O (Vec K a ι) := D.desc.Y' η

abbrev Yl : Submodule O (Vec K a ι) := D.desc.Yl η

abbrev Minv : Submodule O (Vec K a ι) := D.desc.Minv

abbrev Z : Submodule O D.Pol := D.desc.Z η

abbrev Zl : Submodule K D.Pol := D.desc.Zl η

structure IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) : Prop where
  chars_subset : ∀ τ, D.desc.chars τ ⊆ Sig
  jumps_subset : D.jumps ⊆ U

omit [NeZero e] in

theorem exists_conn_eq {m : Vec K a ι} (hm : m ∈ D.MM) : ∃ w ∈ D.MM, D.conn m = (X : K⟦X⟧) • w :=
  ⟨_, D.nabla_mem m hm, rfl⟩

omit [NeZero e] in
theorem conn_mem_MM {m : Vec K a ι} (hm : m ∈ D.MM) : D.conn m ∈ D.MM :=
  D.MM.smul_mem (uIn (S O K e)) (D.nabla_mem m hm)

theorem EN_mem_Man {m : Vec K a ι} (hm : m ∈ D.Man) : D.EN m ∈ D.Man :=
  D.EN_mem_Man_of_basis (fun i => D.EN_mem _ (D.bas_mem_M i)) hm

theorem EN_mem_divE {n : ℕ} {y : Vec K a ι} (hy : y ∈ divE l e n D.Man) :
    D.EN y ∈ divE l e n D.Man := by
  rw [mem_divE, D.E_pow_smul_EN]
  exact sub_mem (D.EN_mem_Man hy) (D.smul_mem_Man
    (mul_mem (natCast_mem _ n) (N_mem (derivative_mem_R l (E_mem l e _)))) hy)

omit [NeZero e] in
theorem conn_bas_mem (i : ι) : D.conn (bas i) ∈ D.Mext (RpiE O K l e) :=
  D.mem_Mext_invE_of_mem_divE (n := 1) (by rw [pow_one]; exact D.EN_mem _ (D.bas_mem_M i))

theorem hatTot_conn [CompleteSpace K] {v : Vec K a ι} (hv : v ∈ D.Mext (RpiE O K l e)) :
    D.hatTot (D.conn v) = D.connHat (D.hatTot v) := D.toPhiMod.hatTot_conn D.conn_bas_mem hv

omit [NeZero e] in

theorem smul_mem_Mext {B : Subalgebra O K⟦X⟧} (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ D.ext B) :
    E K l e ^ η • m ∈ D.Mext B :=
  D.smul_mem_Mext_of_basis (fun i => D.upper _ (D.phi_mem_L (D.bas_mem_M i))) hB hm

def Lc : Module.End K D.Pol := D.Man.mapQ D.Man D.EN fun _ => D.EN_mem_Man

@[simp] theorem Lc_cls (v : Vec K a ι) : D.Lc (D.cls v) = D.cls (D.EN v) := rfl

theorem Lc_mem_PolEta {n : ℕ} {w : D.Pol} (hw : w ∈ D.PolEta n) : D.Lc w ∈ D.PolEta n := by
  obtain ⟨y, hy, rfl⟩ := hw
  exact ⟨_, D.EN_mem_divE hy, rfl⟩

theorem actPol_Lc (g : TameGal K l e a) (w : D.Pol) :
    D.desc.actPol g (D.Lc w) = D.Lc (D.desc.actPol g w) := by
  obtain ⟨y, rfl⟩ := D.Man.mkQ_surjective w
  rw [Lc_cls, Descent.actPol_cls, Descent.actPol_cls, Lc_cls, Descent.act_EN]

theorem Lc_mem_Zl {w : D.Pol} (hw : w ∈ D.Zl) : D.Lc w ∈ D.Zl :=
  ⟨D.Lc_mem_PolEta hw.1, fun g => by rw [actPol_Lc, hw.2 g]⟩

def LcEta : Module.End K (D.PolEta η) := D.Lc.restrict fun _ => D.Lc_mem_PolEta

def LcZ : Module.End K D.Zl := D.Lc.restrict fun _ => D.Lc_mem_Zl

@[simp] theorem coe_LcZ (w : D.Zl) : (D.LcZ w : D.Pol) = D.Lc w := rfl

theorem Mon_eq (y : Vec K a ι) : D.Mon y = D.Lc (D.cls y) - D.cls (E K l e • D.zeta y) := by
  rw [PhiMod.Mon_apply, map_sub, Lc_cls]

theorem Mon_add_phi_sub (y : Vec K a ι) {m : Vec K a ι} (hm : m ∈ D.Man) :
    D.Mon (y + (D.phi m - m)) = D.Mon y := by
  rw [map_add, PhiMod.Mon_phi_sub, D.cls_eq_zero_iff.2 (D.EN_mem_Man hm), neg_zero, add_zero]

theorem Mon_mem_Zl_of_zeta_mem {y : Vec K a ι} (hy : y ∈ D.Yl)
    (hz : D.zeta y ∈ D.ext (Rpi O K l e)) : D.Mon y ∈ D.Zl := by
  refine ⟨⟨_, sub_mem (D.EN_mem_divE ?_) ?_, rfl⟩, D.desc.Mon_mem_invariants hy.2⟩
  · exact D.Mext_mono (invL_A_le_Rpi l e) hy.1
  · rw [mem_divE, Module.End.mul_apply, mulV_apply, smul_comm]
    exact D.smul_mem_Man (E_mem l e _) (D.smul_mem_Mext (A_le_Rpi l e) hz)

theorem _root_.GlobalTheory.BK.BKHom.onPol_Lc {D : BKDat O K l e a ι η H} {D' : BKDat O K l e a κ η' H'}
    (F : BKHom D D') (w : D.Pol) : F.onPol (D.Lc w) = D'.Lc (F.onPol w) := by
  obtain ⟨y, rfl⟩ := D.Man.mkQ_surjective w
  rw [Lc_cls, Hom.onPol_cls, Hom.onPol_cls, Lc_cls, Hom.app_EN]

variable {D} {y : Vec K a ι}

omit [NeZero e] in
theorem mem_invE_of_mem_Y (hy : y ∈ D.Y) : y ∈ D.Mext (invE l e (A O K)) :=
  D.mem_Mext_invE_of_mem_divE hy.1

abbrev plusMod (hy : y ∈ D.Y) : PhiMod O K l e a (ι ⊕ Unit) := D.plus (mem_invE_of_mem_Y hy)

abbrev plusDesc (hy : y ∈ D.Y) : Descent (plusMod hy) := D.desc.plus (mem_invE_of_mem_Y hy) hy.2

omit [NeZero e] in

theorem plusMod_upper (hy : y ∈ D.Y) : ∀ v ∈ (plusMod hy).L, E K l e ^ η • v ∈ (plusMod hy).M :=
  D.plus_upper _ D.upper hy.1

omit [NeZero e] in

theorem plusMod_lower (hy : y ∈ D.Y) :
    ∀ v ∈ (plusMod hy).M, E K l e ^ (H + η) • v ∈ (plusMod hy).L :=
  D.plus_lower _ (fun v hv => by
    rw [pow_add, mul_smul]
    exact D.lower _ (D.M.smul_mem (EIn l e (A O K) ^ η) hv)) (by
    rw [pow_add, mul_smul]
    exact D.lower _ hy.1)

def plusDat (hy : y ∈ D.Y) (hMon : D.Mon y = 0) (hz : ∃ w ∈ D.MM, D.zeta y = (X : K⟦X⟧) • w)
    (hH : E K l e ^ H • y ∈ D.L) : BKDat O K l e a (ι ⊕ Unit) η H where
  toPhiMod := plusMod hy
  desc := plusDesc hy
  nabla_mem _ := PhiMod.nabla_mem_MM_of_basis _ (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [D.bas_inl (mem_invE_of_mem_Y hy), ← Hom.app_phi, ← Hom.app_nabla]
      exact Hom.app_mem_ext _ (A_le_S l e) (D.nabla_mem _
        (D.ext_mono (A_le_S l e) (D.phi_mem_L (D.bas_mem_M i))))
    · obtain ⟨w, hw, h⟩ := hz
      have h1 := D.conn_phi_extension_generator_eq_zeta (mem_invE_of_mem_Y hy)
      rw [h, map_smul, PhiMod.conn_apply] at h1
      rw [PhiMod.bas_inr, smul_right_injective _ X_ne_zero h1]
      exact Hom.app_mem_ext _ (A_le_S l e) hw)
    fun i => PhiMod.ext_mono _ (A_le_S l e) (PhiMod.phi_mem_L _ (PhiMod.bas_mem_M _ i))
  EN_mem _ hm := PhiMod.EN_mem_Man_of_basis _ (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [D.bas_inl (mem_invE_of_mem_Y hy), ← Hom.app_EN]
      exact Hom.app_mem_Mext _ (A_le_Rpi l e) (D.EN_mem _ (D.bas_mem_M i))
    · rw [PhiMod.bas_inr]
      exact (D.Mon_eq_zero_iff _).1 hMon) (PhiMod.M_le_Man _ hm)
  lower := D.plus_lower _ D.lower hH
  upper := plusMod_upper hy

end BKDat

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

def avg : Module.End K (Vec K a ι) :=
  letI := Fintype.ofFinite (TameGal K l e a)
  ((Nat.card (TameGal K l e a) : K)⁻¹) • ∑ g, Δ.act g

omit [IsUltrametricDist K] in
theorem norm_card : ‖(Nat.card (TameGal K l e a) : K)‖ = 1 := by
  rw [norm_natCast_eq l, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 TameGal.not_dvd_card

theorem avg_mem_inv (v : Vec K a ι) : Δ.avg v ∈ Δ.inv := fun g => by
  let _ := Fintype.ofFinite (TameGal K l e a)
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    ← Module.End.mul_apply, ← map_mul]
  exact congrArg _ (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ => rfl)

theorem map_avg {V : Type} [AddCommGroup V] [Module K V] (f : Vec K a ι →ₗ[K] V) {v : Vec K a ι}
    (h : ∀ g, f (Δ.act g v) = f v) : f (Δ.avg v) = f v := by
  let _ := Fintype.ofFinite (TameGal K l e a)
  have h0 : (Nat.card (TameGal K l e a) : K) ≠ 0 := norm_ne_zero_iff.1 (by rw [norm_card]; simp)
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, h, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, inv_smul_smul₀ h0]

theorem avg_of_mem_inv {v : Vec K a ι} (hv : v ∈ Δ.inv) : Δ.avg v = v := Δ.map_avg LinearMap.id hv

theorem avg_mem (W : Submodule O (Vec K a ι)) {v : Vec K a ι} (h : ∀ g, Δ.act g v ∈ W) :
    Δ.avg v ∈ W := by
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) ((Nat.card (TameGal K l e a) : K)⁻¹)).2
    (by rw [norm_inv, norm_card, inv_one])
  rw [avg, LinearMap.smul_apply, LinearMap.sum_apply, ← hc, algebraMap_smul]
  exact W.smul_mem c (W.sum_mem fun g _ => h g)

theorem map_Y (η : ℕ) : (Δ.Y η).map (P.cls.restrictScalars O) = Δ.Z η := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact Δ.cls_mem_Z hy
  · obtain ⟨⟨y, hy, rfl⟩, h⟩ := Δ.mem_Z.1 hw
    exact ⟨Δ.avg y, ⟨Δ.avg_mem _ fun g => Δ.act_mem_EM g hy, Δ.avg_mem_inv y⟩, Δ.map_avg P.cls h⟩

end Descent

section Examples

omit [NeZero a] [TameDescentExponentData K l e a]

theorem Ezpow_mem_invL_A_iff {i : ℤ} : Ezpow K l e i ∈ invL l (A O K) ↔ 0 ≤ i := by
  refine ⟨fun h => not_lt.1 fun hi => ?_, fun h => le_away (A O K) _ (Ezpow_mem_A h)⟩
  have h0 : Ezpow K l e (-1 - i) ∈ invL l (A O K) := le_away _ _ (Ezpow_mem_A (by omega))
  have h1 := mul_mem h0 h
  rw [← Ezpow_add, sub_add_cancel] at h1
  have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h3 : Ezpow K l e (-1) = 0 := eq_zero_of_E_mul l e (invL_A_le_Rpi l e h1) fun n => by
    rw [h2, coeff_one, if_neg (by have := NeZero.pos e; omega)]
  exact Units.ne_zero _ h3

theorem mem_shiftE_of_le {P : PhiMod O K l e a ι} {i k : ℤ} (h : i ≤ k) {v : Vec K a ι}
    (hv : v ∈ shiftE l e k (P.Mext (invL l (A O K)))) :
    v ∈ shiftE l e i (P.Mext (invL l (A O K))) := by
  have := (P.Mext (invL l (A O K))).smul_mem
    ⟨_, (Ezpow_mem_invL_A_iff (e := e)).2 (sub_nonneg.2 h)⟩ hv
  rwa [Subalgebra.smul_def, smul_smul, ← Ezpow_add, show k - i + -k = -i by ring] at this

theorem filL_rankOne (j i : ℤ) : (rankOne O K l e fun _ : ZMod a => j).filL i =
    shiftE l e (if i ≤ j then j else j + 1)
      ((rankOne O K l e fun _ : ZMod a => j).Mext (invL l (A O K))) := by
  set P := rankOne O K l e fun _ : ZMod a => j
  have h0 : P.ext (invL l (A O K)) = shiftE l e j (P.Mext (invL l (A O K))) := by
    ext v
    exact (mem_ext_rankOne j).trans
      ⟨fun h => mem_tot.2 fun τ _ => h τ, fun h τ => mem_tot.1 h τ ()⟩
  have h1 : shiftE l e 1 (P.ext (invL l (A O K))) =
      shiftE l e (j + 1) (P.Mext (invL l (A O K))) := by
    ext v
    rw [h0, mem_shiftE, mem_shiftE, mem_shiftE, smul_smul, ← Ezpow_add, neg_add]
  rw [PhiMod.filL, h1, h0]
  split_ifs with h
  · rw [inf_of_le_left fun _ => mem_shiftE_of_le h,
      sup_of_le_left fun _ => mem_shiftE_of_le (by omega)]
  · exact sup_of_le_right (inf_le_right.trans fun _ => mem_shiftE_of_le (by omega))

theorem jumps_rankOne (j : ℤ) : (rankOne O K l e fun _ : ZMod a => j).jumps = {j} := by
  ext i
  simp only [PhiMod.jumps, Set.mem_ofPred_eq, filL_rankOne, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hi
    exact h (by simp only [show i + 1 ≤ j ↔ i ≤ j by omega])
  · rintro rfl h
    rw [if_neg (by omega), if_pos le_rfl] at h
    have h1 : Ezpow K l e i • (bas () : Vec K a Unit) ∈ shiftE l e i
        ((rankOne O K l e fun _ : ZMod a => i).Mext (invL l (A O K))) := by
      rw [mem_shiftE, smul_smul, Ezpow_neg_mul, one_smul]
      exact PhiMod.Mext_mono _ (le_away _ _)
        ((rankOne O K l e fun _ : ZMod a => i).bas_mem_M ())
    rw [← h, mem_shiftE, smul_smul, ← Ezpow_add] at h1
    have h2 := mem_tot.1 h1 0 ()
    simp only [bas, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      Ezpow_mem_invL_A_iff] at h2
    omega

end Examples

section Examples

variable [CompleteSpace K] {j : ℤ} (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H)

theorem Lc_rankOneDat (χ : TameGal K l e a →* O) :
    (rankOneDat O K l e a η H j h₁ h₂ χ).Lc
        ((rankOneDat O K l e a η H j h₁ h₂ χ).cls (Ezpow K l e (-1) • bas ())) =
      (((j + 1) * e * l : ℤ) : K) •
        (rankOneDat O K l e a η H j h₁ h₂ χ).cls (Ezpow K l e (-1) • bas ()) := by
  obtain ⟨γ, hγ, h⟩ := exists_EN_bas_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
  have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h3 : (rankOneDat O K l e a η H j h₁ h₂ χ).EN (Ezpow K l e (-1) • bas ()) =
      (((j + 1) * e * l : ℤ) : K) • Ezpow K l e (-1) • (bas () : Vec K a Unit) +
        (γ - ((j + 1) * e : ℤ)) • bas () := by
    rw [PhiMod.EN_apply, PhiMod.conn_smul, smul_add, smul_comm (E K l e) (Ezpow K l e (-1)),
      ← PhiMod.EN_apply]
    erw [h]
    rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul K⟦X⟧]
    simp only [smul_smul, ← add_smul]
    congr 1
    rw [E_mul_N_Ezpow, N_E]
    rw [E] at h2 ⊢
    push_cast
    linear_combination (γ - (j + 1) * e) * h2
  rw [BKDat.Lc_cls, h3, map_add, map_smul, add_eq_left, PhiMod.cls_eq_zero_iff]
  exact PhiMod.smul_mem_Man _ (sub_mem (S_le_R l e hγ) (intCast_mem _ _))
    (PhiMod.M_le_Man _ (PhiMod.bas_mem_M _ _))

theorem cls_mem_Z_rankOneDat (hη : 1 ≤ η) :
    (rankOneDat O K l e a η H j h₁ h₂ 1).cls (Ezpow K l e (-1) • bas ()) ∈
        (rankOneDat O K l e a η H j h₁ h₂ 1).Z ∧
      (rankOneDat O K l e a η H j h₁ h₂ 1).cls (Ezpow K l e (-1) • bas ()) ≠ 0 := by
  refine ⟨Descent.cls_mem_Z _ ⟨mem_tot.2 fun τ i => ?_, fun g => ?_⟩, fun h => ?_⟩
  · have := Ezpow_mem_A (O := O) (K := K) (l := l) (e := e) (i := η + -1) (by omega)
    rw [Ezpow_add, Ezpow_natCast] at this
    simpa [bas] using this
  · ext τ i : 2
    refine (rankOneDesc_act j 1 g _ τ).trans ?_
    simpa [bas] using map_Ezpow l e _ (congrFun (ringAct_E g) τ) (-1)
  · have h1 := mem_tot.1 ((PhiMod.cls_eq_zero_iff _).1 h) 0 ()
    have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
    have h3 := eq_zero_of_E_mul (O := O) (g := Ezpow K l e (-1)) l e (by simpa [bas] using h1)
      fun n => by rw [h2, coeff_one, if_neg (by have := NeZero.pos e; omega)]
    exact Units.ne_zero _ h3

def splitDat (χ : TameGal K l e a →* O) : BKDat O K l e a (Unit ⊕ Unit) η H :=
  BKDat.plusDat (D := rankOneDat O K l e a η H j h₁ h₂ χ) (y := 0) (zero_mem _) (map_zero _)
    ⟨0, zero_mem _, by simp⟩ (by simp)

example (χ : TameGal K l e a →* O) :
    BKHom (rankOneDat O K l e a η H j h₁ h₂ χ) (splitDat h₁ h₂ χ) :=
  Descent.plusInl _ _ (zero_mem _)

end Examples

example : BKDat ℤ_[3] ℚ_[3] 3 2 1 Unit 1 2 := rankOneDat _ _ _ _ _ 1 2 (-1) (by simp) (by simp) 1

def Descent.plusProj {P : PhiMod O K l e a ι} (Δ : Descent P) {y : Vec K a ι}
    (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv) :
    Descent.Hom (Δ.plus hy hinv) (rankOneDesc 0 1) where
  toHom := P.plusProj hy
  app_act g w := by
    rw [← join_eta w, Descent.plus_act_join, P.plusProj_app, P.plusProj_app]
    ext τ i : 2
    refine Eq.trans ?_ (rankOneDesc_act 0 1 g _ τ).symm
    simp [ringAct_apply]

theorem isOfType_rankOneDat [CompleteSpace K] {j : ℤ} (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H) :
    (rankOneDat O K l e a η H j h₁ h₂ 1).IsOfType {0} {j} where
  chars_subset := by
    rintro τ c ⟨d, hd, h⟩
    obtain ⟨ζ, hζ⟩ := TameDescentExponentData.prim (K := K) (l := l) (e := e) (a := a)
    have h1 := congrFun (h (powL l τ (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one))) ()
    have h2 := (congrArg constantCoeff (rankOneDesc_act j 1 _ _ τ)).symm.trans h1
    have h3 : (TameGal.inertia (powL l τ (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one)) :
        TameGal K l e a).root τ = ζ := by
      rw [TameGal.root, SemidirectProduct.left_inl, ← powL_add, neg_add_cancel, powL_zero]
      rfl
    have h4 : d τ () ≠ 0 := fun h0 => hd (funext fun _ => h0)
    rw [h3, ← coeff_zero_eq_constantCoeff_apply] at h2
    have h5 : ζ ^ c.val = 1 := by simpa [h4, eq_comm] using h2
    exact (ZMod.val_eq_zero c).1 (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd _).1 h5) c.val_lt)
  jumps_subset := (jumps_rankOne j).le

section Omega

omit [NeZero a] [TameDescentExponentData K l e a]

variable [TameDescentExponentData K l e 1]

omit [IsUltrametricDist K] in
theorem exists_algebraMap_eq_root (g : TameGal K l e 1) : ∃ c : O, algebraMap O K c = g.root 0 :=
  (IsUnitBall.mem_range_iff (O := O) (g.root 0)).2 (g.norm_root 0).le

variable (O) in

def omegaOne : TameGal K l e 1 →* O where
  toFun g := (exists_algebraMap_eq_root g).choose
  map_one' := IsUnitBall.inj (K := K) (by
    rw [(exists_algebraMap_eq_root _).choose_spec, TameGal.root_one, map_one])
  map_mul' g h := IsUnitBall.inj (K := K) (by
    rw [map_mul, (exists_algebraMap_eq_root _).choose_spec, (exists_algebraMap_eq_root _).choose_spec,
      (exists_algebraMap_eq_root _).choose_spec, TameGal.root_mul, Subsingleton.elim (0 - g.shift) 0])

omit [IsUltrametricDist K] in
theorem algebraMap_omegaOne (g : TameGal K l e 1) : algebraMap O K (omegaOne O g) = g.root 0 :=
  (exists_algebraMap_eq_root g).choose_spec

theorem mem_chars_rankOneDesc (j : ℤ) (c : ZMod e) :
    c ∈ (rankOneDesc (K := K) (l := l) j (omegaOne O ^ c.val)).chars 0 := by
  refine ⟨fun _ _ => 1, fun h => one_ne_zero (congrFun h ()), fun ζ => funext fun i => ?_⟩
  refine (congrArg constantCoeff (rankOneDesc_act j _ _ _ 0)).trans ?_
  simp [algebraMap_omegaOne]

end Omega

end GlobalTheory.BK
