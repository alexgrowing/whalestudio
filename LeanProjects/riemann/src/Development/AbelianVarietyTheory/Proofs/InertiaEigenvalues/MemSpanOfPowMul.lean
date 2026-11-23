import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

set_option synthInstance.maxHeartbeats 400000
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

variable {l : ℕ} [Fact l.Prime]

def galD (g : GQ l) : Per.BdRp l →ₐ[ℤ_[l]] Per.BdRp l where
  toRingHom := Per.σDp g
  commutes' z := (GlobalTheory.MemLoc.ActLaws.σDp_aDp g _).trans (congrArg (GlobalTheory.MemLoc.aDp l) ((galA g).commutes z))

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def galOD (g : GQ l) : OD l O →ₐ[O] OD l O := Algebra.TensorProduct.map (AlgHom.id _ _) (galD g)

variable {O}

theorem TWact_smul_of {G Qp LL R : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL]
    [TopologicalSpace LL] [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (g : G) (r : R)
    (z : TW R T) : TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul x y =>
    simp only [TWact, TensorProduct.smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul,
      map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def rhoD {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l)
    (y : ι → OD l ↥(OL LL)) : ι → OD l ↥(OL LL) :=
  jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem TWact_galOD_smul {LL : FinExt l} (T : QLat LL) (h : GQ l) (g : Gl l) (c : OD l ↥(OL LL))
    (z : TW (OD l ↥(OL LL)) T) :
    TWact (galOD ↥(OL LL) h) T g (c • z) = galOD ↥(OL LL) h c • TWact (galOD ↥(OL LL) h) T g z :=
  TWact_smul_of (galOD ↥(OL LL) h) T g c z

set_option synthInstance.maxHeartbeats 400000 in

theorem rhoD_smul {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l) (c : OD l ↥(OL LL))
    (y : ι → OD l ↥(OL LL)) : rhoD T jD g (c • y) = galOD ↥(OL LL) (sQ l g) c • rhoD T jD g y := by
  have h1 : jD (c • y) = c • jD y := jD.map_smul c y
  have h2 := TWact_galOD_smul T (sQ l g) g c (jD y)
  have h3 := jD.symm.map_smul (galOD ↥(OL LL) (sQ l g) c) (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))
  exact (congrArg (fun z => jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g z)) h1).trans
    ((congrArg jD.symm h2).trans h3)

variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type}

open Classical in
variable (O) in

def hatR (f : K⟦X⟧) : Ahat O K l e := if h : f ∈ Rpi O K l e then toHat O K l e ⟨f, h⟩ else 0

theorem hatR_of_mem {f : K⟦X⟧} (h : f ∈ Rpi O K l e) : hatR O f = toHat O K l e ⟨f, h⟩ := by
  rw [hatR, dif_pos h]

def YD (v : Vec K a ι) : ι → OD l O := fun i => ϖ.iD t K (fun τ => hatR O (v τ i))

variable (K) in

def ED : OD l O := ϖ.iD t K (fun _ => Ehat O K l e)

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_Rpi_of_mem_Man {P : PhiMod O K l e a ι} {v : Vec K a ι} (hv : v ∈ P.Man) (τ : ZMod a) (i : ι) :
    v τ i ∈ Rpi O K l e :=
  mem_tot.1 (P.mem_Man.1 hv) τ i

theorem YD_add {P : PhiMod O K l e a ι} {v v' : Vec K a ι} (hv : v ∈ P.Man) (hv' : v' ∈ P.Man) :
    YD t ϖ (v + v') = YD t ϖ v + YD t ϖ v' := by
  funext i
  simp only [YD, Pi.add_apply]
  rw [← map_add]
  congr 1
  funext τ
  rw [Pi.add_apply, hatR_of_mem (O := O) (add_mem (mem_Rpi_of_mem_Man hv τ i) (mem_Rpi_of_mem_Man hv' τ i)),
    hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv τ i), hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv' τ i), ← map_add]
  rfl

theorem YD_E_pow_smul {P : PhiMod O K l e a ι} {v : Vec K a ι} (hv : v ∈ P.Man) (k : ℕ) :
    YD t ϖ (E K l e ^ k • v) = ED K t ϖ ^ k • YD t ϖ v := by
  funext i
  simp only [YD, ED, Pi.smul_apply, smul_eq_mul]
  rw [← map_pow, ← map_mul]
  congr 1
  funext τ
  have hE : E K l e ∈ Rpi O K l e := E_mem (K := K) l e _
  rw [Pi.mul_apply, Pi.pow_apply, hatR_of_mem (O := O) (mul_mem (pow_mem hE k) (mem_Rpi_of_mem_Man hv τ i)),
    hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv τ i), ← toHat_E, ← map_pow, ← map_mul]
  rfl

theorem iD_eq_YD {P : PhiMod O K l e a ι} {v : Vec K a ι} (hv : v ∈ P.Man) (i : ι) (w : ZMod a → Ahat O K l e)
    (hw : ∀ τ, algebraMap _ (AhatE O K l e) (w τ) = hat O l e (v τ i)) : ϖ.iD t K w = YD t ϖ v i := by
  simp only [YD]
  congr 1
  funext τ
  rw [hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv τ i)]
  apply algebraMap_AhatE_injective l e
  rw [hw τ]
  exact hat_coe_Rpi l e ⟨v τ i, mem_Rpi_of_mem_Man hv τ i⟩

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep

theorem mem_span_of_pow_mul {R : Type} [CommRing R] {d : R} (hd : ∀ y : R, d * y = 0 → y = 0) (p n : ℕ) {y : R}
    (h : d ^ p * y ∈ Ideal.span {d ^ (p + n)}) : y ∈ Ideal.span {d ^ n} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have h0 : d ^ p * (y - z * d ^ n) = 0 := by rw [mul_sub, ← hz, pow_add]; ring
  have h1 : ∀ p : ℕ, ∀ y : R, d ^ p * y = 0 → y = 0 := by
    intro p
    induction p with
    | zero => intro y h; simpa using h
    | succ p ih => intro y h; exact ih y (hd _ (by rw [← h, pow_succ]; ring))
  have := h1 p _ h0
  rw [sub_eq_zero] at this
  exact Ideal.mem_span_singleton'.2 ⟨z, this.symm⟩
end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tail_step (P : PhiMod O K l e a ι) (hnz : ∀ y : OD l O, ED K t ϖ * y = 0 → y = 0)
    (hman : ∀ α : ℕ, (∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) →
      ∀ w ∈ P.Mext (invL l (S O K e)), E K l e ^ α • P.xiExt w ∈ P.Man)
    (hdesc : ∀ (i : ℕ) (w : Vec K a ι), w ∈ P.Mext (invL l (S O K e)) →
      (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)))
    (α β₀ n : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) {m : Vec K a ι} (hm : m ∈ P.M)
    (hn : E K l e ^ n • P.EN m ∈ P.Man) {wx : Vec K a ι} (hwx : wx ∈ P.Mext (invL l (S O K e)))
    (hwxdef : P.xiExt wx = E K l e ^ (β₀ + n) • m) (j : ι)
    (hD1 : ED K t ϖ * YD t ϖ (E K l e ^ α • P.xiExt (fun τ k => descN K 1 (wx τ k))) j ∈
      Ideal.span {ED K t ϖ ^ (α + (β₀ + n))}) :
    YD t ϖ (E K l e ^ n • P.EN m) j ∈ Ideal.span {ED K t ϖ ^ n} := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = E K l e ^ (β₀ + n) • m := ⟨_, rfl⟩
  rw [← hxdef] at hwxdef
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = α + (β₀ + n) := ⟨_, rfl⟩
  rw [← hγ] at hD1
  have hwx1 : (fun τ k => descN K 1 (wx τ k)) = fun τ k => N K (wx τ k) := by
    funext τ k
    simp [descN, descPochhammer_one]
  have hconn : P.xiExt (fun τ k => descN K 1 (wx τ k)) = P.conn x := by
    rw [hwx1, ← P.conn_xiExt, hwxdef]
  have hcM : E K l e ^ α • P.conn x ∈ P.Man := by
    rw [← hconn]
    exact hman α hα _ (hdesc 1 wx hwx)
  have hE : E K l e ∈ Rpi O K l e := E_mem l e _
  have hD1' : YD t ϖ (E K l e ^ (α + 1) • P.conn x) j ∈ Ideal.span {ED K t ϖ ^ γ} := by
    have h1 := congrFun (YD_E_pow_smul t ϖ hcM 1) j
    rw [smul_smul, ← pow_add, add_comm 1 α, Pi.smul_apply, smul_eq_mul, pow_one] at h1
    rw [h1]
    rwa [hconn] at hD1
  have hNE : N K (E K l e) ∈ Rpi O K l e := N_mem (derivative_mem_R l hE)
  obtain ⟨y1, hy1def⟩ : ∃ y1, y1 = (((β₀ + n : ℕ) : PowerSeries K) * N K (E K l e)) • m := ⟨_, rfl⟩
  have hy1 : y1 ∈ P.Man := hy1def ▸ P.smul_mem_Man (mul_mem (natCast_mem _ _) hNE) (P.M_le_Man hm)
  have hkey : E K l e ^ (α + 1) * N K (E K l e ^ (β₀ + n)) =
      E K l e ^ γ * (((β₀ + n : ℕ) : PowerSeries K) * N K (E K l e)) := by
    rw [hγ]
    rcases Nat.eq_zero_or_pos (β₀ + n) with h0 | h0
    · rw [h0, pow_zero, Derivation.map_one_eq_zero, Nat.cast_zero]
      ring
    · obtain ⟨b, hb⟩ : ∃ b, β₀ + n = b + 1 := ⟨β₀ + n - 1, by omega⟩
      rw [hb, Derivation.leibniz_pow, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
  have hdec : E K l e ^ (α + 1) • P.conn x = E K l e ^ γ • y1 + E K l e ^ γ • P.EN m := by
    funext τ i
    rw [hxdef, P.conn_smul, hy1def, P.EN_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hγ] at hkey ⊢
    linear_combination (m τ i) * hkey
  have hγM : E K l e ^ γ • y1 ∈ P.Man := P.smul_mem_Man (pow_mem hE γ) hy1
  have hENM : E K l e ^ γ • P.EN m ∈ P.Man := by
    have h1 : E K l e ^ (α + 1) • P.conn x ∈ P.Man := by
      rw [pow_succ, mul_comm, mul_smul]
      exact P.smul_mem_Man hE hcM
    have h2 : E K l e ^ γ • P.EN m = E K l e ^ (α + 1) • P.conn x - E K l e ^ γ • y1 := by
      rw [hdec]
      abel
    rw [h2]
    exact sub_mem h1 hγM
  have hsum := congrFun (YD_add t ϖ hγM hENM) j
  rw [← hdec, Pi.add_apply] at hsum
  have hy1' : YD t ϖ (E K l e ^ γ • y1) j ∈ Ideal.span {ED K t ϖ ^ γ} := by
    rw [YD_E_pow_smul t ϖ hy1 γ, Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hEN : YD t ϖ (E K l e ^ γ • P.EN m) j ∈ Ideal.span {ED K t ϖ ^ γ} := by
    have h1 : YD t ϖ (E K l e ^ γ • P.EN m) j =
        YD t ϖ (E K l e ^ (α + 1) • P.conn x) j - YD t ϖ (E K l e ^ γ • y1) j := by
      rw [hsum]
      ring
    rw [h1]
    exact sub_mem hD1' hy1'
  have hsplit : E K l e ^ γ • P.EN m = E K l e ^ (α + β₀) • (E K l e ^ n • P.EN m) := by
    rw [smul_smul, ← pow_add, hγ, add_assoc]
  rw [hsplit, YD_E_pow_smul t ϖ hn (α + β₀), Pi.smul_apply, smul_eq_mul, hγ, ← add_assoc] at hEN
  exact mem_span_of_pow_mul hnz (α + β₀) n hEN
end GlobalTheory.GalStep
