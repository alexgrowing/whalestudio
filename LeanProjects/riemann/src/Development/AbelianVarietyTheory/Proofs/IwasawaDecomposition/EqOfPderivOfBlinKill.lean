import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubeRatio
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalLogEqSumOfMultiplicativeParam

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CubeSeries

open MvPowerSeries GlobalTheory.RayHoriz.CubeNorm

variable {S : Type} [CommRing S] {ρ : Type}

def blinV {K K' : Type} [Fintype K'] (M : K → K' → ℤ) : K × ρ → MvPowerSeries (K' × ρ) S :=
  fun p => ∑ i, M p.1 i • X (i, p.2)

def blin {K K' : Type} [Fintype K'] (M : K → K' → ℤ) (F : MvPowerSeries (K × ρ) S) :
    MvPowerSeries (K' × ρ) S :=
  subst (blinV (S := S) (ρ := ρ) M) F

def blin1V {K' : Type} [Fintype K'] (v : K' → ℤ) : ρ → MvPowerSeries (K' × ρ) S :=
  fun r => ∑ i, v i • X (i, r)

def blin1 {K' : Type} [Fintype K'] (v : K' → ℤ) (h : MvPowerSeries ρ S) :
    MvPowerSeries (K' × ρ) S :=
  subst (blin1V (S := S) (ρ := ρ) v) h

section Basic

variable {K K' K'' : Type} [Fintype K'] [Fintype K'']

theorem constantCoeff_blinV (M : K → K' → ℤ) (p : K × ρ) :
    constantCoeff (blinV (S := S) (ρ := ρ) M p) = 0 := by
  simp [blinV]

theorem constantCoeff_blin1V (v : K' → ℤ) (r : ρ) :
    constantCoeff (blin1V (S := S) (ρ := ρ) v r) = 0 := by
  simp [blin1V]

variable [Finite ρ]

theorem hasSubst_blinV [Finite K] (M : K → K' → ℤ) : HasSubst (blinV (S := S) (ρ := ρ) M) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_blinV M)

theorem hasSubst_blin1V (v : K' → ℤ) : HasSubst (blin1V (S := S) (ρ := ρ) v) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_blin1V v)

def blinHom [Finite K] (M : K → K' → ℤ) : MvPowerSeries (K × ρ) S →ₐ[S] MvPowerSeries (K' × ρ) S :=
  substAlgHom (hasSubst_blinV M)

theorem blinHom_apply [Finite K] (M : K → K' → ℤ) (F : MvPowerSeries (K × ρ) S) :
    blinHom M F = blin M F := by
  rw [blinHom, coe_substAlgHom]; rfl

def blin1Hom (v : K' → ℤ) : MvPowerSeries ρ S →ₐ[S] MvPowerSeries (K' × ρ) S :=
  substAlgHom (hasSubst_blin1V v)

theorem blin1Hom_apply (v : K' → ℤ) (h : MvPowerSeries ρ S) : blin1Hom v h = blin1 v h := by
  rw [blin1Hom, coe_substAlgHom]; rfl

section Ring

variable [Finite K] (M : K → K' → ℤ) (v : K' → ℤ)

@[simp] theorem blin_add (F G : MvPowerSeries (K × ρ) S) : blin M (F + G) = blin M F + blin M G := by
  simp [← blinHom_apply]
@[simp] theorem blin_sub (F G : MvPowerSeries (K × ρ) S) : blin M (F - G) = blin M F - blin M G := by
  simp [← blinHom_apply]
@[simp] theorem blin_mul (F G : MvPowerSeries (K × ρ) S) : blin M (F * G) = blin M F * blin M G := by
  simp [← blinHom_apply]
@[simp] theorem blin_neg (F : MvPowerSeries (K × ρ) S) : blin M (-F) = -blin M F := by
  simp [← blinHom_apply]
@[simp] theorem blin_zero : blin M (0 : MvPowerSeries (K × ρ) S) = 0 := by
  simp [← blinHom_apply]
@[simp] theorem blin_one : blin M (1 : MvPowerSeries (K × ρ) S) = 1 := by
  simp [← blinHom_apply]
@[simp] theorem blin_zsmul (n : ℤ) (F : MvPowerSeries (K × ρ) S) : blin M (n • F) = n • blin M F := by
  simp [← blinHom_apply]
@[simp] theorem blin_sum {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries (K × ρ) S) :
    blin M (∑ i ∈ s, F i) = ∑ i ∈ s, blin M (F i) := by
  simp [← blinHom_apply]

@[simp] theorem block_substitution_add (g h : MvPowerSeries ρ S) : blin1 v (g + h) = blin1 v g + blin1 v h := by
  simp [← blin1Hom_apply]
@[simp] theorem block_substitution_sub (g h : MvPowerSeries ρ S) : blin1 v (g - h) = blin1 v g - blin1 v h := by
  simp [← blin1Hom_apply]
@[simp] theorem block_substitution_mul (g h : MvPowerSeries ρ S) : blin1 v (g * h) = blin1 v g * blin1 v h := by
  simp [← blin1Hom_apply]
@[simp] theorem block_substitution_zero : blin1 v (0 : MvPowerSeries ρ S) = 0 := by
  simp [← blin1Hom_apply]
@[simp] theorem block_substitution_one : blin1 v (1 : MvPowerSeries ρ S) = 1 := by
  simp [← blin1Hom_apply]
@[simp] theorem block_substitution_zsmul (n : ℤ) (h : MvPowerSeries ρ S) : blin1 v (n • h) = n • blin1 v h := by
  simp [← blin1Hom_apply]

theorem constantCoeff_blin (F : MvPowerSeries (K × ρ) S) : constantCoeff (blin M F) = constantCoeff F := by
  rw [blin, GlobalTheory.FormalCalc.constantCoeff_subst_of_zero (hasSubst_blinV M) (constantCoeff_blinV M)]
  rfl

end Ring

end Basic

end GlobalTheory.CubeSeries

namespace GlobalTheory.CubeSeries

open MvPowerSeries GlobalTheory.RayHoriz.CubeNorm

variable {S : Type} [CommRing S] {ρ : Type} [Finite ρ]
variable {K K' K'' : Type} [Fintype K'] [Fintype K'']

theorem blin_X [Finite K'] (N : K' → K'' → ℤ) (k : K') (r : ρ) :
    blin N (X (k, r) : MvPowerSeries (K' × ρ) S) = ∑ j, N k j • X (j, r) := by
  rw [blin, subst_X (hasSubst_blinV N)]; rfl

theorem blin_blin [Finite K] [Finite K'] (M : K → K' → ℤ) (N : K' → K'' → ℤ) (F : MvPowerSeries (K × ρ) S) :
    blin N (blin M F) = blin (fun k j => ∑ i, M k i * N i j) F := by
  rw [blin, blin, blin, subst_comp_subst_apply (hasSubst_blinV M) (hasSubst_blinV N)]
  congr 1
  funext p
  change blin N (blinV M p) = _
  simp only [blinV, blin_sum, blin_zsmul, blin_X, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_smul]

theorem linSub_eq_blin [Finite K] [DecidableEq K'] (a : K → Finset K') (F : MvPowerSeries (K × ρ) S) :
    linSub a F = blin (fun k i => if i ∈ a k then 1 else 0) F := by
  rw [linSub, blin]
  congr 1
  funext p
  simp [blinV, ite_smul, Finset.sum_ite_mem]

end GlobalTheory.CubeSeries

namespace GlobalTheory.CubeSeries

open MvPowerSeries GlobalTheory.RayHoriz.CubeNorm

variable {S : Type} [CommRing S] {ρ : Type} [Fintype ρ] [DecidableEq ρ]
variable {K K' : Type} [Fintype K] [Fintype K'] [DecidableEq K']

theorem pderiv_blin (M : K → K' → ℤ) (F : MvPowerSeries (K × ρ) S) (j : K') (r : ρ) :
    pderiv S (j, r) (blin M F) = ∑ k, M k j • blin M (pderiv S (k, r) F) := by
  rw [blin, GlobalTheory.FormalCalc.pderiv_subst (hasSubst_blinV M), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single r]
  · simp only [blinV, map_sum, map_zsmul, GlobalTheory.FormalCalc.pderiv_X_ite, Prod.mk.injEq]
    simp [smul_ite, Finset.sum_ite_eq', blin, mul_comm]
  · intro s _ hs
    simp only [blinV, map_sum, map_zsmul, GlobalTheory.FormalCalc.pderiv_X_ite, Prod.mk.injEq]
    simp [hs]
  · simp

end GlobalTheory.CubeSeries

namespace GlobalTheory.CubeSeries

open MvPowerSeries GlobalTheory.RayHoriz.CubeNorm

variable {S : Type} [CommRing S] {ρ : Type} [Fintype ρ]

def killBlock {K : Type} [DecidableEq K] (k₀ : K) : K → K → ℤ :=
  fun k i => if k = k₀ then 0 else if k = i then 1 else 0

def cubeDiff (f : MvPowerSeries ρ S) : MvPowerSeries (Fin 3 × ρ) S :=
  sumSer {0, 1, 2} f - sumSer {0, 1} f - sumSer {0, 2} f - sumSer {1, 2} f +
    sumSer {0} f + sumSer {1} f + sumSer {2} f - sumSer ∅ f

def sqDiff (p : MvPowerSeries ρ S) : MvPowerSeries (Fin 2 × ρ) S :=
  blin1 ![1, 1] p - blin1 ![1, 0] p - blin1 ![0, 1] p

def IsAddCub (G : MvPowerSeries (Fin 3 × ρ) S) : Prop :=
  linSub (K' := Fin 3) ![{0}, {1}, ∅] G = 0 ∧
  linSub (K' := Fin 3) ![{1}, {0}, {2}] G = G ∧
  linSub (K' := Fin 3) ![{0}, {2}, {1}] G = G ∧
  linSub (K' := Fin 4) ![{0, 1}, {2}, {3}] G + linSub (K' := Fin 4) ![{0}, {1}, {3}] G =
    linSub (K' := Fin 4) ![{0}, {1, 2}, {3}] G + linSub (K' := Fin 4) ![{1}, {2}, {3}] G

def IsSymCoc (A : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  blin ![![0, 1], ![1, 0]] A = A ∧
  blin (K' := Fin 3) ![![1, 1, 0], ![0, 0, 1]] A + blin (K' := Fin 3) ![![1, 0, 0], ![0, 1, 0]] A =
    blin (K' := Fin 3) ![![1, 0, 0], ![0, 1, 1]] A + blin (K' := Fin 3) ![![0, 1, 0], ![0, 0, 1]] A

def faceDeriv (G : MvPowerSeries (Fin 3 × ρ) S) (r : ρ) : MvPowerSeries (Fin 2 × ρ) S :=
  blin ![![1, 0], ![0, 1], ![0, 0]] (pderiv S ((2 : Fin 3), r) G)

end GlobalTheory.CubeSeries
