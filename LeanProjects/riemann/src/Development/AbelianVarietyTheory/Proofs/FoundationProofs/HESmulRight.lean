import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.InertSign

abbrev Lat (D : D7) (n : ℕ) : Type := Submodule (𝓞 D.host.E) (Fin n → D.host.E)

def hE (D : D7) {n : ℕ} (x y : Fin n → D.host.E) : D.host.E := ∑ i, x i * D.host.conj (y i)

def IntE (D : D7) (e : D.host.E) : Prop := e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  MulSemiringAction.toRingHom (D.host.E ≃ₐ[ℚ] D.host.E) (𝓞 D.host.E) D.host.conj

theorem sgO_coe (D : D7) (a : 𝓞 D.host.E) : ((sgO D a : 𝓞 D.host.E) : D.host.E) = D.host.conj a := rfl

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  rw [← AdLattice.star_eq_conj, ← AdLattice.star_eq_conj]
  exact star_star x

theorem sgO_sgO (D : D7) (a : 𝓞 D.host.E) : sgO D (sgO D a) = a :=
  Subtype.ext (conj_conj D a)

theorem embT_conj (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = (starRingEnd ℂ) (embT D τ x) := by
  letI := D.host.isCMField_hostE
  rw [← AdLattice.star_eq_conj]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E (embT D τ) x

theorem conj_hE (D : D7) {n : ℕ} (x y : Fin n → D.host.E) : D.host.conj (hE D x y) = hE D y x := by
  simp only [hE, map_sum, map_mul, conj_conj, mul_comm]

theorem hE_add_left (D : D7) {n : ℕ} (x x' y : Fin n → D.host.E) : hE D (x + x') y = hE D x y + hE D x' y := by
  simp only [hE, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hE_add_right (D : D7) {n : ℕ} (x y y' : Fin n → D.host.E) : hE D x (y + y') = hE D x y + hE D x y' := by
  simp only [hE, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hE_smul_left (D : D7) {n : ℕ} (a : D.host.E) (x y : Fin n → D.host.E) : hE D (a • x) y = a * hE D x y := by
  simp only [hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hE_smul_right (D : D7) {n : ℕ} (a : D.host.E) (x y : Fin n → D.host.E) :
    hE D x (a • y) = D.host.conj a * hE D x y := by
  simp only [hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem IntE.conj {D : D7} {e : D.host.E} (h : IntE D e) : IntE D (D.host.conj e) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨sgO D a, rfl⟩

theorem sd_iff (D : D7) {n : ℕ} (L : Lat D n) : SD D L ↔
    L.FG ∧ Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IntE D (hE D y x) := by
  unfold SD IsSDLat
  simp only [stdH, AdLattice.star_eq_conj, IntE, hE, mul_comm]

def nbM (D : D7) {n : ℕ} (B : Lat D n) (x : Fin n → D.host.E) : Lat D n where
  carrier := {y | y ∈ B ∧ IntE D (hE D y x)}
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, by rw [hE_add_left]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨B.zero_mem, by simp only [hE, Pi.zero_apply, zero_mul, Finset.sum_const_zero]; exact zero_mem _⟩
  smul_mem' := fun c a ha => ⟨B.smul_mem c ha.1, by
    rw [← algebraMap_smul D.host.E c a, hE_smul_left]; exact mul_mem ⟨c, rfl⟩ ha.2⟩

theorem mem_nbM {D : D7} {n : ℕ} {B : Lat D n} {x y : Fin n → D.host.E} :
    y ∈ nbM D B x ↔ y ∈ B ∧ IntE D (hE D y x) := Iff.rfl

def nbr (D : D7) {n : ℕ} (B : Lat D n) (x : Fin n → D.host.E) : Lat D n :=
  nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {x}

def NbD (D : D7) {n : ℕ} (P : Ideal (𝓞 D.host.E)) (B : Lat D n) (x : Fin n → D.host.E) : Prop :=
  x ∉ B ∧ (∀ p ∈ P, p • x ∈ B) ∧ IntE D (hE D x x)

def Tri (D : D7) {n : ℕ} (P : Ideal (𝓞 D.host.E)) (A B C : Lat D n) : Prop :=
  SD D A ∧ SD D B ∧ SD D C ∧ ∃ (M : Lat D n) (b x : Fin n → D.host.E),
    A = M ⊔ Submodule.span (𝓞 D.host.E) {b + x} ∧ B = M ⊔ Submodule.span (𝓞 D.host.E) {b} ∧
    C = M ⊔ Submodule.span (𝓞 D.host.E) {x} ∧ (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) ∧ ¬ IntE D (hE D b x)

def Bet (D : D7) {n : ℕ} (L₁ L₂ L₃ : Lat D n) : Prop := L₂ ≤ (L₁ ⊓ L₂) ⊔ (L₂ ⊓ L₃) ∧ L₁ ⊓ L₃ ≤ L₂

def cT (D : D7) {m n : ℕ} (s : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  (s.map D.host.conj).transpose

def SAt (D : D7) {n : ℕ} (q : ℕ) (s : Matrix (Fin n) (Fin n) D.host.E) (L L₁ : Lat D n) : Prop :=
  ∃ m : ℕ, Nat.Coprime m q ∧ (∀ v ∈ L, (m : D.host.E) • s.mulVec v ∈ L₁) ∧
    ∀ v ∈ L₁, (m : D.host.E) • (cT D s).mulVec v ∈ L

def Iid (D : D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ c ∈ cc, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    t = ((c : D.host.K) : D.host.E) * a}

def RL (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (L : Lat D N) (L' : Lat D N') :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E) {z | ∃ t ∈ Iid D cc, ∃ A ∈ homL D L L', z = t • A}

def bc (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I *
    ((Real.sqrt D.host.d * (Hf D T x y).re + (Hf D T x y).im : ℝ) : ℂ))

theorem Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x x' y : VC D N N') :
    Hf D T (x + x') y = Hf D T x y + Hf D T x' y := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y y' : VC D N N') :
    Hf D T x (y + y') = Hf D T x y + Hf D T x y' := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

theorem Hf_conj (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    (starRingEnd ℂ) (Hf D T x y) = Hf D T y x := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem bc_ne_zero (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : bc D T x y ≠ 0 := Complex.exp_ne_zero _

theorem bc_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x x' y : VC D N N') :
    bc D T (x + x') y = bc D T x y * bc D T x' y := by
  rw [bc, bc, bc, ← Complex.exp_add, Hf_add_left, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem bc_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y y' : VC D N N') :
    bc D T x (y + y') = bc D T x y * bc D T x y' := by
  rw [bc, bc, bc, ← Complex.exp_add, Hf_add_right, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem bc_zero_left (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') : bc D T 0 y = 1 := by
  have h := bc_add_left D T 0 0 y
  rw [add_zero] at h
  exact (mul_eq_left₀ (bc_ne_zero D T 0 y)).1 h.symm

theorem bc_zero_right (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : bc D T x 0 = 1 := by
  have h := bc_add_right D T x 0 0
  rw [add_zero] at h
  exact (mul_eq_left₀ (bc_ne_zero D T x 0)).1 h.symm

theorem bc_comm (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T x y).im : ℂ)) * bc D T y x := by
  rw [bc, bc, ← Complex.exp_add, ← Hf_conj D T x y, Complex.conj_re, Complex.conj_im]
  congr 1; push_cast; ring

theorem Wd_Wd (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = bc D T x y • Wd D T (x + y) F := by
  funext z
  have hc := Hf_conj D T x y
  have hre : (Hf D T y x).re = (Hf D T x y).re := by rw [← hc, Complex.conj_re]
  have h2 : Hf D T y x = Hf D T x y - 2 * Complex.I * ((Hf D T x y).im : ℂ) := by
    rw [← hc]; apply Complex.ext <;> simp <;> ring
  simp only [Wd, U, wdPh, ee, bc, qH, Pi.smul_apply, smul_eq_mul, Hf_add_left, Hf_add_right, Complex.add_re, hre,
    add_assoc]
  rw [h2]
  have key : ∀ a b c d' e f g' : ℂ, ∀ v : ℂ, a + b + c + d' = e + f + g' →
      Complex.exp a * (Complex.exp b * (v * Complex.exp c) * Complex.exp d') =
        Complex.exp e * (Complex.exp f * (v * Complex.exp g')) := by
    intro a b c d' e f g' v h
    have := congrArg Complex.exp h
    simp only [Complex.exp_add] at this
    linear_combination v * this
  apply key
  push_cast; ring

theorem Wd_add (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (F G : VC D N N' → ℂ) :
    Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z; simp only [Wd, U, Pi.add_apply]; ring

theorem Wd_smul (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (a : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (a • F) = a • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

theorem Wd_zero (D : D7) (T : Tor D) {N N' : ℕ} (F : VC D N N' → ℂ) : Wd D T 0 F = F := by
  funext z; simp [Wd, U, wdPh, ee, qH, Hf]

def Nice (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) : Prop :=
  (∀ x ∈ A, ∀ F, Wd D T x F = fun z => al D T x * U D T x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, bc D T x y = 1) ∧
    ∀ x, (∀ y ∈ A, bc D T x y = bc D T y x) → x ∈ A

theorem Nice.mem_ThSp {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (h : Nice D T A)
    (F : VC D N N' → ℂ) : F ∈ ThSp D T A ↔ Differentiable ℂ F ∧ ∀ x ∈ A, Wd D T x F = F := by
  refine and_congr_right fun _ => forall₂_congr fun x hx => ?_
  rw [h.1 x hx, funext_iff]

theorem Nice.Iop_eq {D : D7} {T : Tor D} {N N' : ℕ} (A : AddSubgroup (VC D N N')) {B : AddSubgroup (VC D N N')}
    (h : Nice D T B) (F : VC D N N' → ℂ) :
    Iop D T A B F = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') F z := by
  funext z
  simp only [Iop]
  congr 1
  exact finsum_congr fun q => by rw [h.1 _ (Quotient.out q : B).2]

def Trip (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ) : Prop :=
  Nice D T A₁ ∧ Nice D T A₂ ∧ Nice D T A₃ ∧ (A₁.addSubgroupOf A₂).index ≠ 0 ∧ (A₂.addSubgroupOf A₃).index ≠ 0 ∧
    (A₁.addSubgroupOf A₃).index ≠ 0 ∧ e ∈ ThSp D T A₁ ∧ e ≠ 0 ∧ μ ^ 8 = 1 ∧
    Iop D T A₂ A₃ (Iop D T A₁ A₂ e) = fun z => μ * Iop D T A₁ A₃ e z

def Dist {V : Type} [AddCommGroup V] (A₁ A₂ A₃ : AddSubgroup V) : Prop :=
  ∀ x ∈ A₂, ∀ y ∈ A₃, x + y ∈ A₁ → x ∈ (A₁ ⊓ A₂) ⊔ (A₂ ⊓ A₃)

def TriDat (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (P : Ideal (𝓞 D.host.E)) (r : ℕ) : Prop :=
  ∃ (X Y : Fin r → 𝓞 D.host.E →+ VC D N N') (φ : Fin r → 𝓞 D.host.E →+ ℂ),
    (∀ i j a a', Hf D T (Y i a') (X j a) = if i = j then φ i (a' * sgO D a) else 0) ∧
    (∀ i a, X i a ∈ A₂ ∧ Y i a ∈ A₃ ∧ X i a + Y i a ∈ A₁) ∧
    (∀ i, ∀ p ∈ P, X i p ∈ A₁ ⊓ A₃ ∧ Y i p ∈ A₁ ⊓ A₂) ∧
    (∀ z ∈ A₂, ∃ a : Fin r → 𝓞 D.host.E, z - ∑ i, X i (a i) ∈ A₁ ⊓ A₃) ∧
    (∀ z ∈ A₃, ∃ a : Fin r → 𝓞 D.host.E, z - ∑ i, Y i (a i) ∈ A₁ ⊓ A₂) ∧
    (∀ a : Fin r → 𝓞 D.host.E, ∑ i, X i (a i) ∈ A₁ → ∀ i, a i ∈ P) ∧
    (∀ a : Fin r → 𝓞 D.host.E, ∑ i, Y i (a i) ∈ A₂ → ∀ i, a i ∈ P)

end GlobalTheory.InertSign
