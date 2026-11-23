import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis.FrameCompl

variable {E : Type} [Field E]

theorem cT_mul (τ : E →+* E) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add (τ : E →+* E) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i k; simp [cT]

theorem cT_cT (τ : E →+* E) (hτ : ∀ x, τ (τ x) = x) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i k; simp [cT, hτ]

theorem cT_one (τ : E →+* E) {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) E) = 1 := by
  ext i k; simp [cT, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]

theorem cT_zero (τ : E →+* E) {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i k; simp [cT]

end GlobalTheory.SphEis.FrameCompl

open GlobalTheory.SphEis.FrameCompl in

theorem GlobalTheory.SphEis.exists_fr_of_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (j : ℕ) (C D : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) C * J * C = 0 → cT (σ : E →+* E) D * J * D = 0 → cT (σ : E →+* E) C * J * D = 1 → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ := by
  intro F E _ _ _ _ _ σ hcm n J hJ j C D hcc hdd hcd
  set τ : E →+* E := (σ : E →+* E) with hτdef
  have hτ : ∀ x, τ (τ x) = x := fun x => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm x
  have hJJ : cT τ J = J := by ext i k; exact hJ.1 i k
  have hdc : cT τ D * J * C = 1 := by
    have := congrArg (cT τ) hcd
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_one, ← Matrix.mul_assoc] at this

  let W : Submodule E (Fin n → E) :=
    LinearMap.ker (Matrix.toLin' (cT τ C * J)) ⊓ LinearMap.ker (Matrix.toLin' (cT τ D * J))
  let m := Module.finrank E W
  let b : Module.Basis (Fin m) E W := Module.finBasis E W
  let Z : Matrix (Fin n) (Fin m) E := Matrix.of fun r k => (b k : Fin n → E) r
  have hZv : ∀ u : Fin m → E, Z *ᵥ u = ((∑ k, u k • b k : W) : Fin n → E) := by
    intro u; ext r
    simp [Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hk : ∀ k, Z *ᵥ Pi.single k 1 = (b k : Fin n → E) := by
    intro k; rw [hZv]; simp [Pi.single_apply]
  have hCZ : cT τ C * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.1
  have hDZ : cT τ D * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.2
  have hZC : cT τ Z * J * C = 0 := by
    have := congrArg (cT τ) hCZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this
  have hZD : cT τ Z * J * D = 0 := by
    have := congrArg (cT τ) hDZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this

  set Pr : Matrix (Fin n) (Fin n) E := 1 - C * (cT τ D * J) - D * (cT τ C * J) with hPr
  have hCPr : cT τ C * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hcc, hcd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hDPr : cT τ D * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hdc, hdd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hmem : ∀ i, Pr *ᵥ Pi.single i 1 ∈ W := by
    intro i
    refine ⟨?_, ?_⟩
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hCPr, Matrix.zero_mulVec]
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDPr, Matrix.zero_mulVec]
  let M : Matrix (Fin m) (Fin n) E := Matrix.of fun k i => b.repr ⟨_, hmem i⟩ k
  have hZM : Z * M = Pr := by
    apply Matrix.ext_of_mulVec_single; intro i
    rw [← Matrix.mulVec_mulVec]
    have : M *ᵥ Pi.single i 1 = fun k => b.repr ⟨_, hmem i⟩ k := by
      ext k; simp [M, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hZv, b.sum_repr]
  have hdec : C * (cT τ D * J) + D * (cT τ C * J) + Z * M = 1 := by
    rw [hZM, hPr]; abel

  set J₀ : Matrix (Fin m) (Fin m) E := cT τ Z * J * Z with hJ₀
  have hJ₀h : cT τ J₀ = J₀ := by
    rw [hJ₀, cT_mul, cT_mul, cT_cT τ hτ, hJJ, Matrix.mul_assoc]
  have hCZ' : cT τ C * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hCZ
  have hDZ' : cT τ D * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hDZ
  have key : J * Z = cT τ M * J₀ := by
    have h1 : cT τ (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) = 1 := by rw [hdec, cT_one]
    rw [cT_add, cT_add, cT_mul, cT_mul, cT_mul, cT_mul, cT_mul, cT_cT τ hτ, cT_cT τ hτ, hJJ] at h1
    conv_lhs => rw [← Matrix.one_mul (J * Z), ← h1]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', Matrix.mul_zero, zero_add, hJ₀]
  have hdet : J₀.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hJz : J *ᵥ (Z *ᵥ u) = 0 := by
      rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hJz
    rw [hZv] at hz
    have hs : (∑ k, u k • b k : W) = 0 := Subtype.ext hz
    exact hu0 (funext fun k => Fintype.linearIndependent_iff.mp b.linearIndependent u hs k)
  have hinv : J₀⁻¹ * J₀ = 1 := Matrix.nonsing_inv_mul J₀ (isUnit_iff_ne_zero.mpr hdet)
  set S : Matrix (Fin n) (Fin n) E := C * (cT τ D * J) + Z * (J₀⁻¹ * (cT τ Z * J)) + D * (cT τ C * J) with hS
  have a1 : cT τ D * (J * C) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hdc
  have a2 : cT τ Z * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZC
  have a3 : cT τ C * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hcc
  have a4 : cT τ D * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hdd
  have a5 : cT τ Z * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZD
  have a6 : cT τ C * (J * D) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hcd
  have a7 : cT τ Z * (J * Z) = J₀ := (Matrix.mul_assoc _ _ _).symm
  have hSC : S * C = C := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a1, a2, a3, Matrix.mul_zero, Matrix.mul_one, add_zero]
  have hSD : S * D = D := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a4, a5, a6, Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hSZ : S * Z = Z := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', a7, Matrix.mul_zero, add_zero, zero_add]
    rw [hinv, Matrix.mul_one]
  have hS1 : S = 1 := by
    calc S = S * (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) := by rw [hdec, Matrix.mul_one]
      _ = S * C * (cT τ D * J) + S * D * (cT τ C * J) + S * Z * M := by
          simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = 1 := by rw [hSC, hSD, hSZ, hdec]
  have hdim : m + 2 * j = n := by
    have ht := congrArg Matrix.trace hS1
    rw [hS, Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm C, Matrix.trace_mul_comm Z,
      Matrix.trace_mul_comm D] at ht
    simp only [Matrix.mul_assoc, a1, a6, a7, hinv, Matrix.trace_one, Fintype.card_fin] at ht
    have : ((m + 2 * j : ℕ) : E) = (n : E) := by push_cast; rw [← ht]; ring
    exact_mod_cast this
  refine ⟨m, Z, J₀, hcm, hJ, ⟨fun i k => ?_, hdet⟩, hcc, hdd, hcd, hdc, hCZ, hDZ, hZC, hZD, rfl, hS1, hdim⟩
  have := congrFun (congrFun hJ₀h i) k
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact this
