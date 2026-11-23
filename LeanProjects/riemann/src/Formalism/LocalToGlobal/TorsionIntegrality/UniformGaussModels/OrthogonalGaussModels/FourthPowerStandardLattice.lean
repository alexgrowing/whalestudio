import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.StdDataCmProof
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.Inh

open Formalism.L2.Th1.D
open Formalism.L2.Th1.Top
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual)

theorem block_diag_smul_one {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) :
    blk4 (c • (1 : Matrix n n ℂ)) = c • (1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) := by
  ext ⟨a, i⟩ ⟨a', i'⟩
  simp only [blk4, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases h1 : a = a' <;> by_cases h2 : i = i' <;> simp [h1, h2]

theorem fourth_power_standard_lattice (L : PeriodPair) (n : Type) [Fintype n] :
    pow4 (stdLat L n) = stdLat L (Fin 4 × n) := by
  ext z
  rw [Formalism.L2.Th1.H.mem_stdLat]
  constructor
  · intro hz w
    exact (Formalism.L2.Th1.H.mem_stdLat L n _).1 (hz w.1) w.2
  · intro hz a
    exact (Formalism.L2.Th1.H.mem_stdLat L n _).2 fun i => hz (a, i)

theorem imgLat_refl {V : Type} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) :
    imgLat ((LinearEquiv.refl ℂ V : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ = Λ := by
  ext x
  simp [imgLat]

theorem relIdx_self {V : Type} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) : relIdx Λ Λ = 1 := by
  simp [relIdx]

theorem cmTheta_mul_mem (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hok : CmOK a₀ b₀ c₀ dK) (ω : ℂ) (hω : ω ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice) :
    Formalism.L2.Th1.F.cmTheta b₀ dK * ω ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice := by
  have hb : Odd b₀ := Formalism.L2.Th1.H.CmData.odd_b a₀ b₀ c₀ dK hok.1 hok.2.2.1
  have hcm : Formalism.L2.Th1.CM.HasCMBy dK (cmL a₀ b₀ dK ha hdK lam hlam) :=
    Formalism.L2.Th1.F.hasCMByScale dK _ lam hlam (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ dK ha hdK hok.1 hb)
  obtain ⟨k, hk⟩ := hb
  have hθ : Formalism.L2.Th1.F.cmTheta b₀ dK = (k : ℂ) + Formalism.L2.Th1.CM.omegaK dK := by
    unfold Formalism.L2.Th1.F.cmTheta Formalism.L2.Th1.CM.omegaK
    rw [hk]
    push_cast
    ring
  rw [hθ, add_mul]
  refine Submodule.add_mem _ ?_ (hcm ω hω)
  have : (k : ℂ) * ω = k • ω := by rw [zsmul_eq_mul]
  rw [this]
  exact Submodule.smul_of_tower_mem _ k hω

theorem isLatH_std (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hok : CmOK a₀ b₀ c₀ dK) (n : Type) [Fintype n] [DecidableEq n] :
    ∃ (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ := by
  set L := cmL a₀ b₀ dK ha hdK lam hlam with hL
  refine ⟨((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ), stdLat L n,
    LinearEquiv.refl ℂ (Fin 4 × n → ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    rw [block_diag_smul_one]
    rfl
  · exact Formalism.L2.Th1.H.stdSelfDual L n
  · intro x hx
    rw [Formalism.L2.Th1.H.mem_stdLat] at hx ⊢
    intro i
    exact cmTheta_mul_mem a₀ b₀ c₀ dK ha hdK lam hlam hok (x i) (hx i)
  · rw [imgLat_refl, fourth_power_standard_lattice, relIdx_self]; exact one_ne_zero
  · rw [imgLat_refl, fourth_power_standard_lattice, relIdx_self]; exact one_ne_zero

theorem unitary_one {K : Type} [NormedField K] (σ : K →+* K) {m : Type} [Fintype m] [DecidableEq m] :
    IsUnitaryK σ (1 : Matrix m m K) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · by_cases h : a = b
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  · by_cases h : a = b
    · subst h
      rw [Finset.sum_eq_single a]
      · simp
      · intro k _ hk; simp [Matrix.one_apply_ne hk]
      · intro h; exact absurd (Finset.mem_univ a) h
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = a
      · subst hk; simp [Matrix.one_apply_ne h]
      · simp [Matrix.one_apply_ne hk]

theorem isFrameH_refl {l : ℕ} [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (ι : ℂ ≃+* ℂ_[l]) {n : Type} [Fintype n]
    [DecidableEq n] :
    IsFrameH σ ι (LinearEquiv.refl ℂ (Fin 4 × n → ℂ)) (1 : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l))
      (1 : Matrix n n ℂ_[l]) := by
  refine ⟨unitary_one σ, fun i' i w => ?_⟩
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.one_apply_eq, one_mul, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
    by_cases hw : w = (i', i)
    · subst hw; simp
    · rw [Matrix.one_apply_ne (Ne.symm hw), Pi.single_eq_of_ne (Ne.symm hw)]
      simp
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem isLTNorm_one (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 s2 : MaximalUnramifiedExtension l)
    (h2 : (g2 : ℂ_[l]) = ι L.g₂) (h3 : (g3 : ℂ_[l]) = ι L.g₃)
    (hs2 : (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 L)) : IsLTNorm l L ι g2 g3 s2 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [h2, h3, hs2]

end Formalism.L2.Th1.Top.Inh
