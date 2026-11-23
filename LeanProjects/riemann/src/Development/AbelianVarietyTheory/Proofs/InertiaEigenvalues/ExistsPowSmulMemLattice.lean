import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LatticePowerScalar

theorem exists_pow_mul_isIntegral {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K]
    [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] {c : K} (hc : IsAlgebraic ℚ_[l] c) :
    ∃ n : ℕ, IsIntegral ℤ_[l] ((l : K) ^ n * c) := by
  have h1 : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] K).2 hc
  obtain ⟨y, hy, hyc⟩ := h1.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have h2 : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation := by
    rw [Units.inv_mul_eq_iff_eq_mul]
    exact PadicInt.unitCoeff_spec hy
  have h3 : (l : K) ^ y.valuation * c = (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (y • c) := by
    rw [← mul_smul, h2, Algebra.smul_def, map_pow, map_natCast]
  rw [h3]
  exact hyc.smul _

theorem exists_pow_smul_mem {O K V : Type} [CommRing O] [CommRing K] [Algebra O K] [AddCommGroup V]
    [Module K V] [Module O V] [IsScalarTower O K V] (p : O)
    (hp : ∀ c : K, ∃ (n : ℕ) (o : O), algebraMap O K p ^ n * c = algebraMap O K o)
    (M : Submodule O V) (v : V) (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ n : ℕ, algebraMap O K p ^ n • v ∈ M := by
  have up : ∀ (n k : ℕ) (x : V), algebraMap O K p ^ n • x ∈ M → algebraMap O K p ^ (k + n) • x ∈ M := by
    intro n k x hx
    rw [pow_add, mul_smul, ← map_pow, algebraMap_smul]
    exact M.smul_mem _ hx
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rwa [pow_zero, one_smul]⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [smul_add]
    exact M.add_mem (add_comm n m ▸ up m n x hm) (up n m y hn)
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, o, ho⟩ := hp c
    refine ⟨n + m, ?_⟩
    have h : algebraMap O K p ^ (n + m) • c • x = o • (algebraMap O K p ^ m • x) := by
      rw [← algebraMap_smul K o, ← ho, smul_smul, smul_smul, pow_add]
      congr 1
      ring
    rw [h]
    exact M.smul_mem _ hm

theorem exists_pow_smul_mem_lattice {l : ℕ} [Fact (Nat.Prime l)] (LL : FinExt l) (T : GlobalTheory.BKGal.QLat LL) :
    ∀ v ∈ Submodule.span ↥LL.1 ((T.L.T : Submodule ↥(OL LL) T.V) : Set T.V),
      ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  intro v hv
  have hl : algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL)) = (l : ↥LL.1) := map_natCast _ l
  rw [← hl]
  refine exists_pow_smul_mem (l : ↥(OL LL)) (fun c => ?_) T.L.T v hv
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨n, hn⟩ := exists_pow_mul_isIntegral (l := l) (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) c)
  exact ⟨n, ⟨(l : ↥LL.1) ^ n * c, hn⟩, by rw [hl]; rfl⟩

end GlobalTheory.LatticePowerScalar
