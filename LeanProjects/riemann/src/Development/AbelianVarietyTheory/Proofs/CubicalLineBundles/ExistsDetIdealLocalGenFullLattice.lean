import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal

open NumberField IsDedekindDomain Formalism.L2.LamCM WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

section

variable {K : Type} [Field K] [NumberField K]

theorem det_of_smul_rows {n : ℕ} (s : Fin n → 𝓞 K) (x : Fin n → Fin n → K) :
    (Matrix.of fun i => s i • x i).det = (∏ i, s i) • (Matrix.of x).det := by
  have h : (Matrix.of fun i => s i • x i) =
      Matrix.of fun i j => algebraMap (𝓞 K) K (s i) * (Matrix.of x) i j := by
    ext i j
    simp [Algebra.smul_def]
  rw [h, Matrix.det_mul_column, Algebra.smul_def, map_prod]

omit [NumberField K] in

theorem prod_notMem_asIdeal {n : ℕ} (p : HeightOneSpectrum (𝓞 K)) (s : Fin n → 𝓞 K)
    (hs : ∀ i, s i ∉ p.asIdeal) : ∏ i, s i ∉ p.asIdeal := by
  haveI := p.isPrime
  exact prod_mem (S := p.asIdeal.primeCompl) fun i _ => hs i

theorem valuation_smul_of_notMem (p : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ p.asIdeal) (c : K) :
    p.valuation K (s • c) = p.valuation K c := by
  have h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1 := by
    refine le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)
    exact (p.valuation_lt_one_iff_mem s).1 hlt
  rw [Algebra.smul_def, map_mul, h1, one_mul]

theorem valuation_smul_le (p : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (c : K) :
    p.valuation K (s • c) ≤ p.valuation K c := by
  rw [Algebra.smul_def, map_mul]
  exact mul_le_of_le_one_left' (p.valuation_le_one s)

end

theorem exists_detIdeal_isLocGen : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG → Submodule.span K (Λ : Set (Fin n → K)) = ⊤ →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin n) (Fin n) K),
        (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ Λ) →
        (∀ c ∈ Λ, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i)) →
        IsLocGen p M.det I := by
  intro K _ _ n Λ hfg hspan
  let L : MLat K n := MLat.mk Λ (fun _ => 0)
  have hcoe : (L.detIdeal : Submodule (𝓞 K) K) = L.detSub :=
    A2.detIdeal_coe L (A2.detSub_isFractional L hfg)
  have hmem : ∀ y : K, y ∈ L.detIdeal ↔ y ∈ L.detSub := fun y => by
    rw [← hcoe]; rfl
  have hI : L.detIdeal ≠ 0 := by
    obtain ⟨x, hx, hd⟩ := A2.exists_det_ne Λ hspan
    intro h0
    have h := (hmem _).2 (A2.det_mem L x hx)
    rw [h0] at h
    exact hd ((FractionalIdeal.mem_zero_iff _).1 h)
  refine ⟨L.detIdeal, hI, fun p M h1 h2 => ?_⟩
  refine (isLocGen_iff_valuation_eq p _ _).2 (le_antisymm ?_ ?_)
  · choose s hs hsM using h1
    refine (valuation_le_iff_exists_smul_mem p hI _).2 ⟨∏ i, s i, prod_notMem_asIdeal p s hs, ?_⟩
    have h := A2.det_mem L (fun i => s i • M i) hsM
    rw [det_of_smul_rows s (fun i => M i)] at h
    exact (hmem _).2 h
  · obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    rw [← hv]
    have hy' := (hmem y).1 hy
    clear hv hy
    induction hy' using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨x, hx, rfl⟩ := hd
      choose s hs hsx using fun i => h2 (x i) (hx i)
      let L' : MLat K n := MLat.mk (Submodule.span (𝓞 K) (Set.range fun i => M i)) (fun _ => 0)
      have h := A2.det_mem L' (fun i => s i • x i) hsx
      rw [A2.detSub_free L' (fun i => M i) rfl, det_of_smul_rows, Submodule.mem_span_singleton] at h
      obtain ⟨r, hr⟩ := h
      rw [← valuation_smul_of_notMem p (prod_notMem_asIdeal p s hs), ← hr]
      exact valuation_smul_le p r _
    | zero => simp
    | add a b _ _ ha hb => exact (Valuation.map_add _ a b).trans (max_le ha hb)
    | smul r a _ ha => exact (valuation_smul_le p r a).trans ha

end GlobalTheory.LamF
