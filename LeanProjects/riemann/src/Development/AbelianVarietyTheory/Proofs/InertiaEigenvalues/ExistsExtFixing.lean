import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt

theorem phiS_idem : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → phiS P σ L (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  intro l _ P K L _ τ σ hσ
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ
  rw [h, map_sum]
  simp only [phiS_tmul]
  have hc : ∀ i, algebraMap ↥K.1 P.R.BdR (c i) = algebraMap (Om l) P.R.BdR ((c i : ↥K.1) : Om l) := fun i => rfl
  simp only [hc, ← map_mul, ← map_sum]
  have : ∑ i, σ ((a i : ↥L.1) : Om l) * ((c i : ↥K.1) : Om l) = σ (((∑ i, a i * τ (c i) : ↥L.1)) : Om l) := by
    simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, hσ]
  rw [this, h1]
  simp

theorem phiS_mem_Fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K L : FinExt l) (σ : GQ l) (n : ℤ) (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR), r ∈ FilV (P.PD K) (LL := ↥L.1) (V := ↥L.1) n → phiS P σ L r ∈ (P.PD K).Fil n := by
  intro l _ P AI T K L σ n r hr
  have h0 : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD K).Fil 0 := by
    intro x
    rw [T.fil]
    obtain ⟨y, hy, -⟩ := T.om x
    rw [hy]
    exact ((GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.2 0 y).2 (GlobalTheory.MemLoc.FilSeed.mem_filtration_zero' y)
  refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun r => phiS P σ L r ∈ (P.PD K).Fil n) ?_ ?_ ?_ hr
  · simp
  · intro c b hb
    rw [phiS_tmul]
    simpa using (P.PD K).Fil_mul 0 n _ _ (h0 _) hb
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_ext_fixing : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (σ : GQ l), ∃ K' : FinExt l, K.1 ≤ K'.1 ∧ ∀ g ∈ GK K', ∀ y : ↥L.1, g (σ (y : Om l)) = σ (y : Om l) := by
  intro l _ K L σ
  haveI := K.2
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] ↥(L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l)) :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap L.1 (σ : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv
  refine ⟨⟨K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l), IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left, ?_⟩
  intro g hg y
  have hmem : σ (y : Om l) ∈ K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l) :=
    le_sup_right (a := K.1) ((IntermediateField.mem_map _).2 ⟨y, y.2, rfl⟩)
  exact (mem_fixingSubgroup_iff _).1 hg _ hmem

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_xi_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K : FinExt l) (k : ℤ) (q p : ℕ), k + q = p → ∀ x ∈ (P.PD K).Fil k, ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p * z) := by
  intro l _ P AI T C ξ hξ K k q p hkp x hx
  obtain ⟨hP, -, -, -, -, hshift, -⟩ := GlobalTheory.MemLoc.seed_fil l C ξ hξ
  rw [T.fil] at hx
  have hy := (hshift k q (T.eD x)).2 hx
  rw [hkp] at hy
  obtain ⟨y, hye⟩ := (GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C) p _).1 hy
  have h0 : (-(p : ℤ)).toNat = 0 := by omega
  rw [h0, pow_zero, mul_one, Int.toNat_natCast] at hye
  have hz : aDp l (xi C.ε) ^ p * y ∈ Per.FilP l p :=
    ((GlobalTheory.MemLoc.filtration_eq_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C)).1 p _).2 (dvd_mul_right _ _)
  rw [hP, Ideal.mem_span_singleton'] at hz
  obtain ⟨z', hz'⟩ := hz
  refine ⟨z', ?_⟩
  rw [mul_comm (aDp l ξ ^ p) z', hz', hye]

end GlobalTheory.HodgeAt
