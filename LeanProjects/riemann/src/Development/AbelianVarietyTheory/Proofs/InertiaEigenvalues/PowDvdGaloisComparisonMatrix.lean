import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_dvd_map_of_smul_eq {A D W : Type} [CommRing A] [CommRing D] [CommRing W] {n : Type} [Fintype n]
    [DecidableEq n] (i : A →+* D) (hi : Function.Injective i) (j : A →+* W) (t t' : A) (N l k : ℕ)
    (M Y y : Matrix n n A) (ε : Matrix n n D) (h : i t ^ N • M.map i = i t' ^ N • (Y.map i * ε))
    (hy : y.map i = (l : D) ^ k • ε) (ht : IsUnit (j t')) (hY : IsUnit (Y.map j)) (a b : n) :
    (l : W) ^ k ∣ j (y a b) := by
  have h1 : ((l : A) ^ k * t ^ N) • M = t' ^ N • (Y * y) := by
    apply Matrix.map_injective hi
    change (((l : A) ^ k * t ^ N) • M).map i = (t' ^ N • (Y * y)).map i
    have e1 : (((l : A) ^ k * t ^ N) • M).map i = (l : D) ^ k • (i t ^ N • M.map i) := by
      ext p q; simp [mul_assoc]
    have e2 : (t' ^ N • (Y * y)).map i = i t' ^ N • (Y.map i * y.map i) := by
      rw [← Matrix.map_mul]; ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    rw [e1, e2, h, hy, Matrix.mul_smul, smul_comm]
  have h2 : (l : W) ^ k • (j t ^ N • M.map j) = j t' ^ N • (Y.map j * y.map j) := by
    have e := congrArg (fun Z : Matrix n n A => Z.map j) h1
    rw [← Matrix.map_mul]
    ext p q
    have := congrFun (congrFun e p) q
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, mul_assoc]
      using this
  obtain ⟨u, hu⟩ := hY
  obtain ⟨v, hv⟩ := ht.pow N
  have h3 : y.map j = (l : W) ^ k • ((↑v⁻¹ : W) • ((↑u⁻¹ : Matrix n n W) * (j t ^ N • M.map j))) := by
    rw [smul_comm, ← Matrix.mul_smul, h2, ← hu, ← hv, Matrix.mul_smul, ← mul_assoc, Units.inv_mul, one_mul,
      smul_smul, Units.inv_mul, one_smul]
  exact ⟨_, congrFun (congrFun h3 a) b⟩

theorem pow_dvd_of_rel_gal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → ∀ (k : ℕ) (y : Matrix (Fin d) (Fin d) (Ainf l)), y.map bk.iA = ((l : ℕ) : bk.DA bk.ρ₀) ^ k • ε → ∀ i j, ((l : ℕ) : Ainf l) ^ k ∣ y i j := by
  intro l _ K bk d ρ τ s ht hτ _ g ε hε k y hy i j
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨-, hu, hsat⟩ := GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated l K bk τ hτ
  exact hsat k _ (pow_dvd_map_of_smul_eq bk.iA (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1 (inclW l) τ _ s.N l k
    _ ht.Y y ε (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g ε hε) hy (hu g) ht.unit i j)

end GlobalTheory.BSP
