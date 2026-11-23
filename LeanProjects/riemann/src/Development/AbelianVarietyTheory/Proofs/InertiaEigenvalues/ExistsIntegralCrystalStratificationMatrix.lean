import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePrismsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExistsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalCoordinatesConstantCoeffEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCrystalCoordCoeffMemStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysStrat

theorem single_mem_M {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (σ : ZMod a) (j : ι) :
    (Pi.single σ (Pi.single j (1 : K⟦X⟧)) : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  by_cases h : τ = σ
  · subst h; rw [Pi.single_eq_same]
    by_cases h' : i = j
    · subst h'; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h']; exact zero_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem mulVec_single_one' {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (j i : ι) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_stratification : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I hBK sh φ₂ hsh hφC hφsh
  obtain ⟨EE, c, hinj, hcM, hsurj, hsemi, hO, hfr⟩ := GlobalTheory.T.breuilKisinPrism_crystal_coordinates l a e _ _ (thetaW a LL) ϖ ι P _ _ hBS hBK
  obtain ⟨PP, S₀, p₀, p₁, δ, j, j₀, hI, hδ, hj₀, hjp, hjφ, hS, hS', -⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ hl sh φ₂ hsh hφC hφsh
  obtain ⟨lam₀, hl₀, hv₀⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₀ j PowerSeries.C
    (fun τ w => (hjp τ w).1)
  obtain ⟨lam₁, hl₁, hv₁⟩ := GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₁ j sh
    (fun τ w => (hjp τ w).2)
  obtain ⟨ε, hε⟩ := GlobalTheory.T.crystalline_phi_module_map_exists l a e _ _ (thetaW a LL) ϖ ι P EE c hinj hcM hsurj hsemi hO sh hsh PP p₀ p₁ j hjp
    lam₀ lam₁ hl₀ hl₁ hv₀ hv₁
  have hsh0 : ∀ f, PowerSeries.constantCoeff (sh f) = f := fun f => by
    simpa using hsh f 0

  have hcol : ∀ (τ : ZMod a) (jj : ι), ∃ x, c x = Pi.single (τ - 1) (Pi.single jj 1) :=
    fun τ jj => hsurj _ (single_mem_M P _ jj)
  have hv1 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      lam₁ (EE.tr p₁ x) τ = Pi.single jj 1 := fun τ jj x hx => funext fun i => by
    rw [hv₁, hx, Pi.single_eq_same]
    by_cases h : i = jj
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hv0 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      ∀ i, lam₀ (EE.tr p₁ x) τ i = ε τ i jj := fun τ jj x hx i => by
    rw [hε, hv1 τ jj x hx, mulVec_single_one']
  have hlK : (l : ↥LL.1) ≠ 0 := by
    have h := (map_ne_zero (algebraMap ℚ_[l] ↥LL.1)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
    rwa [map_natCast] at h
  have hl0 : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ≠ 0 := fun h => hlK (by
    have := congrArg (fun f => PowerSeries.constantCoeff (PowerSeries.constantCoeff f)) h
    simpa using this)
  refine ⟨ε, fun τ => ?_, fun τ => ?_, fun τ i jj k => ?_⟩
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol τ jj
    rw [Matrix.map_apply, ← hv0 τ jj x hx i,
      GlobalTheory.T.crystal_coordinates_constantCoeff_eq l a e _ _ (thetaW a LL) ϖ ι EE c hsemi sh hsh PP S₀ p₀ p₁ δ j j₀ hδ hj₀ hjp lam₀ lam₁ hl₀ hl₁ hv₀ hv₁,
      hv1 τ jj x hx, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol (τ - 1) jj
    have hlI : ((l : ℕ) : PP.A) ∈ PP.I := by rw [hI]; exact Ideal.mem_span_singleton_self _
    obtain ⟨n, k, hn⟩ := exists_isFrac ((l : ℕ) : PP.A) (EE.Φ PP ⟨_, hlI⟩ (EE.tr p₁ x))
    have G₀ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₀ j PowerSeries.C φ₂
      (fun τ w => (hjp τ w).1) hjφ hφC (PowerSeries.C_injective) lam₀ hl₀ hv₀ _ n k hn τ i
    have G₁ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₁ j sh φ₂
      (fun τ w => (hjp τ w).2) hjφ hφsh (fun f g h => by rw [← hsh0 f, ← hsh0 g, h]) lam₁ hl₁ hv₁ _ n k hn
    have hy1 := hv1 (τ - 1) jj x hx
    have hy0 : ∀ m, lam₀ (EE.tr p₁ x) (τ - 1) m = ε (τ - 1) m jj := hv0 (τ - 1) jj x hx
    have hE := congrFun (hε n τ) i
    rw [G₀] at hE
    simp only [Matrix.mulVec, dotProduct, G₁, hy1, hy0] at hE
    have key : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k *
        (((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) i jj =
        ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k * (ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh) i jj := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have h1 : ∀ q, φ₂ ((Pi.single jj (1 : (↥LL.1)⟦X⟧⟦X⟧) : ι → (↥LL.1)⟦X⟧⟦X⟧) q) =
          (Pi.single jj 1 : ι → (↥LL.1)⟦X⟧⟦X⟧) q := fun q => by
        by_cases h : q = jj
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      simp only [h1] at hE
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true] at hE
      simp only [Matrix.map_apply] at hE ⊢
      rw [hE, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    exact (mul_left_cancel₀ (pow_ne_zero k hl0) key).symm
  · obtain ⟨x, hx⟩ := hcol τ jj
    rw [← hv0 τ jj x hx i]
    exact GlobalTheory.T.factorial_mul_crystalCoord_coeff_mem l a e _ _ (thetaW a LL) ϖ ι P EE c hcM PP p₀ j hS' lam₀ hl₀ hv₀ _ τ i k

end GlobalTheory.CrysStrat
