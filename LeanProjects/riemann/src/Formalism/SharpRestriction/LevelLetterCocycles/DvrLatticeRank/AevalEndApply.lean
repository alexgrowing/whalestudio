import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LevConstOfEv
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def twA (uE' : LetA O n) (h' : ℕ) : LetA O n →ₗ[O] LetA O n :=
  (LinearMap.mulRight O (uE' ^ h')).comp (W.γA W.gam).toLinearMap

variable {W}

theorem twA_apply (uE' : LetA O n) (h' : ℕ) (a : LetA O n) :
    twA W uE' h' a = W.γA W.gam a * uE' ^ h' := rfl

theorem aeval_end_apply {M : Type*} [AddCommGroup M] [Module O M] (f : Module.End O M) (P : Polynomial O)
    (x : M) : Polynomial.aeval f P x = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (f ^ i) x := by
  first
  | (rw [Polynomial.aeval_eq_sum_range, LinearMap.coeFn_sum, Finset.sum_apply]
     simp only [LinearMap.smul_apply])
  | (simp [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]; done)

private theorem gammaA_mem_AΔ (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA g a ∈ W.AΔ := by
  have hc : ∀ (g h : W.Gam) (a : LetA O n), W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
    intro g h a
    funext i
    show W.γ₀ g (W.γ₀ h (a i)) = W.γ₀ h (W.γ₀ g (a i))
    rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]
  intro δ hδ
  rw [hc, ha δ hδ]

theorem twA_pow_mem (uE' : LetA O n) (h' : ℕ) (huΔ : uE' ∈ W.AΔ) (k : ℕ) {a : LetA O n}
    (ha : a ∈ W.AΔ) : (twA W uE' h' ^ k) a ∈ W.AΔ := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, twA_apply]
    exact Subalgebra.mul_mem _ (gammaA_mem_AΔ _ ih) (Subalgebra.pow_mem _ huΔ _)

private theorem gammaA_letE_eq_letE (g : W.Gam) (c : ZMod n) : W.γA g (letE c : LetA O n) = letE c := by
  funext i
  show W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i
  unfold letE
  by_cases h : i = c
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem twA_pow_letE (uE' : LetA O n) (h' : ℕ) (c : ZMod n) (k : ℕ) (a : LetA O n) :
    (twA W uE' h' ^ k) ((letE c : LetA O n) * a) = (letE c : LetA O n) * (twA W uE' h' ^ k) a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, twA_apply, twA_apply, map_mul,
      gammaA_letE_eq_letE, mul_assoc]

theorem aeval_twA_mem (uE' : LetA O n) (h' : ℕ) (huΔ : uE' ∈ W.AΔ) (P : Polynomial O) {a : LetA O n}
    (ha : a ∈ W.AΔ) : Polynomial.aeval (twA W uE' h') P a ∈ W.AΔ := by
  rw [aeval_end_apply]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (twA_pow_mem uE' h' huΔ i ha) _

theorem aeval_twA_letE (uE' : LetA O n) (h' : ℕ) (c : ZMod n) (P : Polynomial O) (a : LetA O n) :
    Polynomial.aeval (twA W uE' h') P ((letE c : LetA O n) * a) =
      (letE c : LetA O n) * Polynomial.aeval (twA W uE' h') P a := by
  rw [aeval_end_apply, aeval_end_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [twA_pow_letE, mul_smul_comm]

theorem ev_twA (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)
    (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (uE uE' : LetA O n) (huu : uE' * uE = 1) (hγE : W.γA W.gam Eπ = uE * Eπ) (u : LL) (hu : u ≠ 0)
    (hlevγ : ∀ a, W.lev c ζ (W.γA W.gam a) = rescale u (W.lev c ζ a)) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (twA W uE' h' a) i = u ^ i * ev W c ζ Eπ h' a i := by
  obtain ⟨V, hVdef⟩ : ∃ V, V = Vs W c ζ Eπ := ⟨_, rfl⟩
  have hEV : W.lev c ζ Eπ = PowerSeries.X * V := by
    ext k
    rcases k with _ | k
    · simp [h0]
    · rw [PowerSeries.coeff_succ_X_mul, hVdef]
      unfold Vs
      rw [PowerSeries.coeff_mk]
  have hV0 : PowerSeries.constantCoeff V ≠ 0 := by
    rw [hVdef, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Vs
    simpa [PowerSeries.coeff_mk] using h1
  have hVinv : V * V⁻¹ = 1 := PowerSeries.mul_inv_cancel V hV0
  have hlevu : W.lev c ζ uE * V = PowerSeries.C u * PowerSeries.rescale u V := by
    have h2 : W.lev c ζ (W.γA W.gam Eπ) = W.lev c ζ uE * W.lev c ζ Eπ := by rw [hγE, map_mul]
    rw [hlevγ, hEV, map_mul, PowerSeries.rescale_X] at h2
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := LL))
    calc PowerSeries.X * (W.lev c ζ uE * V) = W.lev c ζ uE * (PowerSeries.X * V) := by ring
      _ = PowerSeries.C u * PowerSeries.X * PowerSeries.rescale u V := h2.symm
      _ = PowerSeries.X * (PowerSeries.C u * PowerSeries.rescale u V) := by ring
  have hW' : W.lev c ζ uE' * W.lev c ζ uE = 1 := by rw [← map_mul, huu, map_one]
  have hR : PowerSeries.rescale u V * PowerSeries.rescale u V⁻¹ = 1 := by
    rw [← map_mul, hVinv, map_one]
  have hC : PowerSeries.C u * PowerSeries.C u⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hu, map_one]
  have hkey : W.lev c ζ uE' * V⁻¹ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ := by
    calc W.lev c ζ uE' * V⁻¹
        = W.lev c ζ uE' * V⁻¹ * (PowerSeries.C u * PowerSeries.C u⁻¹) *
            (PowerSeries.rescale u V * PowerSeries.rescale u V⁻¹) := by rw [hC, hR]; ring
      _ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ *
            (W.lev c ζ uE' * (PowerSeries.C u * PowerSeries.rescale u V) * V⁻¹) := by ring
      _ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ *
            ((W.lev c ζ uE' * W.lev c ζ uE) * (V * V⁻¹)) := by rw [← hlevu]; ring
      _ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ := by rw [hW', hVinv]; ring
  have hmain : W.lev c ζ (twA W uE' h' a) * Ui W c ζ Eπ h' =
      PowerSeries.C (u⁻¹ ^ h') * PowerSeries.rescale u (W.lev c ζ a * Ui W c ζ Eπ h') := by
    rw [twA_apply, map_mul, map_pow, hlevγ]
    unfold Ui
    rw [← hVdef]
    simp only [map_mul, map_pow]
    calc PowerSeries.rescale u (W.lev c ζ a) * W.lev c ζ uE' ^ h' * V⁻¹ ^ h'
        = PowerSeries.rescale u (W.lev c ζ a) * (W.lev c ζ uE' * V⁻¹) ^ h' := by ring
      _ = PowerSeries.rescale u (W.lev c ζ a) *
            (PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹) ^ h' := by rw [hkey]
      _ = PowerSeries.C u⁻¹ ^ h' * (PowerSeries.rescale u (W.lev c ζ a) *
            PowerSeries.rescale u V⁻¹ ^ h') := by ring
  unfold ev
  split_ifs with hih
  · rw [hmain, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
    have hm : (((i + h').toNat : ℕ) : ℤ) = i + h' := Int.toNat_of_nonneg hih
    have hu' : u⁻¹ ^ h' * u ^ (i + h').toNat = u ^ i := by
      rw [← zpow_natCast u, hm, zpow_add₀ hu, zpow_natCast, inv_pow, mul_comm, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]
    rw [← mul_assoc, hu']
  · simp

theorem ev_twA_pow (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)
    (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (uE uE' : LetA O n) (huu : uE' * uE = 1) (hγE : W.γA W.gam Eπ = uE * Eπ) (u : LL) (hu : u ≠ 0)
    (hlevγ : ∀ a, W.lev c ζ (W.γA W.gam a) = rescale u (W.lev c ζ a)) (k : ℕ) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' ((twA W uE' h' ^ k) a) i = (u ^ i) ^ k * ev W c ζ Eπ h' a i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ev_twA c ζ Eπ h' h0 h1 uE uE' huu hγE u hu hlevγ, ih]
    ring

theorem ev_aeval_twA (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)
    (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (uE uE' : LetA O n) (huu : uE' * uE = 1) (hγE : W.γA W.gam Eπ = uE * Eπ) (u : LL) (hu : u ≠ 0)
    (hlevγ : ∀ a, W.lev c ζ (W.γA W.gam a) = rescale u (W.lev c ζ a)) (P : Polynomial O)
    (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (Polynomial.aeval (twA W uE' h') P a) i =
      Polynomial.aeval (u ^ i) P * ev W c ζ Eπ h' a i := by
  have hzero : ev W c ζ Eπ h' 0 i = 0 := by
    unfold ev; split_ifs <;> simp
  have hadd : ∀ x y : LetA O n, ev W c ζ Eπ h' (x + y) i = ev W c ζ Eπ h' x i + ev W c ζ Eπ h' y i := by
    intro x y; unfold ev; split_ifs <;> simp [map_add, add_mul]
  have hsmul : ∀ (r : O) (x : LetA O n),
      ev W c ζ Eπ h' (r • x) i = algebraMap O LL r * ev W c ζ Eπ h' x i := by
    intro r x
    unfold ev
    split_ifs
    · first
      | (simp only [map_smul, smul_mul_assoc, PowerSeries.coeff_smul, Algebra.smul_def]; done)
      | (rw [map_smul, smul_mul_assoc, PowerSeries.coeff_smul, Algebra.smul_def])
      | (simp [Algebra.smul_def, mul_assoc]; done)
    · simp
  have hsum : ∀ (s : Finset ℕ) (g : ℕ → LetA O n),
      ev W c ζ Eπ h' (∑ k ∈ s, g k) i = ∑ k ∈ s, ev W c ζ Eπ h' (g k) i := by
    intro s g
    classical
    refine Finset.induction_on s ?_ ?_
    · simpa using hzero
    · intro k s hk ih
      rw [Finset.sum_insert hk, Finset.sum_insert hk, hadd, ih]
  rw [aeval_end_apply, Polynomial.aeval_eq_sum_range, Finset.sum_mul, hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsmul, ev_twA_pow c ζ Eπ h' h0 h1 uE uE' huu hγE u hu hlevγ, Algebra.smul_def]
  ring

theorem EE_aeval (Eπ : LetA O n) (h' : ℕ) (uE uE' : LetA O n) (huu : uE' * uE = 1)
    (hγE : W.γA W.gam Eπ = uE * Eπ) (P : Polynomial O) (f : W.EE) (a : LetA O n)
    (h : algebraMap (LetA O n) W.EE (Eπ ^ h') * f = algebraMap (LetA O n) W.EE a) :
    algebraMap (LetA O n) W.EE (Eπ ^ h') * Polynomial.aeval (W.γE W.gam).toLinearMap P f =
      algebraMap (LetA O n) W.EE (Polynomial.aeval (twA W uE' h') P a) := by
  have hγ : W.γE W.gam (algebraMap (LetA O n) W.EE (Eπ ^ h')) =
      algebraMap (LetA O n) W.EE (uE ^ h') * algebraMap (LetA O n) W.EE (Eπ ^ h') := by
    rw [W.γE_ext, ← map_mul, ← mul_pow, ← hγE]
    congr 1
    exact map_pow (W.γA W.gam) Eπ h'
  have hk : ∀ k : ℕ, algebraMap (LetA O n) W.EE (Eπ ^ h') * (((W.γE W.gam).toLinearMap ^ k) f) =
      algebraMap (LetA O n) W.EE ((twA W uE' h' ^ k) a) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have h2 := congrArg (W.γE W.gam) ih
      rw [map_mul, hγ, W.γE_ext] at h2
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, twA_apply,
        AlgHom.toLinearMap_apply]
      calc algebraMap (LetA O n) W.EE (Eπ ^ h') * W.γE W.gam (((W.γE W.gam).toLinearMap ^ k) f)
          = algebraMap (LetA O n) W.EE (uE' ^ h') * (algebraMap (LetA O n) W.EE (uE ^ h') *
              algebraMap (LetA O n) W.EE (Eπ ^ h') * W.γE W.gam (((W.γE W.gam).toLinearMap ^ k) f)) := by
            rw [← mul_assoc, ← mul_assoc, ← map_mul, ← mul_pow, huu, one_pow, map_one, one_mul]
        _ = algebraMap (LetA O n) W.EE (uE' ^ h') *
              algebraMap (LetA O n) W.EE (W.γA W.gam ((twA W uE' h' ^ k) a)) := by
            rw [h2]; rfl
        _ = algebraMap (LetA O n) W.EE (W.γA W.gam ((twA W uE' h' ^ k) a) * uE' ^ h') := by
            rw [map_mul, mul_comm]
  rw [aeval_end_apply, aeval_end_apply, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, hk i, Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply]

theorem aeval_γLA_tmul (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) (P : Polynomial O)
    (e : W.EE) (z : LcQ W T π' c) :
    Polynomial.aeval (γLA W T π' c) P (e ⊗ₜ z) = Polynomial.aeval (W.γE W.gamK).toLinearMap P e ⊗ₜ z := by
  have hp : ∀ i : ℕ, (γLA W T π' c ^ i) (e ⊗ₜ z) = (((W.γE W.gamK).toLinearMap ^ i) e) ⊗ₜ z := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      simp [γLA]
  rw [aeval_end_apply, aeval_end_apply, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hp, TensorProduct.smul_tmul']

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
