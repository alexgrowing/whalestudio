import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOrthogonalComplementStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothIntertwinerExtensionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedIntertwiningIntegralNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedKFiniteRestrictionStatement
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section
open Filter Topology

namespace GlobalTheory.UnitaryBound

theorem re_le_of_chamber {n a : ℕ} (j : Fin a → ℕ) (hj : ∀ i, 1 ≤ j i) (s : Fin a → ℂ) (h : 0 < a)
    (hx : ∀ x : Fin a → ℝ, InChamber x → 0 ≤ (pairing j (rho n j - s) x).re) :
    (s ⟨0, h⟩).re ≤ (n : ℝ) - 1 := by
  set i0 : Fin a := ⟨0, h⟩ with hi0
  have hre : ∀ x : Fin a → ℝ, (pairing j (rho n j - s) x).re =
      ∑ i, (j i : ℝ) * ((rho n j i).re - (s i).re) * x i := by
    intro x; simp [pairing, Complex.re_sum, Complex.mul_re]
  have hI : Finset.Iio i0 = ∅ :=
    Finset.eq_empty_of_forall_notMem fun l hl => by simp [hi0, Fin.lt_def] at hl
  have hrho : (rho n j i0).re = n - j i0 := by simp [rho, hI]
  set A := (j i0 : ℝ) * ((rho n j i0).re - (s i0).re) with hA
  set B := ∑ i, (j i : ℝ) * ((rho n j i).re - (s i).re) * ((a : ℝ) - ((i : ℕ) : ℝ)) with hB
  have key : ∀ δ : ℝ, 0 < δ → 0 ≤ A + δ * B := by
    intro δ hδ
    have hc : InChamber (fun i : Fin a => (if i = i0 then (1 : ℝ) else 0) + δ * ((a : ℝ) - ((i : ℕ) : ℝ))) := by
      refine ⟨fun i l hil => ?_, fun i => ?_⟩
      · have hl : l ≠ i0 := fun e => by
          have : (i : ℕ) < l := hil
          rw [e] at this; simp [hi0] at this
        have hil' : ((i : ℕ) : ℝ) < ((l : ℕ) : ℝ) := by exact_mod_cast hil
        simp only [hl, if_false]
        have : (0 : ℝ) ≤ if i = i0 then 1 else 0 := by split_ifs <;> norm_num
        nlinarith
      · have : ((i : ℕ) : ℝ) < a := by exact_mod_cast i.2
        have : (0 : ℝ) ≤ if i = i0 then 1 else 0 := by split_ifs <;> norm_num
        nlinarith
    have := hx _ hc
    rw [hre] at this
    convert this using 1
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hA, hB, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  have hA0 : 0 ≤ A := by
    have ht : Tendsto (fun δ : ℝ => A + δ * B) (𝓝[>] 0) (𝓝 (A + 0 * B)) :=
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0).mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
    simpa using this
  have hj0 : (1 : ℝ) ≤ j i0 := by exact_mod_cast hj i0
  rw [hA, hrho] at hA0
  have : 0 ≤ (n : ℝ) - j i0 - (s i0).re := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  linarith

theorem re_nonneg_of_tendsto {p L : ℂ} {F : ℝ → ℂ} {B : ℝ} (hB : ∀ r, ‖F r‖ ≤ B) (hL : L ≠ 0)
    (hF : Tendsto (fun r : ℝ => Complex.exp (r * p) * F r) atTop (𝓝 L)) : 0 ≤ p.re := by
  by_contra hp
  push_neg at hp
  have h0 : Tendsto (fun r : ℝ => Complex.exp (r * p) * F r) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun r : ℝ => Real.exp (r * p.re) * B) (fun r => ?_) ?_
    · rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
      exact mul_le_mul_of_nonneg_left (hB r) (Real.exp_pos _).le
    · have : Tendsto (fun r : ℝ => r * p.re) atTop atBot := tendsto_id.atTop_mul_const_of_neg hp
      simpa using (Real.tendsto_exp_atBot.comp this).mul_const B
  exact hL (tendsto_nhds_unique hF h0)

theorem inner_ι {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (f g : I.fns) :
    ⟪I.ι g, I.ι f⟫_ℂ = ∫ k : KG ε, ⟪g.1 k, f.1 k⟫_ℂ ∂muK ε := by
  have hcont : ∀ u : I.fns, Continuous fun k : KG ε => u.1 k := fun u =>
    (mem_indFun_top.1 u.2).1.comp continuous_subtype_val
  have int : ∀ u : I.fns, Integrable (fun k : KG ε => ((‖u.1 k‖ : ℂ)) ^ 2) (muK ε) := fun u =>
    ((Complex.continuous_ofReal.comp (hcont u).norm).pow 2).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have key : ∀ u : I.fns, ((‖I.ι u‖ : ℂ)) ^ 2 = ∫ k : KG ε, ((‖u.1 k‖ : ℂ)) ^ 2 ∂muK ε := fun u => by
    have := I.model.norm_sq u
    rw [← Complex.ofReal_pow, this, ← integral_complex_ofReal]
    push_cast; rfl
  have key' : ∀ u : I.fns, (RCLike.ofReal ‖I.ι u‖ : ℂ) ^ 2 = ∫ k : KG ε, ((‖u.1 k‖ : ℂ)) ^ 2 ∂muK ε := key
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ), ← map_add, ← map_sub, ← map_smul, ← map_sub, ← map_add,
    key', key', key', key']
  have e : (fun k : KG ε => ⟪g.1 k, f.1 k⟫_ℂ) = fun k : KG ε =>
      (((‖(g + f).1 k‖ : ℂ)) ^ 2 - ((‖(g - f).1 k‖ : ℂ)) ^ 2 +
        (((‖(g - (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2 - ((‖(g + (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2) * RCLike.I) / 4 := by
    funext k
    rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ)]
    rfl
  rw [e, integral_div]
  congr 1
  have i12 : Integrable (fun k : KG ε => ((‖(g + f).1 k‖ : ℂ)) ^ 2 - ((‖(g - f).1 k‖ : ℂ)) ^ 2) (muK ε) :=
    (int _).sub (int _)
  have i34 : Integrable (fun k : KG ε => (((‖(g - (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2 -
      ((‖(g + (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2) * RCLike.I) (muK ε) := ((int _).sub (int _)).mul_const _
  rw [integral_add i12 i34, integral_sub (int _) (int _), integral_mul_const, integral_sub (int _) (int _)]

theorem isKFinFun_mul {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {φ : UJ ε → V} (hφ : IsKFinFun φ) {k : UJ ε} (hk : k ∈ KG ε) : IsKFinFun fun g => φ (g * k) := by
  unfold IsKFinFun at *
  have hle : Submodule.span ℂ {ψ : UJ ε → V | ∃ k' ∈ KG ε, ψ = fun g => (fun g => φ (g * k)) (g * k')} ≤
      Submodule.span ℂ {ψ : UJ ε → V | ∃ k' ∈ KG ε, ψ = fun g => φ (g * k')} := by
    refine Submodule.span_mono ?_
    rintro ψ ⟨k', hk', rfl⟩
    exact ⟨k' * k, mul_mem hk' hk, by funext g; simp [mul_assoc]⟩
  exact Submodule.finiteDimensional_of_le hle

theorem unitary_bound : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → (Z : Set I.H) = I.intKer ν) → ∀ h : 0 < I.a, (I.s ⟨0, h⟩).re ≤ (n : ℝ) - 1 := by
  intro hHC hL n ε V _ _ _ π hπ hπu I hI Z hZ hZker h0
  have hL' := hL
  obtain ⟨hInd, hQuot, -, hLim, -⟩ := hL'
  obtain ⟨hadm, -, hgk, hkfin, -, -⟩ := hInd n ε I
  obtain ⟨ν, hν⟩ := GlobalTheory.Published.Langlands.exists_isHaarSub_nbar I.toDatum
  obtain ⟨hZgk, -, -, T, hTY, hTker, hTK, hTX⟩ := hZ
  have hZne : Z ≠ kFinVec ε I.ρ := by
    obtain ⟨-, -, Z', hZ', -, hne, -⟩ := hQuot n ε I hI ν hν
    have : Z = Z' := SetLike.coe_injective ((hZker ν hν).trans hZ'.symm)
    rw [this]; exact hne
  obtain ⟨a₀, ha₀, ha₀K, ha₀Z⟩ := GlobalTheory.T.k_finite_orthogonal_complement n ε I.H I.ρ hadm Z (fun v hv => hZgk.kFin v hv)
    hZgk.kStable hZne
  obtain ⟨φ₀, hφ₀K, rfl⟩ := (hkfin a₀).1 ha₀K
  have hφ₀ : φ₀.1 ≠ 0 := fun e => ha₀ (by rw [show φ₀ = 0 from Subtype.ext e, map_zero])
  obtain ⟨k, hk, hφk⟩ := (GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum φ₀.1 φ₀.2 hφ₀K).2.2 hφ₀
  set φ : I.fns := ⟨fun g => φ₀.1 (g * k), indFun_mul_right φ₀.2 trivial⟩ with hφdef
  have hφK : IsKFinFun φ.1 := isKFinFun_mul hφ₀K hk
  have hφ1 : φ.1 1 ≠ 0 := by simpa [hφdef] using hφk
  have haρ : I.ι φ = I.ρ (uMat k) (I.ι φ₀) := (I.model.transl k trivial φ₀ φ fun g => rfl).symm
  have haK : IsKFin ε I.ρ (I.ι φ) := (hkfin _).2 ⟨φ, hφK, rfl⟩

  have hiso : ∀ v w : I.H, ⟪I.ρ (uMat k) v, I.ρ (uMat k) w⟫_ℂ = ⟪v, w⟫_ℂ := fun v w =>
    (⟨(I.ρ (uMat k)).toLinearMap, fun v => hadm.2.2.1 _ hk v⟩ : I.H →ₗᵢ[ℂ] I.H).inner_map_map v w
  have hinv : ∀ z, I.ρ (uMat k) (I.ρ (uMat k⁻¹) z) = z := fun z => by
    rw [← ContinuousLinearMap.comp_apply, ← hadm.1.2 _ k.2 _ k⁻¹.2, RealIwasawa.uMat_mul_inv, hadm.1.1]; rfl
  have haZ : ∀ z ∈ Z, ⟪I.ι φ, z⟫_ℂ = 0 := fun z hz => by
    rw [haρ, ← hinv z, hiso]
    exact ha₀Z _ (hZgk.kStable _ (inv_mem hk) z hz)

  obtain ⟨w, hwK, hw⟩ := (GlobalTheory.T.intertwiner_of_k_finite_vectors n ε I.H I.ρ V π hadm hπ.2.1 T hTY (fun k hk y hy => hTK k hk y hy)).1
    (I.ι φ) haK fun y hy hTy => haZ y ((hTker y hy).1 hTy)
  have hTfin : ∀ y, IsKFin ε I.ρ y → IsKFin ε π (T y) := fun y hy => by
    have : T y ∈ (kFinVec ε I.ρ).map T := Submodule.mem_map_of_mem hy
    rw [hTY] at this; exact this
  have hcoef := GlobalTheory.T.smooth_intertwiner_extension hHC n ε I.H I.ρ V π hadm hπ.2.1 hgk
    (fun v hv => (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε V π hπu hπ.2.2).2 v hv) T hTfin (fun k hk y hy => hTK k hk y hy)
    (fun X hX y hy => hTX X hX y hy) (I.ι φ) w haK hwK hw

  obtain ⟨f, hf, hfK, hh, -, hint, hne⟩ := GlobalTheory.T.induced_intertwining_integral_nonzero hHC hL n ε I hI ν hν (φ.1 1) hφ1
  obtain ⟨⟨f', hf', hf'K, hf'φ⟩, hφM, -⟩ := GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum φ.1 φ.2 hφK
  obtain ⟨c, hc, -, hlim⟩ := hLim n ε I.toDatum hI ν hν
  have hf'1 : f' 1 = φ.1 1 := hf'φ 1 (one_mem _)
  have hL0 : (c : ℂ) * ∫ u, ⟪f' 1, f u⟫_ℂ ∂ν ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast hc.ne') ?_
    have := (hint 1 (φ.1 1) hφM).2
    simp only [mul_one] at this
    rw [hf'1, ← this]; exact hne
  have hιf : IsKFin ε I.ρ (I.ι ⟨f, hf⟩) := (hkfin _).2 ⟨⟨f, hf⟩, hfK, rfl⟩
  refine re_le_of_chamber I.j I.pos I.s h0 fun x hx => ?_
  choose t ht using fun r : ℝ => exists_isSplit I.flag (r • x)
  refine re_nonneg_of_tendsto (B := ‖w‖ * ‖T (I.ι ⟨f, hf⟩)‖) (fun r => ?_) hL0
    ((hlim f hf hfK f' hf' hf'K x hx t fun r => (ht r).1).2)
  have e1 : ∫ k : KG ε, ⟪f' k, f (k * t r)⟫_ℂ ∂muK ε = ⟪I.ι φ, I.ρ (uMat (t r)) (I.ι ⟨f, hf⟩)⟫_ℂ := by
    rw [I.model.transl (t r) trivial ⟨f, hf⟩ ⟨_, indFun_mul_right hf trivial⟩ fun g => rfl, inner_ι]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only
    rw [hf'φ k k.2]
  rw [e1, hcoef _ hιf _ (t r).2]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [hπu.2.1 _ (t r).2]

end GlobalTheory.UnitaryBound
