import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralPowerSeriesDivisionApproxStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CokerFinLen

theorem divApprox : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧), g ∈ A O K → ∀ n₀ : ℕ, ‖coeff n₀ g‖ = 1 → (∀ i < n₀, ‖coeff i g‖ < 1) → ∀ δ : ℝ, 0 < δ → ∀ f ∈ A O K, ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := GlobalTheory.T.exists_integral_powerSeries_division_approx

theorem exists_net {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : Finset K, (∀ t ∈ T, ‖t‖ ≤ 1) ∧ ∀ x : K, ‖x‖ ≤ 1 → ∃ t ∈ T, ‖x - t‖ < δ := by
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  obtain ⟨t, hts, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : K) 1) hδ
  refine ⟨ht.toFinset, fun y hy => by simpa using hts (ht.mem_toFinset.1 hy), fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : K) 1 := by simpa using hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx')
  exact ⟨y, ht.mem_toFinset.2 hy, by simpa [dist_eq_norm] using hxy⟩

theorem exists_finset_reps {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (g : K⟦X⟧) (hg : g ∈ A O K) (hprim : ∃ n, ‖coeff n g‖ = 1) (c : K) (hc : c ≠ 0) :
    ∃ R : Finset K⟦X⟧, ∀ f ∈ A O K, ∃ r ∈ R, r ∈ A O K ∧ ∃ q ∈ A O K, ∃ h ∈ A O K,
      f = r + q * g + C c * h := by
  classical
  have hδ : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨T, hT1, hT⟩ := exists_net (K := K) l hδ
  let n₀ := Nat.find hprim
  have hn₀ : ‖coeff n₀ g‖ = 1 := Nat.find_spec hprim
  have hlow : ∀ i < n₀, ‖coeff i g‖ < 1 := fun i hi =>
    lt_of_le_of_ne ((mem_A.1 hg) i) (Nat.find_min hprim hi)
  let mkR : (Fin n₀ → T) → K⟦X⟧ := fun t => PowerSeries.mk fun n =>
    if h : n < n₀ then ((t ⟨n, h⟩ : T) : K) else 0
  refine ⟨Finset.univ.image mkR, fun f hf => ?_⟩
  obtain ⟨q, hq, r, hr0, hr1, hrem⟩ := divApprox O K g hg n₀ hn₀ hlow _ hδ f hf
  choose t ht hrt using fun i : Fin n₀ => hT (coeff i r) (hr1 i)
  let r' := mkR fun i => ⟨t i, ht i⟩
  have hcoeff : ∀ n, coeff n r' = if h : n < n₀ then t ⟨n, h⟩ else 0 := fun n => by
    simp [r', mkR, coeff_mk]
  have hr'A : r' ∈ A O K := mem_A.2 fun n => by
    rw [hcoeff]; split_ifs
    · exact hT1 _ (ht _)
    · simp
  set d := f - q * g - r' with hd
  have hdn : ∀ n, ‖coeff n d‖ ≤ ‖c‖ := fun n => by
    have : d = (f - q * g - r) + (r - r') := by rw [hd]; ring
    rw [this, map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hrem n) ?_)
    rw [map_sub, hcoeff]
    split_ifs with h
    · exact (hrt ⟨n, h⟩).le
    · rw [hr0 n (not_lt.1 h), sub_zero, norm_zero]; exact hδ.le
  refine ⟨r', Finset.mem_image_of_mem mkR (Finset.mem_univ (fun i => (⟨t i, ht i⟩ : T))), hr'A, q, hq, C c⁻¹ * d,
    mem_A.2 fun n => ?_, ?_⟩
  · rw [coeff_C_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hdn n) (norm_nonneg _)
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, hd]; ring

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.rdivSet τ) → IsFiniteLength (A O K) F.coker := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F hY h1
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  have hc : ∀ τ, ∃ c : K, c ≠ 0 ∧ ∃ Y : Matrix ι κ K⟦X⟧, (∀ i j, Y i j ∈ A O K) ∧
      F.mat τ * Y = C c • (1 : Matrix κ κ K⟦X⟧) := by
    intro τ
    obtain ⟨-, Y, ⟨B, hB⟩, hFY⟩ := h1 τ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖(l : K)‖ ^ m * B < 1 := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (norm_l_lt_one (K := K) l)).mul_const B
      rw [zero_mul] at h
      exact (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨(l : K) ^ m, pow_ne_zero _ (l_ne_zero l), C ((l : K) ^ m) • Y,
      fun i j => mem_A.2 fun n => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul, coeff_C_mul, norm_mul, norm_pow]
      calc _ ≤ ‖(l : K)‖ ^ m * B := mul_le_mul_of_nonneg_left (hB i j n) (by positivity)
        _ ≤ 1 := hm.le
    · rw [Matrix.mul_smul, hFY, one_smul]
  choose c hc0 Y₁ hY₁A hY₁ using hc
  choose Yg g hYgA hgprim hYg using hY
  have hgA : ∀ τ (j : κ), g τ ∈ A O K := fun τ j => by
    have h := congrFun (congrFun (hYg τ) j) j
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.mul_apply] at h
    rw [← h]
    exact Subalgebra.sum_mem _ fun k _ => mul_mem (F.mem τ j k) (hYgA τ k j)
  have hR : ∀ τ (j : κ), ∃ R : Finset K⟦X⟧, ∀ f ∈ A O K, ∃ r ∈ R, r ∈ A O K ∧ ∃ q ∈ A O K,
      ∃ h ∈ A O K, f = r + q * g τ + C (c τ) * h := fun τ j =>
    exists_finset_reps l (g τ) (hgA τ j) (hgprim τ) (c τ) (hc0 τ)
  choose R hR using hR
  let Sset : Set Q.M := {v | ∀ τ j, (v : Vec K a κ) τ j ∈ R τ j}
  have hS : Sset.Finite := by
    have hfin : (Set.pi Set.univ fun τ => Set.pi Set.univ fun j => ((R τ j : Set K⟦X⟧))).Finite :=
      Set.Finite.pi fun τ => Set.Finite.pi fun j => (R τ j).finite_toSet
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.mem_coe]
    exact hv
  have hsurj : ∀ x : F.coker, x ∈ (Submodule.Quotient.mk '' Sset : Set F.coker) := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hv : ∀ τ j, (v : Vec K a κ) τ j ∈ A O K := fun τ j => mem_tot.1 v.2 τ j
    choose r hrR hrA q hqA h hhA hdec using fun τ j => hR τ j _ (hv τ j)
    refine ⟨⟨fun τ j => r τ j, mem_tot.2 fun τ j => hrA τ j⟩, hrR, ?_⟩
    rw [Submodule.Quotient.eq]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    unfold Hom.imM
    rw [Submodule.mem_map]
    refine ⟨fun τ => -(Yg τ *ᵥ q τ + Y₁ τ *ᵥ h τ), mem_tot.2 fun τ i => ?_, ?_⟩
    · have hmv : ∀ (Y : Matrix ι κ K⟦X⟧) (w : κ → K⟦X⟧), (∀ i j, Y i j ∈ A O K) →
          (∀ j, w j ∈ A O K) → ∀ i, (Y *ᵥ w) i ∈ A O K := fun Y w hY hw i =>
        Subalgebra.sum_mem _ fun j _ => mul_mem (hY i j) (hw j)
      exact neg_mem (add_mem (hmv _ _ (hYgA τ) (hqA τ) i) (hmv _ _ (hY₁A τ) (hhA τ) i))
    · ext τ j
      simp only [LinearMap.restrictScalars_apply, Hom.app_apply, Matrix.mulVec_neg,
        Matrix.mulVec_add, Matrix.mulVec_mulVec, hYg, hY₁, Matrix.smul_mulVec,
        Matrix.one_mulVec, Submodule.coe_sub, Pi.sub_apply, Pi.neg_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hdec τ j]
      ring_nf
  haveI : Finite F.coker :=
    Set.finite_univ_iff.1 ((hS.image _).subset fun x _ => hsurj x)
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨isNoetherian_of_finite _ _, isArtinian_of_finite⟩

end GlobalTheory.CokerFinLen
