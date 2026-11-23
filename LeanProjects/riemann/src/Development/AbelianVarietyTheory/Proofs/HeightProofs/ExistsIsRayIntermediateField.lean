import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRichSmall
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeWeberRay
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayFieldStatement

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem exists_isRay_intermediateField (hR : GlobalTheory.NT.RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮 ≠ ⊥) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R), IsRay R 𝔮 := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hR K 𝔮 h𝔮
  have := hM.1
  let f : M →ₐ[K] ℂ := IsAlgClosed.lift
  let e : M ≃ₐ[K] f.fieldRange := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := e.toLinearEquiv.finiteDimensional
  have : NumberField f.fieldRange := NumberField.of_module_finite K f.fieldRange
  have h := hM.of_algEquiv e
  exact ⟨f.fieldRange, inferInstance, h.1, h.2⟩

theorem exists_weber_of_rayField (hR : GlobalTheory.NT.RayField) (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (hd : discr K < -4) (n : ℕ) (hodd : Odd n) (h3 : 3 ≤ n) :
    ∃ W : IntermediateField ℚ ℂ, Sz W (7 + 3 / 2 * Real.log |(discr K : ℝ)| + 3 * Real.log n)
        (7 + 3 / 2 * Real.log |(discr K : ℝ)| + 3 * Real.log n) ∧
      ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → weberSet L n ⊆ W := by
  have hd1 : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have : ((discr K : ℤ) : ℝ) < -4 := by exact_mod_cast hd
    rw [abs_of_neg (by linarith)]; linarith
  have hd0 := Real.log_nonneg hd1
  have hn0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hn : 0 < n := by omega
  have hq : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  obtain ⟨R, i1, i2, hRay⟩ := exists_isRay_intermediateField hR K _ hq
  have h := log_sizes_of_isRay_natCast K R h2 n hn hRay
  have hs : Sz (R.restrictScalars ℚ) _ _ := ⟨i1.to_finiteDimensional, h⟩
  refine ⟨R.restrictScalars ℚ, sz_mono hs ?_ ?_, fun L hL => GlobalTheory.T.weber_set_subset_ray_field K h2 hd L hL n hodd h3 R hRay⟩
  · rw [Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
    linarith
  · rw [Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith

theorem odd_level (P : Pre) {p : ℕ} (hp : p ∈ P.host.levelPrimes) :
    Odd (P.host.g 0 * P.host.g 1 * p) ∧ 3 ≤ P.host.g 0 * P.host.g 1 * p := by
  have ho : ∀ q ∈ P.host.levelPrimes, Odd q := fun q hq => by
    have := P.level_mod_four q hq
    rw [Nat.odd_iff]; omega
  refine ⟨((ho _ (P.host.g_level 0)).mul (ho _ (P.host.g_level 1))).mul (ho p hp), ?_⟩
  have h2 := (P.level_prime p hp).two_le
  have h4 := P.level_mod_four p hp
  have h0 : 0 < P.host.g 0 * P.host.g 1 := Nat.mul_pos (P.host.g_prime 0).pos (P.host.g_prime 1).pos
  calc 3 ≤ p := by omega
    _ ≤ _ := Nat.le_mul_of_pos_left p h0

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

theorem exists_rich_small_of_rayField : GlobalTheory.NT.RayField → ∀ P : Pre, ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧
    Rich P F ∧ ∀ L : ℝ, HostSz P.host L → Sz F (poR P.R L) (poR P.R L) := by
  intro hW P
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  have hgal : IsGalois ℚ P.host.E := P.host.hostE_isGalois
  obtain ⟨K, _, _, hK2, -, hKd, hKE, hlat, hdeg⟩ := GlobalTheory.T.exists_imag_quadratic_host P.R P.host
  have hg0 := (P.host.g_prime 0).pos
  have hg1 := (P.host.g_prime 1).pos
  have hp := (P.level_prime _ P.host.pde_level.1).pos
  have hp' := (P.level_prime _ P.host.pde_level.2).pos
  have hE := sz_fieldRange_embedding P.host.E P.host.φ₀
  set lE : ℝ := Real.log |((discr P.host.E : ℤ) : ℝ)| / Module.finrank ℚ P.host.E with hlE
  set lh : ℝ := Real.log (classNumber P.host.E) with hlh
  have hlE0 : 0 ≤ lE := by
    refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
    exact_mod_cast Int.one_le_abs (discr_ne_zero P.host.E)
  have hdeg0 : 0 ≤ Real.log (Module.finrank ℚ P.host.E) := Real.log_natCast_nonneg _
  have hdK : Real.log |(discr K : ℝ)| ≤ 2 * lE := by
    obtain ⟨_, -, h⟩ := GlobalTheory.T.field_size_monotone.2 _ _ _ _ hKE hE
    have h' : Real.log |(discr K : ℝ)| / Module.finrank ℚ K ≤ lE := h
    rw [hK2] at h'
    push_cast at h'
    linarith
  have hE' := sz_mono hE (le_add_of_nonneg_right hlE0) (le_add_of_nonneg_left hdeg0)
  obtain ⟨W, hWs, hWc⟩ := exists_weber_of_rayField hW K hK2 hKd (P.host.g 0 * P.host.g 1 * P.host.pde)
    (odd_level P P.host.pde_level.1).1 (odd_level P P.host.pde_level.1).2
  obtain ⟨W', hWs', hWc'⟩ := exists_weber_of_rayField hW K hK2 hKd (P.host.g 0 * P.host.g 1 * P.host.pde')
    (odd_level P P.host.pde_level.2).1 (odd_level P P.host.pde_level.2).2
  have h0 := GlobalTheory.T.field_size_sup_add _ _ _ _ _ _ (GlobalTheory.T.field_size_sup_add _ _ _ _ _ _ hE' hWs) hWs'
  obtain ⟨F₁, l1, s1, r1⟩ := exists_roots [P.restRowsFiniteGroupCard, P.host.g 0 * (P.host.g 0 - 1), P.host.g 1 * (P.host.g 1 - 1),
    3 ^ 4, 5 ^ 4, P.host.pde, P.host.pde',
      classNumber P.host.E, xiOrd P.host (P.host.g 0 * P.host.g 1 * P.host.pde),
      xiOrd P.host (P.host.g 0 * P.host.g 1 * P.host.pde')] _ _ h0
  have hφ : ∀ x, P.host.φ₀ x ∈ F₁ := fun x =>
    l1 ((le_sup_left : _ ≤ _ ⊔ W') ((le_sup_left : _ ≤ _ ⊔ W) ⟨x, rfl⟩))
  obtain ⟨F₂, l2, s2, c2⟩ := GlobalTheory.T.exists_field_ideals_principal P.host.E P.host.φ₀ F₁ _ _ s1 hφ
  have hτ : ∀ (τ : P.host.E →+* ℂ) x, τ x ∈ F₂ := fun τ x => by
    obtain ⟨g, rfl⟩ := (factEmb P.R P.host).1.2 τ
    exact l2 (hφ (P.host.sigmaOf g x))
  obtain ⟨F, l3, s3, c3⟩ := exists_chain (fun j K => ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} = ∏ τ : P.host.E →+* ℂ, Submodule.span (𝓞 K)
        {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : P.host.E)} ^ typeExp P.host (P.R.sigW j).1 (P.R.sigW j).2 τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2)) lh F₂ _ s2
    (fun j G b hG hs => by
      obtain ⟨G', g1, g2, g3⟩ := GlobalTheory.T.exists_capitulation_field_size P.host.E _ _ (typeExp_add P.host (P.R.sigW j).1 (P.R.sigW j).2) G b b hs
        fun τ x => hG (hτ τ x)
      exact ⟨G', g1, g2, fun K hK h => g3 K h⟩) P.R.m
  have hfd := finiteDimensional_of_sz s3
  have l : F₁ ≤ F := l2.trans l3
  refine ⟨F, hfd, ⟨fun x => l (hφ x), fun N hN => l (r1 N hN), c2 F l3, ?_, ?_⟩, ?_⟩
  · intro j j1 j2 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := c3 F hfd le_rfl j j1 j2 𝔞 h𝔞
    refine ⟨β, hβ, ?_, hn⟩
    rw [hsp, prod_typeExp]
    refine Finset.prod_congr rfl fun g _ => ?_
    simp only [conjugate_emb_apply]
    rfl
  · intro L hL p hpm z hz
    have hL' : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := fun z => (hL z).trans (hlat z)
    refine l (l1 ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl
    · exact (le_sup_left : _ ≤ _ ⊔ W') ((le_sup_right : W ≤ _ ⊔ W) (hWc L hL' hz))
    · exact (le_sup_right : W' ≤ _ ⊔ W') (hWc' L hL' hz)
  · intro L hL
    obtain ⟨hG, hxi, hf8, hm⟩ := GlobalTheory.T.host_xi_order_bounds P L hL
    have hx := (hxi P.host.pde (by simp)).2
    have hx' := (hxi P.host.pde' (by simp)).2
    have hcl := GlobalTheory.log_classNumber_le_log_abs_discr_div P.host.E P.R.f hdeg
    have hlE' : lE = Real.log |((discr P.host.E : ℤ) : ℝ)| / (2 * P.R.f) := by rw [hlE, hdeg]; push_cast; rfl
    rw [← hlE'] at hcl
    have hrd := hL.rd
    rw [← hlE'] at hrd
    have hL4 := hL.len
    have hnum := GlobalTheory.sum_sizes_le_ring_polynomial P.R.f P.R.r P.R.m L lE lh (Real.log P.restRowsFiniteGroupCard) (by exact_mod_cast hf8)
      (by exact_mod_cast hL.rank) (by exact_mod_cast hm) (Nat.cast_nonneg _) hL4 hrd hlE0 hL.deg hcl hG
    have hlh0 : 0 ≤ lh := Real.log_natCast_nonneg _
    have a0 := hL.g 0
    have a1 := hL.g 1
    obtain ⟨a2, a3⟩ := hL.p
    have b0 := log_mul_pred_le (P.host.g 0)
    have b1 := log_mul_pred_le (P.host.g 1)
    have hn : ∀ p : ℕ, 0 < p → Real.log ((P.host.g 0 * P.host.g 1 * p : ℕ) : ℝ) =
        Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p := fun p h => by
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have n1 := hn _ hp
    have n2 := hn _ hp'
    have d1 : Real.log (Module.finrank ℚ P.host.E) ≤ 1 + L := by
      rw [hdeg]; push_cast
      rw [Real.log_mul (by norm_num) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      have := hL.deg
      linarith
    have e3 : Real.log ((3 ^ 4 : ℕ) : ℝ) ≤ 8 := by
      push_cast
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      rw [show (81 : ℝ) = 3 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
    have e5 : Real.log ((5 ^ 4 : ℕ) : ℝ) ≤ 16 := by
      push_cast
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
      rw [show (625 : ℝ) = 5 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
    refine sz_mono s3 ?_ ?_ <;>
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, poR]
      rw [← hlh] at hx hx' ⊢
      rw [n1, n2]
      generalize Real.log ((3 ^ 4 : ℕ) : ℝ) = x3 at e3 ⊢
      generalize Real.log ((5 ^ 4 : ℕ) : ℝ) = x5 at e5 ⊢
      linarith only [hx, hx', hnum, hlh0, a0, a1, a2, a3, b0, b1, d1, e3, e5, hdK, hrd, hL4]

end GlobalTheory.FieldSize
