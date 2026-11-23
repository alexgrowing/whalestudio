import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionUniqueUpToParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSquareCongruenceConjugationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueUpperUnipotentLiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCorankEqRankLowerLeftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDoubleCosetOfEqualCorankStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageOverMaximalCompactResidueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariantRightTranslationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankLowerLeftEqLowerRightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFixedLowerRightBlockStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCompletionsToFullRankStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankCompletionSymmetryStatement

noncomputable section
open Matrix
namespace GlobalTheory.CompanionTheory.Jp.Cmp

theorem red_unique : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := GlobalTheory.T.reduction_unique_up_to_parabolic

theorem twist_gam : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ → ∀ γ ∈ Gam2 (n := n) ϖ,
      ∃ j' : GL (Ix n) O, inL γ * tauM w = tauM w * inL j' ∧ resK j' = 1 := GlobalTheory.T.level_square_congruence_conjugation

theorem twist_low : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      ∃ j j' : GL (Ix n) O, inL j * tauM w = tauM w * inL j' ∧ resK j' = x := GlobalTheory.T.residue_upper_unipotent_lift

theorem red_rank : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := GlobalTheory.T.reduction_corank_eq_rank_lower_left

theorem dbl : ∀ (k : Type) [Field k] (n : ℕ) (g₁ g₂ : GL (Ix n) k), iD g₁ = iD g₂ →
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k) (x : GL (Ix n) k),
      x.1.toBlocks₁₂ = 0 ∧ g₂ = pM a d b * g₁ * x := GlobalTheory.T.parabolic_double_coset_of_equal_corank

theorem avg_res : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ f : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ,
      avgK ϖ (fun κ => f (resK κ)) = sumG f / (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := GlobalTheory.T.average_over_maximal_compact_residue

theorem avg_right : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := GlobalTheory.T.average_invariant_right_translation

theorem cnt_swap : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := GlobalTheory.T.card_rank_lower_left_eq_lower_right

theorem cnt_half : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (D : Matrix (Fin n) (Fin n) k),
    Nat.card {g : GL (Ix n) k // dBlk g = D} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
        Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := GlobalTheory.T.card_fixed_lower_right_block

theorem cnt_cols : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (D : Matrix (Fin n) (Fin n) k), D.rank = ρ →
    Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} =
      Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) := GlobalTheory.T.card_completions_to_full_rank

theorem cnt_rank : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ), ρ ≤ n →
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := GlobalTheory.T.card_rank_completion_symmetry

theorem red_mul {O L : Type} [CommRing O] [IsLocalRing O] [Field L] [Algebra O L] {n : ℕ} {w : Lˣ}
    {κ j j' : GL (Ix n) O} {h : GL (Ix n) (IsLocalRing.ResidueField O)} (hr : IsRed (O := O) w κ h)
    (e : inL j * tauM w = tauM w * inL j') : IsRed (O := O) w (κ * j) (h * resK j') := by
  obtain ⟨a, d, b, κ', E, R⟩ := hr
  refine ⟨a, d, b, κ' * j', ?_, ?_⟩
  · rw [map_mul, mul_assoc, e, ← mul_assoc, E, map_mul, mul_assoc]
  · rw [map_mul, R]

theorem iD_mul_low {k : Type} [Field k] {n : ℕ} (g x : GL (Ix n) k) (hx : x.1.toBlocks₁₂ = 0) :
    iD (g * x) = iD g := by
  have hd : dBlk (g * x) = dBlk g * x.1.toBlocks₂₂ := by
    have e : (g * x).1 = fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ g.1.toBlocks₂₁ g.1.toBlocks₂₂ *
        fromBlocks x.1.toBlocks₁₁ x.1.toBlocks₁₂ x.1.toBlocks₂₁ x.1.toBlocks₂₂ := by
      simp [fromBlocks_toBlocks]
    unfold dBlk
    rw [e, fromBlocks_multiply, toBlocks_fromBlocks₂₂, hx]
    simp
  have hu : IsUnit x.1.toBlocks₂₂.det := by
    have h0 : x.1 = fromBlocks x.1.toBlocks₁₁ 0 x.1.toBlocks₂₁ x.1.toBlocks₂₂ := by
      rw [← hx, fromBlocks_toBlocks]
    have hd : IsUnit x.1.det := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
    rw [h0, det_fromBlocks_zero₁₂] at hd
    exact isUnit_of_mul_isUnit_right hd
  unfold iD
  rw [hd, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu]

theorem low_mul {k : Type} [Field k] {n : ℕ} (x y : GL (Ix n) k) (hx : x.1.toBlocks₁₂ = 0) (hy : y.1.toBlocks₁₂ = 0) :
    (x * y).1.toBlocks₁₂ = 0 := by
  have e : (x * y).1 = fromBlocks x.1.toBlocks₁₁ x.1.toBlocks₁₂ x.1.toBlocks₂₁ x.1.toBlocks₂₂ *
      fromBlocks y.1.toBlocks₁₁ y.1.toBlocks₁₂ y.1.toBlocks₂₁ y.1.toBlocks₂₂ := by
    simp [fromBlocks_toBlocks]
  rw [e, fromBlocks_multiply, toBlocks_fromBlocks₁₂, hx, hy]
  simp

theorem avg_lin {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    {n : ℕ} {ϖ : O} (hϖ : Irreducible ϖ) {ι : Type} (s : Finset ι) (c : ℂ) (F : ι → GL (Ix n) O → ℂ) :
    avgK ϖ (fun κ => c * ∑ x ∈ s, F x κ) = c * ∑ x ∈ s, avgK ϖ (F x) := by
  haveI := Unif.finite_quotient_level_square_congruence n hϖ
  classical
  haveI := Fintype.ofFinite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ)
  unfold avgK
  simp only [finsum_eq_sum_of_fintype, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_fib {G : Type} [Fintype G] (t : G → ℕ) (n : ℕ) (ht : ∀ g, t g ≤ n) (F : ℕ → ℂ) :
    ∑ g, F (t g) = ∑ i ∈ Finset.range (n + 1), (Nat.card {g // t g = i} : ℂ) * F i := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (n + 1)) (g := t)
    (fun x _ => Finset.mem_range.2 (Nat.lt_succ_of_le (ht x)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F i) (fun x hx => by rw [(Finset.mem_filter.1 hx).2])]
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_by_rank {k : Type} [Field k] [Fintype k] (n ρ : ℕ) :
    Nat.card {g : GL (Ix n) k // (dBlk g).rank = ρ} =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        (Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
          (Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j))) := by
  classical
  let e : {g : GL (Ix n) k // (dBlk g).rank = ρ} ≃
      Σ D : {D : Matrix (Fin n) (Fin n) k // D.rank = ρ}, {g : GL (Ix n) k // dBlk g = D.1} :=
    { toFun := fun g => ⟨⟨dBlk g.1, g.2⟩, ⟨g.1, rfl⟩⟩
      invFun := fun s => ⟨s.2.1, by rw [s.2.2]; exact s.1.2⟩
      left_inv := fun g => rfl
      right_inv := by
        rintro ⟨⟨D, hD⟩, ⟨g, hg⟩⟩
        dsimp only at hg
        subst hg
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  rw [Finset.sum_congr rfl (g := fun _ => Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
          (Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j)))
    (fun D _ => by rw [cnt_half, cnt_cols k n ρ D.1 D.2])]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]

theorem count {k : Type} [Field k] [Fintype k] (n i : ℕ) (hi : i ≤ n) :
    Nat.card {g : GL (Ix n) k // iD g = i} * Fintype.card k ^ (2 * n * i) =
      Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} * Fintype.card k ^ (n * n) := by
  have h1 : Nat.card {g : GL (Ix n) k // iD g = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = n - i} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    have : (dBlk g).rank ≤ n := by simpa using (dBlk g).rank_le_card_width
    unfold iD
    omega
  rw [h1, cnt_swap, card_by_rank, card_by_rank]
  have hr := cnt_rank k n i hi
  have e1 : n - (n - i) = i := by omega
  rw [e1]
  have e2 : n * (n - i) + 2 * n * i = n * i + n * n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
    simp only [Nat.add_sub_cancel_left]
    ring
  set c := Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1}
  set q := Fintype.card k
  set Ia := ∏ j ∈ Finset.range (n - i), (q ^ n - q ^ j)
  set Ib := ∏ j ∈ Finset.range i, (q ^ n - q ^ j)
  set Ra := Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = i}
  set Rb := Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - i}
  calc Rb * (c * (q ^ (n * (n - i)) * Ib)) * q ^ (2 * n * i)
      = (Rb * Ib) * c * q ^ (n * (n - i) + 2 * n * i) := by rw [pow_add]; ring
    _ = (Ra * Ia) * c * q ^ (n * i + n * n) := by rw [hr, e2]
    _ = Ra * (c * (q ^ (n * i) * Ia)) * q ^ (n * n) := by rw [pow_add]; ring

theorem sum_weight {k : Type} [Field k] [Fintype k] (n : ℕ) (f : ℕ → ℂ) :
    sumG (fun g : GL (Ix n) k => (Fintype.card k : ℂ) ^ (2 * n * iD g) * f (iD g)) =
      (Fintype.card k : ℂ) ^ (n * n) * sumG (fun h : GL (Ix n) k => f (lowerLeftBlock h).rank) := by
  classical
  haveI := Fintype.ofFinite (GL (Ix n) k)
  unfold sumG
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have a := sum_fib (iD (k := k) (n := n)) n (fun g => by unfold iD; omega)
    (fun i => (Fintype.card k : ℂ) ^ (2 * n * i) * f i)
  have b := sum_fib (fun h : GL (Ix n) k => (lowerLeftBlock h).rank) n
    (fun g => by simpa using (lowerLeftBlock g).rank_le_card_width) f
  rw [a, b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have c := count (k := k) n i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have c' := congrArg (Nat.cast : ℕ → ℂ) c
  push_cast at c'
  linear_combination (f i) * c'

theorem jpCmp : JpCmp := by
  intro O L _ _ _ _ _ _ _ n ϖ hϖ w hw Ψ hΨ T hT
  classical
  haveI := Fintype.ofFinite (GL (Ix n) (IsLocalRing.ResidueField O))
  have hinv : ∀ κ h, IsRed (O := O) w κ h → Ψ h = Ψ (T κ) := by
    intro κ h hr
    obtain ⟨a, d, b, e⟩ := red_unique O L n w κ (T κ) h (hT κ) hr
    rw [e, hΨ]
  have hγ : ∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, Ψ (T (κ * γ)) = Ψ (T κ) := by
    intro κ γ hg
    obtain ⟨j', e, r⟩ := twist_gam O L n ϖ hϖ w hw γ hg
    have := red_mul (hT κ) e
    rw [r, mul_one] at this
    exact (hinv _ _ this).symm
  have hx : ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      avgK ϖ (fun κ => Ψ (T κ * x)) = avgK ϖ (fun κ => Ψ (T κ)) := by
    intro x hl
    obtain ⟨j, j', e, r⟩ := twist_low O L n ϖ hϖ w hw x hl
    have h1 : (fun κ => Ψ (T κ * x)) = fun κ => Ψ (T (κ * j)) := by
      funext κ
      have := red_mul (hT κ) e
      rw [r] at this
      exact hinv _ _ this
    rw [h1]
    exact avg_right O n ϖ (fun κ => Ψ (T κ)) hγ j
  set Pm : Finset (GL (Ix n) (IsLocalRing.ResidueField O)) := Finset.univ.filter (fun x => x.1.toBlocks₁₂ = 0) with hPm
  have hmem : ∀ x, x ∈ Pm ↔ x.1.toBlocks₁₂ = 0 := by simp [hPm]
  have hN : (Pm.card : ℂ) ≠ 0 := by
    have : (1 : GL (Ix n) (IsLocalRing.ResidueField O)) ∈ Pm := by
      rw [hmem]; simp [← fromBlocks_one]
    exact_mod_cast (Finset.card_pos.2 ⟨_, this⟩).ne'
  let Φ : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ := fun g => (Pm.card : ℂ)⁻¹ * ∑ x ∈ Pm, Ψ (g * x)
  have hΦavg : avgK ϖ (fun κ => Φ (T κ)) = avgK ϖ (fun κ => Ψ (T κ)) := by
    have := avg_lin hϖ Pm (Pm.card : ℂ)⁻¹ (fun x κ => Ψ (T κ * x))
    simp only [Φ]
    rw [this, Finset.sum_congr rfl (fun x h => hx x ((hmem x).1 h))]
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hΦ : ∀ g₁ g₂, iD g₁ = iD g₂ → Φ g₂ = Φ g₁ := by
    intro g₁ g₂ e
    obtain ⟨a, d, b, x₀, h0, rfl⟩ := dbl _ n g₁ g₂ e
    simp only [Φ]
    congr 1
    have hinj : Set.InjOn (fun x => x₀ * x) (Pm : Set _) := fun _ _ _ _ h => mul_left_cancel h
    have him : Pm.image (fun x => x₀ * x) = Pm := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        obtain ⟨x, hxm, rfl⟩ := Finset.mem_image.1 hy
        exact (hmem _).2 (low_mul _ _ h0 ((hmem _).1 hxm))
      · rw [Finset.card_image_of_injOn hinj]
    conv_rhs => rw [← him]
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, mul_assoc, hΨ]
  let f : ℕ → ℂ := fun i => if h : ∃ g, iD g = i then Φ h.choose else 0
  have hf : ∀ g, Φ g = f (iD g) := by
    intro g
    have h : ∃ g', iD g' = iD g := ⟨g, rfl⟩
    simp only [f, dif_pos h]
    exact hΦ _ _ h.choose_spec
  have hnum : sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g) =
      sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Φ g) := by
    unfold sumG
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    have h1 : ∀ x ∈ Pm, ∑ g, (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ (g * x) =
        ∑ g, (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g := by
      intro x hxm
      rw [← Equiv.sum_comp (Equiv.mulRight x) (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g)]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Equiv.coe_mulRight]
      rw [iD_mul_low g x ((hmem x).1 hxm)]
    simp only [Φ]
    have h2 : ∑ g, (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * ((Pm.card : ℂ)⁻¹ * ∑ x ∈ Pm, Ψ (g * x)) =
        (Pm.card : ℂ)⁻¹ * ∑ x ∈ Pm, ∑ g, (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ (g * x) := by
      rw [Finset.sum_comm (s := Pm), Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Finset.mul_sum]
      ring
    rw [h2, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hq : ((Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (n * n)) ≠ 0 := by
    have : (Fintype.card (IsLocalRing.ResidueField O)) ≠ 0 := Fintype.card_ne_zero
    exact pow_ne_zero _ (by exact_mod_cast this)
  have hL : avgK ϖ (fun κ => Ψ (T κ)) = sumG (fun h : GL (Ix n) (IsLocalRing.ResidueField O) => f (lowerLeftBlock h).rank) /
      (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
    rw [← hΦavg, ← avg_res O n ϖ hϖ (fun h : GL (Ix n) (IsLocalRing.ResidueField O) => f (lowerLeftBlock h).rank)]
    congr 1
    funext κ
    rw [hf, red_rank O L n ϖ hϖ w hw κ _ (hT κ)]
  have hden := sum_weight (k := IsLocalRing.ResidueField O) n (fun _ => 1)
  have hone : sumG (fun _ : GL (Ix n) (IsLocalRing.ResidueField O) => (1 : ℂ)) =
      (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
    unfold sumG
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Nat.card_eq_fintype_card]
  simp only [mul_one] at hden
  rw [hL, hnum, hden, hone]
  have hw2 : sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Φ g) =
      sumG (fun g : GL (Ix n) (IsLocalRing.ResidueField O) => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * f (iD g)) := by
    unfold sumG
    exact finsum_congr fun g => by beta_reduce; rw [hf]
  rw [hw2, sum_weight]
  field_simp

end GlobalTheory.CompanionTheory.Jp.Cmp
end
