import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModule

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.SumCount.DataCount

section General

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [FiniteDimensional K V]

theorem finrank_le_dim (M : Submodule (𝓞 K) V) : Module.finrank (𝓞 K) M ≤ Module.finrank K V := by
  have h1 : Module.rank (𝓞 K) M ≤ Module.rank (𝓞 K) V := Submodule.rank_le M
  have h2 : Module.rank (𝓞 K) V = Module.rank K V := (IsFractionRing.rank_right_eq (𝓞 K) K V).symm
  rw [h2, ← Module.finrank_eq_rank K V] at h1
  exact Module.finrank_le_of_rank_le h1

theorem card_quot_le_of_fg (M : Submodule (𝓞 K) V) [Module.Finite (𝓞 K) M] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Finite (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ∧
      Nat.card (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ≤ Ideal.absNorm I ^ Module.finrank K V := by
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Module.Flat (𝓞 K) M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have h1 : (a : K) • (x : V) = 0 := by
      have h0 : a • (x : V) = 0 := congrArg Subtype.val hx
      rwa [← algebraMap_smul K a] at h0
    have h2 : (a : K) ≠ 0 := by
      have := nonZeroDivisors.ne_zero ha
      exact_mod_cast this
    exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left h2)
  have e := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (N := M) I
  have hN : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hI)
  rw [hN] at e
  refine ⟨Nat.finite_of_card_ne_zero (by rw [e]; exact (pow_pos hpos _).ne'), ?_⟩
  rw [e]
  exact Nat.pow_le_pow_right hpos (finrank_le_dim M)

theorem card_quot_le (M : Submodule (𝓞 K) V) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Nat.card (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ≤ Ideal.absNorm I ^ Module.finrank K V := by
  by_cases hf : Finite (M ⧸ (I • ⊤ : Submodule (𝓞 K) M))
  swap
  · haveI := not_finite_iff_infinite.1 hf
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _
  choose s hs using Submodule.Quotient.mk_surjective (I • ⊤ : Submodule (𝓞 K) M)
  let M' : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range fun q => (s q : V))
  have hle : M' ≤ M := Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact (s q).2)
  haveI : Module.Finite (𝓞 K) M' := Module.Finite.span_of_finite _ (Set.finite_range _)
  obtain ⟨hfin, hc⟩ := card_quot_le_of_fg M' hI
  let φ : (M' ⧸ (I • ⊤ : Submodule (𝓞 K) M')) →ₗ[𝓞 K] (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top)
  have hφ : Function.Surjective φ := fun q =>
    ⟨Submodule.Quotient.mk ⟨s q, Submodule.subset_span ⟨q, rfl⟩⟩, hs q⟩
  exact (Nat.card_le_card_of_surjective φ hφ).trans hc

end General

theorem absNorm_le_sq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm w.asIdeal ≤ Ideal.absNorm (w.under (𝓞 F)).asIdeal ^ 2 := by
  have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← h2]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  have h1 := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) (w.under (𝓞 F)).asIdeal
  rw [hr] at h1
  rw [← h1]
  refine Nat.le_of_dvd ?_ (Ideal.absNorm_dvd_absNorm_of_le Ideal.map_comap_le)
  rw [h1]
  exact pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (w.under (𝓞 F)).ne_bot)) _

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.SumSize GlobalTheory.RowTest

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem sig_nonneg : 0 ≤ sig G :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem absNorm_modul_le : (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  unfold sig
  rw [Finset.mul_sum, Real.exp_sum]
  show ((Ideal.absNorm (∏ v ∈ G.pl.S0, (G.pl.w v).asIdeal ^ G.pl.depth sc v) : ℕ) : ℝ) ≤ _
  rw [map_prod, Nat.cast_prod]
  refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun v hv => ?_
  have h1 := absNorm_le_sq D.sp.cm.deg2 (G.pl.w v)
  rw [G.pl.under_w hv] at h1
  have hpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  have e : Real.exp (2 * ((G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ 2) ^ G.pl.depth sc v := by
    rw [← pow_mul, ← mul_assoc, ← Nat.cast_ofNat, ← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hpos]
  rw [e, map_pow, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h1) _

theorem rank_row_le {i : ℕ} (hi : i ≤ D.R.m) : (G.V (.grid i 0)).rank ≤ bigN D := by
  have hr : (G.V (.grid i 0)).rank = rankV D i 0 := by
    cases i with
    | zero =>
      refine (D.sp.Y_rank _ (min_le_right _ _)).trans ?_
      rw [min_eq_left (Nat.zero_le _)]
      simp [rankV, Ranks.rankY]
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).rank
  have h1 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have hk : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr]
  simp only [rankV, bigN]
  have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
  rw [e]
  omega

theorem card_cosAt_le {i : ℕ} (hi : i < D.R.m) :
    (Nat.card (G.CosAt i) : ℝ) ≤ Real.exp ((bigN D : ℝ) ^ 2 * (2 * sig G)) := by
  have h1 := card_quot_le (homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) (G.pl.modul_ne_bot sc)
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin, Fintype.card_fin] at h1
  have hpos : 0 < Ideal.absNorm G.modul := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (G.pl.modul_ne_bot sc))
  have h2 : (G.V (.grid i 0)).rank * (G.V (.grid (i + 1) 0)).rank ≤ bigN D ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (rank_row_le G hi.le) (rank_row_le G hi)
  have h3 : Nat.card (G.CosAt i) ≤ Ideal.absNorm G.modul ^ (bigN D ^ 2) := h1.trans (Nat.pow_le_pow_right hpos h2)
  calc (Nat.card (G.CosAt i) : ℝ) ≤ (Ideal.absNorm G.modul : ℝ) ^ (bigN D ^ 2) := by exact_mod_cast h3
    _ ≤ Real.exp (2 * sig G) ^ (bigN D ^ 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) (absNorm_modul_le G) _
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; rfl

theorem card_datum_le : (Nat.card G.Datum : ℝ) ≤ Real.exp (D.R.m * ((bigN D : ℝ) ^ 2 * (2 * sig G))) := by
  rw [Nat.card_pi, Nat.cast_prod, Real.exp_nat_mul]
  refine (Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ => card_cosAt_le G i.2).trans (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_datum_le_aOne {C b : ℝ} (hC : 2 ≤ C) (hb : 1 ≤ b) : (Nat.card G.Datum : ℝ) ≤ Real.exp (D.R.m * aOne G C b) := by
  refine (card_datum_le G).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)))
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hl := Real.log_nonneg hb
  have hs : 0 ≤ (bigN D : ℝ) ^ 2 * sig G := mul_nonneg (by positivity) (sig_nonneg G)
  have h1 : 0 ≤ C * D.R.f * bigN D * b * Real.log b := by
    have : 0 ≤ C := by linarith
    have : 0 ≤ b := by linarith
    positivity
  have h2 : 2 ≤ C * D.R.m := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 hs
  unfold aOne
  nlinarith

theorem dataK : GlobalTheory.SumCount.DataK := by
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ _ => ?_⟩⟩⟩
  have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  exact card_datum_le_aOne ch.G hC (Real.one_le_exp (by linarith))

end GlobalTheory.SumCount.DataCount

end
