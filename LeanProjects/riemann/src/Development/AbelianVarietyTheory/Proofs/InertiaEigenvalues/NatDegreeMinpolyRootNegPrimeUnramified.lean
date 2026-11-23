import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.InertiaDeg
open Polynomial

theorem natDegree_minpoly_root_neg_l : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (π : Om l), 0 < N → π ^ N = -(l : Om l) → ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) → (minpoly E π).natDegree = N := by
  intro l _ N π hN hπ E _ _ hE
  have hl0 : (0 : ℝ) < l := by linarith [Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l (l := l)]
  set Q : E[X] := Polynomial.X ^ N + Polynomial.C ((l : ℕ) : E) with hQ
  have hQm : Q.Monic := by
    rw [hQ]; exact monic_X_pow_add_C _ hN.ne'
  have hQr : aeval π Q = 0 := by
    rw [hQ]; simp [hπ]
  have hint : IsIntegral E π := ⟨Q, hQm, by rwa [aeval_def] at hQr⟩
  have hdvd : minpoly E π ∣ Q := minpoly.dvd _ _ hQr
  have hQdeg : Q.natDegree = N := by rw [hQ]; exact natDegree_X_pow_add_C
  have hle : (minpoly E π).natDegree ≤ N := by
    rw [← hQdeg]; exact natDegree_le_of_dvd hdvd hQm.ne_zero
  have hpos : 0 < (minpoly E π).natDegree := minpoly.natDegree_pos hint
  have hmon := minpoly.monic hint
  set P := (minpoly E π).map (algebraMap E (Om l)) with hP
  have hsp : P.Splits := IsAlgClosed.splits P
  have hPm : P.Monic := hmon.map _
  have hπn : ‖π‖ ^ N = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hπ, norm_neg, Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l]
  have hroots : ∀ a ∈ P.roots, ‖a‖ = ‖π‖ := by
    intro a ha
    have h1 : P ∣ Q.map (algebraMap E (Om l)) := Polynomial.map_dvd _ hdvd
    have h2 : (Q.map (algebraMap E (Om l))).IsRoot a := (Polynomial.isRoot_of_mem_roots ha).dvd h1
    have h3 : a ^ N = -(l : Om l) := by
      rw [hQ] at h2
      simp [Polynomial.IsRoot] at h2
      linear_combination h2
    have h4 : ‖a‖ ^ N = ‖π‖ ^ N := by
      rw [← norm_pow, h3, ← hπ, norm_pow]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hN.ne').1 h4
  have heval : ‖P.eval 0‖ = ‖π‖ ^ (minpoly E π).natDegree := by
    rw [hsp.eval_eq_prod_roots_of_monic hPm, ← Polynomial.natDegree_map (algebraMap E (Om l)), ← hP,
      hsp.natDegree_eq_card_roots]
    have h3 := map_multiset_prod (normHom : Om l →*₀ ℝ) (P.roots.map (fun a => 0 - a))
    have h4 : ‖(P.roots.map (fun a => 0 - a)).prod‖
        = ((P.roots.map (fun a => 0 - a)).map (normHom : Om l →*₀ ℝ)).prod := h3
    have h5 : Multiset.map ((normHom : Om l →*₀ ℝ) ∘ fun a => 0 - a) P.roots
        = Multiset.map (fun _ => ‖π‖) P.roots :=
      Multiset.map_congr rfl (fun a ha => by simpa using hroots a ha)
    rw [h4, Multiset.map_map, h5, Multiset.map_const', Multiset.prod_replicate]
  have hy : P.eval 0 = algebraMap E (Om l) ((minpoly E π).eval 0) := by
    rw [hP, Polynomial.eval_map, ← map_zero (algebraMap E (Om l)), Polynomial.eval₂_at_apply]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne', eq_comm, neg_eq_zero] at hπ
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hπ
  have hρ : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have hy0 : algebraMap E (Om l) ((minpoly E π).eval 0) ≠ 0 := by
    rw [← hy, ← norm_pos_iff, heval]
    exact pow_pos hρ _
  obtain ⟨m, hm⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow (hE ((minpoly E π).eval 0)) hy0
  rw [← hy, heval] at hm
  have h8 : (l : ℝ) ^ (m * (N : ℤ)) = (l : ℝ) ^ (-((minpoly E π).natDegree : ℤ)) := by
    rw [_root_.zpow_mul, ← hm, zpow_natCast, ← pow_mul, mul_comm, pow_mul, hπn, _root_.zpow_neg, zpow_natCast, inv_pow]
  have h9 : m * (N : ℤ) = -((minpoly E π).natDegree : ℤ) :=
    zpow_right_injective₀ hl0 (Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l (l := l)).ne' h8
  have h10 : (N : ℤ) ∣ ((minpoly E π).natDegree : ℤ) := ⟨-m, by linarith⟩
  exact le_antisymm hle (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.1 h10))

end GlobalTheory.InertiaDeg
