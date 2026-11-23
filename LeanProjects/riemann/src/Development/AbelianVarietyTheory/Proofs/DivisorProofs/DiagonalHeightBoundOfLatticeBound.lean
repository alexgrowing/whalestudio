import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValVwProdLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagNeZeroOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.CovTop
attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.CovHt.HTDiag

theorem exists_norm_eq_htEx (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] :
    ∃ a : ℂ_[p], ‖a‖ = (p : ℝ) ^ (-htEx E p) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  set d := Module.finrank ℚ E with hdd
  set m := padicValNat p (discr E).natAbs with hmm
  set N : ℕ := d + 40 * m * (p - 1) with hN
  set D : ℕ := (p - 1) * d with hD
  have hD0 : 0 < D := Nat.mul_pos (by omega) hd
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℂ_[p]) ^ N) hD0
  refine ⟨b, ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : ‖b‖ ^ (D : ℝ) = (p : ℝ) ^ (-(N : ℝ)) := by
    rw [Real.rpow_natCast, ← norm_pow, hb, norm_pow, GlobalTheory.PadicComplexHost.norm_p, inv_pow, Real.rpow_neg hp0.le,
      Real.rpow_natCast]
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD0.ne'
  calc ‖b‖ = (‖b‖ ^ (D : ℝ)) ^ ((D : ℝ)⁻¹) := (Real.rpow_rpow_inv (norm_nonneg b) hD').symm
    _ = (p : ℝ) ^ (-(N : ℝ) * (D : ℝ)⁻¹) := by rw [h1, ← Real.rpow_mul hp0.le]
    _ = (p : ℝ) ^ (-htEx E p) := by
      congr 1
      have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hp1' : (p : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      rw [htEx, ← hdd, ← hmm, hN, hD]
      push_cast [hp1]
      field_simp

theorem diagBound_of_latBound (hL : LatBound) : DiagBound := by
  intro E _ _ _ _ H Dw l Xo c p _ _ T io y₀ hy₀ k y z hH hz
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨-, kO, P, ψ, z', hP, hz', g, a, x, hc, hg, ha, hx, hb⟩ := hH
  obtain rfl : z = z' := (FlagTan.frMap_unique hz' hz).symm
  have hd := fun τ => diag_ne_zero_of_linearIndependent (hg τ) (hb τ).1
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  let t : Ix Dw → ℂ_[p]ˣ := fun i => Option.rec (Units.mk0 a ha0) (fun s => Units.mk0 _ (hd s.1 s.2)) i
  have hnorm : ∀ u : ℂ_[p], ‖u‖ = ((Valued.v u : ℝ≥0) : ℝ) := fun u =>
    (GlobalTheory.PadicComplexHost.valuation_coe_eq_norm p u).symm
  have hspan := fun τ => RecSpan.span_bLie_eq_wRec E H Dw l Xo c p ℂ_[p] Valued.v 𝓞_ℂ_[p] T io y₀ k kO P ψ z hP hz' τ
    (x τ) (hx τ)
  have hw : ∀ τ j, P.bLie (x τ j) ∈ P.wRec (embInt c P.integers τ) := fun τ j =>
    (hspan τ).le (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨a₀, ha₀⟩ := exists_norm_eq_htEx E p
  refine ⟨t, (frBor_iff_frChg z y t).2 ⟨g, hg, fun _ _ => rfl, hc⟩, ?_, fun s => ⟨?_, ?_⟩⟩
  · show ‖a‖ = 1
    rw [hnorm, ha, NNReal.coe_one]
  · obtain ⟨τ, i⟩ := s
    show 1 ≤ ‖g τ i i‖
    have hmem : ∑ j, (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ_[p]) i j • P.bLie (x τ j) ∈ htLat c P τ := by
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne' hj, zero_smul]) (by simp),
        Matrix.one_apply_eq, one_smul]
      exact wRec_le_htLat P τ (hw τ i)
    have h := IsLatBasis.diag_le P.integers (hg τ) (fun i j h => Matrix.one_apply_ne h.ne) (hb τ) i hmem
    rw [Matrix.one_apply_eq, map_one] at h
    rw [hnorm]
    exact_mod_cast h
  · obtain ⟨τ, i⟩ := s
    show ‖g τ i i‖ ≤ _
    have hli : LinearIndependent ℂ_[p] fun j => P.bLie (x τ j) := by
      rw [linearIndependent_iff_card_le_finrank_span]
      have h1 := linearIndependent_iff_card_eq_finrank_span.1 (hb τ).1
      rw [h1]
      haveI : FiniteDimensional ℂ_[p] (Submodule.span ℂ_[p] (Set.range fun j => P.bLie (x τ j))) :=
        FiniteDimensional.span_of_finite ℂ_[p] (Set.finite_range _)
      refine Submodule.finrank_mono (Submodule.span_le.2 ?_)
      rintro _ ⟨r, rfl⟩
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hrow : ∑ j, g τ i j • P.bLie (x τ j) ∈
        Submodule.span ℂ_[p] (P.wRec (embInt c P.integers τ) : Set P.V) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hw τ j))
    have h1 := hL E H Dw l Xo c p T io y₀ hy₀ k.toRingHom kO P ψ hP τ _ ((hb τ).mem i) hrow a₀ ha₀.le
    rw [← hspan τ, Finset.smul_sum] at h1
    simp_rw [smul_smul] at h1
    obtain ⟨b, hb'⟩ := ((isLatBasis_span hli).sum_mem_iff (fun j => a₀ * g τ i j)).1 h1 i
    have hv : ‖a₀ * g τ i i‖ ≤ 1 := by
      rw [← hb', hnorm]
      exact_mod_cast P.integers.map_le_one b
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hpos : (0 : ℝ) < (p : ℝ) ^ htEx E p := Real.rpow_pos_of_pos hp0 _
    rw [norm_mul, ha₀, Real.rpow_neg hp0.le] at hv
    rwa [inv_mul_le_iff₀ hpos, _root_.mul_one] at hv

example : LatBound → DiagBound := diagBound_of_latBound

end GlobalTheory.CovHt.HTDiag
