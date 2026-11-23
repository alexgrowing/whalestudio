import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizerSectionAtPrimeSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfDilatedReductionResidueMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeIffUniformiserReductionVanishesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffAdjointFrameMatrixInteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnHStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedPairLatticeDilationMemOfIntegerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueMatrixDatumFourierExpansionGaussSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitAwayFromLevelProdNormalisedMatrixGaussSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LiftFour

theorem dil_add {D : D7} (i : Fin D.R.m) (a : D.host.E) (x y : WO (Vc D i) (Wc D i)) :
    dil i a (x + y) = dil i a x + dil i a y := by
  exact Matrix.ext fun p q => by simp only [dil, Matrix.map_apply, Matrix.add_apply, mul_add]

theorem isHalf_add {D : D7} {m n : ℕ} {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) :
    IsHalf e (x + y) := fun p q => by simp only [Matrix.add_apply, mul_add, hx p q, hy p q]

theorem isHalf_of_add {D : D7} {m n : ℕ} {e : AE D} {x y : Mx D m n} (hxy : IsHalf e (x + y)) (hy : IsHalf e y) :
    IsHalf e x := fun p q => by
  have h1 := hxy p q
  simp only [Matrix.add_apply, mul_add, hy p q] at h1
  exact add_right_cancel h1

theorem isHalf_dil {D : D7} (i : Fin D.R.m) {e : AE D} {a : D.host.E} (ha : a ≠ 0) (x : WO (Vc D i) (Wc D i)) :
    IsHalf e (dil i a x) ↔ IsHalf e x := by
  have hu : incA D a⁻¹ * incA D a = 1 := by rw [← RingHom.map_mul, inv_mul_cancel₀ ha, map_one]
  constructor
  · intro h p q
    have h1 : e * (incA D a * x p q) = incA D a * x p q := h p q
    linear_combination (incA D a⁻¹) * h1 - (e * x p q - x p q) * hu
  · intro h p q
    show e * (incA D a * x p q) = incA D a * x p q
    rw [mul_left_comm, h p q]

theorem redM_frMapO_add {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (PP : Pl D.host.E) (a b : WO S T) (ha : IsIntM (frMapO S T βS βT a)) (hb : IsIntM (frMapO S T βS βT b)) :
    redM PP (frMapO S T βS βT (a + b)) = redM PP (frMapO S T βS βT a) + redM PP (frMapO S T βS βT b) := by
  have e : frMapO S T βS βT (a + b) = frMapO S T βS βT a + frMapO S T βS βT b := by
    ext p q
    have := GlobalTheory.PlaceDatum.frMapO_add βS βT a b 1 p q
    simpa using this
  ext p q
  simp only [redM, e, Matrix.add_apply, Matrix.of_apply]
  rw [dif_pos (add_mem (ha p q) (hb p q)), dif_pos (ha p q), dif_pos (hb p q), ← map_add]
  rfl

theorem datum_conj_half_fourier : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → (∀ PP ∈ Q, ξR PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∃ (Y : Finset (WO (Vc D i) (Wc D i))) (a : WO (Vc D i) (Wc D i) → ℂ) (Gc : ℂ), UnitOff N Gc ∧ (∀ y ∈ Y, IsHalf eQ y) ∧
      (∀ t, (if IsHalf (cA D eQ) t ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t)) else 0) =
        halfInd (cA D eQ) (lattice₂ R i) t * ∑ y ∈ Y, a y * R.ψ (symplO (Vc D i) (Wc D i) t y)) ∧
      ∀ t, ∑ y ∈ Y, a y * halfInd eQ (lattice₂ R i) (t + y) = Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV ξR Q hQ hξ N hN hNQ eQ heQ ϖ hϖ hϖQ
  classical
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by
    intro h; exact hϖ (by exact_mod_cast h)
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hrn : (Wc D i).rank ≤ (Vc D i).rank := by rw [rV, rW]; omega
  obtain ⟨ψP, hψP, hchar⟩ := GlobalTheory.T.exists_uniformizer_section_at_prime_set D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  obtain ⟨c, hinv, hc⟩ := GlobalTheory.T.residueMatrixDatum_fourierExpansion_gaussSum D Q (Vc D i).rank (Wc D i).rank hrn ψP ξR hψP hξ
  choose yx hyh hyl hyr using GlobalTheory.T.exists_half_dilated_reduction_residueMatrices D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  have hker := GlobalTheory.T.mem_lattice_iff_uniformiser_reduction_vanishes D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  have h4a := GlobalTheory.T.mem_completedPairLattice_iff_adjointFrameMatrix_integral_conjHalf D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ
  have h4b := GlobalTheory.T.mem_completedPairLattice_iff_frameMatrix_integral_on_half D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ
  have hdm := GlobalTheory.T.completedPairLattice_dilation_mem_of_integer D G Pl0 T0 A Ks R i ϖ
  have key : ∀ g : WO (Vc D i) (Wc D i) → ℂ,
      ∑ y ∈ Finset.univ.image yx, (∑ x ∈ Finset.univ.filter (fun x => yx x = y), c x) * g y = ∑ x, c x * g (yx x) := by
    intro g
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image yx) (g := yx)
      (fun x _ => Finset.mem_image_of_mem yx (Finset.mem_univ x))]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  refine ⟨Finset.univ.image yx, fun y => ∑ x ∈ Finset.univ.filter (fun x => yx x = y), c x, _,
    GlobalTheory.T.isUnitAwayFromLevel_prod_normalised_matrixGaussSum D Q (Vc D i).rank (Wc D i).rank hrn ψP ξR hψP hξ N hN hNQ, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    exact hyh x
  · intro t
    rw [key (fun y => R.ψ (symplO (Vc D i) (Wc D i) t y))]
    by_cases ht : IsHalf (cA D eQ) t
    · by_cases hl : t ∈ lattice₂ R i
      · have hint := (h4a t ht).2 hl
        rw [if_pos ⟨ht, hint⟩, halfInd, if_pos ⟨hl, ht⟩, one_mul, hinv]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hchar t (yx x) ht hl (hyh x) (hyl x), ← Finset.prod_attach Q]
        refine congrArg _ (Finset.prod_congr rfl fun PP _ => ?_)
        rw [hyr x PP]
      · rw [if_neg (fun h => hl ((h4a t ht).1 h.2)), halfInd, if_neg (fun h => hl h.1), zero_mul]
    · rw [if_neg (fun h => ht h.1), halfInd, if_neg (fun h => ht h.2), zero_mul]
  · intro t
    rw [key (fun y => halfInd eQ (lattice₂ R i) (t + y)), flatDat]
    by_cases ht : IsHalf eQ t
    · have hdt : IsHalf eQ (dil i (ϖ : D.host.E) t) := (isHalf_dil i hϖ' t).2 ht
      by_cases hl : dil i (ϖ : D.host.E) t ∈ lattice₂ R i
      · have hint := (h4b _ hdt).2 hl
        rw [if_pos ⟨hdt, hint⟩]
        set ρt : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1) :=
          fun PP => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) t)) with hρt
        have hterm : ∀ x, halfInd eQ (lattice₂ R i) (t + yx x) = if x = -ρt then 1 else 0 := by
          intro x
          have hh : IsHalf eQ (t + yx x) := isHalf_add ht (hyh x)
          have hdl : dil i (ϖ : D.host.E) (t + yx x) ∈ lattice₂ R i := by
            rw [dil_add]; exact add_mem hl (hyl x)
          have hintx := (h4b _ ((isHalf_dil i hϖ' _).2 (hyh x))).2 (hyl x)
          rw [halfInd]
          by_cases hx : x = -ρt
          · have hm : t + yx x ∈ lattice₂ R i := by
              refine (hker _ hh hdl).2 fun PP hPP => ?_
              rw [dil_add, redM_frMapO_add _ _ _ _ _ hint hintx, hyr x ⟨PP, hPP⟩, hx]
              simp [hρt]
            rw [if_pos hx, if_pos ⟨hm, hh⟩]
          · rw [if_neg hx, if_neg]
            rintro ⟨hm, -⟩
            apply hx
            funext PP
            have h0 := (hker _ hh hdl).1 hm PP.1 PP.2
            rw [dil_add, redM_frMapO_add _ _ _ _ _ hint hintx, hyr x PP] at h0
            rw [Pi.neg_apply, hρt]
            exact eq_neg_of_add_eq_zero_right h0
        simp_rw [hterm, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ (-ρt) c, if_pos (Finset.mem_univ _)]
        exact hc ρt _ fun PP => rfl
      · rw [if_neg (fun h => hl ((h4b _ hdt).1 h.2))]
        rw [mul_zero]
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [halfInd, if_neg, mul_zero]
        rintro ⟨hm, -⟩
        apply hl
        have := hdm _ hm
        rw [dil_add] at this
        simpa using sub_mem this (hyl x)
    · rw [if_neg (fun h => ht ((isHalf_dil i hϖ' t).1 h.1))]
      rw [mul_zero]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [halfInd, if_neg, mul_zero]
      rintro ⟨-, hh⟩
      exact ht (isHalf_of_add hh (hyh x))

end GlobalTheory.LiftFour
