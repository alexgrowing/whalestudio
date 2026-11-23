import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointwiseStabiliserParametrisationBijective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReductionSurjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemIntegralGlOfMiddleBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists

namespace Formalism.FourierDecayAlt.P.FrameLevelIndices

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_one)
open Formalism.FourierDecayAlt.S3

section Index

variable {A : Type} [CommRing A] {r k : ℕ}

theorem pointwise_subgroup_le_parabolic : (S3x1.s0G : Subgroup (GL (Idx r k) A)) ≤ S3x1.parG (r := r) (S3x1.gpUnit (A := A) (k := k)) := by
  intro g hg
  exact ((S3x1.mem_pointwise_stabiliser_iff _).1 hg).1

theorem card_s0G : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsInertiaInfiniteCyclotomic x} =
    Nat.card (S3x1.s0G : Subgroup (GL (Idx r k) A)) := by
  refine S3x2.card_of_subgroupSet _ _ fun x => ⟨fun hx => ?_, ?_⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (S3x1.par_det S3x1.gpUnit ((S3x1.mem_pointwise_stabiliser_iff x).1 hx).1), hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact hg

theorem card_sG : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (S3x1.parG (r := r) (S3x1.gpUnit (A := A) (k := k))) := by
  refine S3x2.card_of_subgroupSet _ _ fun x => ⟨fun hx => ?_, ?_⟩
  · exact ⟨Matrix.GeneralLinearGroup.mk'' x (S3x1.par_det S3x1.gpUnit ((S3x1.isS_iff x).1 hx)),
      (S3x1.isS_iff x).1 hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact (S3x1.isS_iff _).2 hg

end Index

section Local

variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}

theorem first_congruence_eq_reduction_comap (M : FrameLevel o r k) :
    M.K1 = (S3x1.s0G : Subgroup (GL (Idx r k) (IsLocalRing.ResidueField o))).comap (red o (Idx r k)) := by
  ext x
  rw [M.mem_parahoricTimesPrincipalCongruence_iff, Subgroup.mem_comap]
  rfl

theorem Knat_eq (L : Levels o r k) :
    L.Knat = (S3x1.parG (r := r) (S3x1.gpUnit (A := IsLocalRing.ResidueField o) (k := k))).comap
      (red o (Idx r k)) := by
  ext x
  rw [L.mem_Knat, Subgroup.mem_comap, S3x1.isS_iff]
  rfl

end Local

noncomputable def fac (q x : ℕ) : ℝ := 1 - ((q : ℝ) ^ (x + 1))⁻¹

theorem densityProduct_eq_prod_range (q a m : ℕ) :
    densP 1 q ((a : ℤ) + 1) ((a + m : ℕ) : ℤ) = ∏ x ∈ range m, fac q (a + x) := by
  unfold densP
  refine Finset.prod_nbij' (fun i => (i - a - 1).toNat) (fun x => (a : ℤ) + 1 + x) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro x hx
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    omega
  · intro x hx
    show ((a : ℤ) + 1 + x - a - 1).toNat = x
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    obtain ⟨x, rfl⟩ : ∃ x : ℕ, i = (a : ℤ) + 1 + x := ⟨(i - a - 1).toNat, by omega⟩
    have e1 : ((a : ℤ) + 1 + x - a - 1).toNat = x := by omega
    have e2 : (a : ℤ) + 1 + x = ((a + x + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, fac]
    simp only [Int.cast_one, one_pow, one_mul, _root_.zpow_neg, zpow_natCast]

theorem gl_real (q n : ℕ) (hq : 1 ≤ q) :
    ((∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) : ℕ) : ℝ) = (q : ℝ) ^ (n * n) * ∏ x ∈ range n, fac q x := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hpow : (q : ℝ) ^ (n * n) = ∏ _x ∈ range n, (q : ℝ) ^ n := by
    rw [Finset.prod_const, Finset.card_range, pow_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n, ← Finset.prod_range_reflect, Nat.cast_prod,
    hpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega)), fac]
  have e : n = (n - 1 - j) + (j + 1) := by omega
  push_cast
  conv_lhs => rw [e]
  conv_rhs => rw [e]
  have e' : n - 1 - j + (j + 1) - 1 - j = n - 1 - j := by omega
  rw [e', pow_add]
  field_simp

theorem card_GL_idx (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card (GL (Idx r k) K) = Nat.card (GL (Fin (k + 2 * r + 1)) K) := by
  have e : Idx r k ≃ Fin (k + 2 * r + 1) := Fintype.equivFinOfCardEq (by simp; ring)
  exact Nat.card_congr (Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv).toEquiv

section Om

variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}

theorem kppO_mul {j j' : Matrix (Idx r k) (Idx r k) o} (h : KppO j) (h' : KppO j') : KppO (j * j') := by
  refine ⟨by rw [Matrix.det_mul]; exact h.1.mul h'.1, ?_⟩
  rw [Matrix.map_mul, S3x1.isNU_iff]
  exact S3x1.par_mul S3x1.gpUni ((S3x1.isNU_iff _).1 h.2) ((S3x1.isNU_iff _).1 h'.2)

theorem kppO_inv {j : Matrix (Idx r k) (Idx r k) o} (h : KppO j) : KppO j⁻¹ := by
  refine ⟨Matrix.isUnit_nonsing_inv_det j h.1, ?_⟩
  rw [S3x1.isNU_iff]
  refine S3x1.par_rinv S3x1.gpUni ((S3x1.isNU_iff _).1 h.2) ?_
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h.1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem kppO_of_isN {n : Matrix (Idx r k) (Idx r k) o} (hn : IsN n) : KppO n := by
  refine ⟨by rw [S3x3.det_of_isN hn]; exact isUnit_one, ?_⟩
  exact ⟨_, 1, S3x3.isN_map _ hn, ⟨1, isUpUni_one _, S3x1.hEmb_one.symm⟩, (Matrix.mul_one _).symm⟩

theorem kppO_hEmb {h : Matrix (Fin k) (Fin k) o} (hd : IsUnit h.det)
    (hu : IsUpUni (h.map (IsLocalRing.residue o))) : KppO (hEmb r h) := by
  refine ⟨by rw [S3x3.det_hEmb]; exact hd, ?_⟩
  exact ⟨1, _, (S3x1.isN_iff _).2 (S3x1.par_one S3x1.gpOne), ⟨_, hu, rfl⟩, by
    rw [S3x3.hEmb_map, Matrix.one_mul]⟩

end Om

end Formalism.FourierDecayAlt.P.FrameLevelIndices

namespace Formalism.FourierDecayAlt.P

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.FrameLevelIndices

theorem first_congruence_index : Formalism.FourierDecayAlt.S3.CongruenceLevelIndex := by
  intro o _ _ _ r k L M
  refine ⟨?_, ?_⟩
  · rw [first_congruence_eq_reduction_comap M, Knat_eq L]
    exact Subgroup.comap_mono pointwise_subgroup_le_parabolic
  · rw [first_congruence_eq_reduction_comap M, Knat_eq L, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (S3x2.red_surjective o _)]
    have : Fintype (IsLocalRing.ResidueField o) := Fintype.ofFinite _
    have h1 := Subgroup.relIndex_mul_relIndex ⊥
      (S3x1.s0G : Subgroup (GL (Idx r k) (IsLocalRing.ResidueField o)))
      (S3x1.parG (r := r) (S3x1.gpUnit (A := IsLocalRing.ResidueField o) (k := k))) bot_le pointwise_subgroup_le_parabolic
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, ← card_s0G, ← card_sG,
      card_pointwise_stabiliser (IsLocalRing.ResidueField o) r k, ← Nat.card_eq_fintype_card] at h1
    have hpos : 0 < Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsInertiaInfiniteCyclotomic x} := by
      rw [card_s0G]; exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem frameIndex_statement : Formalism.FourierDecayAlt.S3.FrameIndex := by
  intro K _ _ r k
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [card_GL_idx, Matrix.card_GL_field, card_frame_stabiliser K r k, card_unipotent_radical K r k, Matrix.card_GL_field,
    gl_real _ _ hq, Nat.cast_mul, gl_real _ _ hq,
    show k + 2 * r + 1 = k + (2 * r + 1) from rfl, densityProduct_eq_prod_range, Finset.prod_range_add,
    show ((r : ℤ) + 1) * (2 * k + 2 * r + 1) = (((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, Nat.cast_pow]
  have e : (k + (2 * r + 1)) * (k + (2 * r + 1)) =
      k * k + (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) + (r + 1) * (2 * k + 2 * r + 1) := by
    rcases r with _ | r
    · simp; ring
    · simp only [Nat.add_sub_cancel]; ring
  rw [e, pow_add, pow_add]
  ring

theorem omStable_statement : Formalism.FourierDecayAlt.S3.OmStable := by
  intro o _ _ _ ϖ hϖ r k j n n' h hj hn hn' hd hu
  obtain ⟨hK, X, hX, hcm⟩ := hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨kppO_mul (kppO_mul (kppO_of_isN hn) hK) (kppO_of_isN hn'), b33 n * X * b11 n', ?_, ?_⟩
    · obtain ⟨-, -, -, -, n31, n32⟩ := hn
      obtain ⟨-, -, -, n21', n31', -⟩ := hn'
      rw [S3x1.block31_mul, S3x1.block31_mul, n31, n32, n21', n31', hX]
      simp
    · intro l hl
      rw [S3x7.corner_invariant hn.2.1 hn'.1]
      exact hcm l hl
  · refine ⟨kppO_mul (kppO_hEmb hd hu) hK, X, ?_, hcm⟩
    rw [S3x1.block31_mul, S3x1.levi_embedding_block31, S3x1.levi_embedding_block32, S3x1.levi_embedding_block33, hX]
    simp
  · refine ⟨kppO_mul hK (kppO_hEmb hd hu), X, ?_, hcm⟩
    rw [S3x1.block31_mul, S3x1.levi_embedding_block11, S3x1.levi_embedding_block21, S3x1.levi_embedding_block31, hX]
    simp
  · obtain ⟨Y, hY, -, hYc⟩ := S3x7.inverse_corner hϖ j X hK hX
    refine ⟨kppO_inv hK, Y, hY, fun l hl => ?_⟩
    have h1 : IsLocalRing.residue o (cm X l hl) ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact hcm l hl
    have h2 : IsLocalRing.residue o (cm Y l hl) ≠ 0 := by
      rw [hYc l hl]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h2
    exact h2

end Formalism.FourierDecayAlt.P
