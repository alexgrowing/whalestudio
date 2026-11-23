import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationDistinctCharactersSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetPairInducedFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlotCharactersDistinctStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedDetTwistPairCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistInducedMemFullRankSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalThreeBlockStandardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLeviEmbeddingModularCharacterStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IndJacBlock
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.FullRankCoinv.IndTwist

set_option maxHeartbeats 1000000 in

theorem position_coeff : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ), 1 ≤ n → 2 * n < d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
  ∀ ℓ : (GL (Fin d) k → ℂ) →ₗ[ℂ] ℂ,
    (∀ u : GL (Fin d) k, GlobalTheory.JacBlock₂.IsUnipStd u → ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ℓ (fun h => f (h * u)) = ℓ f) →
    ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ p q : ℂ, ∀ x : kˣ,
      ℓ (fun h => f (h * GlobalTheory.JacBlock₂.diagFirst x)) = p + q * (((ν x)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow x (((d : ℂ) - 2 * (n : ℂ)) / 2) := by
  intro hK k _ _ _ _ n d ν hn hnd hνs hνu ℓ hℓ f hf
  have h2 : 2 ≤ d := by omega
  have hnd' : n ≤ d := by omega
  set s : ℂ := (n : ℂ) / 2 with hs
  set π := pairInd k (b2 n d) (block_size_pair_sum hnd') (chi2 k ν) with hπ
  let L : IndSp (pairPlace (b2 n d) (block_size_pair_sum hnd')) (ofChar (pairChar k (b2 n d) (chi2 k ν))) →ₗ[ℂ] ℂ :=
    ℓ ∘ₗ detTw d (-s) ∘ₗ (Submodule.subtype _) ∘ₗ (Submodule.subtype _)
  have hL : ∀ F, L F = ℓ (detTw d (-s) F.1.1) := fun F => rfl

  have htr : ∀ (F : IndSp (pairPlace (b2 n d) (block_size_pair_sum hnd')) (ofChar (pairChar k (b2 n d) (chi2 k ν)))) (g : GL (Fin d) k),
      ℓ (fun h => detTw d (-s) F.1.1 (h * g)) = GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (-s) * L (π g F) := by
    intro F g
    rw [detTw_translate, map_smul, smul_eq_mul, hL]
    rfl
  have hker : twKer π (unipRad k (place3 h2)) 1 ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, F, rfl⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, SetLike.mem_coe, LinearMap.mem_ker, map_sub]
    have hdet : GlobalTheory.SplitFlip.gdet (u : GL (Fin d) k) = 1 := det_eq_one_of_mem_unipRad k u.2
    have h1 := htr F u
    rw [hdet, GlobalTheory.SplitFlip.apow_one, one_mul] at h1
    rw [← h1, hℓ u (GlobalTheory.T.unipotent_radical_three_block_standard k d h2 u u.2) _ (GlobalTheory.T.det_twist_induced_mem_full_rank_space k n d hnd' ν F), hL, sub_self]
  let Lbar := (twKer π (unipRad k (place3 h2)) 1).liftQ L hker
  obtain ⟨F, hF⟩ := GlobalTheory.T.induced_det_twist_pair_character k n d hnd' ν f hf
  have hfF : f = detTw d (-s) F.1.1 := by rw [hF, detTw_neg_detTw]
  have hχs : ∀ j, IsSmoothChar (chi2 k ν j) := fun j => by
    unfold chi2; split_ifs
    · exact isSmoothChar_one
    · exact hνs.inv
  obtain ⟨M, S, r, r', hS, h0, htop, hinj, hstep⟩ :=
    GlobalTheory.T.jacquet_pair_induced_filtration hK.geometricLemmaFiltration k d h2 (b2 n d) (block_size_pair_sum hnd') (chi2 k ν) hχs
  have hdist : ∀ a t : Fin M, a ≠ t → ∃ p, cellChar₂ k (b2 n d) (chi2 k ν) (r a) (r' a) p ≠ cellChar₂ k (b2 n d) (chi2 k ν) (r t) (r' t) p := by
    intro a t hat
    refine GlobalTheory.T.position_characters_distinct k n d ν (by omega) hνu _ _ _ _ ?_
    by_contra hc
    push_neg at hc
    exact hat (hinj a t hc.1 hc.2)
  obtain ⟨w, hw, hwe⟩ := GlobalTheory.T.filtration_distinct_characters_split ((jac (place3 h2) π).comp (tor3 k d)) M S
    (fun t => cellChar₂ k (b2 n d) (chi2 k ν) (r t) (r' t)) hS h0 hstep hdist (Submodule.Quotient.mk F)
    (by rw [htop]; trivial)
  refine ⟨∑ t, (if r t = 0 then Lbar (w t) else 0), ∑ t, (if r t = 0 then 0 else Lbar (w t)), fun x => ?_⟩
  obtain ⟨hemb, hdel⟩ := GlobalTheory.T.torus_levi_embedding_modular_character k d h2 x
  have hgd : GlobalTheory.SplitFlip.gdet (GlobalTheory.JacBlock₂.diagFirst (d := d) x) = x := by
    ext
    simp only [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.JacBlock₂.diagFirst, Matrix.det_diagonal]
    rw [Finset.prod_eq_single (⟨0, by omega⟩ : Fin d)]
    · simp
    · intro i _ hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]
    · simp
  rw [hfF, htr, hgd, ← hemb]
  have hmk : ∀ v, L v = Lbar (Submodule.Quotient.mk v) := fun v => rfl
  have hjac : (Submodule.Quotient.mk (π (leviEmb k (place3 h2) (tor3 k d (x, 1))) F) :
      Jacquet π (unipRad k (place3 h2))) =
      (deltaHalf k (fun j : Fin 3 => Fin (sz3 d j)) (tor3 k d (x, 1)) : ℂ) •
        jac (place3 h2) π (tor3 k d (x, 1)) (Submodule.Quotient.mk F) := by
    have h := jac_mk (place3 h2) π (tor3 k d (x, 1)) (F : IndSp (pairPlace (b2 n d) (block_size_pair_sum hnd')) (ofChar (pairChar k (b2 n d) (chi2 k ν))))
    rw [h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hsum : jac (place3 h2) π (tor3 k d (x, 1)) (Submodule.Quotient.mk F) =
      ∑ t, cellChar₂ k (b2 n d) (chi2 k ν) (r t) (r' t) (x, 1) • w t := by
    rw [hw, map_sum]
    exact Finset.sum_congr rfl fun t _ => hwe t (x, 1)
  rw [hmk, hjac, hsum, hdel, map_smul, map_sum, smul_eq_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, smul_eq_mul]
  have hc : cellChar₂ k (b2 n d) (chi2 k ν) (r t) (r' t) (x, 1) =
      ((chi2 k ν (r t) x : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow x ((1 - (b2 n d (r t) : ℂ)) / 2) := by
    simp only [cellChar₂, map_one, mul_one, Units.val_mul]
    rfl
  rw [hc]
  rcases Fin.exists_fin_two.1 ⟨r t, rfl⟩ with h | h <;> rw [h]
  · have e1 : ((b2 n d 0 : ℕ) : ℂ) = (d : ℂ) - n := by simp [b2, Nat.cast_sub hnd']
    simp only [chi2, Fin.val_zero, if_true, MonoidHom.one_apply, Units.val_one, one_mul, e1, if_pos rfl]
    simp only [← mul_assoc, ← GlobalTheory.SplitFlip.apow_add]
    have : -s + (((d : ℂ) - 1) / 2 + (1 - ((d : ℂ) - n)) / 2) = 0 := by rw [hs]; ring
    rw [this, GlobalTheory.SplitFlip.apow_zero]; simp
  · have e1 : ((b2 n d 1 : ℕ) : ℂ) = n := by simp [b2]
    simp only [chi2, Fin.val_one, one_ne_zero, if_false, MonoidHom.inv_apply, e1]
    have : GlobalTheory.SplitFlip.apow x (-s) * GlobalTheory.SplitFlip.apow x (((d : ℂ) - 1) / 2) * GlobalTheory.SplitFlip.apow x ((1 - (n : ℂ)) / 2) =
        GlobalTheory.SplitFlip.apow x (((d : ℂ) - 2 * n) / 2) := by
      rw [← GlobalTheory.SplitFlip.apow_add, ← GlobalTheory.SplitFlip.apow_add]; congr 1; rw [hs]; ring
    rw [← this]
    simp only [Units.val_inv_eq_inv_val]
    ring

end GlobalTheory.IndJacBlock
