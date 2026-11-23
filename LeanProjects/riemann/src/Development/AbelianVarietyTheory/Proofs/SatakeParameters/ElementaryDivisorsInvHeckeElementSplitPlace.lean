import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMulStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFactsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletedLatticeBasisAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDivisors

section Algebra

variable {R : Type} [CommRing R] {n : ℕ} {ε : R} {A B C : Matrix (Fin n) (Fin n) R}

theorem conj_diag_inv (h1 : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R))
    (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d d' : Fin n → R) (hd : ∀ i, d i * d' i = 1) :
    ε • ((B * Matrix.diagonal d * C) * (B * Matrix.diagonal d' * C)) = ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have h3 : Matrix.diagonal d * Matrix.diagonal d' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hd)
  calc ε • ((B * Matrix.diagonal d * C) * (B * Matrix.diagonal d' * C))
      = B * Matrix.diagonal d * (ε • (C * B)) * Matrix.diagonal d' * C := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = ε • (B * (Matrix.diagonal d * Matrix.diagonal d') * C) := by
        rw [h2]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by rw [h3, Matrix.mul_one, h1]

theorem conj_diag_mulVec (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d : Fin n → R)
    (hA : ε • A = ε • (B * Matrix.diagonal d * C)) {y z : Fin n → R}
    (h : (fun a => ε * y a) = fun a => ε * B.mulVec z a) :
    (fun a => ε * A.mulVec y a) = fun a => ε * B.mulVec (fun i => d i * z i) a := by
  have h' : ε • y = ε • B.mulVec z := h
  have h3 : (fun i => d i * z i) = (Matrix.diagonal d).mulVec z := funext fun i => (Matrix.mulVec_diagonal d z i).symm
  show ε • A.mulVec y = ε • B.mulVec (fun i => d i * z i)
  rw [← Matrix.smul_mulVec, hA, Matrix.smul_mulVec, ← Matrix.mulVec_smul, h', Matrix.mulVec_smul, h3,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, Matrix.mul_assoc _ C,
    ← Matrix.mul_smul, h2, Matrix.mul_smul, Matrix.mul_one]

theorem conj_diag_scale (hε : ε * ε = ε) (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d d' : Fin n → R)
    (x : R) (hd : ∀ i, d i * d' i = x) (hA : ε • A = ε • (B * Matrix.diagonal d * C)) {y z : Fin n → R}
    (h : (fun a => ε * y a) = fun a => ε * B.mulVec z a) :
    (fun a => ε * (x * y a)) = fun a => ε * A.mulVec (fun a => ε * B.mulVec (fun i => d' i * z i) a) a := by
  rw [conj_diag_mulVec h2 d hA (z := fun i => d' i * z i) (funext fun a => by rw [← mul_assoc, hε])]
  have h1 : (fun i => d i * (d' i * z i)) = x • z := funext fun i => by
    rw [← mul_assoc, hd, Pi.smul_apply, smul_eq_mul]
  rw [h1, Matrix.mulVec_smul]
  funext a
  rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, congrFun h a, mul_left_comm]

theorem det_congr (hε : ε * ε = ε) (h : ε • A = ε • B) : ε * A.det = ε * B.det := by
  have h1 : ε * ε ^ Fintype.card (Fin n) = ε := by
    rw [← pow_succ']; exact IsIdempotentElem.pow_succ_eq _ hε
  have h2 := congrArg (fun M => ε * Matrix.det M) h
  simpa only [Matrix.det_smul, ← mul_assoc, h1] using h2

theorem conj_diag_det (hε : ε * ε = ε) (h1 : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d : Fin n → R)
    (hA : ε • A = ε • (B * Matrix.diagonal d * C)) : ε * A.det = ε * ∏ i, d i := by
  have h2 := det_congr hε h1
  rw [Matrix.det_mul, Matrix.det_one] at h2
  rw [det_congr hε hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  linear_combination (∏ i, d i) * h2

end Algebra

theorem getD_label (n k i : ℕ) :
    (List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i 0 = if i < k then 1 else 0 := by
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using h)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem dualLab_label (n k : ℕ) : dualLab (List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0) = splitLab n k := by
  simp [dualLab, splitLab]

theorem prod_label {R : Type} [CommRing R] (x : R) {n k : ℕ} (h : k ≤ n) :
    (∏ i : Fin n, if i.1 < k then x else 1) = x ^ k := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Fin.card_filter_val_lt, min_eq_right h]

theorem int_mul_mem (D : D7) (u : 𝓞 D.host.E) {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    finPart D (incA D (u : D.host.E)) * y ∈ intAE D := by
  refine AddSubgroup.closure_induction (p := fun y _ => finPart D (incA D (u : D.host.E)) * y ∈ intAE D) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨b, hb, u * v, ?_⟩
    show ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x _ h; rw [mul_neg]; exact neg_mem h

theorem one_mem_int (D : D7) : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩

set_option maxHeartbeats 1000000 in

theorem exists_model {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (he : IsIdemAt e P) (h0 : (ϖ : D.host.E) ≠ 0) (hk : k ≤ V.rank) :
    ∃ α : GA D V, IsHeckeElt V e (ϖ : D.host.E) k α ∧
      DivAt V e (ϖ : D.host.E) (List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0) α := by
  obtain ⟨B, hB1, hB2⟩ := GlobalTheory.T.exists_completedLattice_basis_at_prime V P e he
  have hε : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he.1.1]
  obtain ⟨C, hC1, hC2⟩ := (GlobalTheory.T.completedLattice_integrality V).2.2 (finPart D e) B hε fun y hy => (hB2 y hy).imp fun _ h => h.2
  obtain ⟨d, hd⟩ : ∃ d : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
    ∀ i, d i = if i.1 < k then finPart D (incA D (ϖ : D.host.E)) else 1 := ⟨_, fun _ => rfl⟩
  have hdc : ∀ i : Fin V.rank, finPart D (incA D ((ϖ : D.host.E) ^
      ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0))) = d i := fun i => by
    rw [getD_label, hd]
    split_ifs
    · rw [zpow_one]
    · rw [zpow_zero, RingHom.map_one, RingHom.map_one]
  obtain ⟨α, hs, hα⟩ := GlobalTheory.T.exists_adelic_unitary_split_place_component V e he.1 (B * Matrix.diagonal d * C) _
    (conj_diag_inv hC1 hC2 d (fun i => if i.1 < k then finPart D (incA D (ϖ : D.host.E)⁻¹) else 1) fun i => by
      rw [hd]
      split_ifs
      · rw [← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ h0, RingHom.map_one, RingHom.map_one]
      · exact mul_one _)
  have idem : ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (fun a => finPart D e * (finPart D e * y a)) = fun a => finPart D e * y a := fun y =>
    funext fun a => by rw [← mul_assoc, hε]
  refine ⟨α, ⟨((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e (e + cA D e) (Or.inl ⟨he, rfl⟩)).2.2.1 α hs, hs, fun y hy => ?_,
    fun y hy => ?_, 1, 1, ?_, ?_, ?_, ?_⟩, ?_, B, hB1, hB2, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    rw [conj_diag_mulVec hC2 d hα h]
    refine hB1 _ fun i => ?_
    rw [hd]
    split_ifs
    · exact int_mul_mem D ϖ (hz i)
    · rw [one_mul]; exact hz i
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    refine ⟨_, hB1 (fun i => (if i.1 < k then 1 else finPart D (incA D (ϖ : D.host.E))) * z i) fun i => ?_, ?_⟩
    · beta_reduce
      split_ifs
      · rw [one_mul]; exact hz i
      · exact int_mul_mem D ϖ (hz i)
    · refine conj_diag_scale hε hC2 d _ _ (fun i => ?_) hα h
      rw [hd]
      split_ifs
      · exact mul_one _
      · exact one_mul _
  · rw [RingHom.map_one]; exact one_mem_int D
  · rw [RingHom.map_one]; exact one_mem_int D
  · rw [mul_one, mul_one]
  · refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he.1, zero_mul]
    · have h1 := conj_diag_det hε hC1 d hα
      rw [funext hd, prod_label _ hk] at h1
      rw [mul_one, (finPart D).map_mul, (finPart D).map_mul, (finPart D).map_pow, (finPart D).map_det]
      exact h1
  · rw [List.length_append, List.length_replicate, List.length_replicate]; omega
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    refine ⟨z, hz, ?_⟩
    simp only [hdc]
    exact conj_diag_mulVec hC2 d hα h
  · refine ⟨_, hB1 z hz, ?_⟩
    simp only [hdc]
    exact conj_diag_mulVec hC2 d hα (idem _)

theorem divAt_inv_of_isHeckeElt : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → k ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) k α → DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ := by
  intro D V P e ϖ k α he h1 h2 hk hα
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
  obtain ⟨α₀, hH, hD⟩ := exists_model V P e ϖ k he h0 hk
  obtain ⟨a, ha, b, hb, rfl⟩ := (((GlobalTheory.T.involution_spherical_hecke_anti V P e he).2.2 ϖ h1 h2).2 k α₀ hH).2 ϖ α h1 h2 hα
  rw [← dualLab_label]
  exact (GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e _ _ _ he.1.1 h0 ((GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e _ _ _ he.1.1 h0 hD).2 a ha.1 b hb.1)).1

end GlobalTheory.SplitDivisors
