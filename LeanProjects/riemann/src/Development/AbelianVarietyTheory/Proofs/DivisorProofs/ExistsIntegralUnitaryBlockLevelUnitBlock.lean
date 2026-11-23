import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedCompleteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentPowerLimitCongruentOneStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.BlockPoint

variable {D : D7}

theorem det_mem_OhE {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D)) (hM : ∀ i j, M i j ∈ OhE D) : M.det ∈ OhE D := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hM _ _)

theorem one_mem_OhE {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem adjugate_mem_OhE {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D)) (hM : ∀ i j, M i j ∈ OhE D) (i j : Fin n) :
    M.adjugate i j ∈ OhE D := by
  classical
  rw [Matrix.adjugate_apply]
  refine det_mem_OhE _ fun k l => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact hM _ _

theorem exists_sep (𝔪 : Ideal (𝓞 D.host.E)) (hco : IsCoprime 𝔪 (D.host.conj • 𝔪)) :
    ∃ T ∈ OhE D, 1 - T ∈ hatId D 𝔪 ∧ sgA D T ∈ hatId D 𝔪 := by
  have hsup : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ := by
    rw [← Ideal.add_eq_sup, Ideal.isCoprime_iff_add.1 hco, Ideal.one_eq_top]
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ D.host.conj • 𝔪 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  refine ⟨inc D (t : D.host.E), VacMove.inc_int D t, ?_, ?_⟩
  · have e : 1 - inc D (t : D.host.E) = inc D (s : D.host.E) * 1 := by
      rw [mul_one, ← map_one (inc D), ← map_sub]
      congr 1
      have h3 := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hst
      push_cast at h3
      linear_combination -h3
    rw [e]
    exact AddSubgroup.subset_closure ⟨s, hs, 1, one_mem _, rfl⟩
  · have h1 : inc D (t : D.host.E) ∈ hatId D (D.host.conj • 𝔪) :=
      AddSubgroup.subset_closure ⟨t, ht, 1, one_mem _, (mul_one _).symm⟩
    have h2 := DetCong.sgA_mem_hatId h1
    have hcc : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
    rwa [smul_smul, hcc, one_smul] at h2

theorem block_inv_mul {a d : ℕ} (had : a ≤ d) (𝔪 : Ideal (𝓞 D.host.E)) (H H' : Matrix (Fin d) (Fin d) (AE D))
    (hH' : ∀ i j, H' i j ∈ OhE D) (hHH : H' * H = 1)
    (hC : ∀ i j : Fin d, j.1 < a → a ≤ i.1 → H i j ∈ hatId D 𝔪) (i j : Fin a) :
    ((Matrix.of fun i j : Fin a => H' (Fin.castLE had i) (Fin.castLE had j)) *
      (Matrix.of fun i j : Fin a => H (Fin.castLE had i) (Fin.castLE had j)) - 1) i j ∈ hatId D 𝔪 := by
  classical
  have e1 : (1 : Matrix (Fin a) (Fin a) (AE D)) i j = (H' * H) (Fin.castLE had i) (Fin.castLE had j) := by
    rw [hHH, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castLE_inj]
  have e3 : Finset.univ.filter (fun l : Fin d => l.1 < a) = Finset.univ.map (Fin.castLEEmb had) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hl; exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨l', rfl⟩; exact l'.2
  rw [Matrix.sub_apply, e1, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin d => l.1 < a), e3, Finset.sum_map]
  simp only [Matrix.of_apply, Fin.castLEEmb_apply]
  rw [sub_add_cancel_left]
  refine neg_mem (sum_mem fun l hl => mul_mem_hatId (hH' _ _) (hC l _ j.2 ?_))
  exact not_lt.1 (Finset.mem_filter.1 hl).2

section Glue

variable {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}

theorem ct_comb (hσ : ∀ x, σ (σ x) = x) (f g c : R) (M N : Matrix (Fin n) (Fin n) R) :
    ((f • M + g • (N.map σ).transpose + c • (1 : Matrix (Fin n) (Fin n) R)).map σ).transpose =
      σ f • (M.map σ).transpose + σ g • N + σ c • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [hσ]
  · simp [hσ, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

theorem glue_mul_ct (hσ : ∀ x, σ (σ x) = x) (M B : Matrix (Fin n) (Fin n) R) (f0 f e : R) (hidem : f0 * f0 = f0)
    (hf : f = f0 * (1 - σ f0)) (he : e = 1 - f - σ f) (hAB : M * B = f0 • (1 : Matrix (Fin n) (Fin n) R)) :
    (f • M + σ f • (B.map σ).transpose + e • (1 : Matrix (Fin n) (Fin n) R)) *
      ((f • M + σ f • (B.map σ).transpose + e • (1 : Matrix (Fin n) (Fin n) R)).map σ).transpose = 1 := by
  have hs0 : σ f0 * σ f0 = σ f0 := by rw [← map_mul, hidem]
  have sf : σ f = σ f0 * (1 - f0) := by rw [hf, map_mul, map_sub, map_one, hσ]
  have se : σ e = e := by rw [he, map_sub, map_sub, map_one, hσ]; ring
  have hBA : (B.map σ).transpose * (M.map σ).transpose = σ f0 • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hAB]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have hff : f * f = f := by rw [hf]; linear_combination (1 - σ f0) ^ 2 * hidem + f0 * hs0
  have hgg : σ f * σ f = σ f := by rw [← map_mul, hff]
  have hfg : f * σ f = 0 := by rw [sf, hf]; linear_combination (σ f0 * σ f0 - σ f0) * hidem
  have hgf : σ f * f = 0 := by rw [mul_comm, hfg]
  have hfe : f * e = 0 := by rw [he]; linear_combination -hff - hfg
  have hef : e * f = 0 := by rw [mul_comm, hfe]
  have hge : σ f * e = 0 := by rw [he]; linear_combination -hgg - hfg
  have heg : e * σ f = 0 := by rw [mul_comm, hge]
  have hee : e * e = e := by rw [he]; linear_combination hff + hgg + 2 * hfg
  have hff0 : f * f0 = f := by rw [hf]; linear_combination (1 - σ f0) * hidem
  have hgs0 : σ f * σ f0 = σ f := by rw [sf]; linear_combination (1 - f0) * hs0
  rw [ct_comb σ hσ, hσ, se]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_add]
  simp only [hff, hfg, hgf, hfe, hef, hge, heg, hgg, hee, zero_smul, add_zero, zero_add]
  rw [hAB, hBA, smul_smul, smul_smul, hff0, hgs0, ← add_smul, ← add_smul, he]
  rw [show σ f + f + (1 - f - σ f) = 1 by ring, one_smul]

theorem ct_ct (hσ : ∀ x, σ (σ x) = x) (M : Matrix (Fin n) (Fin n) R) :
    (((M.map σ).transpose).map σ).transpose = M := by
  ext i j; simp [hσ]

end Glue

theorem exists_unitary_near {a : ℕ} (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥) (hco : IsCoprime 𝔪 (D.host.conj • 𝔪))
    (A : Matrix (Fin a) (Fin a) (AE D)) (hA : ∀ i j, A i j ∈ OhE D) (δ' : AE D) (hδ' : δ' ∈ OhE D)
    (hδ : δ' * A.det - 1 ∈ hatId D 𝔪) :
    ∃ k ∈ intG D a, ∀ i j, (A - (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
      hatId D 𝔪 := by
  obtain ⟨T, hT, hT1, hTs⟩ := exists_sep 𝔪 hco
  have hdet := det_mem_OhE A hA
  have hy : T * (A.det * δ') ∈ OhE D := mul_mem hT (mul_mem hdet hδ')
  have hy1 : T * (A.det * δ') - 1 ∈ hatId D 𝔪 := by
    have e : T * (A.det * δ') - 1 = T * (δ' * A.det - 1) - (1 - T) := by ring
    rw [e]
    exact sub_mem (mul_mem_hatId hT hδ) hT1
  obtain ⟨g, hg, hidem, hf1⟩ := GlobalTheory.T.exists_idempotent_powerLimit_congruentOne D 𝔪 h𝔪 _ hy hy1
  obtain ⟨f0, hf0⟩ : ∃ f0, f0 = T * (A.det * δ') * g := ⟨_, rfl⟩
  rw [← hf0] at hidem hf1
  have hf0O : f0 ∈ OhE D := hf0 ▸ mul_mem hy hg
  have hs0O : sgA D f0 ∈ OhE D := VacMove.sgA_mem D hf0O
  have hs0m : sgA D f0 ∈ hatId D 𝔪 := by
    have e : sgA D f0 = sgA D T * sgA D ((A.det * δ') * g) := by rw [hf0, mul_assoc, map_mul]
    rw [e]
    exact mem_hatId_mul (VacMove.sgA_mem D (mul_mem (mul_mem hdet hδ') hg)) hTs
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin a) (Fin a) (AE D), B = (T * δ' * g) • A.adjugate := ⟨_, rfl⟩
  have hAB : A * B = f0 • (1 : Matrix (Fin a) (Fin a) (AE D)) := by
    rw [hB, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hf0]
    congr 1; ring
  have hBO : ∀ i j, B i j ∈ OhE D := fun i j => by
    rw [hB, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (mul_mem (mul_mem hT hδ') hg) (adjugate_mem_OhE A hA i j)
  obtain ⟨f, hf⟩ : ∃ f, f = f0 * (1 - sgA D f0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = 1 - f - sgA D f := ⟨_, rfl⟩
  have sf : sgA D f = sgA D f0 * (1 - f0) := by rw [hf, map_mul, map_sub, map_one, VacMove.sgA_sgA]
  have hfO : f ∈ OhE D := hf ▸ mul_mem hf0O (sub_mem (one_mem _) hs0O)
  have hgO : sgA D f ∈ OhE D := VacMove.sgA_mem D hfO
  have heO : e ∈ OhE D := he ▸ sub_mem (sub_mem (one_mem _) hfO) hgO
  have hgm : sgA D f ∈ hatId D 𝔪 := by
    rw [sf]; exact mem_hatId_mul (sub_mem (one_mem _) hf0O) hs0m
  have h1f : 1 - f ∈ hatId D 𝔪 := by
    have e1 : 1 - f = -(f0 - 1) + f0 * sgA D f0 := by rw [hf]; ring
    rw [e1]
    exact add_mem (neg_mem hf1) (mul_mem_hatId hf0O hs0m)
  have hem : e ∈ hatId D 𝔪 := by rw [he]; exact sub_mem h1f hgm
  have hKK := glue_mul_ct (sgA D) (VacMove.sgA_sgA D) A B f0 f e hidem hf he hAB
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin a) (Fin a) (AE D),
      K = f • A + sgA D f • (B.map (sgA D)).transpose + e • (1 : Matrix (Fin a) (Fin a) (AE D)) := ⟨_, rfl⟩
  rw [← hK] at hKK
  have hKO : ∀ i j, K i j ∈ OhE D := fun i j => by
    rw [hK]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.map_apply]
    exact add_mem (add_mem (mul_mem hfO (hA i j)) (mul_mem hgO (VacMove.sgA_mem D (hBO j i))))
      (mul_mem heO (one_mem_OhE i j))
  let kGL : GL (Fin a) (AE D) := ⟨(K.map (sgA D)).transpose, K, mul_eq_one_comm.1 hKK, hKK⟩
  have hmem : kGL ∈ GA D a := by
    rw [PtsMem.mem_GA]
    show (((K.map (sgA D)).transpose).map (sgA D)).transpose * (K.map (sgA D)).transpose = 1
    rw [ct_ct (sgA D) (VacMove.sgA_sgA D)]
    exact hKK
  refine ⟨⟨kGL, hmem⟩, (mem_intG _).2 fun i j => ⟨?_, hKO i j⟩, fun i j => ?_⟩
  · show sgA D (K j i) ∈ OhE D
    exact VacMove.sgA_mem D (hKO j i)
  · show (A - K) i j ∈ hatId D 𝔪
    have e2 : (A - K) i j = (1 - f) * A i j - sgA D f * sgA D (B j i) -
        e * (1 : Matrix (Fin a) (Fin a) (AE D)) i j := by
      rw [hK]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply,
        Matrix.map_apply]
      ring
    rw [e2]
    exact sub_mem (sub_mem (mem_hatId_mul (hA i j) h1f) (mem_hatId_mul (VacMove.sgA_mem D (hBO j i)) hgm))
      (mem_hatId_mul (one_mem_OhE i j) hem)

theorem exists_intG_unitBlock : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ {a d : ℕ}, a ≤ d →
    ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 →
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) →
    ∃ k ∈ intG D a, ∀ i j, (((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D 0 a d).map (inc D) -
      (unitBlock D 0 a d).map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
        hatId D 𝔪 := by
  intro D 𝔪 h𝔪 hco a d had h hh hC
  have hint := (mem_intG h).1 hh
  have hHH : ((((h : GL (Fin d) (AE D))⁻¹ : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) *
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))) = 1 := Units.inv_mul _
  have hAA := block_inv_mul had 𝔪 _ _ (fun i j => (hint i j).2) hHH hC
  have hAAO : ∀ i j, ((Matrix.of fun i j : Fin a => (((h : GL (Fin d) (AE D))⁻¹ : GL (Fin d) (AE D)) :
      Matrix (Fin d) (Fin d) (AE D)) (Fin.castLE had i) (Fin.castLE had j)) *
      (Matrix.of fun i j : Fin a => ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))
        (Fin.castLE had i) (Fin.castLE had j))) i j ∈ OhE D := fun i j => by
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (hint _ _).2 (hint _ _).1
  have hδ := DetCong.det_sub_one_mem_hatId_of _ hAAO hAA
  rw [Matrix.det_mul] at hδ
  obtain ⟨k, hk, hK⟩ := exists_unitary_near 𝔪 h𝔪 hco _ (fun i j => (hint _ _).1) _
    (det_mem_OhE _ fun i j => (hint _ _).2) hδ
  refine ⟨k, hk, fun i j => ?_⟩
  have hHP : (((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D 0 a d).map (inc D)) i j =
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i (Fin.castLE had j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE had j)]
    · simp [unitBlock]
    · intro l _ hl
      have : l.1 ≠ j.1 := fun e => hl (Fin.ext (by simpa using e))
      have e0 : (unitBlock D 0 a d).map (inc D) l j = 0 := by simp [unitBlock, this]
      rw [e0, mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  rw [Matrix.sub_apply, hHP, Matrix.mul_apply]
  by_cases hi : i.1 < a
  · rw [Finset.sum_eq_single ⟨i.1, hi⟩]
    · have e1 : (unitBlock D 0 a d).map (inc D) i ⟨i.1, hi⟩ = 1 := by simp [unitBlock]
      rw [e1, one_mul]
      have := hK ⟨i.1, hi⟩ j
      exact this
    · intro l _ hl
      have : i.1 ≠ l.1 := fun e => hl (Fin.ext (by simp [e]))
      have e0 : (unitBlock D 0 a d).map (inc D) i l = 0 := by simp [unitBlock, this]
      rw [e0, zero_mul]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · rw [Finset.sum_eq_zero fun l _ => by
      have : i.1 ≠ l.1 := by have := l.2; omega
      have e0 : (unitBlock D 0 a d).map (inc D) i l = 0 := by simp [unitBlock, this]
      rw [e0, zero_mul], sub_zero]
    exact hC i _ j.2 (not_lt.1 hi)

end GlobalTheory.FunObj.StdDatum.BlockPoint

end
