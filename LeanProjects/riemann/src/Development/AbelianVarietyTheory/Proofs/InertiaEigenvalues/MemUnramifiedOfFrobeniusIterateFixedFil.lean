import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.CrisPerFix

variable {l : ℕ} [Fact l.Prime]

def maxUnramifiedFrobenius (P : LocPrime l) (K : FinExt l) : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) :=
  AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij

theorem frobK0_apply (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) :
    maxUnramifiedFrobenius P K x = (P.PD K).σ x := rfl

theorem nontrivial_B (P : LocPrime l) (K : FinExt l) : Nontrivial P.R.B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact (P.PD K).not_mem_filtration_two (by rw [Subsingleton.elim ((P.PD K).t) 0, map_zero]; exact Submodule.zero_mem _)

theorem ιB_algebraMap (P : LocPrime l) (K : FinExt l) (a : ↥(K0 K)) :
    P.ιB (algebraMap ↥(K0 K) P.R.B a) = algebraMap ↥(K0 K) P.R.BdR a := by
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes a

theorem orderOf_frobK0 (P : LocPrime l) (K : FinExt l) :
    orderOf (maxUnramifiedFrobenius P K) = finrank ℚ_[l] ↥(K0 K) := by
  haveI := (P.PD K).finK₀
  haveI := nontrivial_B P K
  have hfix : IntermediateField.fixedField (Subgroup.zpowers (maxUnramifiedFrobenius P K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hσ : (P.PD K).σ x = x := hx _ (Subgroup.mem_zpowers _)
    obtain ⟨q, hq⟩ := (P.PD K).fund (algebraMap ↥(K0 K) P.R.B x)
      (by rw [(P.PD K).φ_K₀, hσ])
      (by
        rw [(P.PD K).ι.commutes, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_of_tower_mem _ x (P.PD K).one_mem)
    rw [IntermediateField.mem_bot]
    refine ⟨q, (algebraMap ↥(K0 K) P.R.B).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact hq
  have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers (maxUnramifiedFrobenius P K))
  rw [hfix, IntermediateField.finrank_bot', Nat.card_zpowers] at h
  exact h.symm

theorem iterate_φB_mul (P : LocPrime l) (K : FinExt l) (j : ℕ) (b : ↥(K0 K)) (x : P.R.B) :
    (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * x) =
      algebraMap ↥(K0 K) P.R.B ((maxUnramifiedFrobenius P K ^ j) b) * (⇑P.φB)^[j] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, ← P.PD_φ K (algebraMap _ _ _), (P.PD K).φ_K₀,
      Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, frobK0_apply]

theorem det_ne_zero (P : LocPrime l) (K : FinExt l)
    (bas : Module.Basis (Fin (finrank ℚ_[l] ↥(K0 K))) ℚ_[l] ↥(K0 K)) :
    (Matrix.of fun i j : Fin (finrank ℚ_[l] ↥(K0 K)) => (maxUnramifiedFrobenius P K ^ (j : ℕ)) (bas i)).det ≠ 0 := by
  set τ := maxUnramifiedFrobenius P K
  intro h
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  let L : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    { toFun := fun x => ∑ j : Fin (finrank ℚ_[l] ↥(K0 K)), u j * (τ ^ (j : ℕ)) x
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_smul_comm]
        congr 1
        exact (τ ^ (j : ℕ)).toLinearEquiv.map_smul r x }
  have hL : L = 0 := by
    refine bas.ext fun i => ?_
    have := congrFun hu i
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let f : Fin (finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →* ↥(K0 K)) := fun j => ((τ ^ (j : ℕ)).toRingEquiv : _ ≃+* _).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hi : (i : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  have li := (linearIndependent_monoidHom ↥(K0 K) ↥(K0 K)).comp f hf
  rw [Fintype.linearIndependent_iff] at li
  apply hu0
  funext j
  refine li u ?_ j
  funext x
  have := LinearMap.congr_fun hL x
  simpa [L, f, Finset.sum_apply, smul_eq_mul] using this

theorem mem_unramified_of_frobenius_iterate_fixed_fil_alt :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (c : P.R.B), (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] c = c →
    (∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0) →
    ∃ a : ↥(K0 K), c = algebraMap ↥(K0 K) P.R.B a := by
  intro l _ P _ _ K c hn hF
  set n := finrank ℚ_[l] ↥(K0 K) with hn_def
  haveI := (P.PD K).finK₀
  set τ := maxUnramifiedFrobenius P K
  have hord : orderOf τ = n := orderOf_frobK0 P K
  have hn0 : 0 < n := Module.finrank_pos
  let bas := Module.finBasisOfFinrankEq ℚ_[l] ↥(K0 K) hn_def.symm
  let A : Matrix (Fin n) (Fin n) ↥(K0 K) := Matrix.of fun i j => (τ ^ (j : ℕ)) (bas i)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero P K bas)
  have hs : ∀ b : ↥(K0 K), ∃ q : ℚ_[l], algebraMap ℚ_[l] P.R.B q =
      ∑ j ∈ Finset.range n, (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c) := by
    intro b
    apply (P.PD K).fund
    · rw [P.PD_φ, map_sum]
      have e1 : ∀ j, P.φB ((⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) =
          (⇑P.φB)^[j + 1] (algebraMap ↥(K0 K) P.R.B b * c) :=
        fun j => (Function.iterate_succ_apply' _ _ _).symm
      simp_rw [e1]
      have hfn : (⇑P.φB)^[n] (algebraMap ↥(K0 K) P.R.B b * c) =
          (⇑P.φB)^[0] (algebraMap ↥(K0 K) P.R.B b * c) := by
        rw [iterate_φB_mul, hn, ← hord, pow_orderOf_eq_one, AlgEquiv.one_apply, Function.iterate_zero, id]
      have h := Finset.sum_range_succ' (fun j => (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) n
      rw [Finset.sum_range_succ, hfn] at h
      exact (add_right_cancel h).symm
    · rw [P.PD_ι, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [iterate_φB_mul, map_mul, ιB_algebraMap, ← Algebra.smul_def]
      exact Submodule.smul_of_tower_mem _ _ (hF j)
  choose q hq using fun i => hs (bas i)
  let v : Fin n → P.R.B := fun j => (⇑P.φB)^[(j : ℕ)] c
  have hAv : Matrix.mulVec (A.map (algebraMap ↥(K0 K) P.R.B)) v =
      fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i)) := by
    funext i
    rw [← IsScalarTower.algebraMap_apply, hq i, Finset.sum_range]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, A, v, Matrix.of_apply, iterate_φB_mul]
    rfl
  have hinv : (A⁻¹.map (algebraMap ↥(K0 K) P.R.B)) * (A.map (algebraMap ↥(K0 K) P.R.B)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv : v = Matrix.mulVec (A⁻¹.map (algebraMap ↥(K0 K) P.R.B))
      (fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i))) := by
    rw [← hAv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  refine ⟨∑ i, A⁻¹ ⟨0, hn0⟩ i * algebraMap ℚ_[l] ↥(K0 K) (q i), ?_⟩
  have h0 := congrFun hv ⟨0, hn0⟩
  simp only [v, Function.iterate_zero, id] at h0
  rw [h0]
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.CrisPerFix
