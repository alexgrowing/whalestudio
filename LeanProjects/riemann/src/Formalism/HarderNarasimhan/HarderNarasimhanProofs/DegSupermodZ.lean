import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax

open Module Submodule

noncomputable section

namespace Formalism.RankSupermodularCovolume

open Formalism.F

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem cast_rank_eq_moduleRank (N : Submodule ℤ E) [DiscreteTopology N] :
    ((rk N : ℕ) : Cardinal) = Module.rank ℤ N := by
  unfold rk
  exact Module.finrank_eq_rank ℤ N

private theorem discreteTopology_of_le_discrete (L A : Submodule ℤ E) [DiscreteTopology L] (h : A ≤ L) :
    DiscreteTopology A :=
  DiscreteTopology.of_subset (s := (L : Set E)) ‹_› h

theorem rk_sup_add_rk_inf (L A B : Submodule ℤ E) [DiscreteTopology L] (hA : A ≤ L)
    (hB : B ≤ L) : rk (A ⊔ B) + rk (A ⊓ B) = rk A + rk B := by
  haveI : DiscreteTopology A := discreteTopology_of_le_discrete L A hA
  haveI : DiscreteTopology B := discreteTopology_of_le_discrete L B hB
  haveI : DiscreteTopology ↥(A ⊔ B) := discreteTopology_of_le_discrete L _ (sup_le hA hB)
  haveI : DiscreteTopology ↥(A ⊓ B) := discreteTopology_of_le_discrete L _ (inf_le_left.trans hA)
  have h := Submodule.rank_sup_add_rank_inf_eq A B
  apply Nat.cast_injective (R := Cardinal)
  push_cast
  rw [cast_rank_eq_moduleRank, cast_rank_eq_moduleRank,
    cast_rank_eq_moduleRank, cast_rank_eq_moduleRank]
  exact h

theorem mem_span_inf_of_mem_span (L A B : Submodule ℤ E) [DiscreteTopology L] (hA : A ≤ L)
    (hB : B ≤ L) {b : E} (hbB : b ∈ B) (hbA : b ∈ span ℝ (A : Set E)) :
    b ∈ span ℝ ((A ⊓ B : Submodule ℤ E) : Set E) := by
  classical
  obtain ⟨-, hAAs, hrk⟩ := saturProps E L A ‹_› hA
  haveI : DiscreteTopology (satur L A) := discreteTopology_of_le_discrete L _ inf_le_left
  haveI : DiscreteTopology A := discreteTopology_of_le_discrete L A hA
  have hbAs : b ∈ satur L A := Submodule.mem_inf.2 ⟨hB hbB, hbA⟩
  let N : Submodule ℤ (satur L A) := A.comap (satur L A).subtype
  have hN : Module.finrank ℤ N = Module.finrank ℤ (satur L A) := by
    rw [(Submodule.comapSubtypeEquivOfLe hAAs).finrank_eq]
    exact hrk.symm
  haveI := Submodule.finiteQuotientOfFreeOfRankEq N hN
  have hn : 0 < Nat.card (satur L A ⧸ N) := Nat.card_pos
  have h0 : Nat.card (satur L A ⧸ N) • (Submodule.Quotient.mk ⟨b, hbAs⟩ : satur L A ⧸ N) = 0 :=
    card_nsmul_eq_zero'
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  have hA' : Nat.card (satur L A ⧸ N) • b ∈ A := by simpa [N] using h0
  have hC : Nat.card (satur L A ⧸ N) • b ∈ A ⊓ B :=
    Submodule.mem_inf.2 ⟨hA', B.nsmul_mem hbB _⟩
  have hb : b = ((Nat.card (satur L A ⧸ N) : ℕ) : ℝ)⁻¹ • (Nat.card (satur L A ⧸ N) • b) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  rw [hb]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hC)

theorem covol_eq_relIndex_mul_covol (N N' : Submodule ℤ E) [DiscreteTopology N'] (hle : N ≤ N')
    (hrk : rk N = rk N') :
    covol N = (N.toAddSubgroup.relIndex N'.toAddSubgroup : ℝ) * covol N' := by
  classical
  haveI : DiscreteTopology N := DiscreteTopology.of_subset (s := (N' : Set E)) ‹_› hle
  let K : Submodule ℤ N' := N.comap N'.subtype
  let eK : K ≃ₗ[ℤ] N := Submodule.comapSubtypeEquivOfLe hle
  have hK : Module.finrank ℤ K = Module.finrank ℤ N' := by
    rw [eK.finrank_eq]; exact hrk
  let b : Basis (Fin (Module.finrank ℤ N')) ℤ N' := Module.finBasis ℤ N'
  let bK : Basis (Fin (Module.finrank ℤ N')) ℤ K := Module.finBasisOfFinrankEq ℤ K hK
  let A : Matrix (Fin (Module.finrank ℤ N')) (Fin (Module.finrank ℤ N')) ℤ :=
    Matrix.of fun i j => b.repr (bK j : N') i
  let Ar : Matrix (Fin (Module.finrank ℤ N')) (Fin (Module.finrank ℤ N')) ℝ :=
    Matrix.of fun i j => ((b.repr (bK j : N') i : ℤ) : ℝ)
  have hidx : N.toAddSubgroup.relIndex N'.toAddSubgroup = (b.det (Subtype.val ∘ bK)).natAbs := by
    rw [Submodule.natAbs_det_basis_change b K bK]
    rfl
  let v : Fin (Module.finrank ℤ N') → E := fun i => (b i : E)
  let w : Fin (Module.finrank ℤ N') → E := fun i => ((bK i : N') : E)
  have hw : ∀ j, w j = ∑ i, Ar i j • v i := by
    intro j
    have h := b.sum_repr ((bK j : N'))
    have h2 := congrArg (fun x : N' => (x : E)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    show ((bK j : N') : E) = _
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Ar, v, Int.cast_smul_eq_zsmul]
  have hgram : Matrix.gram ℝ w = Ar.transpose * (Matrix.gram ℝ v * Ar) := by
    ext i j
    simp only [Matrix.gram_apply, hw, Matrix.mul_apply, Matrix.transpose_apply,
      inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hA : Ar.det = (A.det : ℝ) := by
    have := ((Int.castRingHom ℝ).map_det A).symm
    simpa [Ar, A, RingHom.mapMatrix_apply, Matrix.map] using this
  have hdet : (Matrix.gram ℝ w).det = (A.det : ℝ) ^ 2 * (Matrix.gram ℝ v).det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hA]
    ring
  have hcw : (fun i => ((bK.map eK) i : E)) = w := by
    funext i
    rfl
  have hbd : b.det (Subtype.val ∘ bK) = A.det := by
    rw [Basis.det_apply]
    rfl
  rw [covolEqGram E N (Fin (Module.finrank ℤ N')) (bK.map eK), covolEqGram E N' _ b, hcw, hdet,
    hidx, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, hbd]
  simp [Nat.cast_natAbs, Int.cast_abs]
  exact Or.inl rfl

theorem orthogonal_starProjection_comp_of_le {U W : Submodule ℝ E} (hUW : U ≤ W) (x : E) :
    Wᗮ.starProjection (Uᗮ.starProjection x) = Wᗮ.starProjection x := by
  have h1 := U.starProjection_add_starProjection_orthogonal x
  have h2 : Wᗮ.starProjection (U.starProjection x) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
    exact hUW (U.starProjection_apply_mem x)
  calc Wᗮ.starProjection (Uᗮ.starProjection x)
      = Wᗮ.starProjection (U.starProjection x) + Wᗮ.starProjection (Uᗮ.starProjection x) := by
        rw [h2, zero_add]
    _ = Wᗮ.starProjection x := by rw [← map_add, h1]

theorem mem_of_orthogonal_starProjection_eq_zero {W : Submodule ℝ E} {x : E}
    (h : Wᗮ.starProjection x = 0) : x ∈ W := by
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h
  exact h

theorem covol_le_of_contraction (Q1 Q2 : Submodule ℤ E) [DiscreteTopology Q1]
    [DiscreteTopology Q2] (φ : Q1 ≃ₗ[ℤ] Q2) (f : E →L[ℝ] E)
    (hf : ∀ x : Q1, ((φ x : Q2) : E) = f x) (hn : ∀ v, ‖f v‖ ≤ ‖v‖) : covol Q2 ≤ covol Q1 := by
  let v := Module.finBasis ℤ Q1
  let w := v.map φ
  rw [covol_eq_gram E Q1 _ v, covol_eq_gram E Q2 _ w]
  apply Real.sqrt_le_sqrt
  have h := gram_det_le E E _ (fun i => (v i : E)) (fun i => (w i : E)) 1 (fun c => by
    have : ∑ i, c i • ((w i : Q2) : E) = f (∑ i, c i • ((v i : Q1) : E)) := by
      simp only [w, Basis.map_apply, hf, map_sum, map_smul]
    rw [this, one_mul]
    exact hn _)
  simpa using h

end

end Formalism.RankSupermodularCovolume

namespace Formalism.HN

open Formalism.F Formalism.RankSupermodularCovolume

theorem degree_supermodular_integral : DegSupermodZ := by
  intro E _ _ _ L A B hL hA hB
  haveI := hL
  refine ⟨rk_sup_add_rk_inf L A B hA hB, ?_⟩
  have dsc : ∀ N : Submodule ℤ E, N ≤ L → DiscreteTopology N := fun N h =>
    DiscreteTopology.of_subset (s := (L : Set E)) ‹_› h
  have hSL : A ⊔ B ≤ L := sup_le hA hB
  haveI := dsc _ hSL
  haveI := dsc A hA
  haveI := dsc B hB
  haveI := dsc (A ⊓ B) (inf_le_left.trans hA)
  obtain ⟨hAsSat, hAAs, hrkAs⟩ := saturProps E (A ⊔ B) A ‹_› le_sup_left
  obtain ⟨hBsSat, hCBs, hrkBs⟩ := saturProps E B (A ⊓ B) ‹_› inf_le_right
  haveI := dsc (satur (A ⊔ B) A) (inf_le_left.trans hSL)
  haveI := dsc (satur B (A ⊓ B)) (inf_le_left.trans hB)
  obtain ⟨hqS, -, -⟩ := degQuot E (A ⊔ B) (satur (A ⊔ B) A) ‹_› hAsSat
  obtain ⟨hqB, -, -⟩ := degQuot E B (satur B (A ⊓ B)) ‹_› hBsSat
  haveI := hqS
  haveI := hqB
  have hdS := deg_eq_deg_add_deg_quot hAsSat
  have hdB := deg_eq_deg_add_deg_quot hBsSat

  have hAs_span : ∀ x ∈ satur (A ⊔ B) A, x ∈ span ℝ (A : Set E) := fun x hx =>
    (Submodule.mem_inf.1 hx).2
  have hBs_span : ∀ x ∈ satur B (A ⊓ B), x ∈ span ℝ ((A ⊓ B : Submodule ℤ E) : Set E) :=
    fun x hx => (Submodule.mem_inf.1 hx).2
  have hBsAs : satur B (A ⊓ B) ≤ satur (A ⊔ B) A := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨(le_sup_right : B ≤ A ⊔ B) (Submodule.mem_inf.1 hx).1, ?_⟩
    exact span_mono (fun y hy => (Submodule.mem_inf.1 hy).1) (hBs_span x hx)

  have hcA := covol_eq_relIndex_mul_covol A (satur (A ⊔ B) A) hAAs hrkAs.symm
  have hcC := covol_eq_relIndex_mul_covol (A ⊓ B) (satur B (A ⊓ B)) hCBs hrkBs.symm
  have hiA : A.toAddSubgroup.relIndex (satur (A ⊔ B) A).toAddSubgroup ≠ 0 := by
    intro h0
    have := covol_pos A
    rw [hcA, h0] at this
    simp at this
  have hiC : (A ⊓ B).toAddSubgroup.relIndex (satur B (A ⊓ B)).toAddSubgroup =
      A.toAddSubgroup.relIndex (satur B (A ⊓ B)).toAddSubgroup := by
    unfold AddSubgroup.relIndex
    congr 1
    ext x
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    have hxB : (x : E) ∈ B := (Submodule.mem_inf.1 x.2).1
    exact ⟨fun h => (Submodule.mem_inf.1 h).1, fun h => Submodule.mem_inf.2 ⟨h, hxB⟩⟩
  have hle : (A ⊓ B).toAddSubgroup.relIndex (satur B (A ⊓ B)).toAddSubgroup ≤
      A.toAddSubgroup.relIndex (satur (A ⊔ B) A).toAddSubgroup := by
    rw [hiC]
    exact AddSubgroup.relIndex_le_of_le_right hBsAs hiA
  have hii : covol (satur (A ⊔ B) A) * covol (A ⊓ B) ≤ covol A * covol (satur B (A ⊓ B)) := by
    rw [hcA, hcC]
    have h1 := covol_pos (satur (A ⊔ B) A)
    have h2 := covol_pos (satur B (A ⊓ B))
    have h3 : ((A ⊓ B).toAddSubgroup.relIndex (satur B (A ⊓ B)).toAddSubgroup : ℝ) ≤
        (A.toAddSubgroup.relIndex (satur (A ⊔ B) A).toAddSubgroup : ℝ) := by exact_mod_cast hle
    have h4 := mul_le_mul_of_nonneg_right h3 (mul_pos h1 h2).le
    nlinarith [h4]

  have hspan : span ℝ ((satur B (A ⊓ B) : Submodule ℤ E) : Set E) ≤
      span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E) := span_mono hBsAs
  have hPW0 : ∀ y ∈ span ℝ ((A ⊓ B : Submodule ℤ E) : Set E),
      (span ℝ ((satur B (A ⊓ B) : Submodule ℤ E) : Set E))ᗮ.starProjection y = 0 := by
    intro y hy
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
    exact span_mono hCBs hy
  have hPU0 : ∀ y ∈ A, (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection y = 0 := by
    intro y hy
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
    exact subset_span (hAAs hy)
  have hmaps : ∀ x ∈ quot B (satur B (A ⊓ B)),
      (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection x ∈
        quot (A ⊔ B) (satur (A ⊔ B) A) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hx
    refine Submodule.mem_map.2 ⟨b, (le_sup_right : B ≤ A ⊔ B) hb, ?_⟩
    simp only [LinearMap.coe_restrictScalars, ContinuousLinearMap.coe_coe]
    exact (orthogonal_starProjection_comp_of_le hspan b).symm
  let g : quot B (satur B (A ⊓ B)) →ₗ[ℤ] quot (A ⊔ B) (satur (A ⊔ B) A) :=
    (((span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection : E →L[ℝ] E).toLinearMap.restrictScalars ℤ).restrict
      hmaps
  have hg : ∀ x, ((g x : quot (A ⊔ B) (satur (A ⊔ B) A)) : E) =
      (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection x := fun x => rfl
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection x = 0 := by
      rw [← hg, hx]; rfl
    obtain ⟨b, hb, hbx⟩ := Submodule.mem_map.1 x.2
    simp only [LinearMap.coe_restrictScalars, ContinuousLinearMap.coe_coe] at hbx
    rw [← hbx, orthogonal_starProjection_comp_of_le hspan] at hx0
    have hbU := mem_of_orthogonal_starProjection_eq_zero hx0
    have hbA : b ∈ span ℝ (A : Set E) :=
      span_le.2 (fun y hy => hAs_span y hy) hbU
    have hbC := mem_span_inf_of_mem_span L A B hA hB hb hbA
    apply Subtype.ext
    rw [← hbx, hPW0 b hbC]
    rfl
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hs
    have hpb : (span ℝ ((satur B (A ⊓ B) : Submodule ℤ E) : Set E))ᗮ.starProjection b ∈
        quot B (satur B (A ⊓ B)) := Submodule.mem_map.2 ⟨b, hb, rfl⟩
    refine ⟨⟨_, hpb⟩, Subtype.ext ?_⟩
    rw [hg]
    simp only [LinearMap.coe_restrictScalars, ContinuousLinearMap.coe_coe, map_add, hPU0 a ha,
      zero_add]
    exact orthogonal_starProjection_comp_of_le hspan b
  let φ := LinearEquiv.ofBijective g ⟨hinj, hsurj⟩
  have hcov : covol (quot (A ⊔ B) (satur (A ⊔ B) A)) ≤ covol (quot B (satur B (A ⊓ B))) := by
    refine covol_le_of_contraction _ _ φ
      ((span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection) (fun x => hg x) ?_
    intro v
    first
      | exact Submodule.norm_starProjection_apply_le _ v
      | exact (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.norm_starProjection_apply_le v
      | exact ContinuousLinearMap.le_of_opNorm_le _ (Submodule.starProjection_norm_le _) v
      | simpa using ContinuousLinearMap.le_of_opNorm_le _ (Submodule.starProjection_norm_le _) v
  have k1 : Real.log (covol (quot (A ⊔ B) (satur (A ⊔ B) A))) ≤
      Real.log (covol (quot B (satur B (A ⊓ B)))) :=
    Real.log_le_log (covol_pos _) hcov
  have k2 : Real.log (covol (satur (A ⊔ B) A)) + Real.log (covol (A ⊓ B)) ≤
      Real.log (covol A) + Real.log (covol (satur B (A ⊓ B))) := by
    rw [← Real.log_mul (covol_pos _).ne' (covol_pos _).ne',
      ← Real.log_mul (covol_pos _).ne' (covol_pos _).ne']
    exact Real.log_le_log (mul_pos (covol_pos _) (covol_pos _)) hii
  rw [hdS, hdB]
  unfold Formalism.F.deg
  linarith

end Formalism.HN
