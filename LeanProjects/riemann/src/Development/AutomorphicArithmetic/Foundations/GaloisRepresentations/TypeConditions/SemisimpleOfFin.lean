import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzTame
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne Module

namespace UpperTheory.GalS

theorem char_pow_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {M : Type} [CommGroup M] (ξ : G E Ω →* M)
    (hW : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → ξ σ = 1) (t : G E Ω) (ht : t ∈ Ine (F := E) A) :
    ξ t ^ (normV w - 1) = 1 := by
  have h1 : ξ ((frob h : G E Ω) * t * (frob h : G E Ω)⁻¹ * (t ^ normV w)⁻¹) = 1 := hW _ fun y hy => by
    have k := (DiscreteGroups.sglob.DzType.isWild_frob (isFrob_frob (h := h)) ⟨t, ht⟩).2 y hy
    rw [div_sub_one hy, map_div₀, div_lt_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy))]
    exact k
  simp only [map_mul, map_inv, map_pow] at h1
  have h3 : ξ t = ξ t ^ normV w := by
    rw [mul_inv_eq_one, mul_comm (ξ _), mul_inv_cancel_right] at h1
    exact h1
  have hq : 1 ≤ normV w := Nat.pos_of_ne_zero fun h0 => by
    have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    exact (Nat.card_pos (α := 𝓞 E ⧸ w.asIdeal)).ne' h0
  have h4 : ξ t ^ (normV w - 1) * ξ t = 1 * ξ t := by
    rw [← pow_succ, Nat.sub_add_cancel hq, one_mul]
    exact h3.symm
  exact mul_right_cancel h4

theorem semisimple_of_fin {K : Type} [Field K] [CharZero K] {n : ℕ} {M : GL (Fin n) K} (h : IsOfFinOrder M) :
    Module.End.IsSemisimple (Matrix.toLin' (M : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ k - C 1)
    (separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hk.ne') one_ne_zero).squarefree ?_
  rw [map_sub, map_pow, aeval_X, aeval_C, map_one, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, e]
  simp [Module.End.one_eq_id]

theorem split_tame {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [CharZero K] [IsAlgClosed K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] {n t : ℕ} (I : Subgroup Γ) (Wd : Set Γ) (γ₀ : Γ) (h0 : γ₀ ∈ I)
    (hgen : (I : Set Γ) ⊆ closure ((Subgroup.closure (insert γ₀ Wd) : Subgroup Γ) : Set Γ))
    (ρ : Γ →* GL (Fin n) K) (hρ : Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) K))
    (χ : Γ →* Kˣ) (hχ : Continuous fun g => (χ g : K)) (hfin : ∀ σ ∈ I, IsOfFinOrder (ρ σ))
    (hW : ∀ σ ∈ Wd, σ ∈ I ∧ (ρ σ : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n ∧ χ σ = 1)
    (hm : (ρ γ₀ : Matrix (Fin n) (Fin n) K).charpoly.rootMultiplicity (χ γ₀ : K) = t) :
    ∃ U U' : Submodule K (Fin n → K), IsCompl U U' ∧ finrank K U' = t ∧ ∀ γ ∈ I,
      (∀ v ∈ U, (ρ γ : Matrix (Fin n) (Fin n) K).mulVec v ∈ U) ∧
      ∀ v ∈ U', (ρ γ : Matrix (Fin n) (Fin n) K).mulVec v = (χ γ : K) • v := by
  have hW1 : ∀ σ ∈ Wd, ρ σ = 1 := fun σ hσ => by
    obtain ⟨a, b, -⟩ := hW σ hσ
    have s := semisimple_of_fin (hfin σ a)
    have h1 : IsNilpotent (Matrix.toLin' (ρ σ : Matrix (Fin n) (Fin n) K) - algebraMap K (End K (Fin n → K)) 1) := ⟨n, by
      have := LinearMap.aeval_self_charpoly (Matrix.toLin' (ρ σ : Matrix (Fin n) (Fin n) K))
      rw [Matrix.charpoly_toLin', b] at this
      simpa using this⟩
    have h3 := sub_eq_zero.1 (End.eq_zero_of_isNilpotent_isSemisimple h1 (End.isSemisimple_sub_algebraMap_iff.2 s))
    apply Units.ext
    apply Matrix.toLin'.injective
    rw [h3]; simp [Module.End.one_eq_id]
  let f : End K (Fin n → K) := Matrix.toLin' (ρ γ₀ : Matrix (Fin n) (Fin n) K)
  let c : K := χ γ₀
  let d : End K (Fin n → K) := f - algebraMap K _ c
  have hs : f.IsSemisimple := semisimple_of_fin (hfin γ₀ h0)
  have hd : d.IsSemisimple := End.isSemisimple_sub_algebraMap_iff.2 hs
  have hdv : ∀ v, d v = (ρ γ₀ : Matrix (Fin n) (Fin n) K).mulVec v - c • v := fun v => by simp [d, f]

  let S : Subgroup Γ :=
    { carrier := {γ | ρ γ * ρ γ₀ = ρ γ₀ * ρ γ ∧ ∀ v, d v = 0 → (ρ γ : Matrix (Fin n) (Fin n) K).mulVec v = (χ γ : K) • v}
      one_mem' := ⟨by simp, fun v _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, mul_assoc, hb.1, ← mul_assoc, ha.1, mul_assoc], fun v hv => by
        rw [map_mul, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb.2 v hv, Matrix.mulVec_smul, ha.2 v hv, smul_smul,
          Units.val_mul, mul_comm]⟩
      inv_mem' := fun {a} ha => ⟨by rw [map_inv]; exact (Commute.inv_left ha.1 : Commute _ _), fun v hv => by
        have e := congrArg ((ρ a⁻¹ : Matrix (Fin n) (Fin n) K).mulVec) (ha.2 v hv)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec,
          Matrix.mulVec_smul] at e
        conv_rhs => rw [e, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]⟩ }
  have hcl : IsClosed (S : Set Γ) := by
    have e : (S : Set Γ) = {γ | (ρ γ : Matrix (Fin n) (Fin n) K) * ρ γ₀ = ρ γ₀ * ρ γ} ∩
        ⋂ v : {v // d v = 0}, {γ | (ρ γ : Matrix (Fin n) (Fin n) K).mulVec v = (χ γ : K) • v.1} := by
      ext γ
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall, ← Units.val_mul, Units.val_inj]
      rfl
    rw [e]
    exact (isClosed_eq (hρ.matrix_mul continuous_const) (continuous_const.matrix_mul hρ)).inter
      (isClosed_iInter fun v => isClosed_eq (hρ.matrix_mulVec continuous_const) (hχ.smul continuous_const))
  have hI : ∀ γ ∈ I, γ ∈ S := fun γ hγ => by
    refine hcl.closure_subset (closure_mono ?_ (hgen hγ))
    refine (Subgroup.closure_le S).2 ?_
    rintro σ (rfl | hσ)
    · exact ⟨rfl, fun v hv => sub_eq_zero.1 ((hdv v).symm.trans hv)⟩
    · exact ⟨by rw [hW1 σ hσ]; simp, fun v _ => by rw [hW1 σ hσ, (hW σ hσ).2.2]; simp⟩
  have hk : LinearMap.ker d = f.eigenspace c := by
    ext v; rw [End.mem_eigenspace_iff, LinearMap.mem_ker, hdv, sub_eq_zero]; rfl
  refine ⟨LinearMap.range d, LinearMap.ker d, ?_, ?_, fun γ hγ => ⟨?_, fun v hv => (hI γ hγ).2 v hv⟩⟩
  · have hdj : Disjoint (LinearMap.range d) (LinearMap.ker d) := by
      rw [Submodule.disjoint_def]
      rintro _ ⟨u, rfl⟩ hu
      have : u ∈ d.maxGenEigenspace 0 := (End.mem_maxGenEigenspace _ _ _).2 ⟨2, by simpa [pow_two] using hu⟩
      rw [hd.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, End.mem_eigenspace_iff] at this
      simpa using this
    exact ⟨hdj, codisjoint_iff.2 (Submodule.eq_top_of_disjoint _ _ (LinearMap.finrank_range_add_finrank_ker d).ge hdj)⟩
  · rw [hk, ← hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, LinearMap.finrank_maxGenEigenspace_eq,
      Matrix.charpoly_toLin']
    exact hm
  · rintro _ ⟨u, rfl⟩
    refine ⟨(ρ γ : Matrix (Fin n) (Fin n) K).mulVec u, ?_⟩
    rw [hdv, hdv, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
      ← Units.val_mul, (hI γ hγ).1]

end UpperTheory.GalS
