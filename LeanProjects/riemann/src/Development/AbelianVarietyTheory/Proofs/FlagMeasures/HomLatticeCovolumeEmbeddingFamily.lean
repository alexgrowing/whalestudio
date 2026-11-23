import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.HomCovolumeFamily

attribute [local instance] GlobalTheory.HomCovolume.haar_two GlobalTheory.HomCovolume.haar_three

theorem exists_twist {E : Type} [Field E] (φ : E →+* ℂ) :
    ∃ σ : ℂ ≃ₐ[ℝ] ℂ, (∀ x, ‖σ x‖ = ‖x‖) ∧ ∀ x, (InfinitePlace.mk φ).embedding x = σ (φ x) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨AlgEquiv.refl, fun _ => rfl, fun x => by rw [h]; rfl⟩
  · exact ⟨Complex.conjAe, fun x => by simp, fun x => by rw [h]; rfl⟩

theorem det_map_twist {j : ℕ} (σ : ℂ ≃ₐ[ℝ] ℂ) (A : Matrix (Fin j) (Fin j) ℂ) :
    (A.map σ).det = σ A.det := by
  have := RingHom.map_det (σ : ℂ →+* ℂ) A
  rw [RingHom.mapMatrix_apply] at this
  exact this.symm

theorem map_inv_twist {j : ℕ} (σ : ℂ ≃ₐ[ℝ] ℂ) (A : Matrix (Fin j) (Fin j) ℂ) (hA : A.det ≠ 0) :
    (A⁻¹).map σ = (A.map σ)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

variable {E : Type} [Field E] [NumberField E]

theorem detNorm_twist {ι : Type} [Fintype ι] (e : ι ≃ InfinitePlace E) (σ : ι → ℂ ≃ₐ[ℝ] ℂ)
    (hσ : ∀ v x, ‖σ v x‖ = ‖x‖) {j : ℕ} (G : ι → Matrix (Fin j) (Fin j) ℂ) :
    detNorm E j (fun w => Matrix.of.symm ((G (e.symm w)).map (σ (e.symm w)))⁻¹) =
      (∏ v, ‖(G v).det‖ ^ 2)⁻¹ := by
  change ∏ w, ‖(Matrix.of (Matrix.of.symm ((G (e.symm w)).map (σ (e.symm w)))⁻¹)).det‖ ^ 2 = _
  rw [← Finset.prod_inv_distrib, ← e.prod_comp]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv,
    inv_pow, det_map_twist, hσ]

theorem covAt_eq (hE : IsTotallyComplex E) {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsLattice E Λ) (g : MatInf E j) (hg : 0 < detNorm E j g) :
    covAt E j (latAt E j Λ g) = covStd j Λ / detNorm E j g := by
  obtain ⟨κ, -, h⟩ := (GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  have h1 : detNorm E j (fun _ a b => if a = b then 1 else 0) = 1 := by
    have h2 : (Matrix.of fun a b : Fin j => if a = b then (1 : ℂ) else 0) = 1 := rfl
    simp only [detNorm, h2, Matrix.det_one, norm_one, one_pow, Finset.prod_const_one]
  have h3 : covStd j Λ = κ := ((h _ (h1.symm ▸ one_pos)).2.1.trans (congrArg (κ / ·) h1)).trans (div_one κ)
  rw [(h g hg).2.1, h3]

theorem homCovolume_family : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ (r s : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin s → E)), Submodule.IsLattice E Λ → Submodule.IsLattice E Λ' → ∀ (G : ι → Matrix (Fin r) (Fin r) ℂ) (G' : ι → Matrix (Fin s) (Fin s) ℂ), (∀ v, (G v).det ≠ 0) → (∀ v, (G' v).det ≠ 0) → ∀ L : Submodule ℤ (ι → Fin r → Fin s → ℂ), (∀ z, z ∈ L ↔ ∃ T : Matrix (Fin r) (Fin s) E, (∀ y ∈ Λ', T *ᵥ y ∈ Λ) ∧ ∀ v, Matrix.of (z v) = G v * T.map (φ v) * (G' v)⁻¹) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = (covStd r Λ * ∏ v, ‖(G v).det‖ ^ 2) ^ s * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * s) / (covStd s Λ' * ∏ v, ‖(G' v).det‖ ^ 2)) ^ r := by
  intro E _ _ hE ι _ φ hφ r s Λ Λ' hΛ hΛ' G G' hG hG' L hL
  let e : ι ≃ InfinitePlace E := Equiv.ofBijective _ hφ
  choose σ hσ hσφ using fun v => exists_twist (φ v)
  have he : ∀ v x, (e v).embedding x = σ v (φ v x) := hσφ
  let Φ : (ι → Fin r → Fin s → ℂ) ≃ₗ[ℝ] (InfinitePlace E → Fin r → Fin s → ℂ) :=
    { toFun := fun z w i k => σ (e.symm w) (z (e.symm w) i k)
      invFun := fun y v i k => (σ v).symm (y (e v) i k)
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun c z => funext fun w => funext fun i => funext fun k =>
        (σ (e.symm w)).toLinearEquiv.map_smul c (z (e.symm w) i k)
      left_inv := fun _ => by ext; simp
      right_inv := fun _ => by ext; simp }
  have hΦ : ∀ z v i k, Φ z (e v) i k = σ v (z v i k) := fun z v i k => by
    change σ (e.symm (e v)) (z (e.symm (e v)) i k) = _
    rw [e.symm_apply_apply]
  have hmp : MeasurePreserving Φ.toContinuousLinearEquiv volume volume := by
    refine GlobalTheory.HomCovolume.measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · simp only [pi_norm_le_iff_of_nonneg zero_le_one]
      change (∀ w i k, ‖Φ x w i k‖ ≤ 1) ↔ _
      rw [e.forall_congr_right.symm]
      simp only [hΦ, hσ]
    · simp [volume_pi_closedBall _ zero_le_one, Fintype.card_congr e]
  have hD : 0 < ∏ v, ‖(G v).det‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hG v)) _
  have hD' : 0 < ∏ v, ‖(G' v).det‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hG' v)) _
  have hn := detNorm_twist e σ hσ G
  have hn' := detNorm_twist e σ hσ G'
  have hp := hn ▸ inv_pos.2 hD
  have hp' := hn' ▸ inv_pos.2 hD'
  let L' : Submodule ℤ (InfinitePlace E → Fin r → Fin s → ℂ) :=
    L.comap (Φ.symm.toLinearMap.restrictScalars ℤ)
  have hLL : ∀ z, z ∈ L ↔ Φ z ∈ L' := fun z => by
    change _ ↔ Φ.symm (Φ z) ∈ L
    rw [Φ.symm_apply_apply]
  have hmain := GlobalTheory.HomCovolume.homCovolume E hE r s Λ Λ' hΛ hΛ' _ _ hp hp' L' (fun y => by
    obtain ⟨z, rfl⟩ := Φ.surjective y
    rw [← hLL, hL]
    refine exists_congr fun T => and_congr Iff.rfl ?_
    rw [← e.forall_congr_right]
    refine forall_congr' fun v => ?_
    have h1 : Matrix.of (Φ z (e v)) = (Matrix.of (z v)).map (σ v) := by
      ext i k; exact hΦ z v i k
    have h2 : T.map (e v).embedding = (T.map (φ v)).map (σ v) := by
      ext i k; exact he v _
    have h3 : IsUnit ((G v).map (σ v)).det := by
      rw [det_map_twist]; exact ((map_ne_zero _).2 (hG v)).isUnit
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply, h1, h2,
      Matrix.nonsing_inv_nonsing_inv _ h3, ← map_inv_twist _ _ (hG' v), ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (σ v).injective).eq_iff.symm)
  rw [covAt_eq hE Λ hΛ _ hp, covAt_eq hE Λ' hΛ' _ hp', hn, hn', div_inv_eq_mul, div_inv_eq_mul] at hmain
  exact GlobalTheory.HomCovolume.HasCov.of_measurePreserving Φ.toContinuousLinearEquiv hmp hLL hmain

end GlobalTheory.HomCovolumeFamily
