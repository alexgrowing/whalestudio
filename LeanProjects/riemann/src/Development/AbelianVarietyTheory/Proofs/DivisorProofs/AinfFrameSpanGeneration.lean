import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem frame_of_spanning : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N d h : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)) (x : Fin N → Fin h → Ainf p O), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) → h = N * d → Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ x ij.1) = ⊤ → ∃ e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame ρ e ∧ ∀ (i : Fin N) (l : Λ), e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = ρ l *ᵥ x i := by
  intro p _ O _ _ _ Λ _ _ N d h b ρ x hsc hh hspan
  subst hh
  classical
  let bR : Module.Basis (Fin d) (Ainf p O) (RL p O Λ) := Algebra.TensorProduct.basis (Ainf p O) b
  let bP := Pi.basis (fun _ : Fin N => bR)
  let L : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin (N * d) → Ainf p O) :=
    bP.constr (Ainf p O) (fun ij => ρ (b ij.2) *ᵥ x ij.1)
  have hL : ∀ i j, L (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j)) = ρ (b j) *ᵥ x i := by
    intro i j
    have hb : Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) = bP ⟨i, j⟩ := by
      simp [bP, bR, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    rw [hb]
    exact bP.constr_basis (Ainf p O) (fun ij : (Σ _ : Fin N, Fin d) => ρ (b ij.2) *ᵥ x ij.1) ⟨i, j⟩
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨_, hL i j⟩
  let σ : (Σ _ : Fin N, Fin d) ≃ Fin (N * d) := (Equiv.sigmaEquivProd _ _).trans finProdFinEquiv
  let E := (bP.reindex σ).equivFun
  have hinj : Function.Injective L := by
    have hf : Function.Surjective (L ∘ₗ E.symm.toLinearMap) := by
      intro y; obtain ⟨w, rfl⟩ := hsurj y; exact ⟨E w, by simp⟩
    have hi := OrzechProperty.injective_of_surjective_endomorphism _ hf
    intro u v huv
    have : E u = E v := hi (by simpa using huv)
    exact E.injective this
  let e := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have he : ∀ w, e w = L w := fun w => rfl
  have hform : ∀ (i : Fin N) (l : Λ), e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = ρ l *ᵥ x i := by
    intro i l
    rw [he]
    have hps : ∀ (f : Fin d → RL p O Λ), Pi.single i (∑ j, f j) = ∑ j, Pi.single (M := fun _ : Fin N => RL p O Λ) i (f j) :=
      fun f => map_sum (AddMonoidHom.single (fun _ : Fin N => RL p O Λ) i) f _
    rw [← b.sum_repr l, TensorProduct.tmul_sum, hps, map_sum, map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    set c := (b.repr l) j
    have h1 : c • ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) = ofPadic p O c • ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) :=
      (algebraMap_smul (Ainf p O) c _).symm
    have h2 : Pi.single i (ofPadic p O c • ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j))
        = ofPadic p O c • Pi.single (M := fun _ : Fin N => RL p O Λ) i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [TensorProduct.tmul_smul, h1, h2, map_smul, hL, Algebra.smul_def c (b j), map_mul, hsc,
      smul_mul_assoc, one_mul, Matrix.smul_mulVec]
  refine ⟨e, ?_, hform⟩
  intro l w
  let f1 : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin (N * d) → Ainf p O) :=
    e.toLinearMap ∘ₗ DistribMulAction.toLinearMap (Ainf p O) (Fin N → RL p O Λ)
      ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)
  let f2 : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin (N * d) → Ainf p O) :=
    (Matrix.mulVecLin (ρ l)) ∘ₗ e.toLinearMap
  have hf : f1 = f2 := by
    refine bP.ext fun ij => ?_
    obtain ⟨i, j⟩ := ij
    have hb : bP ⟨i, j⟩ = Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) := by
      simp [bP, bR, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    have hs : ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • Pi.single (M := fun _ : Fin N => RL p O Λ) i
        ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) = Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (l * b j)) := by
      funext k; by_cases hk : k = i
      · subst hk; simp [Algebra.TensorProduct.tmul_mul_tmul]
      · simp [hk]
    show e (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • bP ⟨i, j⟩) = ρ l *ᵥ e (bP ⟨i, j⟩)
    simp only [ hb, hs,
      LinearEquiv.coe_coe, hform, Matrix.mulVecLin_apply, map_mul, Matrix.mulVec_mulVec]
  exact LinearMap.congr_fun hf w

end GlobalTheory.DetInv
