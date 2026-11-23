import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

namespace GlobalTheory

theorem descend_multilinear_mod : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A P₀ Q : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup P₀] [Module ℂ P₀] [AddCommGroup Q] [Module ℂ Q] (S P : ι → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] (A₀ : Submodule ℂ A) (S₀ : ∀ i, Submodule ℂ (S i)) (NQ : Submodule ℂ Q) (p₀ : A →ₗ[ℂ] P₀) (p : ∀ i, S i →ₗ[ℂ] P i) (Ψ : A →ₗ[ℂ] MultilinearMap ℂ S Q), A₀.map p₀ = ⊤ → (∀ i, (S₀ i).map (p i) = ⊤) → (∀ a ∈ A₀, ∀ s : ∀ i, S i, (∀ i, s i ∈ S₀ i) → p₀ a = 0 → Ψ a s ∈ NQ) → (∀ a ∈ A₀, ∀ s : ∀ i, S i, (∀ i, s i ∈ S₀ i) → ∀ i, p i (s i) = 0 → Ψ a s ∈ NQ) → ∀ (m : ℕ) (a : Fin m → A) (s : Fin m → ∀ i, S i), (∀ k, a k ∈ A₀ ∧ ∀ i, s k i ∈ S₀ i) → ∑ k, p₀ (a k) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun i => p i (s k i)) = 0 → ∑ k, Ψ (a k) (s k) ∈ NQ := by
  intro ι _ _ A P₀ Q _ _ _ _ _ _ S P _ _ _ _ A₀ S₀ NQ p₀ p Ψ hA hS h0 h1 m a s hmem hsum
  obtain ⟨σ₀, hσ₀⟩ := LinearMap.exists_rightInverse_of_surjective (p₀.comp A₀.subtype)
    (by rw [LinearMap.range_comp, Submodule.range_subtype]; exact hA)
  have hσ : ∀ i, ∃ g : P i →ₗ[ℂ] S₀ i, ((p i).comp (S₀ i).subtype).comp g = LinearMap.id :=
    fun i => LinearMap.exists_rightInverse_of_surjective _
      (by rw [LinearMap.range_comp, Submodule.range_subtype]; exact hS i)
  choose σ hσ using hσ
  have hs₀ : ∀ u, p₀ ((σ₀ u : A)) = u := fun u => LinearMap.congr_fun hσ₀ u
  have hsi : ∀ i (x : P i), p i ((σ i x : S i)) = x := fun i x => LinearMap.congr_fun (hσ i) x
  let τ : ∀ i, S i → S i := fun i x => (σ i (p i x) : S i)
  have hττ : ∀ i x, τ i (τ i x) = τ i x := by intro i x; simp only [τ, hsi]
  have hτmem : ∀ i x, τ i x ∈ S₀ i := fun i x => (σ i (p i x)).2
  have hpτ : ∀ i x, p i (x - τ i x) = 0 := by intro i x; simp [τ, hsi]
  have key_s : ∀ b ∈ A₀, ∀ (T : Finset ι) (t : ∀ i, S i), (∀ i, t i ∈ S₀ i) →
      (∀ i ∉ T, τ i (t i) = t i) → NQ.mkQ (Ψ b t) = NQ.mkQ (Ψ b (fun i => τ i (t i))) := by
    intro b hb T
    induction T using Finset.induction_on with
    | empty =>
      intro t _ ht
      congr 2; funext i; exact (ht i (by simp)).symm
    | @insert j T hj ih =>
      intro t ht htau
      have ht' : ∀ i, Function.update t j (τ j (t j)) i ∈ S₀ i := by
        intro i; by_cases h : i = j
        · subst h; simp only [Function.update_self]; exact hτmem _ _
        · simp only [Function.update_of_ne h]; exact ht i
      have htau' : ∀ i ∉ T, τ i (Function.update t j (τ j (t j)) i) = Function.update t j (τ j (t j)) i := by
        intro i hi; by_cases h : i = j
        · subst h; simp only [Function.update_self]; exact hττ _ _
        · simp only [Function.update_of_ne h]; exact htau i (by simp [h, hi])
      have e1 := ih _ ht' htau'
      have e2 : (fun i => τ i (Function.update t j (τ j (t j)) i)) = fun i => τ i (t i) := by
        funext i; by_cases h : i = j
        · subst h; simp only [Function.update_self]; exact hττ _ _
        · simp only [Function.update_of_ne h]
      have hdiff : Ψ b t - Ψ b (Function.update t j (τ j (t j))) ∈ NQ := by
        have : Ψ b t - Ψ b (Function.update t j (τ j (t j))) = Ψ b (Function.update t j (t j - τ j (t j))) := by
          rw [MultilinearMap.map_update_sub, Function.update_eq_self]
        rw [this]
        refine h1 b hb _ ?_ j ?_
        · intro i; by_cases h : i = j
          · subst h; simp only [Function.update_self]; exact sub_mem (ht i) (hτmem _ _)
          · simp only [Function.update_of_ne h]; exact ht i
        · simp only [Function.update_self]; exact hpτ _ _
      calc NQ.mkQ (Ψ b t) = NQ.mkQ (Ψ b (Function.update t j (τ j (t j)))) := by
            simp only [Submodule.mkQ_apply]; exact (Submodule.Quotient.eq NQ).2 hdiff
        _ = _ := e1
        _ = _ := by rw [e2]
  have key : ∀ x ∈ A₀, ∀ t : ∀ i, S i, (∀ i, t i ∈ S₀ i) →
      NQ.mkQ (Ψ x t) = NQ.mkQ (Ψ ((σ₀ (p₀ x) : A)) (fun i => τ i (t i))) := by
    intro x hx t ht
    have hd : Ψ x t - Ψ ((σ₀ (p₀ x) : A)) t ∈ NQ := by
      rw [← MultilinearMap.sub_apply, ← map_sub]
      refine h0 _ (sub_mem hx (σ₀ (p₀ x)).2) t ht ?_
      rw [map_sub, hs₀, sub_self]
    rw [← key_s _ (σ₀ (p₀ x)).2 Finset.univ t ht (by simp)]
    simp only [Submodule.mkQ_apply]; exact (Submodule.Quotient.eq NQ).2 hd
  let L : P₀ →ₗ[ℂ] MultilinearMap ℂ P (Q ⧸ NQ) :=
    { toFun := fun u => (NQ.mkQ.compMultilinearMap (Ψ (σ₀ u : A))).compLinearMap
          (fun i => (S₀ i).subtype.comp (σ i))
      map_add' := by intro x y; ext t; simp
      map_smul' := by intro c x; ext t; simp }
  let Λ : P₀ ⊗[ℂ] (⨂[ℂ] i, P i) →ₗ[ℂ] Q ⧸ NQ :=
    TensorProduct.lift ((PiTensorProduct.lift (R := ℂ) (s := P) (E := Q ⧸ NQ)).toLinearMap.comp L)
  have hk : ∀ k, NQ.mkQ (Ψ (a k) (s k)) = Λ (p₀ (a k) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun i => p i (s k i))) := by
    intro k
    rw [key _ (hmem k).1 _ (hmem k).2]
    simp [Λ, L, τ]
  have : NQ.mkQ (∑ k, Ψ (a k) (s k)) = 0 := by
    rw [map_sum]; simp_rw [hk]; rw [← map_sum, hsum, map_zero]
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end GlobalTheory
