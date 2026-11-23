import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem contracts_of_iso_directSum (H G I F V : Type) [Monoid H] [Monoid G] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup V] [Module ℂ V] (A B : I → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (a : ∀ i, Representation ℂ H (A i))
    (b : ∀ i, Representation ℂ G (B i)) (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V) (i₀ : I)
    (hφ : Iso (Representation.directSum fun i =>
      Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) φ)
    (h0 : ∀ i, i ≠ i₀ → invFun ((a i).tprod σ) = ⊥)
    (h1 : Module.finrank ℂ (invFun ((a i₀).tprod σ)) = 1) : Contracts φ σ (b i₀) := by
  classical
  refine Contracts.congr ?_ hφ (Iso.refl σ) (Iso.refl _)
  obtain ⟨⟨ε, hε⟩, hne, hspan⟩ := finrank_eq_one_iff'.1 h1
  have hε0 : ε ≠ 0 := fun h => hne (Subtype.ext h)
  have hεi : ∀ h x v, ε (a i₀ h x ⊗ₜ σ h v) = ε (x ⊗ₜ v) := fun h x v => by
    simpa using mem_invFun.1 hε h (x ⊗ₜ v)
  obtain ⟨z, hz⟩ : ∃ z, ε z = 1 := LinearMap.surjective hε0 1
  let P : (A i₀ ⊗[ℂ] B i₀) ⊗[ℂ] V →ₗ[ℂ] B i₀ :=
    (TensorProduct.lid ℂ (B i₀)).toLinearMap ∘ₗ LinearMap.rTensor (B i₀) ε ∘ₗ
      (TensorProduct.rightComm ℂ (A i₀) (B i₀) V).toLinearMap
  have hP : ∀ x y v, P ((x ⊗ₜ y) ⊗ₜ v) = ε (x ⊗ₜ v) • y := fun x y v => by simp [P]
  let J : ∀ i, B i → A i ⊗[ℂ] V →ₗ[ℂ] (⨁ i, A i ⊗[ℂ] B i) ⊗[ℂ] V := fun i y =>
    LinearMap.rTensor V (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i ∘ₗ (TensorProduct.mk ℂ (A i) (B i)).flip y)
  have hJ : ∀ i y x v, J i y (x ⊗ₜ v) = DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i (x ⊗ₜ y) ⊗ₜ v :=
    fun i y x v => by simp [J]
  let π : (⨁ i, A i ⊗[ℂ] B i) ⊗[ℂ] V →ₗ[ℂ] B i₀ :=
    P ∘ₗ LinearMap.rTensor V (DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀)
  have hπ : ∀ f v, π (f ⊗ₜ v) = P (DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ f ⊗ₜ v) :=
    fun f v => by simp [π]
  have hπJ : ∀ y w, π (J i₀ y w) = ε w • y := fun y w => by
    induction w with
    | zero => simp
    | tmul x v => rw [hJ, hπ, DirectSum.component.lof_self, hP]
    | add s t hs ht => simp only [map_add, hs, ht, add_smul]
  have hπJ' : ∀ i, i ≠ i₀ → ∀ y x v, π (J i y (x ⊗ₜ v)) = 0 := fun i hi y x v => by
    rw [hJ, hπ, DirectSum.component.of, dif_neg hi]; simp
  refine ⟨π, fun y => ⟨J i₀ y z, by rw [hπJ, hz, one_smul]⟩, fun h g f v => ?_, fun l hl => ?_⟩
  · rw [hπ, hπ]
    have e : DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ ((Representation.directSum fun i =>
        Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) (h, g) f) =
        TensorProduct.map (a i₀ h) (b i₀ g) (DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ f) := rfl
    rw [e]
    generalize DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ f = t
    induction t with
    | zero => simp
    | tmul x y => rw [TensorProduct.map_tmul, hP, hP, hεi, map_smul]
    | add s t hs ht => simp only [map_add, TensorProduct.add_tmul, hs, ht]
  · have hinv : ∀ i y, l ∘ₗ J i y ∈ invFun ((a i).tprod σ) := fun i y => mem_invFun.2 fun h w => by
      induction w with
      | zero => simp
      | tmul x v =>
        have := hl h (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i (x ⊗ₜ y)) v
        simpa [hJ] using this
      | add s t hs ht => simp only [map_add, hs, ht]
    let c : B i₀ →ₗ[ℂ] ℂ := l ∘ₗ LinearMap.rTensor V (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i₀) ∘ₗ
      (TensorProduct.rightComm ℂ (A i₀) (B i₀) V).symm.toLinearMap ∘ₗ TensorProduct.mk ℂ _ _ z
    have hc : ∀ y, c y = l (J i₀ y z) := fun y => by
      simp only [c, LinearMap.comp_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe]
      congr 1
      generalize z = w
      induction w with
      | zero => simp
      | tmul x v => simp [hJ]
      | add s t hs ht => simp only [map_add, TensorProduct.add_tmul, hs, ht]
    have key : ∀ i y x v, l (J i y (x ⊗ₜ v)) = c (π (J i y (x ⊗ₜ v))) := fun i y x v => by
      by_cases hi : i = i₀
      · subst hi
        obtain ⟨r, hr⟩ := hspan ⟨_, hinv i y⟩
        have hr' : ∀ w, l (J i y w) = r * ε w := fun w => by
          simpa using (congrArg (fun m : invFun ((a i).tprod σ) => m.1 w) hr).symm
        rw [hπJ, map_smul, hc, hr', hr', hz, smul_eq_mul]
        ring
      · have := hinv i y
        rw [h0 i hi, Submodule.mem_bot] at this
        rw [hπJ' i hi, map_zero]
        exact LinearMap.congr_fun this _
    have hl' : l = c ∘ₗ π := by
      refine TensorProduct.ext (DirectSum.linearMap_ext _ fun i => TensorProduct.ext' fun x y => ?_)
      ext v
      simpa [hJ] using key i y x v
    intro x hx
    rw [hl', LinearMap.comp_apply, hx, map_zero]

end GlobalTheory.OneFunctional
