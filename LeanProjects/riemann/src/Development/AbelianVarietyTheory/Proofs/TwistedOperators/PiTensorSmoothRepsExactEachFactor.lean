import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL

def piTensorHom {α : Type} {Γ : α → Type} [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)]
    {X Y : ∀ i, SmRep (Γ i)} (f : ∀ a, (X a).ρ.IntertwiningMap (Y a).ρ) :
    (piTensor fun a => (X a).ρ).IntertwiningMap (piTensor fun a => (Y a).ρ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod,
      PiTensorProduct.map_tprod]
    congr 1
    funext a
    exact LinearMap.congr_fun ((f a).isIntertwining' (g a)) (x a)

theorem piTensorMap_add_eq_id {α : Type} [DecidableEq α] {Y : α → Type} [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] (i : α) (u v : ∀ a, Y a →ₗ[ℂ] Y a) (hu : ∀ a, a ≠ i → u a = LinearMap.id)
    (hv : ∀ a, a ≠ i → v a = LinearMap.id) (h : u i + v i = LinearMap.id) :
    PiTensorProduct.map u + PiTensorProduct.map v = LinearMap.id := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, PiTensorProduct.map_tprod,
    LinearMap.id_apply]

  have hx : ∀ w : ∀ a, Y a →ₗ[ℂ] Y a, (∀ a, a ≠ i → w a = LinearMap.id) →
      (fun a => w a (x a)) = Function.update x i (w i (x i)) := by
    intro w hw
    funext a
    by_cases ha : a = i
    · subst ha
      simp
    · rw [Function.update_of_ne ha, hw a ha, LinearMap.id_apply]
  rw [hx u hu, hx v hv, ← MultilinearMap.map_update_add, ← LinearMap.add_apply, h,
    LinearMap.id_apply, Function.update_eq_self]

theorem piTensor_exact_position : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → ∃ (ι' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₁ a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ)) (p' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₂ a).ρ)), Function.Injective ι' ∧ Function.Surjective p' ∧ (∀ u, p' (ι' u) = 0) ∧ (∀ v, p' v = 0 → ∃ u, ι' u = v) := by
  intro α _ _ Γ _ _ A i B B₁ B₂ ι p hι hp hpι hker

  have key : ∀ a, ∃ (f : (Function.update A i B₁ a).ρ.IntertwiningMap (Function.update A i B a).ρ)
      (g : (Function.update A i B a).ρ.IntertwiningMap (Function.update A i B₂ a).ρ)
      (s : (Function.update A i B a).V →ₗ[ℂ] (Function.update A i B₁ a).V)
      (t : (Function.update A i B₂ a).V →ₗ[ℂ] (Function.update A i B a).V),
      s ∘ₗ f.toLinearMap = LinearMap.id ∧ g.toLinearMap ∘ₗ t = LinearMap.id ∧
      (a ≠ i → f.toLinearMap ∘ₗ s = LinearMap.id ∧ t ∘ₗ g.toLinearMap = LinearMap.id) ∧
      (a = i → f.toLinearMap ∘ₗ s + t ∘ₗ g.toLinearMap = LinearMap.id ∧
        g.toLinearMap ∘ₗ f.toLinearMap = 0) := by
    intro a
    by_cases ha : a = i
    · subst ha
      rw [Function.update_self, Function.update_self, Function.update_self]
      obtain ⟨t, ht⟩ := p.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
      obtain ⟨s₀, hs₀⟩ := ι.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hι)
      have hs₀' : ∀ u, s₀ (ι u) = u := fun u => LinearMap.congr_fun hs₀ u
      have ht' : ∀ z, p (t z) = z := fun z => LinearMap.congr_fun ht z
      refine ⟨ι, p, s₀ ∘ₗ (LinearMap.id - t ∘ₗ p.toLinearMap), t, ?_, ht, fun h => absurd rfl h,
        fun _ => ⟨?_, ?_⟩⟩
      · ext u
        simp [hpι, hs₀']
      · ext y

        obtain ⟨u, hu⟩ := hker (y - t (p y)) (by simp [ht'])
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
          Representation.IntertwiningMap.coe_toLinearMap]
        rw [← hu, hs₀', hu, sub_add_cancel]
      · ext u
        simp [hpι]
    · rw [Function.update_of_ne ha, Function.update_of_ne ha, Function.update_of_ne ha]
      exact ⟨Representation.IntertwiningMap.id _, Representation.IntertwiningMap.id _, LinearMap.id, LinearMap.id, by ext; rfl,
        by ext; rfl, fun _ => ⟨by ext; rfl, by ext; rfl⟩, fun h => absurd h ha⟩
  choose f g s t hsf hgt hne heq using key
  have hF : ∀ x, piTensorHom f x = PiTensorProduct.map (fun a => (f a).toLinearMap) x := fun _ => rfl
  have hG : ∀ x, piTensorHom g x = PiTensorProduct.map (fun a => (g a).toLinearMap) x := fun _ => rfl
  have hSF : PiTensorProduct.map s ∘ₗ PiTensorProduct.map (fun a => (f a).toLinearMap) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, funext hsf, PiTensorProduct.map_id]
  have hGT : PiTensorProduct.map (fun a => (g a).toLinearMap) ∘ₗ PiTensorProduct.map t = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, funext hgt, PiTensorProduct.map_id]
  have hsum : PiTensorProduct.map (fun a => (f a).toLinearMap) ∘ₗ PiTensorProduct.map s +
      PiTensorProduct.map t ∘ₗ PiTensorProduct.map (fun a => (g a).toLinearMap) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    exact piTensorMap_add_eq_id i _ _ (fun a ha => (hne a ha).1) (fun a ha => (hne a ha).2)
      (heq i rfl).1
  have hGF : PiTensorProduct.map (fun a => (g a).toLinearMap) ∘ₗ
      PiTensorProduct.map (fun a => (f a).toLinearMap) = 0 := by
    rw [← PiTensorProduct.map_comp]
    ext x
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]

    exact MultilinearMap.map_coord_zero _ i (by rw [(heq i rfl).2, LinearMap.zero_apply])
  refine ⟨piTensorHom f, piTensorHom g, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have := congrArg (PiTensorProduct.map s) hxy
    rw [hF, hF] at this
    simpa using (LinearMap.congr_fun hSF x).symm.trans (this.trans (LinearMap.congr_fun hSF y))
  · intro z
    exact ⟨PiTensorProduct.map t z, by rw [hG]; exact LinearMap.congr_fun hGT z⟩
  · intro u
    rw [hG, hF]
    exact LinearMap.congr_fun hGF u
  · intro v hv
    refine ⟨PiTensorProduct.map s v, ?_⟩
    rw [hG] at hv
    have := LinearMap.congr_fun hsum v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hv, map_zero, add_zero,
      LinearMap.id_apply] at this
    rw [hF]
    exact this

end GlobalTheory.SmGL
