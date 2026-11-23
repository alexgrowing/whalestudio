import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigVia

open ReciprocityTheory.Gal UpperTheory.V.Base

set_option maxHeartbeats 200000 in
theorem UpperTheory.V.Base.lenEigSign :
    ∀ (O W Q N : Type) [CommRing O] [IsDomain O] [Group W] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O W N) (p : W →* Q), Function.Surjective p →
      (∀ g, p g = 1 → ∀ x, π g x = x) →
      IsUnit (2 : O) → ∀ (c : W) (s : Oˣ), p c * p c = 1 → s * s = 1 → ∀ T : Finset (Q →* Oˣ), (∀ ψ, ψ (p c) = s → ψ ∈ T) →
      Module.length O (Module.End.eigenspace (π c) (s : O)) ≤ ∑ ψ ∈ T, Module.length O (eig π (ψ.comp p)) := by
  intro O W Q N _ _ _ _ _ _ _ _ _ π p hp hker h2 c s hc hs T hT
  have hcomm : ∀ (g : W) (x : N), π g (π c x) = π c (π g x) := by
    intro g x
    have hk : p ((c * g)⁻¹ * (g * c)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (p g) (p c), inv_mul_cancel]
    have e1 : g * c = (c * g) * ((c * g)⁻¹ * (g * c)) := by group
    have a1 : π g (π c x) = π (g * c) x := by rw [map_mul]; rfl
    have a2 : π c (π g x) = π (c * g) x := by rw [map_mul]; rfl
    rw [a1, a2, e1, map_mul, Module.End.mul_apply, hker _ hk]
  have hE : ∀ g, Module.End.eigenspace (π c) (s : O) ≤
      (Module.End.eigenspace (π c) (s : O)).comap (π g) := by
    intro g x hx
    rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff] at *
    rw [← hcomm, hx, map_smul]
  let πE := π.subrepresentation _ hE
  have hkerE : ∀ g, p g = 1 → ∀ x, πE g x = x := by
    intro g hg x
    apply Subtype.ext
    exact hker g hg x
  obtain ⟨hlen, -⟩ := lenEigVia O W Q _ πE p hp hkerE
  refine hlen.trans ?_
  have hzero : ∀ ψ : Q →* Oˣ, ψ ∉ T → Module.length O (eig πE (ψ.comp p)) = 0 := by
    intro ψ hψ
    have hne : ψ (p c) ≠ s := fun h => hψ (hT ψ h)
    have hu : IsUnit ((s : O) - (ψ (p c) : O)) := by
      have a : (s : O) * s = 1 := by rw [← Units.val_mul, hs, Units.val_one]
      have b : (ψ (p c) : O) * ψ (p c) = 1 := by
        rw [← Units.val_mul, ← map_mul, hc, map_one, Units.val_one]
      have hsq : ((s : O) - ψ (p c)) * ((s : O) + ψ (p c)) = 0 := by
        linear_combination a - b
      rcases mul_eq_zero.mp hsq with h | h
      · exact absurd (Units.ext (sub_eq_zero.mp h)).symm hne
      · have e : (s : O) - ψ (p c) = 2 * s := by linear_combination (-1 : O) * h
        rw [e]
        exact h2.mul s.isUnit
    have key : ∀ y : eig πE (ψ.comp p), y = 0 := by
      intro y
      have h1 : π c y.1.1 = (ψ (p c) : O) • y.1.1 :=
        congrArg Subtype.val ((mem_eig.mp y.2) c)
      have h2' : π c y.1.1 = (s : O) • y.1.1 :=
        Module.End.mem_eigenspace_iff.mp y.1.2
      have h3 : ((s : O) - ψ (p c)) • y.1.1 = 0 := by
        rw [sub_smul, ← h1, ← h2', sub_self]
      have h4 : y.1.1 = 0 := hu.smul_eq_zero.mp h3
      apply Subtype.ext
      apply Subtype.ext
      exact h4
    rw [Module.length_eq_zero_iff]
    exact ⟨fun a b => (key a).trans (key b).symm⟩
  have hmono : ∀ ψ : Q →* Oˣ,
      Module.length O (eig πE (ψ.comp p)) ≤ Module.length O (eig π (ψ.comp p)) := by
    intro ψ
    refine Module.length_le_of_injective
      (LinearMap.codRestrict (eig π (ψ.comp p))
        ((Module.End.eigenspace (π c) (s : O)).subtype ∘ₗ (eig πE (ψ.comp p)).subtype) ?_) ?_
    · intro y
      rw [mem_eig]
      intro g
      exact congrArg Subtype.val ((mem_eig.mp y.2) g)
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  rw [← Finset.sum_subset (Finset.subset_univ T) (fun ψ _ hψ => hzero ψ hψ)]
  exact Finset.sum_le_sum fun ψ _ => hmono ψ
