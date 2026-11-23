import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzRedF
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic
  GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

section Inv

variable {m : ℕ} (τ : FDRep ℂ (Gn g (m + 1))) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (π : Representation ℂ (GL (Fin (m + 1)) (w.adicCompletion E)) V)
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (L : Module.Dual ℂ V) (l' : Module.Dual ℂ V')
    (φ : τ →ₗ[ℂ] V)

include hi in
theorem FR_right
    (hφ : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g (m + 1) κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) κ)) (φ x))
    (v' : V') (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (x : τ) (h : GL (Fin m) (w.adicCompletion E)) {k : GL (Fin m) (w.adicCompletion E)}
    (hk : k ∈ KOne (w.adicCompletion E) (Fin m)) :
    FR π ρ₀ L l' (φ x) v' (h * k) = FR π ρ₀ L l' (φ x) v' h := by
  obtain ⟨κ, h1, rfl⟩ := DzIso.exists_of_mem_KOne i hi hk
  unfold FR
  rw [corner_mul, rep_mul_apply, rep_mul_apply ρ₀, hv' κ (by rw [h1]; exact isLower_one), ← phi_corner, ← hφ,
    red_corner, h1, corner_one, rep_one_apply]

include hi in
theorem FL_right
    (hφ : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g (m + 1) κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) κ)) (φ x))
    (v' : V') (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (x : τ) (h : GL (Fin m) (w.adicCompletion E)) {k : GL (Fin m) (w.adicCompletion E)}
    (hk : k ∈ KOne (w.adicCompletion E) (Fin m)) :
    FL π ρ₀ L l' (φ x) v' (h * k) = FL π ρ₀ L l' (φ x) v' h := by
  obtain ⟨κ, h1, rfl⟩ := DzIso.exists_of_mem_KOne i hi hk
  unfold FL
  rw [corner_mul, tilde_mul, tilde_mul, rep_mul_apply, rep_mul_apply ρ₀, ← phi_invT,
    hv' _ (by rw [red_invT, h1, map_one]; exact isLower_one), ← phi_corner, ← phi_invT, ← hφ,
    red_invT, red_corner, h1, corner_one, map_one, rep_one_apply]

include hi in
theorem FR_supp (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1)
    (hτ : IsCusp τ.character)
    (hφ : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g (m + 1) κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) κ)) (φ x))
    (hL : IsFunctional ψ π L) (hl' : IsFunctional ψ⁻¹ ρ₀ l') (v' : V') (x : τ) (h : GL (Fin m) (w.adicCompletion E))
    (hne : FR π ρ₀ L l' (φ x) v' h ≠ 0) :
    ∃ u ∈ unipB (w.adicCompletion E) (Fin m), ∃ k ∈ KO (w.adicCompletion E) (Fin m), h = u * k := by
  obtain ⟨u, hu, d, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (w.adicCompletion E) m h
  obtain ⟨κ, rfl⟩ := DzLc.exists_inc_eq i hi k hk
  rw [mul_assoc, FR_left π ρ₀ L l' hL hl' _ _ (unipotent_le_unipB hu)] at hne
  unfold FR at hne
  have hne' := left_ne_zero_of_mul hne
  rw [corner_mul, rep_mul_apply, ← phi_corner, ← hφ, corner_torusPow] at hne'
  have hd := supp_const i hi hψ h0 τ hτ π φ hφ L hL _ _ hne'
  have hd0 : d = 0 := funext fun j => by simpa using hd j.castSucc (Fin.last m)
  refine ⟨u, unipotent_le_unipB hu, _, DzIso.map_inc_mem_KO i hi κ, ?_⟩
  rw [hd0, torusPow_zero', mul_one]

include hi in
theorem FL_supp (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1)
    (hτ : IsCusp τ.character)
    (hφ : ∀ (κ : GL (Fin (m + 1)) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g (m + 1) κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) κ)) (φ x))
    (hL : IsFunctional ψ π L) (hl' : IsFunctional ψ⁻¹ ρ₀ l') (v' : V') (x : τ) (h : GL (Fin m) (w.adicCompletion E))
    (hne : FL π ρ₀ L l' (φ x) v' h ≠ 0) :
    ∃ u ∈ unipB (w.adicCompletion E) (Fin m), ∃ k ∈ KO (w.adicCompletion E) (Fin m), h = u * k := by
  obtain ⟨u, hu, d, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (w.adicCompletion E) m h
  obtain ⟨κ, rfl⟩ := DzLc.exists_inc_eq i hi k hk
  rw [mul_assoc, FL_left π ρ₀ L l' hL hl' _ _ (unipotent_le_unipB hu)] at hne
  unfold FL at hne
  have hne' := left_ne_zero_of_mul hne
  rw [corner_mul, tilde_mul,
    show tilde (corner (Iwasawa.torusPow (w.adicCompletion E) m d)) =
      longElt (m + 1) _ * GlobalTheory.CuspRep.invT (m + 1) _ (corner (Iwasawa.torusPow (w.adicCompletion E) m d)) from rfl,
    corner_torusPow, longElt_mul_invT_torusPow, mul_assoc, rep_mul_apply, ← phi_corner, ← phi_invT,
    ← phi_longElt (g := g) i (m + 1), ← map_mul (Matrix.GeneralLinearGroup.map i.toRingHom), ← map_mul (inc g (m + 1)), ← hφ] at hne'
  have hd := supp_const i hi hψ h0 τ hτ π φ hφ L hL _ _ hne'
  have hd0 : d = 0 := funext fun j => by simpa using hd (j.castSucc).rev (Fin.last m).rev
  refine ⟨u, unipotent_le_unipB hu, _, DzIso.map_inc_mem_KO i hi κ, ?_⟩
  rw [hd0, torusPow_zero', mul_one]

end Inv

end DiscreteGroups.sglob.DzRed
