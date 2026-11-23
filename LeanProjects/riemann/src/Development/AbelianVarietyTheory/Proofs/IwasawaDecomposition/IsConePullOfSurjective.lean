import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPartOfBasisOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfCoeffNeZero

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem apply_eq_zero_of_diag {X : Type} [AddCommGroup X] {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hp : ∀ y, 0 ≤ β y y) {y : X} (hy : β y y = 0) (z : X) : β y z = 0 := by
  by_contra hb
  have hA := hp z
  have h := hp (z + (-(β z z + 1) * β y z) • y)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hy, hs z y] at h
  have hb2 : 1 ≤ β y z * β y z := mul_self_pos.2 hb
  have h3 := mul_nonneg (by linarith : 0 ≤ β z z + 1) (sub_nonneg.2 hb2)
  nlinarith [h3]

theorem exists_pull_eq {O : Type} [CommRing O] {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hk : ∀ y, r y = 0 → ∀ z, β y z = 0) : ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = β := by
  have key1 : ∀ a a' b, r a = r a' → β a b = β a' b := fun a a' b h => by
    have := hk (a - a') (by rw [map_sub, h, sub_self]) b
    rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  have key : ∀ a a' b b', r a = r a' → r b = r b' → β a b = β a' b' := fun a a' b b' h h' => by
    rw [key1 a a' b h, hs a' b, key1 b b' a' h', hs]
  have hs' : ∀ a, r (Function.surjInv hr a) = a := Function.surjInv_eq hr
  refine ⟨LinearMap.mk₂ ℤ (fun a b => β (Function.surjInv hr a) (Function.surjInv hr b)) ?_ ?_ ?_ ?_,
    LinearMap.ext₂ fun a b => ?_⟩
  · intro a a' b
    rw [← LinearMap.add_apply, ← map_add]
    exact key _ _ _ _ (by rw [map_add, hs', hs', hs']) rfl
  · intro n a b
    rw [← LinearMap.smul_apply, ← map_smul]
    exact key _ _ _ _ (by rw [map_zsmul r, hs', hs']) rfl
  · intro a b b'
    rw [← map_add]
    exact key _ _ _ _ rfl (by rw [map_add, hs', hs', hs'])
  · intro n a b
    rw [← map_smul]
    exact key _ _ _ _ rfl (by rw [map_zsmul r, hs', hs'])
  · simpa using key _ _ _ _ (hs' (r a)) (hs' (r b))

theorem isCone_pull_of_surjective : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (φ : InvFun O) (X₁ : Type) [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₁), IsPolFanOn bar φ X → Function.Surjective r → IsCone bar φ γ → IsCone bar φ (fun i => pull r (γ i)) := by
  intro O _ _ _ _ bar X _ _ _ φ X₁ _ _ _ r m γ hF hr hγ
  classical
  have hx := GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X m (fun i => pull r (γ i)) (fun _ => 1) (fun i => pull_mem r (hγ.mem i))
    (fun i y => hγ.nonneg i _) (fun _ => zero_le_one)
  obtain ⟨m₂, σ, c, hσ, hc, hsum⟩ := hF.cover _ hx
  let J : Finset (Fin m₂) := Finset.univ.filter fun j => c j ≠ 0
  let t : Fin J.card ↪ Fin m₂ := (J.orderEmbOfFin rfl).toEmbedding
  have hpos : ∀ k, c (t k) ≠ 0 := fun k => (Finset.mem_filter.1 (J.orderEmbOfFin_mem rfl k)).2
  have hout : ∀ j, j ∉ Set.range t → c j = 0 := fun j hj => by
    by_contra h0
    refine hj ?_
    have : j ∈ Set.range (J.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩)
    exact this
  have hδ := hF.face _ _ σ t hσ
  have hsum' : ∑ i, (1 : ℝ) • toReal (pull r (γ i)) = ∑ k, c (t k) • toReal (σ (t k)) :=
    hsum.trans (Fintype.sum_of_injective t t.injective _ _ (fun j hj => by simp [hout j hj]) fun _ => rfl).symm
  have hvan : ∀ k y, r y = 0 → σ (t k) y y = 0 := fun k y hy => by
    have h1 := LinearMap.congr_fun₂ hsum' y y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, hy, map_zero, LinearMap.zero_apply,
      Int.cast_zero, smul_zero, smul_eq_mul, mul_zero, Finset.sum_const_zero] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hc (t k))
      (by exact_mod_cast hσ.nonneg (t k) y : (0 : ℝ) ≤ (σ (t k) y y : ℝ))).1 h1.symm k (Finset.mem_univ _)
    exact_mod_cast (mul_eq_zero.1 h2).resolve_left (hpos k)
  have hex : ∀ k, ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = σ (t k) := fun k =>
    exists_pull_eq hr (hσ.mem (t k)).1 fun y hy z =>
      apply_eq_zero_of_diag (hσ.mem (t k)).1 (hσ.nonneg (t k)) (hvan k y hy) z
  choose δ hδ' using hex
  have hδc : IsCone bar φ δ := GlobalTheory.PolFan.isCone_of_pull O bar φ X X₁ r _ δ hr (by simpa only [hδ'] using hδ)
  have hsum₁ : ∑ i, (1 : ℝ) • toReal (γ i) = ∑ k, c (t k) • toReal (δ k) := LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    have h1 := LinearMap.congr_fun₂ hsum' a b
    simp only [← hδ'] at h1
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply] using h1
  have hmeet := GlobalTheory.PolFan.cone_meet O bar φ X₁ m _ γ δ (fun _ => 1) (fun k => c (t k)) hγ hδc (fun _ => zero_le_one)
    (fun k => hc _) hsum₁
  choose j hj using fun i => hmeet i one_ne_zero
  have hinj : Function.Injective j := fun i i' h =>
    hγ.injective ((hj i).1.trans ((congrArg δ h).trans (hj i').1.symm))
  have hfin := hF.face _ _ _ ⟨j, hinj⟩ hδ
  have heq : (fun i => pull r (γ i)) = fun i => σ (t (j i)) := funext fun i => by rw [(hj i).1, hδ']
  rw [heq]
  exact hfin

end GlobalTheory.PolFan
