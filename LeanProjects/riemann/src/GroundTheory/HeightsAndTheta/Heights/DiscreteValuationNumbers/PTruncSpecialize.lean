import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTruncSpecialize
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Ring

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E]

def projCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (u : Fin N → B) :
    (Σ o, bundleIdx ι M o) → B
  | ⟨none, l⟩ => ∑ i, u i * algebraMap Ω B (φ l (w i))
  | ⟨some k, i⟩ => algebraMap Ω B (y ⟨k, i⟩)

theorem projCoordRing_map {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (u : Fin N → B) (p : Σ o, bundleIdx ι M o) :
    g (projCoordRing y w φ u p) = projCoordRing y w φ (g ∘ u) p := by
  rcases p with ⟨_ | k, l⟩ <;> simp [projCoordRing, map_sum]

theorem projCoord_eq_projCoordRing {Φ : Type*} [Field Φ] [Algebra Ω Φ] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    projCoord y w φ t = projCoordRing y w φ t := by
  funext p
  rcases p with ⟨_ | k, l⟩ <;> rfl

end Ring

theorem map_coneMap {σ τ R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] (f : R →+* B)
    (g : B →+* B') (c : σ → B) (q : σ → τ) (x : MvPolynomial σ R) :
    map g (eval₂ (C.comp f) (fun p => C (c p) * X (q p)) x) =
      eval₂ (C.comp (g.comp f)) (fun p => C (g (c p)) * X (q p)) x := by
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext p
    simp

theorem TruncSpecialize.proof : TruncSpecialize.Statement := by
  intro F _ Ω _ _ K ι y N E _ _ w M φ Φ _ _ t ht i
  let ev : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ := aeval t
  have hev : Function.Injective ev := ht
  let sub : MvPolynomial (Fin N) Ω →ₐ[Ω] MvPolynomial (Fin N) Ω := aeval fun k => if k = i then 0 else X k
  have hevT : ∀ j : ℕ, ev ∘ truncCoord (X : Fin N → MvPolynomial (Fin N) Ω) j = truncCoord t j := by
    intro j
    funext k
    by_cases hk : (k : ℕ) < j <;> simp [truncCoord, hk, ev]
  have hsubT : sub ∘ truncCoord (X : Fin N → MvPolynomial (Fin N) Ω) ((i : ℕ) + 1) = truncCoord X i := by
    funext k
    simp only [Function.comp_apply, truncCoord]
    rcases lt_trichotomy (k : ℕ) i with h | h | h
    · have hki : k ≠ i := fun e => by subst e; exact lt_irrefl _ h
      simp [h, Nat.lt_succ_of_lt h, sub, hki]
    · have hki : k = i := Fin.ext h
      subst hki
      simp [sub]
    · have h1 : ¬ (k : ℕ) < i + 1 := by omega
      have h2 : ¬ (k : ℕ) < i := by omega
      simp [h1, h2]
  let cA : ℕ → (Σ o, bundleIdx ι M o) → MvPolynomial (Fin N) Ω :=
    fun j => projCoordRing y w φ (truncCoord X j)
  have hcoord : ∀ j : ℕ, projCoord y w φ (truncCoord t j) = fun p => ev (cA j p) := by
    intro j
    funext p
    rw [projCoord_eq_projCoordRing, ← hevT, projCoordRing_map]
  have hsubc : ∀ p, sub (cA ((i : ℕ) + 1) p) = cA i p := by
    intro p
    simp only [cA]
    rw [projCoordRing_map, hsubT]
  let algA : F →+* MvPolynomial (Fin N) Ω := (algebraMap Ω (MvPolynomial (Fin N) Ω)).comp (algebraMap F Ω)
  have hevA : (ev : MvPolynomial (Fin N) Ω →+* Φ).comp algA = (algebraMap Ω Φ).comp (algebraMap F Ω) :=
    RingHom.ext fun a => by simp [algA]
  have hsubA : (sub : MvPolynomial (Fin N) Ω →+* MvPolynomial (Fin N) Ω).comp algA = algA :=
    RingHom.ext fun a => by simp [algA]
  refine ⟨fun x hx => ?_, fun x z hxz => ?_⟩
  · have key : ∀ j : ℕ, eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
        (fun p => C (projCoord y w φ (truncCoord t j) p) * X p.1) x =
        map (ev : MvPolynomial (Fin N) Ω →+* Φ) (eval₂ (C.comp algA) (fun p => C (cA j p) * X p.1) x) := by
      intro j
      rw [map_coneMap, hevA, hcoord]
      rfl
    have ksub : map (sub : MvPolynomial (Fin N) Ω →+* MvPolynomial (Fin N) Ω)
        (eval₂ (C.comp algA) (fun p => C (cA ((i : ℕ) + 1) p) * X p.1) x) =
        eval₂ (C.comp algA) (fun p => C (cA i p) * X p.1) x := by
      rw [map_coneMap, hsubA]
      simp only [AlgHom.coe_toRingHom, hsubc]
    simp only [projIdeal, RingHom.mem_ker] at hx ⊢
    rw [key] at hx ⊢
    have h0 : eval₂ (C.comp algA) (fun p => C (cA ((i : ℕ) + 1) p) * X p.1) x = 0 :=
      map_injective _ hev (hx.trans (map_zero _).symm)
    rw [← ksub, h0, map_zero, map_zero]
  · have val : ∀ (j : ℕ) (v : MRing (bundleIdx ι M) F),
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t j)) v =
          ev (eval₂ algA (cA j) v) := by
      intro j v
      rw [← AlgHom.coe_toRingHom, eval₂_comp_left, hevA, hcoord]
      rfl
    have vsub : ∀ v : MRing (bundleIdx ι M) F,
        sub (eval₂ algA (cA ((i : ℕ) + 1)) v) = eval₂ algA (cA i) v := by
      intro v
      rw [← AlgHom.coe_toRingHom, eval₂_comp_left, hsubA]
      congr 1
      funext p
      exact hsubc p
    rw [val, val] at hxz
    have hx' : eval₂ algA (cA ((i : ℕ) + 1)) x = X i * eval₂ algA (cA ((i : ℕ) + 1)) z :=
      hev (by rw [hxz, map_mul]; simp [ev])
    rw [val, ← vsub, hx', map_mul]
    simp [sub]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
