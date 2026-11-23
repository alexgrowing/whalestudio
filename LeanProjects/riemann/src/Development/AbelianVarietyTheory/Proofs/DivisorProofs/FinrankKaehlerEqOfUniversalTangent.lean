import Mathlib

open TrivSqZeroExt

namespace GlobalTheory

theorem finrank_kaehler_eq_of_universal_tangent :
    ∀ (R A k : Type) [CommRing R] [CommRing A] [Algebra R A] [Field k] (n d : ℕ)
    [Module.Free A (Ω[A⁄R])] [Module.Finite A (Ω[A⁄R])], Module.finrank A (Ω[A⁄R]) = n →
    ∀ (φ : A →+* k) (ψ : A →+* TrivSqZeroExt k (Fin d → k)),
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ →
    ψ.comp (algebraMap R A) = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (algebraMap R A)) →
    (∀ v : A →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
      v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) →
      ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ) → d = n := by
  intro R A k _ _ _ _ n d _ _ hn φ ψ hfst hR huniv
  classical
  haveI : Nontrivial A := φ.domain_nontrivial
  letI : Algebra A k := φ.toAlgebra
  letI : Algebra R k := (φ.comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A k := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hψf : ∀ a, (ψ a).fst = φ a := fun a => by
    simpa using RingHom.congr_fun hfst a
  have hψR : ∀ r, (ψ (algebraMap R A r)).snd = 0 := fun r => by
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hR r)
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using this
  have hsA : ∀ (a : A) (x : k), a • x = φ a * x := fun a x => rfl
  have hsR : ∀ (r : R) (x : k), r • x = φ (algebraMap R A r) * x := fun r x => rfl

  let E : Derivation R A (Fin d → k) := Derivation.mk'
    { toFun := fun a => (ψ a).snd
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        funext i
        simp [Algebra.smul_def, hψR, hψf, hsR, RingHom.algebraMap_toAlgebra] }
    (fun a b => by
      funext i
      simp [hψf, hsA, mul_comm])
  have hE : ∀ a, E a = (ψ a).snd := fun a => rfl
  let El : Ω[A⁄R] →ₗ[A] (Fin d → k) := E.liftKaehlerDifferential
  have hEl : ∀ a, El (KaehlerDifferential.D R A a) = (ψ a).snd := fun a => by
    simp [El, hE]
  let b : Module.Basis (Fin n) A (Ω[A⁄R]) := Module.finBasisOfFinrankEq A _ hn
  have hcA : ∀ (c : (Fin d → k) →ₗ[k] k) (a : A) (x : Fin d → k), c (a • x) = a • c x :=
    fun c a x => by
      have : a • x = φ a • x := rfl
      rw [this, c.map_smul]; rfl
  let cA : ((Fin d → k) →ₗ[k] k) → ((Fin d → k) →ₗ[A] k) := fun c =>
    { toFun := c, map_add' := c.map_add, map_smul' := hcA c }
  have hcA' : ∀ c x, cA c x = c x := fun _ _ => rfl
  have hc1 : ∀ c : (Fin d → k) →ₗ[k] k,
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp ((TrivSqZeroExt.map c).toRingHom.comp ψ) = φ :=
    fun c => by
      ext a
      simp [hψf]
  have hc2 : ∀ c : (Fin d → k) →ₗ[k] k,
      ((TrivSqZeroExt.map c).toRingHom.comp ψ).comp (algebraMap R A) =
        (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) := fun c => by
    ext r
    · simp [hψf, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [hψR, TrivSqZeroExt.algebraMap_eq_inl]
  let L : ((Fin d → k) →ₗ[k] k) →ₗ[k] (Fin n → k) :=
    LinearMap.pi (fun i => LinearMap.applyₗ (R := k) (El (b i)))
  have hL : ∀ c i, L c i = c (El (b i)) := fun _ _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : (cA c).comp El = 0 := b.ext fun i => by
      simpa [hL, hcA'] using congrFun hc i
    have h0' : ∀ a, c (ψ a).snd = 0 := fun a => by
      have := LinearMap.congr_fun h0 (KaehlerDifferential.D R A a)
      simpa [hEl, hcA'] using this
    have heq : (TrivSqZeroExt.map c).toRingHom.comp ψ = (TrivSqZeroExt.map 0).toRingHom.comp ψ := by
      ext a
      · simp
      · simp [h0']
    exact (huniv _ (hc1 c) (hc2 c)).unique rfl heq
  have hsurj : Function.Surjective L := by
    intro f
    let g : Ω[A⁄R] →ₗ[A] k := b.constr A f
    let Df : Derivation R A k := g.compDer (KaehlerDifferential.D R A)
    let v : A →+* DualNumber k :=
      { toFun := fun a => TrivSqZeroExt.inl (φ a) + TrivSqZeroExt.inr (Df a)
        map_one' := by ext <;> simp
        map_mul' := fun a a' => by ext <;> simp [hsA, mul_comm, add_comm]
        map_zero' := by ext <;> simp
        map_add' := fun a a' => by ext <;> simp [add_add_add_comm] }
    have hv1 : (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ := by
      ext a
      simp [v]
    have hv2 : v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) := by
      ext r
      · simp [v, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [v, TrivSqZeroExt.algebraMap_eq_inl]
    obtain ⟨c, hc, -⟩ := huniv v hv1 hv2
    have key : ∀ a, Df a = c (ψ a).snd := fun a => by
      have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hc a)
      simpa [v] using this
    have hg : (cA c).comp El = g := Derivation.liftKaehlerDifferential_unique _ _
      (Derivation.ext fun a => by simp [hEl, hcA', ← key, Df])
    refine ⟨c, funext fun i => ?_⟩
    rw [hL, ← hcA' c, ← LinearMap.comp_apply, hg]
    simp [g]
  have e := (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_linearMap, Module.finrank_fin_fun, Module.finrank_fin_fun, Module.finrank_self] at e
  simpa using e

end GlobalTheory
