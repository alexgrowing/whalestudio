import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain

set_option autoImplicit false

noncomputable section

open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise ChangeOfRings

namespace GlobalTheory.RingChain.FrobLin

variable {A : Type} [CommRing A]

variable (A) in

def Univ (p q : ℕ) {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (σ : M →+ N) : Prop :=
  (∀ y : N, (p : A) • y = 0) ∧ (∀ (a : A) (x : M), σ (a • x) = a ^ q • σ x) ∧ Submodule.span A (Set.range σ) = ⊤ ∧
    ∀ (P : Type) [AddCommGroup P] [Module A P] (τ : M →+ P), (∀ y : P, (p : A) • y = 0) →
      (∀ (a : A) (x : M), τ (a • x) = a ^ q • τ x) → ∃ g : N →ₗ[A] P, ∀ x, g (σ x) = τ x

variable {p q : ℕ} {M N N' : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']

theorem ind (f : A →+* A ⧸ Ideal.span {(p : A)}) (Q : (ModuleCat.extendScalars f).obj (ModuleCat.of A M) → Prop)
    (h0 : Q 0) (ha : ∀ s t, Q s → Q t → Q (s + t))
    (ht : ∀ (a : A) (x : M), Q ((Ideal.Quotient.mk _ a : A ⧸ Ideal.span {(p : A)}) ⊗ₜ[A, f] x)) (t) : Q t := by
  induction t using TensorProduct.induction_on with
  | zero => exact h0
  | add s t hs ht => exact ha s t hs ht
  | tmul b x =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : A)}) b
    exact ht a x

theorem tmul_smul (f : A →+* A ⧸ Ideal.span {(p : A)}) (hf : ∀ a, f a = Ideal.Quotient.mk _ (a ^ q)) (a b : A) (x : M) :
    ((Ideal.Quotient.mk _ b : A ⧸ Ideal.span {(p : A)}) ⊗ₜ[A, f] (a • x) :
      (ModuleCat.extendScalars f).obj (ModuleCat.of A M)) =
      (Ideal.Quotient.mk _ (a ^ q * b) : A ⧸ Ideal.span {(p : A)}) ⊗ₜ[A, f] x := by
  let X : ModuleCat A := (ModuleCat.restrictScalars f).obj (ModuleCat.of _ (A ⧸ Ideal.span {(p : A)}))
  let k : A → X := fun r => (Ideal.Quotient.mk _ r : A ⧸ Ideal.span {(p : A)})
  have hs : ∀ r s : A, r • k s = k (r ^ q * s) := fun r s => by
    change f r * Ideal.Quotient.mk _ s = Ideal.Quotient.mk _ _
    rw [hf, map_mul]
  change k b ⊗ₜ[A] (a • x) = k _ ⊗ₜ[A] x
  rw [← hs, TensorProduct.smul_tmul]

theorem lift (f : A →+* A ⧸ Ideal.span {(p : A)}) (hf : ∀ a, f a = Ideal.Quotient.mk _ (a ^ q)) (τ : M →+ N)
    (hp : ∀ y : N, (p : A) • y = 0) (hτ : ∀ (a : A) (x : M), τ (a • x) = a ^ q • τ x) :
    ∃ u : (ModuleCat.extendScalars f).obj (ModuleCat.of A M) →+ N,
      ∀ (a : A) (x : M), u ((Ideal.Quotient.mk _ a : A ⧸ Ideal.span {(p : A)}) ⊗ₜ[A, f] x) = a • τ x := by
  let X : ModuleCat A := (ModuleCat.restrictScalars f).obj (ModuleCat.of _ (A ⧸ Ideal.span {(p : A)}))
  let k : A → X := fun r => (Ideal.Quotient.mk _ r : A ⧸ Ideal.span {(p : A)})
  have hs : ∀ r s : A, r • k s = k (r ^ q * s) := fun r s => by
    change f r * Ideal.Quotient.mk _ s = Ideal.Quotient.mk _ _
    rw [hf, map_mul]
  let v : (A ⧸ Ideal.span {(p : A)}) →ₗ[A] (M →+ N) :=
    Submodule.liftQ (Ideal.span {(p : A)}) (LinearMap.toSpanSingleton A (M →+ N) τ) (by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact AddMonoidHom.ext fun x => hp _)
  let v' : X →+ (M →+ N) := v.toAddMonoidHom
  have hv : ∀ a x, v' (k a) x = a • τ x := fun _ _ => rfl
  let u : X ⊗[A] M →+ N := TensorProduct.liftAddHom v' fun r b x => by
    obtain ⟨s, rfl⟩ : ∃ s, k s = b := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : A)}) b
    rw [hs, hv, hv, hτ, mul_comm, mul_smul]
  exact ⟨u, fun a x => hv a x⟩

theorem iff_univ (f : A →+* A ⧸ Ideal.span {(p : A)}) (hf : ∀ a, f a = Ideal.Quotient.mk _ (a ^ q)) (σ : M →+ N) :
    IsFrobLin A p q σ ↔ Univ A p q σ := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := h f hf
    refine ⟨fun y => ?_, fun a x => ?_, ?_, fun P _ _ τ hp hτ => ?_⟩
    · obtain ⟨t, rfl⟩ := e.surjective y
      refine ind f (fun t => (p : A) • e t = 0) (by simp) (fun s t hs ht => by rw [map_add, smul_add, hs, ht, add_zero])
        (fun a x => ?_) t
      rw [he, ← mul_smul, ← he, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))]
      exact (congrArg e (TensorProduct.zero_tmul _ _)).trans (map_zero e)
    · have := (he 1 (a • x)).symm.trans ((congrArg e (tmul_smul f hf a 1 x)).trans (he _ x))
      rwa [mul_one, one_smul] at this
    · refine eq_top_iff.2 fun y _ => ?_
      obtain ⟨t, rfl⟩ := e.surjective y
      refine ind f (fun t => e t ∈ Submodule.span A (Set.range σ)) (by simp)
        (fun s t hs ht => by rw [map_add]; exact add_mem hs ht) (fun a x => ?_) t
      rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    · obtain ⟨u, hu⟩ := lift f hf τ hp hτ
      have key : ∀ a x, u (e.symm (a • σ x)) = a • τ x := fun a x => (congrArg u (e.symm_apply_eq.2 (he a x).symm)).trans (hu a x)
      refine ⟨{ toFun := fun y => u (e.symm y), map_add' := fun y z => by rw [map_add, map_add], map_smul' := fun a y => ?_ },
        fun x => ?_⟩
      · obtain ⟨t, rfl⟩ := e.surjective y
        refine ind f (fun t => u (e.symm (a • e t)) = a • u (e.symm (e t))) (by simp)
          (fun s t hs ht => by rw [map_add, smul_add, map_add, map_add, hs, ht, map_add, map_add, smul_add]) (fun b x => ?_) t
        rw [he, ← mul_smul, key, key, mul_smul]
      · simpa using key 1 x
  · rintro ⟨hp, hσ, hsp, hU⟩ f' hf'
    obtain rfl : f' = f := RingHom.ext fun a => (hf' a).trans (hf a).symm
    obtain ⟨u, hu⟩ := lift f' hf σ hp hσ
    let T : Type := (ModuleCat.extendScalars f').obj (ModuleCat.of A M)
    letI : Module A T := Module.compHom T (Ideal.Quotient.mk (Ideal.span {(p : A)}))
    let k : A → M → T := fun a x => (Ideal.Quotient.mk _ a : A ⧸ Ideal.span {(p : A)}) ⊗ₜ[A, f'] x
    have hk : ∀ a b x, a • k b x = k (a * b) x := fun a b x => rfl
    let τ : M →+ T := AddMonoidHom.mk' (k 1) fun x y => TensorProduct.tmul_add _ _ _
    obtain ⟨g, hg⟩ := hU T τ (fun y => by
      change Ideal.Quotient.mk (Ideal.span {(p : A)}) (p : A) • y = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_smul])
      (fun a x => (tmul_smul f' hf a 1 x).trans (hk _ _ _).symm)
    have hgu : ∀ t, g (u t) = t := fun t => by
      refine ind f' (fun t => g (u t) = t) (by rw [map_zero, map_zero])
        (fun s t hs ht => by rw [map_add, map_add, hs, ht]) (fun a x => ?_) t
      rw [hu, map_smul, hg]
      exact (hk a 1 x).trans (by rw [mul_one])
    refine ⟨AddEquiv.ofBijective u ⟨fun s t h => by rw [← hgu s, h, hgu], fun y => ?_⟩, hu⟩
    have hy : y ∈ Submodule.span A (Set.range σ) := hsp ▸ Submodule.mem_top
    have hsm : ∀ (a : A) (t : T), u (a • t) = a • u t := fun a t => by
      refine ind f' (fun t : T => u (a • t) = a • u t) ?_ (fun s t hs ht => ?_) (fun b x => ?_) t
      · have : a • (0 : T) = 0 := smul_zero a
        exact (congrArg u this).trans (by rw [map_zero, smul_zero])
      · have : a • (s + t : T) = a • (s : T) + a • (t : T) := smul_add a (s : T) t
        refine (congrArg u this).trans ?_
        rw [map_add, map_add, smul_add, hs, ht]
      · exact (hu (a * b) x).trans (by rw [hu, mul_smul])
    induction hy using Submodule.span_induction with
    | mem y h => obtain ⟨x, rfl⟩ := h; exact ⟨k 1 x, (hu 1 x).trans (one_smul _ _)⟩
    | zero => exact ⟨0, map_zero u⟩
    | add y z _ _ hy hz => obtain ⟨s, rfl⟩ := hy; obtain ⟨t, rfl⟩ := hz; exact ⟨s + t, map_add u _ _⟩
    | smul a y _ hy => obtain ⟨s, rfl⟩ := hy; exact ⟨_, hsm a s⟩

variable (A) in

theorem exists_frob (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ∃ f : A →+* A ⧸ Ideal.span {(p : A)}, ∀ a, f a = Ideal.Quotient.mk _ (a ^ p ^ k) := by
  have h0 : ((p : ℕ) : A ⧸ Ideal.span {(p : A)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rcases subsingleton_or_nontrivial (A ⧸ Ideal.span {(p : A)}) with h | h
  · exact ⟨Ideal.Quotient.mk _, fun _ => Subsingleton.elim _ _⟩
  · haveI : CharP (A ⧸ Ideal.span {(p : A)}) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 h0
    exact ⟨(iterateFrobenius _ p k).comp (Ideal.Quotient.mk _), fun a => by
      rw [RingHom.comp_apply, iterateFrobenius_def, map_pow]⟩

theorem iff_univ' [Fact p.Prime] (k : ℕ) (σ : M →+ N) : IsFrobLin A p (p ^ k) σ ↔ Univ A p (p ^ k) σ :=
  (exists_frob A p k).elim fun f hf => iff_univ f hf σ

theorem Univ.ext {σ : M →+ N} (h : Univ A p q σ) {g g' : N →ₗ[A] N'} (e : ∀ x, g (σ x) = g' (σ x)) : g = g' :=
  LinearMap.ext_on_range h.2.2.1 e

theorem Univ.unique {σ : M →+ N} {ψ : M →+ N'} (h : Univ A p q σ) (h' : Univ A p q ψ) :
    ∃ e : N ≃ₗ[A] N', ∀ x, e (σ x) = ψ x := by
  obtain ⟨g, hg⟩ := h.2.2.2 N' ψ h'.1 h'.2.1
  obtain ⟨g', hg'⟩ := h'.2.2.2 N σ h.1 h.2.1
  exact ⟨LinearEquiv.ofLinear g g' (h'.ext fun x => by simp [hg, hg']) (h.ext fun x => by simp [hg, hg']), hg⟩

theorem comp [Fact p.Prime] (k k' : ℕ) {σ : M →+ N} {τ : N →+ N'} (h : Univ A p (p ^ k) σ) (h' : Univ A p (p ^ k') τ) :
    Univ A p (p ^ (k + k')) (τ.comp σ) := by
  refine ⟨h'.1, fun a x => ?_, eq_top_iff.2 ?_, fun P _ _ ρ hp hρ => ?_⟩
  · rw [AddMonoidHom.comp_apply, h.2.1, h'.2.1, ← pow_mul, ← pow_add, AddMonoidHom.comp_apply]
  · rw [← h'.2.2.1, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ Submodule.span A (Set.range σ) := h.2.2.1 ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y h => obtain ⟨x, rfl⟩ := h; exact Submodule.subset_span ⟨x, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy => rw [h'.2.1]; exact Submodule.smul_mem _ _ hy
  · obtain ⟨f, hf⟩ := exists_frob A p k'
    have tors : Module.IsTorsionBySet A P (Ideal.span {(p : A)}) := by
      rw [Module.isTorsionBySet_span_singleton_iff]
      exact fun y => hp y
    obtain ⟨g, hg, hg'⟩ : ∃ g : N →+ P, (∀ (a : A) y, g (a • y) = a ^ p ^ k' • g y) ∧ ∀ x, g (σ x) = ρ x := by
      letI mB : Module (A ⧸ Ideal.span {(p : A)}) P := tors.module
      have hm : ∀ (a : A) (y : P), f a • y = a ^ p ^ k' • y := fun a y => by rw [hf]; rfl
      have h1 : ∀ y : P, f p • y = 0 := fun y => (hm p y).trans (by
        rw [← Nat.sub_add_cancel (Nat.one_le_pow k' p (Fact.out : p.Prime).pos), pow_succ, mul_smul, hp, smul_zero])
      have h2 : ∀ (a : A) x, ρ (a • x) = f (a ^ p ^ k) • ρ x := fun a x => by
        rw [hρ, hm, ← pow_mul, ← pow_add]
      let mF : Module A P := Module.compHom P f
      obtain ⟨g, hg⟩ := @h.2.2.2 P _ mF ρ h1 h2
      exact ⟨@LinearMap.toAddMonoidHom _ _ _ _ _ _ _ _ _ mF _ g,
        fun a y => (@LinearMap.map_smul _ _ _ _ _ _ _ mF g a y).trans (hm a _), hg⟩
    obtain ⟨g₂, hg₂⟩ := h'.2.2.2 P g hp hg
    exact ⟨g₂, fun x => (hg₂ _).trans (hg' x)⟩

theorem Univ.comp_equiv (e : M ≃ₗ[A] N) {τ : N →+ N'} (h : Univ A p q τ) :
    Univ A p q (τ.comp e.toLinearMap.toAddMonoidHom) := by
  refine ⟨h.1, fun a x => ?_, ?_, fun P _ _ ρ hp hρ => ?_⟩
  · change τ (e (a • x)) = a ^ q • τ (e x)
    rw [map_smul, h.2.1]
  · rw [← h.2.2.1]
    exact congrArg _ (e.surjective.range_comp τ)
  · obtain ⟨g, hg⟩ := h.2.2.2 P (ρ.comp e.symm.toLinearMap.toAddMonoidHom) hp fun a y => by
      change ρ (e.symm (a • y)) = a ^ q • ρ (e.symm y)
      rw [map_smul, hρ]
    exact ⟨g, fun x => (hg (e x)).trans (congrArg ρ (e.symm_apply_apply x))⟩

theorem main : ∀ (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime] (M N N' : Type) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N'], (∀ (k : ℕ) (σ : M →+ N), IsFrobLin A p (p ^ k) σ → Submodule.span A (Set.range σ) = ⊤ ∧ (∀ (a : A) (x : M), σ (a • x) = a ^ p ^ k • σ x) ∧ ∀ y : N, (p : A) • y = 0) ∧ (∀ (k : ℕ) (σ : M →+ N) (ψ : M →+ N'), IsFrobLin A p (p ^ k) σ → IsFrobLin A p (p ^ k) ψ → ∃ e : N ≃ₗ[A] N', ∀ x, e (σ x) = ψ x) ∧ (∀ (k k' : ℕ) (σ : M →+ N) (τ : N →+ N'), IsFrobLin A p (p ^ k) σ → IsFrobLin A p (p ^ k') τ → IsFrobLin A p (p ^ (k + k')) (τ.comp σ)) ∧ (∀ (q : ℕ) (e : M ≃ₗ[A] N) (τ : N →+ N'), IsFrobLin A p q τ → IsFrobLin A p q (τ.comp e.toLinearMap.toAddMonoidHom)) ∧ ∀ (q : ℕ) (σ : M →+ N) (e : N ≃ₗ[A] N'), IsFrobLin A p q σ → IsFrobLin A p q (e.toLinearMap.toAddMonoidHom.comp σ) := by
  intro A _ p _ M N N' _ _ _ _ _ _
  refine ⟨fun k σ h => ?_, fun k σ ψ h h' => ((iff_univ' k σ).1 h).unique ((iff_univ' k ψ).1 h'),
    fun k k' σ τ h h' => (iff_univ' _ _).2 (comp k k' ((iff_univ' k σ).1 h) ((iff_univ' k' τ).1 h')),
    fun q e τ h f hf => (iff_univ f hf _).2 (((iff_univ f hf _).1 h).comp_equiv e) f hf, fun q σ e h f hf => ?_⟩
  · have := (iff_univ' k σ).1 h
    exact ⟨this.2.2.1, this.2.1, this.1⟩
  · obtain ⟨e₀, he₀⟩ := h f hf
    exact ⟨e₀.trans e.toAddEquiv, fun a x => (congrArg e (he₀ a x)).trans (map_smul e a _)⟩

end GlobalTheory.RingChain.FrobLin

end
