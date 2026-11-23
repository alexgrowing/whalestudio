import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.FlatLocCompl

theorem mem_pow_smul_top_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (r : R) (k : ℕ) (z : S) :
    z ∈ ((Ideal.span {r}) ^ k • ⊤ : Submodule R S) ↔ z ∈ Ideal.span {(algebraMap R S r) ^ k} := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨e, -, rfl⟩
    exact ⟨e, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, Submodule.mem_top, by rw [Algebra.smul_def, map_pow]⟩

theorem mem_pow_smul_top_self_iff {R : Type} [CommRing R] (r : R) (k : ℕ) (z : R) :
    z ∈ ((Ideal.span {r}) ^ k • ⊤ : Submodule R R) ↔ z ∈ Ideal.span {r ^ k} := by
  rw [mem_pow_smul_top_iff]; rfl

theorem flat_of_levels {B E : Type} [CommRing B] [IsNoetherianRing B] [CommRing E] [Algebra B E] (p : B)
    (hc : IsAdicComplete (Ideal.span {algebraMap B E p}) E)
    (hinj : ∀ (b : B) (k : ℕ), algebraMap B E b ∈ Ideal.span {(algebraMap B E p) ^ k} →
      b ∈ Ideal.span {p ^ k})
    (hden : ∀ (y : E) (k : ℕ), ∃ b : B, algebraMap B E b - y ∈ Ideal.span {(algebraMap B E p) ^ k}) :
    Module.Flat B E := by
  set I : Ideal B := Ideal.span {p} with hI
  haveI : IsAdicComplete I E := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := E)]
    rwa [hI, Ideal.map_span, Set.image_singleton]
  let f : B →ₗ[B] E := Algebra.linearMap B E
  have hle : ∀ k, (I ^ k • ⊤ : Submodule B B) ≤ (I ^ k • ⊤ : Submodule B E).comap f := by
    intro k z hz
    rw [Submodule.mem_comap, mem_pow_smul_top_iff]
    rw [mem_pow_smul_top_self_iff, Ideal.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    exact Ideal.mem_span_singleton.2 ⟨algebraMap B E c, by simp [f, map_pow]⟩
  let fk : ∀ k : ℕ, AdicCompletion I B →ₗ[B] E ⧸ (I ^ k • ⊤ : Submodule B E) := fun k =>
    (Submodule.mapQ _ _ f (hle k)) ∘ₗ AdicCompletion.eval I B k
  have hfk : ∀ {m n : ℕ} (hmn : m ≤ n), Submodule.factorPow I E hmn ∘ₗ fk n = fk m := by
    intro m n hmn
    refine LinearMap.ext fun x => ?_
    simp only [fk, LinearMap.comp_apply, AdicCompletion.eval_apply]
    rw [← AdicCompletion.transitionMap_comp_eval_apply I B hmn x]
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [← hb]
    rfl
  let G : AdicCompletion I B →ₗ[B] E := IsAdicComplete.lift I fk hfk
  have hG : ∀ k x, Submodule.Quotient.mk (p := (I ^ k • ⊤ : Submodule B E)) (G x) = fk k x :=
    fun k x => IsAdicComplete.mk_lift I hfk k x
  have hbij : Function.Bijective G := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      ext k
      have h1 := hG k x
      rw [hx, Submodule.Quotient.mk_zero] at h1
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (x.val k)
      have h2 : fk k x = Submodule.Quotient.mk (f b) := by
        simp only [fk, LinearMap.comp_apply, AdicCompletion.eval_apply, ← hb]; rfl
      rw [h2, eq_comm, Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_iff] at h1
      rw [← hb, AdicCompletion.val_zero_apply, Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_self_iff]
      exact hinj b k h1
    · intro y
      choose b hb using fun k => hden y k
      have hcau : ∀ k, b k ≡ b (k + 1) [SMOD (I ^ k • ⊤ : Submodule B B)] := by
        intro k
        rw [SModEq.sub_mem, mem_pow_smul_top_self_iff]
        apply hinj
        have h3 : algebraMap B E (b k - b (k + 1)) =
            (algebraMap B E (b k) - y) - (algebraMap B E (b (k + 1)) - y) := by rw [map_sub]; ring
        rw [h3]
        refine Ideal.sub_mem _ (hb k) ?_
        refine Ideal.span_singleton_le_span_singleton.2 ?_ (hb (k + 1))
        exact pow_dvd_pow _ (Nat.le_succ k)
      refine ⟨AdicCompletion.mk I B (AdicCompletion.AdicCauchySequence.mk I B b hcau), ?_⟩
      rw [IsHausdorff.eq_iff_smodEq (I := I)]
      intro k
      rw [SModEq, hG]
      change Submodule.Quotient.mk (f (b k)) = Submodule.Quotient.mk y
      rw [← SModEq, SModEq.sub_mem, mem_pow_smul_top_iff]
      exact hb k
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective G hbij).symm

end GlobalTheory.FlatLocCompl

namespace GlobalTheory.FlatLocCompl

theorem flat_letA (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (E : Type) [CommRing E]
    [Algebra (LetA O n) E] (p : ℕ) (hπ : IsUnit (algebraMap (LetA O n) E letπ))
    (hc : IsAdicComplete (Ideal.span {(p : E)}) E)
    (hden : ∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) -
      algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k})
    (hsat : ∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) :
    Module.Flat (LetA O n) E := by
  let B := Localization.Away (letπ : LetA O n)
  let g : B →+* E := IsLocalization.Away.lift (S := B) (letπ : LetA O n) hπ
  letI : Algebra B E := g.toAlgebra
  have hg : ∀ a : LetA O n, algebraMap B E (algebraMap (LetA O n) B a) = algebraMap (LetA O n) E a :=
    fun a => IsLocalization.Away.lift_eq (S := B) (letπ : LetA O n) hπ a
  haveI : IsScalarTower (LetA O n) B E := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have hp : algebraMap B E (p : B) = (p : E) := map_natCast _ _
  haveI : Module.Flat B E := by
    refine flat_of_levels (p : B) (by rwa [hp]) ?_ ?_
    · intro b k hb
      rw [hp] at hb
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (letπ : LetA O n)) b
      have h1 : IsLocalization.mk' B a s * algebraMap (LetA O n) B s = algebraMap (LetA O n) B a :=
        IsLocalization.mk'_spec B a s
      have h2 : algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} := by
        rw [← hg, ← h1, map_mul]
        exact Ideal.mul_mem_right _ _ hb
      obtain ⟨c, rfl⟩ := hsat a k h2
      refine Ideal.mem_span_singleton.2 ⟨IsLocalization.mk' B c s, ?_⟩
      show IsLocalization.mk' B ((p : LetA O n) ^ k * c) s = (p : B) ^ k * IsLocalization.mk' B c s
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_pow, map_natCast]
    · intro y k
      obtain ⟨a, m, h⟩ := hden y k
      let s : Submonoid.powers (letπ : LetA O n) := ⟨letπ ^ m, m, rfl⟩
      refine ⟨IsLocalization.mk' B a s, ?_⟩
      rw [hp]
      have h1 : IsLocalization.mk' B a s * algebraMap (LetA O n) B (letπ ^ m) = algebraMap (LetA O n) B a :=
        IsLocalization.mk'_spec B a s
      have h2 : algebraMap B E (IsLocalization.mk' B a s) * algebraMap (LetA O n) E (letπ ^ m) =
          algebraMap (LetA O n) E a := by rw [← hg, ← hg, ← map_mul, h1]
      obtain ⟨v, hv⟩ := hπ.pow m
      rw [← map_pow] at hv
      have h3 : algebraMap B E (IsLocalization.mk' B a s) - y =
          -((y * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a) * ↑v⁻¹) := by
        rw [← h2, ← hv, neg_mul_eq_neg_mul, neg_sub, ← sub_mul, mul_assoc, Units.mul_inv, mul_one]
      rw [h3]
      exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ h)
  exact Module.Flat.trans (LetA O n) B E

end GlobalTheory.FlatLocCompl
