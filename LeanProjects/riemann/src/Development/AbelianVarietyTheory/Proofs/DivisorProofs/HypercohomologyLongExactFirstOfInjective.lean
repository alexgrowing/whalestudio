import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainShortExactOfInjectiveTerms
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LesFirst

section
variable {R : Type} [CommRing R]

theorem ofHom_comp_comp {K L M I : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) {n : ℤ} (z : Cochain M I n) :
    (Cochain.ofHom φ).comp ((Cochain.ofHom ψ).comp z (zero_add n)) (zero_add n) =
      (Cochain.ofHom (φ ≫ ψ)).comp z (zero_add n) := by
  ext p q hpq; simp

theorem δ_ofHom_comp' {K L I : Cx R} (φ : K ⟶ L) {n m : ℤ} (z : Cochain L I n) :
    δ n m ((Cochain.ofHom φ).comp z (zero_add n)) = (Cochain.ofHom φ).comp (δ n m z) (zero_add m) := by
  by_cases h : n + 1 = m
  · rw [δ_comp _ _ (zero_add n) 1 m m h (zero_add 1) h]; simp
  · simp [δ_shape _ _ h]

theorem cpull_mk {K L I : Cx R} (φ : K ⟶ L) {n : ℤ} (z : Cocycle L I n) :
    cpull φ I n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom φ) z (zero_add n)) := rfl

theorem cpull_comp {K L M I : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull φ I n (cpull ψ I n x) = cpull (φ ≫ ψ) I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (ofHom_comp_comp φ ψ x.1))

theorem cpull_zero' {K L I : Cx R} (n : ℤ) (x : CohomologyClass L I n) :
    cpull (0 : K ⟶ L) I n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpull_mk, ← CohomologyClass.mk_zero]
  exact congrArg CohomologyClass.mk (Cocycle.ext (by simp [zcomp]))

variable {I : Cx R} (S : ShortComplex (Cx R))

def Snake {n : ℤ} (a : Cochain S.X₁ I n) (c : Cochain S.X₃ I (n + 1)) : Prop :=
  ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a ∧
    (Cochain.ofHom S.g).comp c (zero_add (n + 1)) = δ n (n + 1) b

theorem fg_zero {n : ℤ} (e : Cochain S.X₃ I n) :
    (Cochain.ofHom S.f).comp ((Cochain.ofHom S.g).comp e (zero_add n)) (zero_add n) = 0 := by
  rw [ofHom_comp_comp, S.zero]; simp

theorem snake_add {n : ℤ} {a a' : Cochain S.X₁ I n} {c c' : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (h' : Snake S a' c') : Snake S (a + a') (c + c') := by
  obtain ⟨b, hb, hc⟩ := h; obtain ⟨b', hb', hc'⟩ := h'
  exact ⟨b + b', by rw [Cochain.comp_add, hb, hb'], by rw [Cochain.comp_add, hc, hc', δ_add]⟩

theorem snake_sub {n : ℤ} {a a' : Cochain S.X₁ I n} {c c' : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (h' : Snake S a' c') : Snake S (a - a') (c - c') := by
  obtain ⟨b, hb, hc⟩ := h; obtain ⟨b', hb', hc'⟩ := h'
  exact ⟨b - b', by rw [Cochain.comp_sub, hb, hb'], by rw [Cochain.comp_sub, hc, hc', δ_sub]⟩

variable (hI : ∀ n, Injective (I.X n)) (hS : S.ShortExact)
include hI hS

theorem snake_exists {n : ℤ} (a : Cocycle S.X₁ I n) : ∃ c : Cocycle S.X₃ I (n + 1), Snake S a.1 c.1 := by
  have L := cochain_shortExact_of_injective R I hI S hS
  obtain ⟨b, hb⟩ := (L n).1 a.1
  have h1 : (Cochain.ofHom S.f).comp (δ n (n + 1) b) (zero_add (n + 1)) = 0 := by
    rw [← δ_ofHom_comp', hb]; exact a.δ_eq_zero (n + 1)
  obtain ⟨c, hc⟩ := (L (n + 1)).2.1 _ h1
  have h2 : δ (n + 1) (n + 1 + 1) c = 0 := by
    apply (L (n + 1 + 1)).2.2
    rw [← δ_ofHom_comp', hc, δ_δ]
  exact ⟨Cocycle.mk c (n + 1 + 1) rfl h2, b, hb, hc⟩

theorem snake_bdry {n m : ℤ} (hm : m + 1 = n) {a : Cochain S.X₁ I n} {c : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (β : Cochain S.X₁ I m) (hβ : δ m n β = a) :
    ∃ e : Cochain S.X₃ I n, δ n (n + 1) e = c := by
  have L := cochain_shortExact_of_injective R I hI S hS
  obtain ⟨b, hb, hc⟩ := h
  obtain ⟨β₂, hβ₂⟩ := (L m).1 β
  have h1 : (Cochain.ofHom S.f).comp (b - δ m n β₂) (zero_add n) = 0 := by
    rw [Cochain.comp_sub, ← δ_ofHom_comp', hβ₂, hβ, hb, sub_self]
  obtain ⟨e, he⟩ := (L n).2.1 _ h1
  refine ⟨e, ?_⟩
  rw [← sub_eq_zero]
  apply (L (n + 1)).2.2
  rw [Cochain.comp_sub, ← δ_ofHom_comp', he, hc, δ_sub, δ_δ, sub_zero, sub_self]

theorem snake_unique {n : ℤ} {a : Cochain S.X₁ I n} {c c' : Cocycle S.X₃ I (n + 1)}
    (h : Snake S a c.1) (h' : Snake S a c'.1) :
    CohomologyClass.mk c = CohomologyClass.mk c' := by
  have h0 := snake_sub S h h'
  rw [sub_self] at h0
  obtain ⟨e, he⟩ := snake_bdry S hI hS (sub_add_cancel n 1) h0 0 (by simp)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ n rfl]
  exact ⟨e, by rw [he]; rfl⟩

def conn0 (n : ℤ) (a : Cocycle S.X₁ I n) : CohomologyClass S.X₃ I (n + 1) :=
  CohomologyClass.mk (Classical.choose (snake_exists S hI hS a))

theorem etaleSnakeConnectingOnCocycles_eq {n : ℤ} (a : Cocycle S.X₁ I n) (c : Cocycle S.X₃ I (n + 1)) (h : Snake S a.1 c.1) :
    conn0 S hI hS n a = CohomologyClass.mk c :=
  snake_unique S hI hS (Classical.choose_spec (snake_exists S hI hS a)) h

def conn (n : ℤ) : CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1) :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (conn0 S hI hS n) (fun a a' => by
      obtain ⟨c, hc⟩ := snake_exists S hI hS a
      obtain ⟨c', hc'⟩ := snake_exists S hI hS a'
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c hc, etaleSnakeConnectingOnCocycles_eq S hI hS a' c' hc',
        etaleSnakeConnectingOnCocycles_eq S hI hS (a + a') (c + c') (snake_add S hc hc'), CohomologyClass.mk_add]))
    (by
      intro a ha
      rw [mem_coboundaries_iff a (n - 1) (sub_add_cancel n 1)] at ha
      obtain ⟨β, hβ⟩ := ha
      obtain ⟨c, hc⟩ := snake_exists S hI hS a
      obtain ⟨e, he⟩ := snake_bdry S hI hS (sub_add_cancel n 1) hc β hβ
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, etaleSnakeConnectingOnCocycles_eq S hI hS a c hc,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]
      exact ⟨e, he⟩)

end

end GlobalTheory.EtC.LesFirst

namespace GlobalTheory.EtC

open LesFirst in

theorem longExact_first_of_injective :
    ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x) := by
  intro R _ I hI
  refine ⟨fun S hS n => conn S hI hS n, fun S hS n => ⟨?_, ?_, ?_⟩, ?_⟩
  · have L := cochain_shortExact_of_injective R I hI S hS
    intro y
    constructor
    · intro hy
      obtain ⟨y, rfl⟩ := y.mk_surjective
      rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (sub_add_cancel n 1)] at hy
      obtain ⟨β, hβ⟩ := hy
      obtain ⟨β₂, hβ₂⟩ := (L (n - 1)).1 β
      have h1 : (Cochain.ofHom S.f).comp (y.1 - δ (n - 1) n β₂) (zero_add n) = 0 := by
        rw [Cochain.comp_sub, ← δ_ofHom_comp', hβ₂, hβ]; exact sub_self _
      obtain ⟨c, hc⟩ := (L n).2.1 _ h1
      have h2 : δ n (n + 1) c = 0 := by
        apply (L (n + 1)).2.2
        rw [← δ_ofHom_comp', hc, δ_sub, δ_δ, y.δ_eq_zero, sub_zero]
      refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl h2), ?_⟩
      rw [cpull_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (sub_add_cancel n 1)]
      refine ⟨-β₂, ?_⟩
      rw [δ_neg]
      change -(δ (n - 1) n β₂) = (Cochain.ofHom S.g).comp c (zero_add n) - y.1
      rw [hc]; abel
    · rintro ⟨x, rfl⟩
      rw [cpull_comp, S.zero, cpull_zero']
  · intro y
    constructor
    · intro hy
      obtain ⟨a, rfl⟩ := y.mk_surjective
      obtain ⟨c, b, hb, hc⟩ := snake_exists S hI hS a
      change conn0 S hI hS n a = 0 at hy
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c ⟨b, hb, hc⟩, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ n rfl] at hy
      obtain ⟨e, he⟩ := hy
      have h : δ n (n + 1) (b - (Cochain.ofHom S.g).comp e (zero_add n)) = 0 := by
        rw [δ_sub, δ_ofHom_comp', he, ← hc, sub_self]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl h), ?_⟩
      rw [cpull_mk]
      refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
      change (Cochain.ofHom S.f).comp (b - (Cochain.ofHom S.g).comp e (zero_add n)) (zero_add n) = a.1
      rw [Cochain.comp_sub, fg_zero, sub_zero, hb]
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := x.mk_surjective
      change conn0 S hI hS n _ = 0
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS _ 0 ⟨b.1, rfl, by simp⟩, CohomologyClass.mk_zero]
  · intro z
    constructor
    · intro hz
      obtain ⟨c, rfl⟩ := z.mk_surjective
      rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨β, hβ⟩ := hz
      have h : δ n (n + 1) ((Cochain.ofHom S.f).comp β (zero_add n)) = 0 := by
        rw [δ_ofHom_comp', hβ]; exact fg_zero S c.1
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl h), ?_⟩
      exact etaleSnakeConnectingOnCocycles_eq S hI hS _ c ⟨β, rfl, hβ.symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := x.mk_surjective
      obtain ⟨c, hs⟩ := snake_exists S hI hS a
      change cpull S.g I (n + 1) (conn0 S hI hS n a) = 0
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c hs, cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]
      obtain ⟨b, hb, hc⟩ := hs
      exact ⟨b, hc.symm⟩
  · intro S S' hS hS' φ n x
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨c, b, hb, hc⟩ := snake_exists S' hI hS' a
    change cpull φ.τ₃ I (n + 1) (conn0 S' hI hS' n a) = conn0 S hI hS n _
    rw [etaleSnakeConnectingOnCocycles_eq S' hI hS' a c ⟨b, hb, hc⟩, cpull_mk,
      etaleSnakeConnectingOnCocycles_eq S hI hS _ _ ⟨(Cochain.ofHom φ.τ₂).comp b (zero_add n), ?_, ?_⟩]
    · change _ = (Cochain.ofHom φ.τ₁).comp a.1 (zero_add n)
      rw [ofHom_comp_comp, ← φ.comm₁₂, ← ofHom_comp_comp, hb]
    · change (Cochain.ofHom S.g).comp ((Cochain.ofHom φ.τ₃).comp c.1 (zero_add (n + 1))) (zero_add (n + 1)) = _
      rw [ofHom_comp_comp, ← φ.comm₂₃, ← ofHom_comp_comp, hc, δ_ofHom_comp']

end GlobalTheory.EtC
