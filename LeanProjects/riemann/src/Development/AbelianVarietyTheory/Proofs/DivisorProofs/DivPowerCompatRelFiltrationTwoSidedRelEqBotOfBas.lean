import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section General

variable {A : Type} [Ring A]

theorem span_mul_mem {S : Set A} (h : ∀ s ∈ S, ∀ y, s * y ∈ Ideal.span S) {x : A} (hx : x ∈ Ideal.span S) (y : A) :
    x * y ∈ Ideal.span S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx y
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul r x _ ih => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ ih

theorem span_map_mem (f : A →+* A) {S : Set A} (h : ∀ s ∈ S, f s ∈ Ideal.span S) {x : A} (hx : x ∈ Ideal.span S) :
    f x ∈ Ideal.span S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul r x _ ih => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ ih

theorem sup_mul_mem {I K : Ideal A} (hI : ∀ x ∈ I, ∀ y, x * y ∈ I) (hK : ∀ x ∈ K, ∀ y, x * y ∈ K) {x : A}
    (hx : x ∈ I ⊔ K) (y : A) : x * y ∈ I ⊔ K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [add_mul]
  exact add_mem (Ideal.mem_sup_left (hI a ha y)) (Ideal.mem_sup_right (hK b hb y))

theorem sup_map_mem (f : A →+* A) {I K : Ideal A} (hI : ∀ x ∈ I, f x ∈ I) (hK : ∀ x ∈ K, f x ∈ K) {x : A}
    (hx : x ∈ I ⊔ K) : f x ∈ I ⊔ K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact add_mem (Ideal.mem_sup_left (hI a ha)) (Ideal.mem_sup_right (hK b hb))

end General

section Filt

variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J)

theorem fil_anti' {m n : ℕ} (h : m ≤ n) : fil δ n ≤ fil δ m :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, h.trans h2, h3⟩

theorem fil_mul_mem' {m n : ℕ} {a b : B} (ha : a ∈ fil δ m) (hb : b ∈ fil δ n) : a * b ∈ fil δ (m + n) := by
  have key : fil δ m * fil δ n ≤ fil δ (m + n) := by
    rw [fil, fil, Ideal.span_mul_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨x, ⟨l, hl, hs, rfl⟩, y, ⟨l', hl', hs', rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨l ++ l', fun p hp ↦ ?_, ?_, ?_⟩
    · rcases List.mem_append.1 hp with hp | hp
      exacts [hl p hp, hl' p hp]
    · simp only [List.map_append, List.sum_append]; omega
    · simp only [List.map_append, List.prod_append]
  exact key (Ideal.mul_mem_mul ha hb)

end Filt

section Main

variable (R : Type) [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

def relGen : Set (DR R B) :=
  {x | ∃ n : ℕ, ∃ a ∈ J, x = ι1 (D R B (δ.dpow (n + 1) a) - δ.dpow n a • D R B a)}

theorem rel_eq_span : rel R δ = Ideal.span (relGen R δ) := rfl

theorem rel_mul_mem {x : DR R B} (hx : x ∈ rel R δ) (y : DR R B) : x * y ∈ rel R δ := by
  rw [rel_eq_span] at hx ⊢
  refine span_mul_mem (fun s hs y ↦ ?_) hx y
  obtain ⟨n, a, ha, rfl⟩ := hs
  rw [ι_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, a, ha, rfl⟩)

theorem sgn_mem_rel {x : DR R B} (hx : x ∈ rel R δ) : sgn x ∈ rel R δ := by
  rw [rel_eq_span] at hx ⊢
  refine span_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun s hs ↦ ?_) hx
  obtain ⟨n, a, ha, rfl⟩ := hs
  change sgn (ι1 _) ∈ _
  rw [sgn_ι]
  exact neg_mem (Ideal.subset_span ⟨n, a, ha, rfl⟩)

theorem filSpan_mul_mem (n : ℕ) {x : DR R B} (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n))
    (y : DR R B) : x * y ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n) := by
  refine span_mul_mem (fun s hs y ↦ ?_) hx y
  obtain ⟨b, hb, rfl⟩ := hs
  rw [Algebra.commutes]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, hb, rfl⟩)

theorem filSpan_sgn_mem (n : ℕ) {x : DR R B} (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n)) :
    sgn x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n) := by
  refine span_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun s hs ↦ ?_) hx
  obtain ⟨b, hb, rfl⟩ := hs
  change sgn (algebraMap B _ b) ∈ _
  rw [AlgHom.commutes]
  exact Ideal.subset_span ⟨b, hb, rfl⟩

theorem filSpan_smul_mem (m n : ℕ) {b : B} (hb : b ∈ fil δ m) {x : DR R B}
    (hx : x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ n)) :
    b • x ∈ Ideal.span (algebraMap B (DR R B) '' fil δ (m + n)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [Algebra.smul_def, ← map_mul]
    exact Ideal.subset_span ⟨b * c, fil_mul_mem' δ hb hc, rfl⟩
  | zero => simp
  | add x z _ _ hx hz => rw [smul_add]; exact add_mem hx hz
  | smul r x _ ih =>
    rw [smul_eq_mul, Algebra.smul_def, ← mul_assoc, Algebra.commutes b r, mul_assoc, ← Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ ih

theorem rel_filDR_properties :
    (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧
    (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧
    filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧
    ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n) := by
  refine ⟨fun x hx y ↦ rel_mul_mem R δ hx y, fun x hx ↦ sgn_mem_rel R δ hx, fun n x hx y ↦ ?_, fun n x hx ↦ ?_,
    ?_, fun m n h ↦ ?_, fun m n b hb x hx ↦ ?_⟩
  · exact sup_mul_mem (fun x hx y ↦ filSpan_mul_mem R δ n hx y) (fun x hx y ↦ rel_mul_mem R δ hx y) hx y
  · exact sup_map_mem (sgn : DR R B →ₐ[B] DR R B).toRingHom (fun x hx ↦ filSpan_sgn_mem R δ n hx)
      (fun x hx ↦ sgn_mem_rel R δ hx) hx
  · refine (Ideal.eq_top_iff_one _).2 (Ideal.mem_sup_left (Ideal.subset_span ⟨1, ?_, map_one _⟩))
    rw [fil_zero_eq_top]; trivial
  · exact sup_le_sup_right (Ideal.span_mono (Set.image_mono (fil_anti' δ h))) _
  · obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine add_mem (Ideal.mem_sup_left (filSpan_smul_mem R δ m n hb ha)) (Ideal.mem_sup_right ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hc

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler in

theorem rel_eq_bot_of_map (I : Ideal R) (κ : DividedPowers I) (h : IsDPMorphism κ δ (algebraMap R B))
    (hJ : J ≤ I.map (algebraMap R B)) : rel R δ = ⊥ := by
  have hD := GlobalTheory.CrysConn.isDPDer_of_map h hJ (D R B)
  rw [rel, Ideal.span_eq_bot]
  rintro _ ⟨n, a, ha, rfl⟩
  rw [hD n a ha, sub_self, map_zero]

end Main

theorem rel_two_sided_and_bot :
    (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J),
      (∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) ∧ (∀ x ∈ rel R δ, sgn x ∈ rel R δ) ∧
      (∀ n, ∀ x ∈ filDR R δ n, ∀ y, x * y ∈ filDR R δ n) ∧ (∀ n, ∀ x ∈ filDR R δ n, sgn x ∈ filDR R δ n) ∧
      filDR R δ 0 = ⊤ ∧ (∀ m n, m ≤ n → filDR R δ n ≤ filDR R δ m) ∧
      ∀ m n, ∀ b ∈ fil δ m, ∀ x ∈ filDR R δ n, b • x ∈ filDR R δ (m + n)) ∧
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (I : Ideal R)
      (κ : DividedPowers I), IsDPMorphism κ δ (algebraMap R B) → J ≤ I.map (algebraMap R B) → rel R δ = ⊥ :=
  ⟨fun R _ _ _ _ _ δ ↦ rel_filDR_properties R δ, fun R _ _ _ _ _ δ I κ h hJ ↦ rel_eq_bot_of_map R δ I κ h hJ⟩

end GlobalTheory.PDForm
