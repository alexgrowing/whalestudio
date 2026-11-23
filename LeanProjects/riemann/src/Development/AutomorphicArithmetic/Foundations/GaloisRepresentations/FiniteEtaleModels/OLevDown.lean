import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.MOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Generic

variable {A B M : Type} [CommRing A] [Ring B] [Algebra A B] [AddCommGroup M] [Module B M]

private def idealSub (B M : Type) {A : Type} [CommRing A] [Ring B] [Algebra A B] [AddCommGroup M] [Module B M]
    (𝔞 : Ideal A) : Submodule B M :=
  Submodule.span B {z | ∃ c ∈ 𝔞, ∃ z' : M, z = algebraMap A B c • z'}

private theorem smul_mem_idealSub {𝔞 : Ideal A} {c : A} (hc : c ∈ 𝔞) (z : M) :
    algebraMap A B c • z ∈ idealSub B M 𝔞 :=
  Submodule.subset_span ⟨c, hc, z, rfl⟩

private theorem functional_mem (hb : Function.Surjective (algebraMap A B)) (f : M →ₗ[B] B) (𝔞 : Ideal A) {w : M}
    (hw : w ∈ idealSub B M 𝔞) : ∃ d ∈ 𝔞, f w = algebraMap A B d := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    obtain ⟨e, he⟩ := hb (f z')
    exact ⟨c * e, 𝔞.mul_mem_right e hc, by rw [map_smul, ← he, smul_eq_mul, map_mul]⟩
  | zero => exact ⟨0, 𝔞.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, h₁, e₁⟩ := hx
    obtain ⟨d₂, h₂, e₂⟩ := hy
    exact ⟨d₁ + d₂, 𝔞.add_mem h₁ h₂, by rw [map_add, e₁, e₂, map_add]⟩
  | smul b x _ hx =>
    obtain ⟨d, hd, e⟩ := hx
    obtain ⟨a, rfl⟩ := hb b
    exact ⟨a * d, 𝔞.mul_mem_left a hd, by rw [map_smul, e, smul_eq_mul, map_mul]⟩

private theorem mem_of_mul_mem [IsDedekindDomain A] [Module.Projective B M]
    (hb : Function.Bijective (algebraMap A B)) (I J : Ideal A) (hI : I ≠ ⊥) (z : M)
    (h : ∀ c ∈ I, algebraMap A B c • z ∈ idealSub B M (I * J)) : z ∈ idealSub B M J := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective B M›
  have key : ∀ m : M, ∃ d ∈ J, s z m = algebraMap A B d := by
    intro m
    let f : M →ₗ[B] B := Finsupp.lapply m ∘ₗ s
    obtain ⟨e, he⟩ := hb.2 (f z)
    refine ⟨e, ?_, he.symm⟩
    have hle : I * Ideal.span {e} ≤ I * J := by
      rw [Ideal.mul_le]
      intro r hr t ht
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ht
      obtain ⟨d, hd, hde⟩ := functional_mem hb.2 f (I * J) (h (r * u) (I.mul_mem_right u hr))
      have hrd : algebraMap A B (r * u * e) = algebraMap A B d := by
        rw [← hde, map_smul, smul_eq_mul, ← he, ← map_mul]
      rw [← _root_.mul_assoc, hb.1 hrd]
      exact hd
    have hdvd : I * J ∣ I * Ideal.span {e} := Ideal.dvd_iff_le.mpr hle
    rw [mul_dvd_mul_iff_left hI] at hdvd
    exact (Ideal.dvd_iff_le.mp hdvd) (Ideal.mem_span_singleton_self e)
  have hz : z = Finsupp.linearCombination B id (s z) := (LinearMap.congr_fun hs z).symm
  rw [hz, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun m _ => ?_)
  obtain ⟨d, hd, e⟩ := key m
  rw [e]
  exact smul_mem_idealSub hd m

private theorem exists_sub_mem {ε : A} {𝔟 : Ideal A} {z : M}
    (hz : z ∈ idealSub B M (Ideal.span {ε} ⊔ 𝔟)) :
    ∃ y, z - algebraMap A B ε • y ∈ idealSub B M 𝔟 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hc
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hu
    refine ⟨algebraMap A B a • z', ?_⟩
    rw [smul_smul, ← map_mul, mul_comm ε a, map_add, add_smul, add_sub_cancel_left]
    exact smul_mem_idealSub hv z'
  | zero =>
    refine ⟨0, ?_⟩
    rw [smul_zero, sub_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨y₁, h₁⟩ := hx
    obtain ⟨y₂, h₂⟩ := hy
    refine ⟨y₁ + y₂, ?_⟩
    rw [smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ h₁ h₂
  | smul b x _ hx =>
    obtain ⟨y, h⟩ := hx
    refine ⟨b • y, ?_⟩
    have := Submodule.smul_mem _ b h
    rwa [smul_sub, smul_smul, ← Algebra.commutes, ← smul_smul] at this

private theorem smul_mem_of_mul {ε : A} {𝔟₁ 𝔟₂ : Ideal A} (h : (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁) {x : M}
    (hx : x ∈ idealSub B M 𝔟₂) : algebraMap A B ε • x ∈ idealSub B M 𝔟₁ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    rw [smul_smul, ← map_mul]
    have hm : ε * c ∈ 𝔟₁ := by
      rw [← h]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self ε)) hc
    exact smul_mem_idealSub hm z'
  | zero =>
    rw [smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    rw [smul_smul, Algebra.commutes, ← smul_smul]
    exact Submodule.smul_mem _ b hx

private theorem smul_mem_of_eps {ε c : A} {𝔟 : Ideal A} {y : M} (hc : c ∈ Ideal.span {ε} ⊔ 𝔟)
    (hy : algebraMap A B ε • y ∈ idealSub B M 𝔟) : algebraMap A B c • y ∈ idealSub B M 𝔟 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hc
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  rw [map_add, add_smul, map_mul, ← smul_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (smul_mem_idealSub hv y)

end Generic

private theorem wSub_one {q : ℕ} [Fact q.Prime] (D : Datum q) (𝔟 : Ideal (𝓞 D.F)) :
    wSub D 𝔟 1 = idealSub D.O D.La 𝔟 := by
  unfold wSub idealSub
  rw [pow_one]

set_option maxHeartbeats 800000 in
theorem levDown : LevDown := by
  unfold LevDown
  intro q _ D hm R _ b N S s o 𝔟₁ 𝔟₂ ε h𝔟 hmul l hl
  obtain ⟨hbij, hproj, -⟩ := mOne q D hm
  haveI := hproj
  have hw₁ : wSub D 𝔟₁ 1 = idealSub D.O D.La 𝔟₁ := wSub_one D 𝔟₁
  have hw₂ : wSub D 𝔟₂ 1 = idealSub D.O D.La 𝔟₂ := wSub_one D 𝔟₂
  have hI : Ideal.span {ε} ⊔ 𝔟₁ ≠ ⊥ := fun h0 => h𝔟 (eq_bot_iff.mpr (h0 ▸ le_sup_right))
  have h𝔟₂ : 𝔟₂ ≠ ⊥ := by
    rintro rfl
    exact h𝔟 (by rw [← hmul, Ideal.mul_bot])
  have h21 : ∀ c, c ∈ 𝔟₁ ^ 1 → c ∈ 𝔟₂ ^ 1 := by
    intro c hc
    rw [pow_one] at hc ⊢
    rw [← hmul] at hc
    exact Ideal.mul_le_right (I := Ideal.span {ε} ⊔ 𝔟₁) (J := 𝔟₂) hc
  have down : ∀ y : D.La, algebraMap (𝓞 D.F) D.O ε • y ∈ idealSub D.O D.La 𝔟₁ →
      y ∈ idealSub D.O D.La 𝔟₂ := by
    intro y hy
    refine mem_of_mul_mem hbij _ 𝔟₂ hI y (fun c hc => ?_)
    rw [hmul]
    exact smul_mem_of_eps hc hy
  obtain ⟨hadd, hact, hker, hpt⟩ := id hl
  unfold IsEtLev
  beta_reduce
  refine ⟨fun x y => by rw [smul_add, hadd], fun c x => ?_, fun x hx => ?_,
    fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩
  · rw [smul_smul, Algebra.commutes, ← smul_smul, hact]
  · apply hker
    rw [hw₁]
    rw [hw₂] at hx
    exact smul_mem_of_mul hmul hx
  · rw [hw₂]
    exact down y (by rw [← hw₁]; exact (hpt k x).1 _ hy)
  · obtain ⟨hpt1, hpt2⟩ := hpt k x
    obtain ⟨y, hy⟩ := hpt2 g (fun c hc => hg c (h21 c hc))
    have hyI : y ∈ idealSub D.O D.La (Ideal.span {ε} ⊔ 𝔟₁) := by
      refine mem_of_mul_mem hbij 𝔟₂ _ h𝔟₂ y (fun c hc => ?_)
      rw [mul_comm, hmul, ← hw₁]
      apply hpt1
      rw [hact, ← Category.assoc, hy]
      exact hg c (by rw [pow_one]; exact hc)
    obtain ⟨y', hy'⟩ := exists_sub_mem hyI
    refine ⟨y', ?_⟩
    have e := hl.congr (show y - algebraMap (𝓞 D.F) D.O ε • y' ∈ wSub D 𝔟₁ 1 by rw [hw₁]; exact hy')
    rw [← hy, e]

end UpperTheory.Gal.FiniteEtaleModels.O
