import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.DualLattices.PowMemCarrier

noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

open ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

lemma unimod {S V ι : Type} [CommRing S] [CommRing V] [Algebra S V] [Fintype ι] (f : ι → V)
    (b : ι → S) (h1 : 1 = ∑ j, b j • f j)
    (hmul : ∀ i j, f j * f i ∈ Submodule.span S (Set.range f)) :
    ∃ e : ι → S, algebraMap S V (∑ j, e j * b j) = 1 := by
  let A : Submodule S V := Submodule.span S (Set.range f)
  let J : Ideal S := Ideal.span (Set.range b)
  have hJ : A ≤ J • A := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : f i = ∑ j, b j • (f j * f i) := by
      conv_lhs => rw [← one_mul (f i), h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
    rw [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul
      (Ideal.subset_span ⟨j, rfl⟩) (hmul i j)
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J A
    (Submodule.fg_span (Set.finite_range f)) hJ
  have h1A : (1 : V) ∈ A := by
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => A.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hr := hr0 1 h1A
  rw [Algebra.smul_def, mul_one] at hr
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 (J.neg_mem hr1)
  refine ⟨e, ?_⟩
  simp only [smul_eq_mul] at he
  rw [he, neg_sub, map_sub, hr, map_one, sub_zero]

theorem invres : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ K K' : AddSubgroup N, K ≤ K' → ∀ g ∈ AA.carrier, (∀ x ∈ K', ∀ k ∈ K, g (x + k) = g x) → ∃ g' ∈ invFun AA.carrier K, ∀ x ∈ K', g' x = g x := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA K K' _ g hg hinv
  classical
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨⟨f, hf, hfree⟩, -⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N K AA
  have hB : ∀ b ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K), b ∈ invFun AA.carrier K := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hq, fun x k hk => ?_⟩
    show q ((x + k : N) : N ⧸ K) = q (x : N ⧸ K)
    rw [QuotientAddGroup.mk_add_of_mem x hk]
  have hdec : ∀ a ∈ AA.carrier, ∃ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) ∧
      a = ∑ j, b j * f j := by
    intro a ha
    obtain ⟨b, ⟨hb, hab⟩, -⟩ := hfree a ha
    exact ⟨b, fun j => hB _ (hb j), hab⟩
  let S : Subalgebra R (N → C) := (invFun AA.carrier K).toSubalgebra ⟨AA.one_mem, fun _ _ _ => rfl⟩
    (fun x y hx hy => ⟨AA.mul_mem _ _ hx.1 hy.1, fun z k hk => by
      simp only [Pi.mul_apply, hx.2 z k hk, hy.2 z k hk]⟩)
  let A : Submodule S (N → C) := Submodule.span S (Set.range f)
  have hA : ∀ a ∈ AA.carrier, a ∈ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hdec a ha
    exact Submodule.sum_mem _ fun j _ =>
      A.smul_mem (⟨b j, hb j⟩ : S) (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hb, h1⟩ := hdec 1 AA.one_mem
  obtain ⟨e, he⟩ := unimod f (fun j => (⟨b j, hb j⟩ : S)) h1
    (fun i j => hA _ (AA.mul_mem _ _ (hf j) (hf i)))
  have he' : ∀ x, ∑ j, (e j : N → C) x * b j x = 1 := by
    intro x
    have : ((∑ j, e j * (⟨b j, hb j⟩ : S) : S) : N → C) x = 1 := congrFun he x
    simpa using this
  obtain ⟨c, hc, hgc⟩ := hdec g hg
  refine ⟨((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C), (∑ j, e j * (⟨c j, hc j⟩ : S) : S).2,
    fun x hx => ?_⟩
  let ρ : (N → C) →ₗ[C] (K → C) := LinearMap.funLeft C C fun k : K => x + (k : N)
  have hρ : ∀ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) →
      ρ (∑ j, b j * f j) = ∑ j, b j x • ρ (f j) := by
    intro b hb
    funext k
    simp only [ρ, LinearMap.funLeft_apply, Finset.sum_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [(hb j).2 x k k.2]
  have hli : LinearIndependent C fun j => ρ (f j) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · have hsurj : Function.Surjective ρ :=
        LinearMap.funLeft_surjective_of_injective _ _ _
          (fun k k' h => Subtype.ext (add_left_cancel h))
      rw [← LinearMap.range_eq_top.2 hsurj, ← Submodule.map_top, ← span_top_of_isLat (C := C) AA.lat,
        Submodule.map_span_le]
      intro a ha
      obtain ⟨b', hb', rfl⟩ := hdec a ha
      rw [hρ b' hb']
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp
  have hkey : ∀ j, c j x = g x * b j x := by
    have h2 : ∑ j, (c j x - g x * b j x) • ρ (f j) = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [← hρ c hc, ← hρ b hb, ← hgc, ← h1]
      funext k
      simp [ρ, LinearMap.funLeft_apply, hinv x hx k k.2]
    intro j
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 j)
  have : ((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C) x = ∑ j, (e j : N → C) x * c j x := by
    simp
  rw [this]
  simp only [hkey]
  calc ∑ j, (e j : N → C) x * (g x * b j x) = g x * ∑ j, (e j : N → C) x * b j x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = g x := by rw [he', mul_one]

end PositivityTheory.HtPt.Rc
