import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex

variable {L : Type} [Field L] [NumberField L] {W : Type} [AddCommGroup W] [Module (𝓞 L) W]

def cond (A B : Submodule (𝓞 L) W) : Ideal (𝓞 L) where
  carrier := {u | ∀ x ∈ A, u • x ∈ B}
  add_mem' := fun {a b} ha hb x hx => by
    rw [add_smul]; exact B.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by rw [zero_smul]; exact B.zero_mem
  smul_mem' := fun c u hu x hx => by
    rw [smul_eq_mul, mul_smul]; exact B.smul_mem c (hu x hx)

theorem mem_cond {A B : Submodule (𝓞 L) W} {u : 𝓞 L} :
    u ∈ cond A B ↔ ∀ x ∈ A, u • x ∈ B := Iff.rfl

theorem exists_reps {A B : Submodule (𝓞 L) W}
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ S : Finset W, (∀ r ∈ S, r ∈ A) ∧ ∀ x ∈ A, ∃ r ∈ S, x - r ∈ B := by
  classical
  have hQ : Finite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hfin
  have := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)
  refine ⟨Finset.univ.image
    (fun q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup =>
      ((Quotient.out q : A.toAddSubgroup) : W)), ?_, ?_⟩
  · intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    exact (Quotient.out q).2
  · intro x hx
    let q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup :=
      QuotientAddGroup.mk ⟨x, hx⟩
    refine ⟨((Quotient.out q : A.toAddSubgroup) : W),
      Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    have hq : (QuotientAddGroup.mk (Quotient.out q) :
        A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup) = q := Quotient.out_eq q
    have h := QuotientAddGroup.eq.mp hq
    rw [AddSubgroup.mem_addSubgroupOf] at h
    have h' : -((Quotient.out q : A.toAddSubgroup) : W) + x ∈ B := h
    rwa [neg_add_eq_sub] at h'

theorem cond_ne_bot {A B : Submodule (𝓞 L) W}
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) : cond A B ≠ ⊥ := by
  intro hbot

  have hmem : ((B.toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : 𝓞 L) ∈ cond A B := by
    refine mem_cond.mpr fun x hx => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup hx
  rw [hbot, Ideal.mem_bot] at hmem
  exact hfin (Nat.cast_eq_zero.mp hmem)

theorem exists_mem_cond_notMem {A B : Submodule (𝓞 L) W} (w : FinitePlace L)
    (hloc : locAt w A = locAt w B)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ s ∈ cond A B, s ∉ w.maximalIdeal.asIdeal := by
  classical
  obtain ⟨S, hSA, hS⟩ := exists_reps hfin
  have hex : ∀ r ∈ S, ∃ t : 𝓞 L, t ∉ w.maximalIdeal.asIdeal ∧ t • r ∈ B := by
    intro r hr
    have hr' : r ∈ locAt w B := by rw [← hloc]; exact le_locAt w A (hSA r hr)
    exact mem_locAt.mp hr'
  choose! t ht using hex
  have := w.maximalIdeal.isPrime
  refine ⟨∏ r ∈ S, t r, mem_cond.mpr fun x hx => ?_, ?_⟩
  · obtain ⟨r, hr, hxr⟩ := hS x hx
    have hrB : (∏ r ∈ S, t r) • r ∈ B := by
      rw [← Finset.mul_prod_erase S t hr, mul_comm, mul_smul]
      exact B.smul_mem _ (ht r hr).2
    have hx' : x = r + (x - r) := by abel
    rw [hx', smul_add]
    exact B.add_mem hrB (B.smul_mem _ hxr)
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨r, hr, hmem⟩
    exact (ht r hr).1 hmem

theorem cond_sup_span_eq_top {A B : Submodule (𝓞 L) W} (v : FinitePlace L)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B)
    {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) : cond A B ⊔ Ideal.span {t} = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hPbot : P ≠ ⊥ := by
    intro hP
    apply cond_ne_bot hfin
    rw [eq_bot_iff, ← hP]
    exact le_sup_left.trans hle
  obtain ⟨Q, hQ⟩ : ∃ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal = P :=
    ⟨⟨P, hPmax.isPrime, hPbot⟩, rfl⟩
  by_cases hw : FinitePlace.mk Q = v
  · apply ht
    rw [← hw, FinitePlace.maximalIdeal_mk, hQ]
    exact hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  · obtain ⟨s, hs, hsP⟩ := exists_mem_cond_notMem (FinitePlace.mk Q) (hloc _ hw) hfin
    apply hsP
    rw [FinitePlace.maximalIdeal_mk, hQ]
    exact hle (Ideal.mem_sup_left hs)

theorem exists_bezout {A B : Submodule (𝓞 L) W} (v : FinitePlace L)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B)
    {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) :
    ∃ s u : 𝓞 L, u ∈ cond A B ∧ s * t + u = 1 := by
  have h1 : (1 : 𝓞 L) ∈ cond A B ⊔ Ideal.span {t} := by
    rw [cond_sup_span_eq_top v hfin hloc ht]; exact Submodule.mem_top
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  exact ⟨s, u, hu, by rw [add_comm]; exact huz⟩

theorem relIndex_locAt (L : Type) [Field L] [NumberField L] (W : Type) [AddCommGroup W]
    [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W) (hBA : B ≤ A)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) :
    (locAt v B).toAddSubgroup.relIndex (locAt v A).toAddSubgroup =
      B.toAddSubgroup.relIndex A.toAddSubgroup := by
  have hle : A.toAddSubgroup ≤ (locAt v A).toAddSubgroup := fun x hx => le_locAt v A hx

  have hback : ∀ x ∈ A, x ∈ locAt v B → x ∈ B := by
    intro x hxA hx
    obtain ⟨t, ht, htx⟩ := mem_locAt.mp hx
    obtain ⟨s, u, hu, hsu⟩ := exists_bezout v hfin hloc ht
    have hx' : x = s • (t • x) + u • x := by rw [smul_smul, ← add_smul, hsu, one_smul]
    rw [hx']
    exact B.add_mem (B.smul_mem s htx) (mem_cond.mp hu x hxA)

  let f := (QuotientAddGroup.mk' ((locAt v B).toAddSubgroup.addSubgroupOf
    (locAt v A).toAddSubgroup)).comp (AddSubgroup.inclusion hle)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    obtain ⟨t, ht, hty⟩ := mem_locAt.mp hy
    obtain ⟨s, u, hu, hsu⟩ := exists_bezout v hfin hloc ht
    refine ⟨⟨s • (t • y), A.smul_mem s hty⟩, ?_⟩
    simp only [f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -(s • (t • y)) + y ∈ locAt v B
    have hu' : u = 1 - s * t := by rw [← hsu]; ring
    have hyeq : -(s • (t • y)) + y = u • y := by
      rw [hu', sub_smul, one_smul, smul_smul, neg_add_eq_sub]
    rw [hyeq]
    exact mem_locAt.mpr ⟨t, ht, by rw [smul_comm]; exact mem_cond.mp hu _ hty⟩
  have hker : f.ker = B.toAddSubgroup.addSubgroupOf A.toAddSubgroup := by
    ext ⟨x, hx⟩
    simp only [f, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_inclusion,
      Submodule.mem_toAddSubgroup]
    exact ⟨fun h => hback x hx h, fun h => le_locAt v B h⟩
  unfold AddSubgroup.relIndex
  rw [← hker, AddSubgroup.index_eq_card, AddSubgroup.index_eq_card]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex
