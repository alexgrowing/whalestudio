import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.TraceBlocks.Decomp

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

theorem secM_apply' (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x : G) (v : V) (y : G) :
    secM ι ρ K x v y =
      ((stabCard ι K x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) v := rfl

theorem finsum_apply_eq (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) {φ : G → V}
    (hφ : φ ∈ eqvM ι ρ K) (x y : G) (hs : Set.Finite {h : H | (ι h * x)⁻¹ * y ∈ K}) :
    (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) (φ x) =
      Nat.card {h : H | (ι h * x)⁻¹ * y ∈ K} • φ y := by
  rw [finsum_eq_sum_of_support_subset _ (s := hs.toFinset) ?_]
  · rw [LinearMap.sum_apply,
      Finset.sum_congr rfl (g := fun _ => φ y) ?_, Finset.sum_const, ← Nat.card_eq_card_finite_toFinset]
    intro h hh
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hh
    rw [if_pos hh, ← hφ.1 h x, ← hφ.2 _ hh (ι h * x), mul_inv_cancel_left]
  · intro h hh
    rw [Function.mem_support] at hh
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    by_contra hc
    exact hh (if_neg hc)

theorem card_eq (ι : H →* G) (hι : Function.Injective ι) (K : Subgroup G) (x : G) (h₀ : H) {k₀ : G}
    (hk₀ : k₀ ∈ K) :
    ∃ e : {h : H | (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K} → ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom),
      Function.Bijective e := by
  have key : ∀ h : H, (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K ↔ x⁻¹ * ι (h⁻¹ * h₀) * x ∈ K := by
    intro h
    have : (ι h * x)⁻¹ * (ι h₀ * x * k₀) = x⁻¹ * ι (h⁻¹ * h₀) * x * k₀ := by
      simp only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]
    rw [this, Subgroup.mul_mem_cancel_right K hk₀]
  refine ⟨fun h => ⟨ι (h.1⁻¹ * h₀), Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
    Subgroup.mem_map.mpr ⟨x⁻¹ * ι (h.1⁻¹ * h₀) * x, (key h.1).mp h.2, ?_⟩⟩⟩, ?_, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · intro a b hab
    have := hι (congrArg Subtype.val hab)
    exact Subtype.ext (by simpa using this)
  · rintro ⟨g, hg⟩
    obtain ⟨⟨s, rfl⟩, hm⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp hm
    refine ⟨⟨h₀ * s⁻¹, ?_⟩, ?_⟩
    · show (ι (h₀ * s⁻¹) * x)⁻¹ * (ι h₀ * x * k₀) ∈ K
      rw [key]
      have : x⁻¹ * ι ((h₀ * s⁻¹)⁻¹ * h₀) * x = k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hks
        simp [← hks, mul_assoc]
      rw [this]; exact hk
    · apply Subtype.ext
      simp

end GlobalTheory.BCT.TraceBlocks.Decomp

namespace GlobalTheory.BCT.TraceBlocks.Decomp

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

theorem secM_self (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H V) (K : Subgroup G)
    {φ : G → V} (hφ : φ ∈ eqvM ι ρ K) (x : G) [Finite ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom)]
    (h₀ : H) {k₀ : G} (hk₀ : k₀ ∈ K) :
    secM ι ρ K x (φ x) (ι h₀ * x * k₀) = φ (ι h₀ * x * k₀) := by
  obtain ⟨e, he⟩ := card_eq ι hι K x h₀ hk₀
  have hfin : Set.Finite {h : H | (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K} :=
    Set.finite_coe_iff.mp (Finite.of_injective e he.1)
  rw [secM_apply', finsum_apply_eq ι ρ K hφ x _ hfin, Nat.card_congr (Equiv.ofBijective e he),
    ← Nat.cast_smul_eq_nsmul ℂ]
  have hpos : (0 : ℕ) < Nat.card ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom) := Nat.card_pos
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr hpos.ne') _

theorem secM_off (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x y : G) (v : V)
    (hy : ∀ h : H, (ι h * x)⁻¹ * y ∉ K) : secM ι ρ K x v y = 0 := by
  rw [secM_apply']
  simp only [hy, if_false, finsum_zero, LinearMap.zero_apply, smul_zero]

end GlobalTheory.BCT.TraceBlocks.Decomp

open GlobalTheory.BCT.TraceBlocks.Decomp in

theorem GlobalTheory.BCT.TraceBlocks.eqvM_eq_finsum_secM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G), Function.Injective ι → ∀ (ρ : Representation ℂ H V) (K' : Subgroup G), Finite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)) → (∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G)) → ∀ φ ∈ eqvM ι ρ K', ∑ᶠ q : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G), secM ι ρ K' (Quotient.out q) (φ (Quotient.out q)) = φ := by
  intro G H V _ _ _ _ ι hι ρ K' hQ hS φ hφ
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G))
  funext y
  rw [finsum_eq_sum_of_fintype, Finset.sum_apply, Finset.sum_eq_single (DoubleCoset.mk ι.range K' y)]
  · obtain ⟨g, hg, k₀, hk₀, hy⟩ := (DoubleCoset.eq ι.range K'
      (Quotient.out (DoubleCoset.mk ι.range K' y)) y).mp (DoubleCoset.out_eq' _ _ _)
    obtain ⟨h₀, rfl⟩ := hg
    haveI := hS (Quotient.out (DoubleCoset.mk ι.range K' y))
    have key := secM_self ι hι ρ K' hφ (Quotient.out (DoubleCoset.mk ι.range K' y)) h₀ hk₀
    rw [← hy] at key
    exact key
  · intro q _ hq
    refine secM_off ι ρ K' _ y _ fun h hh => hq ?_
    refine (DoubleCoset.out_eq' _ _ q).symm.trans ((DoubleCoset.eq _ _ _ _).mpr
      ⟨ι h, ⟨h, rfl⟩, _, hh, (mul_inv_cancel_left _ _).symm⟩)
  · intro h
    exact absurd (Finset.mem_univ _) h
