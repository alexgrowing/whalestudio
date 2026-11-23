import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorProductAction
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic

open scoped TensorProduct nonZeroDivisors
open Polynomial

namespace GlobalTheory.NilpFiltration

theorem charpoly_eq_of_intertwine {K : Type} [Field K] {A B : Type} [AddCommGroup A] [Module K A]
    [FiniteDimensional K A] [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    (φ : A ≃ₗ[K] B) (f : Module.End K A) (g : Module.End K B) (h : ∀ a, φ (f a) = g (φ a)) :
    LinearMap.charpoly f = LinearMap.charpoly g := by
  rw [← LinearEquiv.charpoly_conj φ f]
  congr 1
  ext b
  rw [LinearEquiv.conj_apply_apply, h, LinearEquiv.apply_symm_apply]

theorem charpoly_eq_quotient_charpoly_pow_succ (K : Type) [Field K] : ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module K X]
    [FiniteDimensional K X] (t T : Module.End K X) (_ : Commute t T) (_ : t ^ (n + 1) = 0)
    (_ : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ n))
    (hT : LinearMap.range t ≤ (LinearMap.range t).comap T),
    LinearMap.charpoly T =
      (LinearMap.charpoly ((LinearMap.range t).mapQ (LinearMap.range t) T hT)) ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro X _ _ _ t T _ he _ hT
    have ht : t = 0 := by simpa using he
    subst ht
    rw [pow_one]
    have hinj : Function.Injective (LinearMap.range (0 : Module.End K X)).mkQ := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ, LinearMap.range_zero]
    refine charpoly_eq_of_intertwine
      (LinearEquiv.ofBijective _ ⟨hinj, Submodule.mkQ_surjective _⟩) T _ (fun x => ?_)
    rfl
  | succ n ih =>
    intro X _ _ _ t T hc he hk hT
    have htY : ∀ x ∈ LinearMap.range t, t x ∈ LinearMap.range t := fun x _ => LinearMap.mem_range_self t x
    have hTY : ∀ x ∈ LinearMap.range t, T x ∈ LinearMap.range t := fun x hx => hT hx
    set Y := LinearMap.range t with hYdef
    set t' := t.restrict htY with ht'
    set T' := T.restrict hTY with hT'def
    have hcomm : ∀ x, t (T x) = T (t x) := fun x => LinearMap.congr_fun hc.eq x
    have hc' : Commute t' T' := by
      show t' * T' = T' * t'
      ext x
      simp only [Module.End.mul_apply, t', T', LinearMap.restrict_coe_apply]
      exact hcomm x
    have hpow : ∀ k (x : Y), ((t' ^ k) x : X) = (t ^ k) x := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ihk =>
        intro x
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply,
          LinearMap.restrict_coe_apply, ihk]
    have he' : t' ^ (n + 1) = 0 := by
      ext x
      obtain ⟨y, hy⟩ := x.2
      rw [hpow, LinearMap.zero_apply, ZeroMemClass.coe_zero, ← hy, ← Module.End.mul_apply, ← pow_succ, he,
        LinearMap.zero_apply]
    have hk' : ∀ x : Y, t' x = 0 → x ∈ LinearMap.range (t' ^ n) := by
      intro x hx
      have hx' : t x = 0 := by
        have := congrArg Subtype.val hx
        simpa [t', LinearMap.restrict_coe_apply] using this
      obtain ⟨z, hz⟩ := hk x hx'
      refine ⟨⟨t z, LinearMap.mem_range_self t z⟩, Subtype.ext ?_⟩
      rw [hpow, ← Module.End.mul_apply, ← pow_succ, hz]
    have hT' : LinearMap.range t' ≤ (LinearMap.range t').comap T' := by
      rintro y ⟨x, rfl⟩
      show T' (t' x) ∈ LinearMap.range t'
      exact ⟨T' x, by rw [← Module.End.mul_apply, hc'.eq, Module.End.mul_apply]⟩
    have hmain : LinearMap.charpoly T = LinearMap.charpoly T' * LinearMap.charpoly (Y.mapQ Y T hT) :=
      GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ Y T hTY
    let f : X →ₗ[K] Y ⧸ LinearMap.range t' := (LinearMap.range t').mkQ ∘ₗ t.rangeRestrict
    have hf : ∀ x, f x = Submodule.Quotient.mk (⟨t x, LinearMap.mem_range_self t x⟩ : Y) := fun x => rfl
    have hsurj : Function.Surjective f :=
      (Submodule.mkQ_surjective _).comp t.surjective_rangeRestrict
    have hker : LinearMap.ker f = Y := by
      ext x
      rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨w, hw⟩ := y.2
        have h1 : t (x - t w) = 0 := by
          have := congrArg Subtype.val hy
          simp only [t', LinearMap.restrict_coe_apply] at this
          rw [map_sub, ← this, hw, sub_self]
        obtain ⟨z, hz⟩ := hk _ h1
        have h2 : x - t w ∈ Y := by
          rw [← hz, pow_succ', Module.End.mul_apply]
          exact LinearMap.mem_range_self t _
        have h3 := Y.add_mem h2 (LinearMap.mem_range_self t w)
        rwa [sub_add_cancel] at h3
      · rintro ⟨w, rfl⟩
        exact ⟨⟨t w, LinearMap.mem_range_self t w⟩, rfl⟩
    let φ : (X ⧸ Y) ≃ₗ[K] Y ⧸ LinearMap.range t' :=
      (Submodule.quotEquivOfEq Y (LinearMap.ker f) hker.symm).trans (f.quotKerEquivOfSurjective hsurj)
    have hφ : ∀ x, φ (Submodule.Quotient.mk x) = f x := fun x => rfl
    have hq : LinearMap.charpoly (Y.mapQ Y T hT) = LinearMap.charpoly ((LinearMap.range t').mapQ (LinearMap.range t') T' hT') := by
      refine charpoly_eq_of_intertwine φ _ _ (fun a => ?_)
      induction a using Submodule.Quotient.induction_on with
      | H x =>
        rw [Submodule.mapQ_apply, hφ, hφ, hf, hf, Submodule.mapQ_apply]
        congr 1
        exact Subtype.ext (hcomm x)
    rw [hmain, ih Y t' T' hc' he' hk' hT', ← hq, ← pow_succ]

theorem charpoly_eq_charpoly_mapQ_pow : ∀ (K : Type) [Field K] (X : Type) [AddCommGroup X] [Module K X]
    [FiniteDimensional K X]
    (t T : Module.End K X) (_ : Commute t T) (e : ℕ) (_ : 0 < e) (_ : t ^ e = 0)
    (_ : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ (e - 1)))
    (hT : LinearMap.range t ≤ (LinearMap.range t).comap T),
    LinearMap.charpoly T = (LinearMap.charpoly ((LinearMap.range t).mapQ (LinearMap.range t) T hT)) ^ e := by
  intro K _ X _ _ _ t T hc e he0 he hk hT
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0.ne'
  exact charpoly_eq_quotient_charpoly_pow_succ K n X t T hc he (by simpa using hk) hT

end GlobalTheory.NilpFiltration
