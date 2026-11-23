import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.EichlerLocal

open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem smul_mem' {Λ : Submodule L.O (Fin n → E)} {a : E} (ha : a ∈ L.O) {v : Fin n → E}
    (hv : v ∈ Λ) : a • v ∈ Λ := Λ.smul_mem (⟨a, ha⟩ : L.O) hv

theorem mem_of_close (hH : IsHerm L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    {p : E} (hp : p ∈ L.O) (hpc : L.cj p = p) {x u a b : Fin n → E} {s t : E}
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u)
    (hxΛ : p • x ∈ Λ) (huΛ : u ∈ Λ) (hsO : s ∈ L.O) (ha : a ∈ Λ) (hb : b ∈ Λ) (ht : t ∈ L.O)
    {v : Fin n → E} (hv : eich L Hm x u s v ∈ Λ) :
    eich L Hm (x + p ^ 4 • a) (u + p ^ 4 • b) (s + p ^ 4 * t) v ∈ Λ := by
  have hint : ∀ {y z}, y ∈ Λ → z ∈ Λ → hf L Hm y z ∈ L.O := fun hy hz => (hΛ.2 _).2 hz _ hy
  have hV : p ^ 2 • v ∈ Λ := by
    rw [← eich_inv L hH x u s hx hu hs v]
    generalize eich L Hm x u s v = w at hv
    have e : p ^ 2 • eich L Hm x (-u) (L.cj s) w = p ^ 2 • w - (p * hf L Hm w u) • (p • x)
        + (p * hf L Hm w (p • x)) • u - (hf L Hm w (p • x) * L.cj s) • (p • x) := by
      simp only [eich, hf_neg_r, hf_smul_r, hpc]
      module
    rw [e]
    exact Λ.sub_mem (Λ.add_mem (Λ.sub_mem (smul_mem' L (L.O.pow_mem hp 2) hv)
      (smul_mem' L (L.O.mul_mem hp (hint hv huΛ)) hxΛ))
      (smul_mem' L (L.O.mul_mem hp (hint hv hxΛ)) huΛ))
      (smul_mem' L (L.O.mul_mem (hint hv hxΛ) (GlobalTheory.UnramOrder.cj_mem L hsO)) hxΛ)
  have hu1 : u + p ^ 4 • b ∈ Λ := Λ.add_mem huΛ (smul_mem' L (L.O.pow_mem hp 4) hb)
  have hx1 : p • x + p ^ 5 • a ∈ Λ := Λ.add_mem hxΛ (smul_mem' L (L.O.pow_mem hp 5) ha)
  have hs1 : s + p ^ 4 * t ∈ L.O := L.O.add_mem hsO (L.O.mul_mem (L.O.pow_mem hp 4) ht)
  have e : eich L Hm (x + p ^ 4 • a) (u + p ^ 4 • b) (s + p ^ 4 * t) v = eich L Hm x u s v
      + (p * hf L Hm (p ^ 2 • v) b) • (p • x) + (p ^ 2 * hf L Hm (p ^ 2 • v) (u + p ^ 4 • b)) • a
      - (p * hf L Hm (p ^ 2 • v) (p • x)) • b - (p ^ 2 * hf L Hm (p ^ 2 • v) a) • (u + p ^ 4 • b)
      - (p * hf L Hm (p ^ 2 • v) a * (s + p ^ 4 * t)) • (p • x + p ^ 5 • a)
      - (hf L Hm (p ^ 2 • v) (p • x) * t) • (p • x + p ^ 5 • a)
      - (p * hf L Hm (p ^ 2 • v) (p • x) * s) • a := by
    simp only [eich, hf_add_r, hf_smul_r, hf_smul_l, map_pow, hpc]
    module
  rw [e]
  have hp2 := L.O.pow_mem hp 2
  exact Λ.sub_mem (Λ.sub_mem (Λ.sub_mem (Λ.sub_mem (Λ.sub_mem (Λ.add_mem (Λ.add_mem hv
    (smul_mem' L (L.O.mul_mem hp (hint hV hb)) hxΛ))
    (smul_mem' L (L.O.mul_mem hp2 (hint hV hu1)) ha))
    (smul_mem' L (L.O.mul_mem hp (hint hV hxΛ)) hb))
    (smul_mem' L (L.O.mul_mem hp2 (hint hV ha)) hu1))
    (smul_mem' L (L.O.mul_mem (L.O.mul_mem hp (hint hV ha)) hs1) hx1))
    (smul_mem' L (L.O.mul_mem (hint hV hxΛ) ht) hx1))
    (smul_mem' L (L.O.mul_mem (L.O.mul_mem hp (hint hV hxΛ)) hsO) ha)

end

theorem moved_locally_constant : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ Λ : Submodule L.O S.V, IsSD L S.Hm Λ → ∀ c : ℕ, ∃ N : ℕ, ∀ (x x₁ u u₁ : S.V) (s s₁ : E), S.h x x = 0 → S.h u x = 0 → s + L.cj s = S.h u u → S.h x₁ x₁ = 0 → S.h u₁ x₁ = 0 → s₁ + L.cj s₁ = S.h u₁ u₁ → algebraMap F E ((S.ϖ : F) ^ c) • x ∈ Λ → u ∈ Λ → s ∈ L.O → (∃ y ∈ Λ, x₁ - x = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ Λ, u₁ - u = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ L.O, s₁ - s = algebraMap F E ((S.ϖ : F) ^ N) * y) → S.moved Λ x₁ u₁ s₁ = S.moved Λ x u s := by
  intro F _ _ _ _ _ E _ _ _ L r k S Λ hΛ c
  refine ⟨c * 4, ?_⟩
  rintro x x₁ u u₁ s s₁ hx hu hs hx₁ hu₁ hs₁ hxΛ huΛ hsO ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ ⟨t, ht, et⟩
  rw [pow_mul, map_pow] at ea eb et
  have hp : algebraMap F E ((S.ϖ : F) ^ c) ∈ L.O :=
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subring.pow_mem _ S.ϖ.2 c)
  have hpc : L.cj (algebraMap F E ((S.ϖ : F) ^ c)) = algebraMap F E ((S.ϖ : F) ^ c) :=
    L.cj.commutes _
  generalize algebraMap F E ((S.ϖ : F) ^ c) = p at *
  obtain rfl : x₁ = x + p ^ 4 • a := by rw [← ea]; abel
  obtain rfl : u₁ = u + p ^ 4 • b := by rw [← eb]; abel
  obtain rfl : s₁ = s + p ^ 4 * t := by rw [← et]; ring
  ext v
  constructor
  · intro hv
    have h := mem_of_close L S.herm.1 hΛ hp hpc hx₁ hu₁ hs₁
      (by
        rw [smul_add]
        exact Λ.add_mem hxΛ (smul_mem' L hp (smul_mem' L (L.O.pow_mem hp 4) ha)))
      (Λ.add_mem huΛ (smul_mem' L (L.O.pow_mem hp 4) hb))
      (L.O.add_mem hsO (L.O.mul_mem (L.O.pow_mem hp 4) ht))
      (Λ.neg_mem ha) (Λ.neg_mem hb) (L.O.neg_mem ht) hv
    simp only [smul_neg, mul_neg, add_neg_cancel_right] at h
    exact h
  · intro hv
    exact mem_of_close L S.herm.1 hΛ hp hpc hx hu hs hxΛ huΛ hsO ha hb ht hv

end GlobalTheory.HL.EichlerLocal
