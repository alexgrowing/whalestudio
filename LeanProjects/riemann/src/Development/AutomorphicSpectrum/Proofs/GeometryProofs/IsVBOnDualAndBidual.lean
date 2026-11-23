import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LatDual

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem mem_span_basis_iff (p : Cpt ξ) {r : ℕ} (B : Module.Basis (Fin r) Ω E) (e : E) :
    e ∈ Submodule.span (regAt ξ p) (Set.range B) ↔ ∀ i, B.repr e i ∈ regAt ξ p := by
  constructor
  · intro he
    let N : Submodule (regAt ξ p) E :=
      { carrier := {x | ∀ i, B.repr x i ∈ regAt ξ p}
        add_mem' := fun ha hb i => by simpa using add_mem (ha i) (hb i)
        zero_mem' := fun i => by simp
        smul_mem' := fun c x hx i => by
          show B.repr ((c : Ω) • x) i ∈ regAt ξ p
          simpa using mul_mem c.2 (hx i) }
    have hle : Submodule.span (regAt ξ p) (Set.range B) ≤ N := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show ∀ i, B.repr (B j) i ∈ regAt ξ p
      intro i
      rw [B.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    exact hle he
  · intro h
    rw [← B.sum_repr e]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : B.repr e i • B i = (⟨B.repr e i, h i⟩ : regAt ξ p) • B i := rfl
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_dual_iff (L : Lat ξ E) (p : Cpt ξ) {r : ℕ} (b : Fin r → E)
    (h : L p = Submodule.span (regAt ξ p) (Set.range b)) (w : Module.Dual Ω E) :
    w ∈ L.dual p ↔ ∀ i, w (b i) ∈ regAt ξ p := by
  show (∀ e ∈ L p, w e ∈ regAt ξ p) ↔ _
  rw [h]
  constructor
  · intro hw i
    exact hw _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hw
    let N : Submodule (regAt ξ p) E :=
      { carrier := {x | w x ∈ regAt ξ p}
        add_mem' := fun {a c} ha hc => by
          show w (a + c) ∈ regAt ξ p
          rw [map_add]
          exact add_mem ha hc
        zero_mem' := by
          show w 0 ∈ regAt ξ p
          simp
        smul_mem' := fun c x hx => by
          show w ((c : Ω) • x) ∈ regAt ξ p
          rw [map_smul, smul_eq_mul]
          exact mul_mem c.2 hx }
    have hle : Submodule.span (regAt ξ p) (Set.range b) ≤ N := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hw i
    intro e he
    exact hle he

theorem dual_eq_span (L : Lat ξ E) (p : Cpt ξ) {r : ℕ} (B : Module.Basis (Fin r) Ω E)
    (h : L p = Submodule.span (regAt ξ p) (Set.range B)) :
    L.dual p = Submodule.span (regAt ξ p) (Set.range B.dualBasis) := by
  ext w
  rw [mem_dual_iff L p B h w, mem_span_basis_iff p B.dualBasis w]
  simp only [Module.Basis.dualBasis_repr]

end GlobalTheory.CompanionTheory.Ar.LatDual

namespace GlobalTheory.CompanionTheory.Ar

open LatDual

theorem Lat.isVBOn_dual_and_bidual :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ), L.IsVBOn T r ⊤ → L.dual.IsVBOn T r ⊤ ∧ ∀ p ∈ T, ∀ e : E, e ∈ L p ↔ ∀ w ∈ L.dual p, w e ∈ regAt ξ p := by
  intro X Ω _ ξ E _ _ L T r hL
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨U, hpU, b, hspan, hfr⟩ := hL p hp
    obtain ⟨hli, -⟩ := hfr p hp hpU
    obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin r) Ω E, ⇑B = b :=
      ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli _⟩
    refine ⟨U, hpU, ⇑B.dualBasis, B.dualBasis.span_eq, ?_⟩
    intro q hq hqU
    obtain ⟨-, hLq⟩ := hfr q hq hqU
    refine And.intro B.dualBasis.linearIndependent ?_
    exact LatDual.dual_eq_span L q B (by rw [hB]; exact hLq)
  · intro p hp e
    obtain ⟨U, hpU, b, hspan, hfr⟩ := hL p hp
    obtain ⟨hli, hLp0⟩ := hfr p hp hpU
    obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin r) Ω E, ⇑B = b :=
      ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli _⟩
    have hLp : L p = Submodule.span (regAt ξ p) (Set.range B) := by rw [hB]; exact hLp0
    constructor
    · intro he w hw
      exact hw e he
    · intro h
      rw [hLp, LatDual.mem_span_basis_iff p B e]
      intro i
      have hmem : B.dualBasis i ∈ L.dual p := by
        rw [LatDual.dual_eq_span L p B hLp]
        exact Submodule.subset_span ⟨i, rfl⟩
      have hi := h _ hmem
      rwa [Module.Basis.dualBasis_apply] at hi

end GlobalTheory.CompanionTheory.Ar
