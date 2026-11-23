import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.QuotEig

section Free

variable {K : Type} [Field K] {A : Subring K} {W : Type} [AddCommGroup W] [Module K W]
  {E : Type} [Field E] [NumberField E] {ρ : 𝓞 E →+* Module.End K W} {Y : Submodule A W} {N : ℕ} {t : Fin N → W}

theorem act_mem_of_free (h : HT.IsFreeOn ρ Y t) (a : 𝓞 E) {y : W} (hy : y ∈ Y) : ρ a y ∈ Y := by
  have key : Y ≤ Y.comap ((ρ a).restrictScalars A) := by
    conv_lhs => rw [h.2.2]
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    change ρ a (ρ (RingOfIntegers.basis E q.2) (t q.1)) ∈ Y
    rw [← Module.End.mul_apply, ← map_mul, h.2.2,
      ← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E q.2), map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(q.1, k), rfl⟩)) _
  exact key hy

theorem eigProj_mem_of_free (h : HT.IsFreeOn ρ Y t) (σ : E →+* K) (hσ : ∀ a : E, σ a ∈ A) {y : W} (hy : y ∈ Y) :
    HT.eigProj ρ σ y ∈ Y := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  exact Y.smul_mem (⟨_, hσ (HT.dualInt E k)⟩ : A) (act_mem_of_free h _ hy)

end Free

section Main

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

theorem fst_eigProj (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (y : V × Module.Dual Ω V) :
    (HT.eigProj 𝓗.ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, 𝓗.act_fst]

theorem mem_L_iff (𝓗 : HodgeLat L ρ bar r) (x : Cpt ξ) {z : V} :
    z ∈ L x ↔ ∃ h ∈ 𝓗.HL x, h.1 = z := by
  have e : L x = (𝓗.HL.map (LinearMap.fst Ω V (Module.Dual Ω V))) x := congrFun 𝓗.map_fst.symm x
  rw [e]
  exact Iff.rfl

end Main

theorem quot_eig : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (x : Cpt ξ), (∀ a : E, σ a ∈ regAt ξ x) → (∀ y, y ∈ 𝓗.quot σ x ↔ y ∈ 𝓗.HL x ∧ y ∈ HT.eigSp 𝓗.ρH σ) ∧ (∀ z ∈ L x, HT.eigProj ρ σ z ∈ L x) ∧ (𝓗.quot σ x).map ((LinearMap.fst Ω V (Module.Dual Ω V)).restrictScalars (regAt ξ x)) = (L.inter (HT.eigSp ρ σ)) x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar r 𝓗 σ x hσ
  obtain ⟨U, hU, t, ht⟩ := 𝓗.free x
  have hfree := ht x hU
  have hstab : ∀ {h}, h ∈ 𝓗.HL x → HT.eigProj 𝓗.ρH σ h ∈ 𝓗.HL x := fun hh =>
    eigProj_mem_of_free hfree σ hσ hh
  refine ⟨fun y => ⟨?_, ?_⟩, fun z hz => ?_, ?_⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hstab hh, HT.LatBasic.eigProj_mem _ _ _⟩
  · rintro ⟨h1, h2⟩
    exact ⟨y, h1, HT.LatBasic.eigProj_of_mem h2⟩
  · obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
    exact (mem_L_iff 𝓗 x).2 ⟨_, hstab hh, fst_eigProj 𝓗 σ h⟩
  · ext z
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      have e : (HT.eigProj 𝓗.ρH σ h).1 = HT.eigProj ρ σ h.1 := fst_eigProj 𝓗 σ h
      refine ⟨(mem_L_iff 𝓗 x).2 ⟨_, hstab hh, rfl⟩, ?_⟩
      change (HT.eigProj 𝓗.ρH σ h).1 ∈ HT.eigSp ρ σ
      rw [e]
      exact HT.LatBasic.eigProj_mem _ _ _
    · rintro ⟨hz, hz'⟩
      obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
      refine ⟨HT.eigProj 𝓗.ρH σ h, ⟨h, hh, rfl⟩, ?_⟩
      exact (fst_eigProj 𝓗 σ h).trans (HT.LatBasic.eigProj_of_mem hz')

end GlobalTheory.CompanionTheory.Ar.Flat.QuotEig
