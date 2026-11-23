import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompletedLatticeFinite

section General

variable {E : Type} [Field E] [NumberField E]

theorem exists_denom {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : E, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ (d * x i) := by
  classical
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ (Finset.univ : Finset (Fin n))).image fun p => p.1 p.2)
  refine ⟨(y : E), by exact_mod_cast hy0, fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have := hy (x i) (Finset.mem_image.2 ⟨(x, i), by simpa using hx, rfl⟩)
    simpa [zsmul_eq_mul] using this
  | zero => simpa using isIntegral_zero
  | add x z _ _ hx hz => rw [Pi.add_apply, mul_add]; exact hx.add hz
  | smul c x _ hx =>
    have : (y : E) * (c • x) i = (c : E) * ((y : E) * x i) := by
      change (y : E) * ((c : E) * x i) = _
      ring
    rw [this]
    exact c.isIntegral_coe.mul hx

theorem finite_of_denom (d : E) (hd : d ≠ 0) (R : ℝ) :
    {x : E | IsIntegral ℤ (d * x) ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ R}.Finite := by
  have h := NumberField.Embeddings.finite_of_norm_le E ℂ ((∑ φ : E →+* ℂ, ‖φ d‖) * R)
  refine (h.preimage (f := fun x => d * x) (mul_right_injective₀ hd).injOn).subset ?_
  rintro x ⟨hx, hb⟩
  refine ⟨hx, fun φ => ?_⟩
  rw [map_mul, norm_mul]
  exact mul_le_mul (Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ d‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ φ)) (hb φ) (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem mem_spanSingleton_inv (d : E) (hd : d ≠ 0) (x : E) :
    x ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ ↔ IsIntegral ℤ (d * x) := by
  rw [FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, rfl⟩
    have : d * (z • d⁻¹) = (z : E) := by
      change d * ((z : E) * d⁻¹) = _
      field_simp
    rw [this]
    exact z.isIntegral_coe
  · intro h
    refine ⟨⟨d * x, h⟩, ?_⟩
    change d * x * d⁻¹ = x
    field_simp

end General

theorem isIntegral_star (D : D7) {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem norm_emb_le (D : D7) {x : D.host.E} {R : ℝ} (h : ∀ τ, ‖tauE D τ x‖ ≤ R) (φ : D.host.E →+* ℂ) :
    ‖φ x‖ ≤ R := by
  obtain ⟨τ, hτ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk φ)
  have := h τ
  rw [← InfinitePlace.apply] at this ⊢
  rw [← hτ]
  exact this

theorem finite_rational_points : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ R : ℝ, {g : Matrix (Fin T.rank) (Fin S.rank) D.host.E | (∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ((ratW T S g : WO S T) - l).map (finPart D) = 0) ∧ ∀ τ i j, ‖tauE D τ (g i j)‖ ≤ R}.Finite := by
  classical
  intro D S T ΛS ΛT hS hT R
  obtain ⟨dS, hdS, hS'⟩ := exists_denom ΛS hS.1.fg
  obtain ⟨dT, hdT, hT'⟩ := exists_denom ΛT hT.1.fg
  obtain ⟨dA, hdA, hA'⟩ := D.host.AA.2
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (Fin S.rank × Fin S.rank)).image fun p => S.gram p.1 p.2)
  have hdA0 : (dA : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hdA
    exact_mod_cast this
  have hd : (dA : D.host.E) * dT * (star dS * (y : D.host.E)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdA0 hdT) (mul_ne_zero (star_ne_zero.2 hdS) (by exact_mod_cast hy0))
  set d : D.host.E := (dA : D.host.E) * dT * (star dS * (y : D.host.E)) with hdd
  have hgen : ∀ a ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, ∀ i j,
      IsIntegral ℤ (d * (a * t i * ∑ k, star (s k) * S.gram k j)) := by
    intro a ha s hs t ht i j
    have e : d * (a * t i * ∑ k, star (s k) * S.gram k j) =
        ((dA : D.host.E) * a) * (dT * t i) * ∑ k, star (dS * s k) * ((y : D.host.E) * S.gram k j) := by
      simp only [hdd, Finset.mul_sum, star_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine IsIntegral.mul (IsIntegral.mul ?_ (hT' t ht i)) (IsIntegral.sum _ fun k _ =>
      (isIntegral_star D (hS' s hs k)).mul ?_)
    · obtain ⟨b, hb⟩ := hA' a ha
      have : (dA : D.host.E) * a = (b : D.host.E) := hb.symm
      rw [this]
      exact b.isIntegral_coe
    · have := hy (S.gram k j) (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)
      simpa [zsmul_eq_mul] using this
  have hlat : ∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ i j, finPart D (l i j) ∈ GlobalTheory.AdLat.hat1 D.host.F
        ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ d⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Set D.host.E) := by
    intro l hl i j
    induction hl using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨α, hα, _, (mem_spanSingleton_inv d hd _).2 (hgen a ha s hs t ht i j), rfl⟩
    | zero => rw [Matrix.zero_apply, RingHom.map_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [Matrix.add_apply, RingHom.map_add]; exact add_mem hx hz
    | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg]; exact neg_mem hx
  refine (Set.Finite.pi' fun _ : Fin T.rank => Set.Finite.pi' fun _ : Fin S.rank =>
    finite_of_denom d hd R).subset ?_
  rintro g ⟨⟨l, hl, hgl⟩, hb⟩ i j
  refine ⟨?_, norm_emb_le D fun τ => hb τ i j⟩
  have h1 : finPart D (incA D (g i j) - l i j) = 0 := congrFun (congrFun hgl i) j
  rw [RingHom.map_sub, sub_eq_zero] at h1
  have h2 := hlat l hl i j
  rw [← h1] at h2
  exact (mem_spanSingleton_inv d hd _).1 (((GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties D.host.F D.host.E).2.1 _ (g i j)).1 h2)

end GlobalTheory.CompletedLatticeFinite
