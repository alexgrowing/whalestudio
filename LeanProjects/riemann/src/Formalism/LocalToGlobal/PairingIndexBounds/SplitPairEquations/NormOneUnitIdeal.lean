import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.ReductionOf

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Matrix

variable (D : D7)

theorem detId_eq_vol {N : ℕ} {L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    TaylorLogMetric.detId D L L' = DN.vol D L' * CU.cS D (DN.vol D L) := by
  have h1 : DN.vol D L * CU.cS D (DN.vol D L) = 1 :=
    le_antisymm (DN.vol_mul_cS_le_one (D := D) L (DN.sd_int (D := D) hL)) (DN.unitDisc (D := D) N L hL)
  apply le_antisymm
  · calc TaylorLogMetric.detId D L L' = TaylorLogMetric.detId D L L' * (DN.vol D L * CU.cS D (DN.vol D L)) := by rw [h1, mul_one]
      _ = TaylorLogMetric.detId D L L' * DN.vol D L * CU.cS D (DN.vol D L) := by rw [mul_assoc]
      _ ≤ DN.vol D L' * CU.cS D (DN.vol D L) :=
        Submodule.mul_le.mpr fun a ha b hb =>
          Submodule.mul_mem_mul (DN.detId_mul_vol_le (D := D) L L' ha) hb
  · exact DN.vol_mul_cS_le (D := D) L L' (DN.sd_int (D := D) hL)

theorem vol_unit {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    DN.vol D L * CU.cS D (DN.vol D L) = 1 :=
  le_antisymm (DN.vol_mul_cS_le_one (D := D) L (DN.sd_int (D := D) hL)) (DN.unitDisc (D := D) N L hL)

theorem detMul : DetMul D := by
  intro N L L' L'' _ hL hL' hL''
  rw [detId_eq_vol D hL, detId_eq_vol D hL, detId_eq_vol D hL']
  calc DN.vol D L'' * CU.cS D (DN.vol D L)
      = DN.vol D L'' * CU.cS D (DN.vol D L) * (DN.vol D L' * CU.cS D (DN.vol D L')) := by
        rw [vol_unit D hL', mul_one]
    _ = DN.vol D L' * CU.cS D (DN.vol D L) * (DN.vol D L'' * CU.cS D (DN.vol D L')) := by ring

theorem norm_one_unit_ideal : NormOneUnitIdeal D := by
  intro z
  letI := D.host.cmStar
  have hz : star (z : D.host.E) * (z : D.host.E) = 1 := (show _ ∧ _ from z.2).1
  have hint : ∀ a : 𝓞 D.host.E, star ((algebraMap (𝓞 D.host.E) D.host.E) a) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := fun a =>
    ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) a, rfl⟩
  have hz0 : (z : D.host.E) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hz
    exact zero_ne_one hz
  obtain ⟨L, hL⟩ : ∃ L : Submodule (𝓞 D.host.E) (Fin 1 → D.host.E),
      L = Submodule.span (𝓞 D.host.E) {(fun _ : Fin 1 => (z : D.host.E))} := ⟨_, rfl⟩
  have hmemL : ∀ y : Fin 1 → D.host.E, y ∈ L ↔ ∃ a : 𝓞 D.host.E, (algebraMap (𝓞 D.host.E) D.host.E) a * (z : D.host.E) = y 0 := by
    intro y
    rw [hL, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by rw [Pi.smul_apply, Algebra.smul_def]⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, funext fun i => ?_⟩
      rw [Subsingleton.elim i 0, Pi.smul_apply, Algebra.smul_def]
      exact ha
  have hH : ∀ x y : Fin 1 → D.host.E, stdH D.host.E 1 x y = star (x 0) * y 0 := fun x y => by
    simp only [stdH, Fin.sum_univ_one]
  have hSD : SD D L := by
    unfold SD IsSDLat
    refine ⟨by rw [hL]; exact Submodule.fg_span_singleton _, ?_, ?_⟩
    · rw [hL, Submodule.span_span_of_tower, eq_top_iff]
      intro w _
      rw [Submodule.mem_span_singleton]
      refine ⟨w 0 * (z : D.host.E)⁻¹, funext fun i => ?_⟩
      rw [Subsingleton.elim i 0, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_right₀ hz0]
    · intro y
      rw [hmemL]
      constructor
      · rintro ⟨b, hb⟩ x hx
        obtain ⟨a, ha⟩ := (hmemL x).1 hx
        have e : stdH D.host.E 1 x y = star ((algebraMap (𝓞 D.host.E) D.host.E) a) * (algebraMap (𝓞 D.host.E) D.host.E) b := by
          rw [hH, ← ha, ← hb, star_mul']
          linear_combination star ((algebraMap (𝓞 D.host.E) D.host.E) a) * (algebraMap (𝓞 D.host.E) D.host.E) b * hz
        rw [e]
        exact (algebraMap (𝓞 D.host.E) D.host.E).range.mul_mem (hint a) (RingHom.mem_range_self _ b)
      · intro H
        obtain ⟨c, hc⟩ := H (fun _ : Fin 1 => (z : D.host.E)) ((hmemL _).2 ⟨1, by rw [map_one, one_mul]⟩)
        refine ⟨c, ?_⟩
        rw [hc, hH]
        linear_combination y 0 * hz
  have hvol : DN.vol D L = Submodule.span (𝓞 D.host.E) {(z : D.host.E)} := by
    unfold DN.vol
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨U, hU, rfl⟩
      obtain ⟨a, ha⟩ := (hmemL _).1 (hU 0)
      rw [Matrix.det_fin_one, SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨a, by rw [Algebra.smul_def]; exact ha⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      apply Submodule.subset_span
      refine ⟨Matrix.of fun _ _ => (z : D.host.E), fun j => ?_, by rw [Matrix.det_fin_one, Matrix.of_apply]⟩
      rw [hL]
      exact Submodule.subset_span rfl
  have h1 := vol_unit D hSD
  rw [hvol] at h1
  exact ⟨CU.cS D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}), fun x => Iff.rfl, h1⟩

private theorem mem_smulLat_lemma [StarRing D.host.E] {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (g g' : Matrix (Fin N) (Fin N) D.host.E) (h1 : g' * g = 1) (h2 : g * g' = 1) (w : Fin N → D.host.E) :
    w ∈ SDLat.smulLat g L ↔ g' *ᵥ w ∈ L := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w', hw', rfl⟩
    change g' *ᵥ (g *ᵥ w') ∈ L
    rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · intro h
    refine ⟨_, h, ?_⟩
    change g *ᵥ (g' *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

private theorem vol_smul_lemma_2 [StarRing D.host.E] {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (g g' : Matrix (Fin N) (Fin N) D.host.E) (h1 : g' * g = 1) (h2 : g * g' = 1) :
    DN.vol D (SDLat.smulLat g L) = Submodule.span (𝓞 D.host.E) {g.det} * DN.vol D L := by
  have hc : ∀ (A B : Matrix (Fin N) (Fin N) D.host.E) (j : Fin N),
      (fun i => (A * B) i j) = A *ᵥ (fun i => B i j) := fun A B j => by
    funext i
    rfl
  unfold DN.vol
  rw [Submodule.span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨U, hU, rfl⟩
    have e : U.det = g.det * (g' * U).det := by
      rw [← Matrix.det_mul, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [e]
    refine Set.mul_mem_mul (Set.mem_singleton _) ⟨g' * U, fun j => ?_, rfl⟩
    rw [hc]
    exact (mem_smulLat_lemma D L g g' h1 h2 _).1 (hU j)
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨U, hU, rfl⟩ := hb
    refine ⟨g * U, fun j => ?_, (Matrix.det_mul _ _).symm⟩
    rw [mem_smulLat_lemma D L g g' h1 h2, hc, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    exact hU j

theorem detSmul : DetSmul D := by
  intro N L₀ L γ _ hL₀ hL
  letI := D.host.cmStar
  have hu : star (γ : Matrix (Fin N) (Fin N) D.host.E) * (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := (show _ ∧ _ from γ.2).1
  have hu2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := (show _ ∧ _ from γ.2).2
  rw [detId_eq_vol D hL₀, detId_eq_vol D hL₀, vol_smul_lemma_2 D L _ _ hu hu2, mul_assoc]

theorem stdH_unitary {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (hu' : (letI := D.host.cmStar; star γ * γ) = 1) (a b : Fin N → D.host.E) :
    (letI := D.host.cmStar; stdH D.host.E N (γ *ᵥ a) (γ *ᵥ b)) = (letI := D.host.cmStar; stdH D.host.E N a b) := by
  letI := D.host.cmStar
  have key : ∀ v w : Fin N → D.host.E, stdH D.host.E N v w = star v ⬝ᵥ w := fun v w => rfl
  rw [key, key, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, hu', Matrix.vecMul_one]

theorem smulSD : SmulSD D := by
  intro N L γ hL
  letI := D.host.cmStar
  obtain ⟨hfg, hsp, hdual⟩ := hL
  have hu : star (γ : Matrix (Fin N) (Fin N) D.host.E) * (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := (show _ ∧ _ from γ.2).1
  have hu2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := (show _ ∧ _ from γ.2).2
  have happ : ∀ v, ((toLin' (γ : Matrix (Fin N) (Fin N) D.host.E)).restrictScalars (𝓞 D.host.E)) v = (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v := fun v => rfl
  have hy : ∀ y, y = (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, hu2, Matrix.one_mulVec]
  have hmem : ∀ w, w ∈ L.map ((toLin' (γ : Matrix (Fin N) (Fin N) D.host.E)).restrictScalars (𝓞 D.host.E)) ↔ star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ w ∈ L := by
    intro w
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨w', hw', rfl⟩
      rwa [happ, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
    · intro h
      exact ⟨_, h, by rw [happ, ← hy]⟩
  unfold SD SDLat.smulLat
  refine ⟨hfg.map _, ?_, ?_⟩
  · have himg : ((L.map ((toLin' (γ : Matrix (Fin N) (Fin N) D.host.E)).restrictScalars (𝓞 D.host.E)) : Submodule _ _) : Set (Fin N → D.host.E)) =
        (toLin' (γ : Matrix (Fin N) (Fin N) D.host.E)) '' (L : Set (Fin N → D.host.E)) := by
      rw [Submodule.map_coe]; rfl
    rw [himg, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top]
    intro v
    exact ⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v, by rw [Matrix.toLin'_apply, ← hy]⟩
  · intro y
    rw [hmem, hdual]
    constructor
    · intro H x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      have h1 := H x' hx'
      rw [← stdH_unitary D (γ : Matrix (Fin N) (Fin N) D.host.E) hu x' (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y), ← hy] at h1
      rwa [happ]
    · intro H x' hx'
      have h1 := H _ (Submodule.mem_map_of_mem hx')
      rw [happ, hy y, stdH_unitary D (γ : Matrix (Fin N) (Fin N) D.host.E) hu] at h1
      exact h1

end Formalism.L2.PairingIndexBounds.Eq
