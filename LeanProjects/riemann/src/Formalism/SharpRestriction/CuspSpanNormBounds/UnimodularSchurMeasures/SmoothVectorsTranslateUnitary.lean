import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Sm

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)}

theorem smooth_vectors_add {v1 v2 : H} (h1 : v1 ∈ smoothVecs (k := k) (r := r) σ)
    (h2 : v2 ∈ smoothVecs (k := k) (r := r) σ) : v1 + v2 ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U1, F1, o1, m1, c1, e1⟩ := h1 g₀ hg₀
  obtain ⟨U2, F2, o2, m2, c2, e2⟩ := h2 g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g + F2 g, o1.inter o2, ⟨m1, m2⟩,
    (c1.mono Set.inter_subset_left).add (c2.mono Set.inter_subset_right), fun g hg hgU => ?_⟩
  have a1 : σ g v1 = F1 g := e1 g hg.1 hgU
  have a2 : σ g v2 = F2 g := e2 g hg.2 hgU
  show σ g (v1 + v2) = F1 g + F2 g
  rw [map_add, a1, a2]

theorem smooth_vectors_smul (c : ℂ) {v : H} (h1 : v ∈ smoothVecs (k := k) (r := r) σ) :
    c • v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U1, F1, o1, m1, c1, e1⟩ := h1 g₀ hg₀
  refine ⟨U1, fun g => c • F1 g, o1, m1, c1.const_smul c, fun g hg hgU => ?_⟩
  have a1 : σ g v = F1 g := e1 g hg hgU
  show σ g (c • v) = c • F1 g
  rw [map_smul, a1]

theorem smooth_vectors_translate_unitary
    (hrep : ∀ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ (a * b) = (σ a).comp (σ b))
    {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ a v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U, F, o, m, c, e⟩ := hv (g₀ * a) (unitary_group_mul_mem hg₀ ha)
  have hR : ContDiff ℝ ∞ (fun x : Mat k r => x * a) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ a)).contDiff
  refine ⟨(fun x : Mat k r => x * a) ⁻¹' U, fun x => F (x * a), o.preimage hR.continuous, m,
    c.comp hR.contDiffOn (fun x hx => hx), fun g hg hgU => ?_⟩
  have a1 : σ (g * a) v = F (g * a) := e (g * a) hg (unitary_group_mul_mem hgU ha)
  show σ g (σ a v) = F (g * a)
  rw [← a1, hrep g hgU a ha]
  rfl

end Sm

namespace BData

variable (X : BData)

def LowSmooth : Prop := X.w ∈ smoothVecs (k := X.k) (r := X.r) X.σ

def SmoothCyc : Prop :=
  ∀ x ∈ smoothVecs (k := X.k) (r := X.r) X.σ, ∀ Ws : List (List (Mat X.k X.r)),
    (∀ w ∈ Ws, ∀ Y ∈ w, InLieHpk X.k X.r Y) → ∀ δ : ℝ, 0 < δ →
    ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Mat X.k X.r), (∀ i, g i ∈ X.G) ∧
      (Ws.map fun w => ‖dsigW (k := X.k) (r := X.r) X.σ w (x - ∑ i, c i • X.σ (g i) X.w)‖).sum < δ

variable {X}

theorem orbitSmooth_of (hX : X.Hyp) (hw : X.LowSmooth) : X.OrbitSmooth :=
  fun _ hg => smooth_vectors_translate_unitary (fun _ ha _ hb => discrete_series_map_mul hX.2.1 ha hb) hw hg

theorem orbitNZ_of (hX : X.Hyp) {B : X.H → X.Vp} (hB : X.IsFun B) (hw : X.LowSmooth) (hc : X.SmoothCyc) :
    X.OrbitNZ B := by
  by_contra hne
  have hz : ∀ g ∈ X.G, B (X.σ g X.w) = 0 := by
    intro g hg
    by_contra h
    exact hne ⟨g, hg, h⟩
  obtain ⟨⟨hadd, hsm, -, -⟩, ⟨C, Ws, hWs, hbd⟩, x, hx, hBx⟩ := hB
  have hos := orbitSmooth_of hX hw
  have hpos : 0 < ‖B x‖ := norm_pos_iff.2 hBx
  have hsum0 : ∀ v : X.H, 0 ≤ (Ws.map fun w => ‖dsigW (k := X.k) (r := X.r) X.σ w v‖).sum := by
    intro v
    refine List.sum_nonneg fun a ha => ?_
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 ha
    exact norm_nonneg _
  have hC : 0 < C := by
    by_contra hC
    have h1 := hbd x hx
    have h2 : C * (Ws.map fun w => ‖dsigW (k := X.k) (r := X.r) X.σ w x‖).sum ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hC) (hsum0 x)
    linarith
  obtain ⟨N, c, g, hg, hlt⟩ := hc x hx Ws (fun w hw' => (hWs w hw').2) (‖B x‖ / C) (div_pos hpos hC)
  have h00 : (0 : X.H) ∈ smoothVecs (k := X.k) (r := X.r) X.σ ∧ B 0 = 0 := by
    have h1 := smooth_vectors_smul (σ := X.σ) 0 hw
    have h2 := hsm 0 X.w hw
    rw [zero_smul] at h1 h2
    rw [zero_smul] at h2
    exact ⟨h1, h2⟩
  have hy : ∀ s : Finset (Fin N), (∑ i ∈ s, c i • X.σ (g i) X.w) ∈ smoothVecs (k := X.k) (r := X.r) X.σ ∧
      B (∑ i ∈ s, c i • X.σ (g i) X.w) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h00
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 := smooth_vectors_smul (σ := X.σ) (c a) (hos (g a) (hg a))
      refine ⟨smooth_vectors_add h1 ih.1, ?_⟩
      rw [hadd _ h1 _ ih.1, ih.2, hsm _ _ (hos (g a) (hg a)), hz _ (hg a), smul_zero, add_zero]
  obtain ⟨y1, y2⟩ := hy Finset.univ
  set y : X.H := ∑ i, c i • X.σ (g i) X.w with hydef
  have hny := smooth_vectors_smul (σ := X.σ) (-1) y1
  have hxy : x - y = x + (-1 : ℂ) • y := by rw [neg_one_smul, sub_eq_add_neg]
  have hsm' : x - y ∈ smoothVecs (k := X.k) (r := X.r) X.σ := by rw [hxy]; exact smooth_vectors_add hx hny
  have hBxy : B (x - y) = B x := by
    rw [hxy, hadd _ hx _ hny, hsm _ _ y1, y2, smul_zero, add_zero]
  have h3 := hbd (x - y) hsm'
  rw [hBxy] at h3
  have h4 : C * (Ws.map fun w => ‖dsigW (k := X.k) (r := X.r) X.σ w (x - y)‖).sum < C * (‖B x‖ / C) :=
    mul_lt_mul_of_pos_left hlt hC
  rw [mul_div_cancel₀ _ hC.ne'] at h4
  linarith

end BData

end Formalism.MainNotions.LeviCoordinates

end
