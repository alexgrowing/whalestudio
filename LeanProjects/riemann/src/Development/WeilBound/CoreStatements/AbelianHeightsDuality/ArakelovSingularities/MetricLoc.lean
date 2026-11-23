import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k]

theorem exists_local_ext {P X : Scheme.{0}} {q : P ⟶ Sp k} {p : X ⟶ Sp k} (i : X ⟶ P) [IsClosedImmersion i]
    (hi : i ≫ q = p) {σ : k →+* ℂ} (f : CxPts p σ → ℝ) (x₀ : CxPts p σ) (hf : CInfAt f x₀) :
    ∃ (V : Set (CxPts q σ)) (θ : CxPts q σ → ℝ), IsOpen V ∧ PtsOver.map i hi (spMap σ) x₀ ∈ V ∧
      (∀ y ∈ V, CInfAt θ y) ∧ ∀ x, PtsOver.map i hi (spMap σ) x ∈ V → θ (PtsOver.map i hi (spMap σ) x) = f x := by
  classical
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := hf
  have hu₀ : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ W := mem_ptsIn.1 h₁
  obtain ⟨U, hU, hiu, -⟩ := exists_isAffineOpen_mem_and_subset (X := P)
    (x := i (x₀.1 (IsLocalRing.closedPoint ℂ))) (U := ⊤) trivial
  have hU' : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  obtain ⟨h, hhV, hxh⟩ := hU'.exists_basicOpen_le (V := W ⊓ i ⁻¹ᵁ U)
    ⟨x₀.1 (IsLocalRing.closedPoint ℂ), ⟨hu₀, hiu⟩⟩ hiu
  obtain ⟨H, hH⟩ := i.app_surjective U hU h
  have hUa : IsAffineOpen (P.basicOpen H) := hU.basicOpen H
  have hpre : i ⁻¹ᵁ P.basicOpen H = X.basicOpen h := by
    rw [Scheme.preimage_basicOpen]
    exact congrArg X.basicOpen hH
  have hle : i ⁻¹ᵁ P.basicOpen H ≤ W := hpre.le.trans (hhV.trans inf_le_left)
  choose G hG using fun a => i.app_surjective (P.basicOpen H) hUa (resG X hle (g a))
  have hmem (x : CxPts p σ) : PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (P.basicOpen H) ↔
      x ∈ ptsIn p σ (i ⁻¹ᵁ P.basicOpen H) := by
    rw [mem_ptsIn, mem_ptsIn]
    rfl
  have hev (x : CxPts p σ) (hx : PtsOver.map i hi (spMap σ) x ∈ ptsIn q σ (P.basicOpen H)) (a : ι) :
      ev q σ (P.basicOpen H) (G a) (PtsOver.map i hi (spMap σ) x) = ev p σ W (g a) x := by
    rw [← ev_app i hi (P.basicOpen H) (G a) x]
    have e : (i.app (P.basicOpen H)) (G a) = resG X hle (g a) := hG a
    rw [e, ev_res hle ((hmem x).1 hx)]
  have hemb := PtsOver.isClosedEmbedding_map (C := ℂ) i hi (spMap σ)
  have hN : {x | f x = F fun a => ev p σ W (g a) x} ∈ 𝓝 x₀ := h₅
  rw [hemb.isInducing.nhds_eq_comap] at hN
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hN
  obtain ⟨V', hV't, hV'o, hx₀V'⟩ := mem_nhds_iff.1 ht
  have hcont : ContinuousOn (fun y (a : ι) => ev q σ (P.basicOpen H) (G a) y) (ptsIn q σ (P.basicOpen H)) :=
    continuousOn_pi.2 fun a => continuousOn_ev (G a)
  refine ⟨V' ∩ (ptsIn q σ (P.basicOpen H) ∩ (fun y (a : ι) => ev q σ (P.basicOpen H) (G a) y) ⁻¹' O),
    fun y => F fun a => ev q σ (P.basicOpen H) (G a) y,
    hV'o.inter (hcont.isOpen_inter_preimage (isOpen_ptsIn _) h₂), ?_, ?_, ?_⟩
  · have hx₀ : PtsOver.map i hi (spMap σ) x₀ ∈ ptsIn q σ (P.basicOpen H) := by
      rw [hmem, mem_ptsIn, hpre]
      exact hxh
    refine ⟨hx₀V', hx₀, ?_⟩
    simp only [Set.mem_preimage, hev x₀ hx₀]
    exact h₃
  · rintro y ⟨-, hy₁, hy₂⟩
    exact ⟨P.basicOpen H, ι, inferInstance, G, F, O, hy₁, h₂, hy₂, h₄, EventuallyEq.rfl⟩
  · rintro x ⟨hx₁, hx₂, -⟩
    have e : f x = F fun a => ev p σ W (g a) x := hts (hV't hx₁)
    rw [e]
    exact congrArg F (funext fun a => hev x hx₂ a)

end GlobalTheory.AmbMetric
