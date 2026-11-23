import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionConvolutionIdentity

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.PlaceDegreeData (phA IsOpIntA)

section One

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]

theorem pj_PxP [μ.IsMulLeftInvariant] [SigmaFinite μ] (φ : G → ℂ) (hφc : Continuous φ) (hφi : Integrable φ μ)
    (x : G) (c : ℂ) (hB : ∀ y : G, ∫ g, φ g * φ (x⁻¹ * g⁻¹ * y) ∂μ = c * φ y)
    (π : G →* (Hp →L[ℂ] Hp)) (hU : ∀ g x, ‖π g x‖ = ‖x‖) (hc : ∀ x, Continuous fun g => π g x)
    (P : Hp →L[ℂ] Hp) (hP : IsOpIntA μ π φ P) : P ∘L π x ∘L P = c • P := by
  ext y
  refine ext_inner_left ℂ fun u => ?_
  show ⟪u, P (π x (P y))⟫_ℂ = ⟪u, c • P y⟫_ℂ
  rw [hP.2 u (π x (P y)), inner_smul_right, hP.2 u y]
  have e1 : ∀ g, φ g * ⟪u, π g (π x (P y))⟫_ℂ = ∫ h, φ g * φ (x⁻¹ * g⁻¹ * h) * ⟪u, π h y⟫_ℂ ∂μ := by
    intro g
    have a : ⟪u, π g (π x (P y))⟫_ℂ = ⟪π (g * x)⁻¹ u, P y⟫_ℂ := by
      rw [← inner_map_inv_eq π hU, inv_inv, rep_mul_apply']
    rw [a, hP.2]
    have b : ∫ h, φ h * ⟪π (g * x)⁻¹ u, π h y⟫_ℂ ∂μ = ∫ h, φ (x⁻¹ * g⁻¹ * h) * ⟪u, π h y⟫_ℂ ∂μ := by
      rw [← integral_mul_left_eq_self (fun h => φ (x⁻¹ * g⁻¹ * h) * ⟪u, π h y⟫_ℂ) (g * x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
      show φ h * ⟪π (g * x)⁻¹ u, π h y⟫_ℂ = φ (x⁻¹ * g⁻¹ * (g * x * h)) * ⟪u, π (g * x * h) y⟫_ℂ
      rw [← inner_map_inv_eq π hU, inv_inv, ← rep_mul_apply']
      congr 2
      group
    rw [b, ← integral_const_mul]
    simp only [mul_assoc]
  simp only [e1]
  rw [integral_integral_swap (convolution_kernel_prod_integrable μ φ hφc hφi π hU hc x u y), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  show ∫ g, φ g * φ (x⁻¹ * g⁻¹ * h) * ⟪u, π h y⟫_ℂ ∂μ = c * (φ h * ⟪u, π h y⟫_ℂ)
  rw [integral_mul_const, hB]
  ring

theorem pj_starProj [μ.IsMulLeftInvariant] [μ.IsInvInvariant] [SigmaFinite μ] (φ : G → ℂ) (hφc : Continuous φ)
    (hφi : Integrable φ μ) (hA : ∀ g, star (φ g⁻¹) = φ g) (hB : ∀ y : G, ∫ g, φ g * φ (g⁻¹ * y) ∂μ = φ y)
    (π : G →* (Hp →L[ℂ] Hp)) (hU : ∀ g x, ‖π g x‖ = ‖x‖) (hc : ∀ x, Continuous fun g => π g x)
    (P : Hp →L[ℂ] Hp) (hP : IsOpIntA μ π φ P) : IsStarProjection P := by
  have h1 := pj_PxP μ φ hφc hφi 1 1 (fun y => by simpa using hB y) π hU hc P hP
  refine ⟨?_, (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 fun x y => convolution_operator_symmetric μ φ hA π hU P hP x y⟩
  rw [map_one, one_smul] at h1
  exact h1

end One

section Two

variable {G1 G2 : Type} [Group G1] [Group G2] [MeasurableSpace G1] [MeasurableSpace G2]
  (μ1 : Measure G1) (μ2 : Measure G2) [SFinite μ1] [SFinite μ2]
  {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]

theorem pj_fubini (R : G1 × G2 → (Hp →L[ℂ] Hp)) (hmul : ∀ g h, R (g * h) = R g ∘L R h)
    (hU : ∀ g x, ‖R g x‖ = ‖x‖)
    (hmeas : ∀ x y : Hp, AEStronglyMeasurable (fun g => ⟪x, R g y⟫_ℂ) (μ1.prod μ2))
    (φ1 : G1 → ℂ) (φ2 : G2 → ℂ) (hφ : Integrable (fun p : G1 × G2 => φ1 p.1 * φ2 p.2) (μ1.prod μ2))
    (P1 P2 T : Hp →L[ℂ] Hp)
    (hP1 : ∀ x y : Hp, ⟪x, P1 y⟫_ℂ = ∫ g, φ1 g * ⟪x, R (g, 1) y⟫_ℂ ∂μ1)
    (hP2 : ∀ x y : Hp, ⟪x, P2 y⟫_ℂ = ∫ k, φ2 k * ⟪x, R (1, k) y⟫_ℂ ∂μ2)
    (hT : ∀ x y : Hp, ⟪x, T y⟫_ℂ = ∫ p, (φ1 p.1 * φ2 p.2) * ⟪x, R p y⟫_ℂ ∂(μ1.prod μ2)) :
    T = P1 ∘L P2 ∧ T = P2 ∘L P1 := by
  have hint : ∀ x y : Hp, Integrable (fun p : G1 × G2 => (φ1 p.1 * φ2 p.2) * ⟪x, R p y⟫_ℂ) (μ1.prod μ2) := fun x y =>
    hφ.mul_bdd (c := ‖x‖ * ‖y‖) (hmeas x y) (Filter.Eventually.of_forall fun p => by
      refine le_trans (norm_inner_le_norm _ _) ?_
      rw [hU])
  constructor
  · ext y
    refine ext_inner_left ℂ fun x => ?_
    show ⟪x, T y⟫_ℂ = ⟪x, P1 (P2 y)⟫_ℂ
    rw [hT, integral_prod _ (hint x y), hP1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show ∫ k, (φ1 g * φ2 k) * ⟪x, R (g, k) y⟫_ℂ ∂μ2 = φ1 g * ⟪x, R (g, 1) (P2 y)⟫_ℂ
    rw [← ContinuousLinearMap.adjoint_inner_left, hP2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show (φ1 g * φ2 k) * ⟪x, R (g, k) y⟫_ℂ = φ1 g * (φ2 k * ⟪ContinuousLinearMap.adjoint (R (g, 1)) x, R (1, k) y⟫_ℂ)
    rw [ContinuousLinearMap.adjoint_inner_left]
    have : R (g, k) = R (g, 1) ∘L R (1, k) := by
      rw [← hmul]; simp
    rw [this]
    simp only [ContinuousLinearMap.comp_apply]
    ring
  · ext y
    refine ext_inner_left ℂ fun x => ?_
    show ⟪x, T y⟫_ℂ = ⟪x, P2 (P1 y)⟫_ℂ
    rw [hT, integral_prod_symm _ (hint x y), hP2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show ∫ g, (φ1 g * φ2 k) * ⟪x, R (g, k) y⟫_ℂ ∂μ1 = φ2 k * ⟪x, R (1, k) (P1 y)⟫_ℂ
    rw [← ContinuousLinearMap.adjoint_inner_left, hP1, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show (φ1 g * φ2 k) * ⟪x, R (g, k) y⟫_ℂ = φ2 k * (φ1 g * ⟪ContinuousLinearMap.adjoint (R (1, k)) x, R (g, 1) y⟫_ℂ)
    rw [ContinuousLinearMap.adjoint_inner_left]
    have : R (g, k) = R (1, k) ∘L R (g, 1) := by
      rw [← hmul]; simp
    rw [this]
    simp only [ContinuousLinearMap.comp_apply]
    ring

theorem pj_comm (R : G1 × G2 → (Hp →L[ℂ] Hp)) (hmul : ∀ g h, R (g * h) = R g ∘L R h)
    (φ2 : G2 → ℂ) (P2 : Hp →L[ℂ] Hp)
    (hP2 : ∀ x y : Hp, ⟪x, P2 y⟫_ℂ = ∫ k, φ2 k * ⟪x, R (1, k) y⟫_ℂ ∂μ2) (g : G1) :
    P2 ∘L R (g, 1) = R (g, 1) ∘L P2 := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  show ⟪x, P2 (R (g, 1) y)⟫_ℂ = ⟪x, R (g, 1) (P2 y)⟫_ℂ
  rw [hP2 x (R (g, 1) y), ← ContinuousLinearMap.adjoint_inner_left (R (g, 1)) (P2 y) x, hP2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  show φ2 k * ⟪x, R (1, k) (R (g, 1) y)⟫_ℂ = φ2 k * ⟪ContinuousLinearMap.adjoint (R (g, 1)) x, R (1, k) y⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left]
  have h1 : R (1, k) (R (g, 1) y) = (R (1, k) ∘L R (g, 1)) y := rfl
  have h2 : R (g, 1) (R (1, k) y) = (R (g, 1) ∘L R (1, k)) y := rfl
  rw [h1, h2, ← hmul, ← hmul]
  simp

end Two

section Three

variable {G1 : Type} {Hs L : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem pj_counted (σs : G1 → (Hs →L[ℂ] Hs)) (π1 : G1 → (L →L[ℂ] L)) (w0 : Hs) (P1 Re T : L →L[ℂ] L)
    (hP1 : IsStarProjection P1) (hRe : IsStarProjection Re) (hT1 : T = P1 ∘L Re) (hT2 : T = Re ∘L P1)
    (hrange : ((LinearMap.range (P1 : L →ₗ[ℂ] L) : Submodule ℂ L) : Set L) =
      {v | ∃ io : Hs →L[ℂ] L, (∀ g, io ∘L σs g = π1 g ∘L io) ∧ v = io w0})
    (hcomm : ∀ g, Re ∘L π1 g = π1 g ∘L Re)
    (hcyc : (Submodule.span ℂ (Set.range fun g => σs g w0)).topologicalClosure = ⊤)
    (Hm : Submodule ℂ (Hs →L[ℂ] L)) (hHm : ∀ Ψ, Ψ ∈ Hm ↔ ∀ g, Ψ ∘L σs g = π1 g ∘L Ψ) :
    IsStarProjection T ∧
      ∃ κ : (Hm.map ((ContinuousLinearMap.compL ℂ Hs L L Re) : (Hs →L[ℂ] L) →ₗ[ℂ] (Hs →L[ℂ] L))) ≃ₗ[ℂ]
          LinearMap.range (T : L →ₗ[ℂ] L),
        ∀ Φ, ((κ Φ : LinearMap.range (T : L →ₗ[ℂ] L)) : L) = (Φ : Hs →L[ℂ] L) w0 := by
  have hcm : Commute P1 Re := by
    show P1 * Re = Re * P1
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ← hT1, ← hT2]
  have hTP : IsStarProjection T := by
    rw [hT1]
    exact ⟨hP1.1.mul_of_commute hcm hRe.1, (hP1.2.commute_iff hRe.2).1 hcm⟩
  refine ⟨hTP, ?_⟩
  have hReRe : ∀ x, Re (Re x) = Re x := fun x => by
    have := hRe.1
    exact congrArg (fun A : L →L[ℂ] L => A x) this
  set E := Hm.map ((ContinuousLinearMap.compL ℂ Hs L L Re) : (Hs →L[ℂ] L) →ₗ[ℂ] (Hs →L[ℂ] L)) with hE
  have hmem : ∀ Φ : E, (Φ : Hs →L[ℂ] L) w0 ∈ LinearMap.range (T : L →ₗ[ℂ] L) := by
    rintro ⟨Φ, Ψ, hΨ, rfl⟩
    have h1 : Ψ w0 ∈ ((LinearMap.range (P1 : L →ₗ[ℂ] L) : Submodule ℂ L) : Set L) := by
      rw [hrange]
      exact ⟨Ψ, (hHm Ψ).1 hΨ, rfl⟩
    obtain ⟨u, hu⟩ := h1
    refine ⟨u, ?_⟩
    show T u = Re (Ψ w0)
    rw [hT2, ← hu]
    rfl
  let f : E →ₗ[ℂ] LinearMap.range (T : L →ₗ[ℂ] L) :=
    LinearMap.codRestrict _ (((ContinuousLinearMap.apply ℂ L w0 : (Hs →L[ℂ] L) →L[ℂ] L) :
      (Hs →L[ℂ] L) →ₗ[ℂ] L).comp E.subtype) hmem
  have hf : ∀ Φ : E, ((f Φ : LinearMap.range (T : L →ₗ[ℂ] L)) : L) = (Φ : Hs →L[ℂ] L) w0 := fun Φ => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨Φ, Ψ, hΨ, rfl⟩ h0
    have h0' : Re (Ψ w0) = 0 := congrArg Subtype.val h0
    apply Subtype.ext
    show (ContinuousLinearMap.compL ℂ Hs L L Re) Ψ = 0
    set Φ : Hs →L[ℂ] L := (ContinuousLinearMap.compL ℂ Hs L L Re) Ψ with hΦ
    have hle : Submodule.span ℂ (Set.range fun g => σs g w0) ≤ LinearMap.ker (Φ : Hs →ₗ[ℂ] L) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      show Re (Ψ (σs g w0)) = 0
      have a : Ψ (σs g w0) = π1 g (Ψ w0) := congrArg (fun A : Hs →L[ℂ] L => A w0) ((hHm Ψ).1 hΨ g)
      have b : Re (π1 g (Ψ w0)) = π1 g (Re (Ψ w0)) := congrArg (fun A : L →L[ℂ] L => A (Ψ w0)) (hcomm g)
      rw [a, b, h0', map_zero]
    have hcl := Submodule.topologicalClosure_minimal _ hle (ContinuousLinearMap.isClosed_ker Φ)
    rw [hcyc] at hcl
    ext x
    exact hcl (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ Hs))
  have hsurj : Function.Surjective f := by
    rintro ⟨v, u, hu⟩
    have hu' : T u = v := hu
    have h1 : v ∈ ((LinearMap.range (P1 : L →ₗ[ℂ] L) : Submodule ℂ L) : Set L) := by
      refine ⟨Re u, ?_⟩
      show P1 (Re u) = v
      rw [← hu', hT1]
      rfl
    rw [hrange] at h1
    obtain ⟨io, hio, hv⟩ := h1
    refine ⟨⟨(ContinuousLinearMap.compL ℂ Hs L L Re) io, Submodule.mem_map_of_mem ((hHm io).2 hio)⟩, ?_⟩
    apply Subtype.ext
    show Re (io w0) = v
    rw [← hv, ← hu', hT2]
    exact hReRe _
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun Φ => rfl⟩

end Three

end Formalism.MainNotions.LeviCoordinates

end
