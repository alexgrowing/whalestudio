import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

private theorem hasFinTrace_conj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) {A : V →ₗ[ℂ] V} {c : ℂ} (h : HasFinTrace A c) :
    HasFinTrace ((e : V →ₗ[ℂ] W) ∘ₗ A ∘ₗ (e.symm : W →ₗ[ℂ] V)) c := by
  obtain ⟨hfd, rfl⟩ := h
  set B : W →ₗ[ℂ] W := (e : V →ₗ[ℂ] W) ∘ₗ A ∘ₗ (e.symm : W →ₗ[ℂ] V) with hB
  have hr : (LinearMap.range A).map (e : V →ₗ[ℂ] W) = LinearMap.range B := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp [hB]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨A (e.symm y), ⟨_, rfl⟩, by simp [hB]⟩
  let f : LinearMap.range A ≃ₗ[ℂ] LinearMap.range B :=
    (e.submoduleMap (LinearMap.range A)).trans (LinearEquiv.ofEq _ _ hr)
  refine ⟨f.finiteDimensional, ?_⟩
  rw [← LinearMap.trace_conj' _ f]
  congr 1

private theorem isIntegralOp_tw {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {m : Measure G}
    {χ : G → ℂ} {τ τ₁ : SmIrr G} {e : τ.V ≃ₗ[ℂ] τ₁.V} (hT : TwOf χ τ τ₁ e) {f : G → ℂ} {A : τ.V →ₗ[ℂ] τ.V}
    (hA : IsIntegralOp m τ.ρ (fun g => f g * χ g) A) :
    IsIntegralOp m τ₁.ρ f ((e : τ.V →ₗ[ℂ] τ₁.V) ∘ₗ A ∘ₗ (e.symm : τ₁.V →ₗ[ℂ] τ.V)) := by
  intro w l
  have key : (fun g => f g * l (τ₁.ρ g w)) =
      fun g => f g * χ g * (l ∘ₗ (e : τ.V →ₗ[ℂ] τ₁.V)) (τ.ρ g (e.symm w)) := by
    funext g
    have := hT g (e.symm w)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, map_smul, map_smul, smul_eq_mul]
    simp [mul_assoc]
  obtain ⟨h₁, h₂⟩ := hA (e.symm w) (l ∘ₗ (e : τ.V →ₗ[ℂ] τ₁.V))
  rw [key]
  refine ⟨h₁, ?_⟩
  rw [← h₂]
  simp

private theorem isIntegralOp_untw {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {m : Measure G}
    {χ : G → ℂ} {τ τ₁ : SmIrr G} {e : τ.V ≃ₗ[ℂ] τ₁.V} (hT : TwOf χ τ τ₁ e) {f : G → ℂ} {B : τ₁.V →ₗ[ℂ] τ₁.V}
    (hB : IsIntegralOp m τ₁.ρ f B) :
    IsIntegralOp m τ.ρ (fun g => f g * χ g) ((e.symm : τ₁.V →ₗ[ℂ] τ.V) ∘ₗ B ∘ₗ (e : τ.V →ₗ[ℂ] τ₁.V)) := by
  intro v l
  have key : (fun g => f g * χ g * l (τ.ρ g v)) =
      fun g => f g * (l ∘ₗ (e.symm : τ₁.V →ₗ[ℂ] τ.V)) (τ₁.ρ g (e v)) := by
    funext g
    rw [← hT g v]
    simp [mul_assoc]
  obtain ⟨h₁, h₂⟩ := hB (e v) (l ∘ₗ (e.symm : τ₁.V →ₗ[ℂ] τ.V))
  rw [key]
  refine ⟨h₁, ?_⟩
  rw [← h₂]
  simp

theorem UpperTheory.Gal.InertialTypesAlt.G.trTw :
    UpperTheory.Gal.InertialTypesAlt.G.TrTw := by
  intro G _ _ _ m χ τ τ₁ e hT f z
  refine ⟨⟨?_, ?_⟩, fun I => ⟨?_, ?_⟩⟩
  · rintro ⟨A, hA, hF⟩
    exact ⟨_, isIntegralOp_tw hT hA, hasFinTrace_conj e hF⟩
  · rintro ⟨B, hB, hF⟩
    exact ⟨_, isIntegralOp_untw hT hB, hasFinTrace_conj e.symm hF⟩
  · rintro ⟨A, hA, hF⟩
    refine ⟨_, isIntegralOp_tw hT hA, ?_⟩
    convert hasFinTrace_conj e hF using 1
    ext x
    simp
  · rintro ⟨B, hB, hF⟩
    refine ⟨_, isIntegralOp_untw hT hB, ?_⟩
    convert hasFinTrace_conj e.symm hF using 1
    ext x
    simp
