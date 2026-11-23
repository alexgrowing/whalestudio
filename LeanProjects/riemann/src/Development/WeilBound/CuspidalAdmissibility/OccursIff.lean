import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.WeilBound.CuspidalAdmissibility.OccPair
import Development.WeilBound.CuspidalAdmissibility.OccTrace
import Development.WeilBound.CuspidalAdmissibility.CuspProjectionOrthogonality

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace PositivityTheory.TfC.OccursIff

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

section Items

theorem exists_integralOp_of_admissible {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
    (m : Measure G) [m.IsHaarMeasure] {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (hρ : GroundTheory.Automorphic.IsAdmissible ρ) (φ : G → ℂ) (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ) :
    ∃ A : X →ₗ[ℂ] X, (∀ (v : X) (l : Module.Dual ℂ X), Integrable (fun g => φ g * l (ρ g v)) m ∧
      l (A v) = ∫ g, φ g * l (ρ g v) ∂m) ∧ FiniteDimensional ℂ (LinearMap.range A) :=
  PositivityTheory.TfC.OccursIff.Trace.exists_integralOp m ρ hρ φ hφ hφc

theorem admissible_and_equiv_of_pairing {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ G X) (π : Representation ℂ G Y)
    (hσ : GroundTheory.Automorphic.IsSmooth σ) (hσi : σ.IsIrreducible)
    (hπ : GroundTheory.Automorphic.IsAdmissible π) (hπi : π.IsIrreducible)
    (B : X →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hB : ∀ g x y, B (σ g x) (π g y) = B x y) (hB0 : B ≠ 0)
    (C : Y →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hC : ∀ g x y, C (π g x) (π g y) = C x y) (hC0 : C ≠ 0) :
    GroundTheory.Automorphic.IsAdmissible σ ∧ Nonempty (σ.Equiv π) :=
  PositivityTheory.TfC.OccursIff.Pair.admissible_and_equiv σ π hσ hσi hπ hπi B hB hB0 C hC hC0

theorem exists_localComponent_family (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n))
    [μ.IsHaarMeasure] (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)))
    (hle : V ≤ cuspidalL2 μ) (hcl : IsClosed (V : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))))
    (hinv : (rightRegularRep (rationalGLOne K n) μ).IsInvariant V) (hne : V ≠ ⊥)
    (hirr : ∀ V' ≤ V, IsClosed (V' : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))) →
      (rightRegularRep (rationalGLOne K n) μ).IsInvariant V' → V' = ⊥ ∨ V' = V)
    (w : HeightOneSpectrum (𝓞 K)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (π : Representation ℂ (GL (Fin n) (w.adicCompletion K)) W),
      GroundTheory.Automorphic.IsAdmissible π ∧ π.IsIrreducible ∧
      ∃ F : Set (W →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)),
        (∀ f ∈ F, (∀ x, f x ∈ V) ∧ ∀ g x, f (π g x) =
          rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) (f x)) ∧
        ∀ u ∈ V, u ≠ 0 → ∃ f ∈ F, ∃ x, inner ℂ (f x) u ≠ 0 :=
  PositivityTheory.TfC.CuspProjectionOrthogonality.occ_loccomp K n μ V hle hcl hinv hne hirr w

end Items

theorem isSmooth_of_smIrr {G : Type} [Group G] [TopologicalSpace G] (σ : GlobalTheory.CuspRep.SmIrr G) :
    GroundTheory.Automorphic.IsSmooth σ.ρ := fun v => σ.smooth v

def pairL {X Y H : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (f' : X →ₗ[ℂ] H) (f : Y →ₗ[ℂ] H) : X →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => inner ℂ (f y) (f' x))
    (fun x x' y => by simp)
    (fun c x y => by simp)
    (fun x y y' => by simp)
    (fun c x y => by simp [mul_comm])

theorem pairL_apply {X Y H : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (f' : X →ₗ[ℂ] H) (f : Y →ₗ[ℂ] H) (x : X) (y : Y) :
    pairL f' f x y = inner ℂ (f y) (f' x) := rfl

theorem pairL_invariant {G G' X Y H : Type} [Group G] [Group G'] [TopologicalSpace G'] [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : UnitaryRep G' H) (h : G → G') (σ : Representation ℂ G X) (π : Representation ℂ G Y)
    (f' : X →ₗ[ℂ] H) (f : Y →ₗ[ℂ] H) (hf' : ∀ g x, f' (σ g x) = R (h g) (f' x))
    (hf : ∀ g y, f (π g y) = R (h g) (f y)) (g : G) (x : X) (y : Y) :
    pairL f' f (σ g x) (π g y) = pairL f' f x y := by
  rw [pairL_apply, pairL_apply, hf, hf']
  exact UnitaryRep.inner_map_map _ _ _ _

theorem rhoL_def (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (g : GL (Fin n) (w.adicCompletion K))
    (v : LL μ) :
    rhoL μ w g v = rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v :=
  rfl

end PositivityTheory.TfC.OccursIff

open PositivityTheory.TfC.OccursIff in
theorem PositivityTheory.TfC.OccursBasics_holds : UpperTheory.ConvolutionTheory.C.OccursBasics := by
  intro K _ _ n μ _ V w _ _ m _ hV
  obtain ⟨W, _, _, π, hπ, hπi, F, hF, hdense⟩ :=
    exists_localComponent_family K n μ V hV.le hV.closed hV.inv hV.ne_bot hV.irred w

  have key : ∀ σ : GlobalTheory.CuspRep.SmIrr (Gw n w), Occurs μ V w σ →
      GroundTheory.Automorphic.IsAdmissible σ.ρ ∧ Nonempty (σ.ρ.Equiv π) := by
    rintro σ ⟨f', hf'0, hf'V, hf'eq⟩
    obtain ⟨x₀, hx₀⟩ : ∃ x, f' x ≠ 0 := by
      by_contra h
      exact hf'0 (LinearMap.ext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
    obtain ⟨f, hfF, z, hz⟩ := hdense (f' x₀) (hf'V x₀) hx₀
    have hfz : f z ≠ 0 := fun h => hz (by rw [h, inner_zero_left])
    refine admissible_and_equiv_of_pairing σ.ρ π (isSmooth_of_smIrr σ) σ.irred hπ hπi (pairL f' f) ?_ ?_
      (pairL f f) ?_ ?_
    · exact pairL_invariant (rightRegularRep (rationalGLOne K n) μ)
        (fun g => MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) σ.ρ π f' f
        (fun g x => (hf'eq g x).trans (rhoL_def μ w g _)) (hF f hfF).2
    · intro h
      apply hz
      have := LinearMap.congr_fun (LinearMap.congr_fun h x₀) z
      simpa [pairL_apply] using this
    · exact pairL_invariant (rightRegularRep (rationalGLOne K n) μ)
        (fun g => MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) π π f f
        (hF f hfF).2 (hF f hfF).2
    · intro h
      apply hfz
      have := LinearMap.congr_fun (LinearMap.congr_fun h z) z
      rw [pairL_apply, LinearMap.zero_apply, LinearMap.zero_apply, inner_self_eq_zero] at this
      exact this
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
    obtain ⟨f, hfF, z, hz⟩ := hdense u hu hu0
    refine ⟨⟨W, π, fun v => hπ.1 v, hπi⟩, f, ?_, (hF f hfF).1, fun g x => (hF f hfF).2 g x⟩
    intro h
    apply hz
    rw [h, LinearMap.zero_apply, inner_zero_left]
  · intro σ σ' h h'
    obtain ⟨-, ⟨e⟩⟩ := key σ h
    obtain ⟨-, ⟨e'⟩⟩ := key σ' h'
    exact ⟨e.trans e'.symm⟩
  · intro σ h φ hφ
    obtain ⟨A, hA, hAf⟩ := exists_integralOp_of_admissible m σ.ρ (key σ h).1 φ hφ.1 hφ.2
    exact ⟨_, A, hA, hAf, rfl⟩
