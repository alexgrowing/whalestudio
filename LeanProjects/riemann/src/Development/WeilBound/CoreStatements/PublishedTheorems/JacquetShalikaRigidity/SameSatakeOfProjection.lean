import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.WeilBound.CoreStatements.RegularisedThetaMirabolic.KFiniteCuspForms.CuspSp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemL2OfBoundedContinuousInvariant
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyMemFixed

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open scoped InnerProductSpace

open PositivityTheory.jumpWindows

namespace PositivityTheory.AdelicQuotientData.QORTX

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

variable (μ) in

def rhoL (w : Pl E) : Representation ℂ (GL (Fin a) (w.adicCompletion E)) (L2 (latticeGL E a) μ) :=
  (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp (R (latticeGL E a) μ)).comp ((finGL E a).comp (locGL E a w))

theorem rhoL_apply (w : Pl E) (g : GL (Fin a) (w.adicCompletion E)) (v : L2 (latticeGL E a) μ) :
    rhoL μ w g v = R (latticeGL E a) μ (finGL E a (locGL E a w g)) v := rfl

theorem toL2ₗ_locRep {π : CuspSub E a} (hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1) (w : Pl E)
    (g : GL (Fin a) (w.adicCompletion E)) (x : π.V) :
    toL2ₗ μ π.V hm (π.locRep w g x) = rhoL μ w g (toL2ₗ μ π.V hm x) :=
  (R_toL2ₗ hm x (π.stable (.fin _) _ x.2)).symm

theorem kFinite_L2_projection {π : CuspSub E a} (hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1)
    {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : IsSubrep (R (latticeGL E a) μ) H) [H.HasOrthogonalProjection]
    {F : L2 (latticeGL E a) μ} (hF : F ∈ classes π.V μ) : IsKFinL2 μ (H.starProjection F) := by
  have hK := isKFinL2_of_mem_classes hm hF
  have hc : ∀ g v, H.starProjection (R (latticeGL E a) μ g v) = R (latticeGL E a) μ g (H.starProjection v) :=
    fun g v => hH.starProjection_apply (isUnitaryRep_R (latticeGL E a) μ) g v
  refine ⟨?_, ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro k hk
    refine ⟨(fun s => k⁻¹ * s) ⁻¹' {s | R (latticeGL E a) μ (finGL E a s) F = F}, fun s hs => ?_,
      hK.1.preimage (continuous_const.mul continuous_id), by
        simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]⟩
    have hs' : R (latticeGL E a) μ (finGL E a (k⁻¹ * s)) F = F := hs
    have e : s = k * (k⁻¹ * s) := by group
    change R (latticeGL E a) μ (finGL E a s) (H.starProjection F) = H.starProjection F
    rw [e, map_mul, map_mul, ContinuousLinearMap.mul_apply, ← hc, hs']
    exact hk
  · have := hK.2
    have e : (Set.range fun k : Kinf E a => R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (H.starProjection F)) =
        (H.starProjection : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) ''
          Set.range fun k : Kinf E a => R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun k => (hc _ F).symm)
    rw [e, Submodule.span_image]
    infer_instance

theorem same_satake_of_projection {π : CuspSub E a} (hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1)
    {H : Submodule ℂ (L2 (latticeGL E a) μ)}
    (hH : IsSubrep (R (latticeGL E a) μ) H) {π' : CuspSub E a} (h' : IsFinitePartOf μ π' H)
    (hne : ∃ F ∈ classes π.V μ, F ∉ Hᗮ) : SameSat π π' := by
  have := hH.completeSpace
  obtain ⟨F, hF, hFn⟩ := hne
  obtain ⟨x0, hx0F⟩ := (range_toL2ₗ hm).ge hF
  have hP0 : H.starProjection (toL2ₗ μ π.V hm x0) ≠ 0 := fun e =>
    hFn (hx0F ▸ (Submodule.starProjection_apply_eq_zero_iff H).1 e)
  have hk : IsKFinL2 μ (H.starProjection (toL2ₗ μ π.V hm x0)) :=
    kFinite_L2_projection hm hH ((range_toL2ₗ hm).le ⟨x0, rfl⟩)
  obtain ⟨y0, hy0⟩ := (range_toL2ₗ h'.finitePartMemL2).ge (h'.kfin _ (H.starProjection_apply_mem _) hk)
  have hc : ∀ g v, H.starProjection (R (latticeGL E a) μ g v) = R (latticeGL E a) μ g (H.starProjection v) :=
    fun g v => hH.starProjection_apply (isUnitaryRep_R (latticeGL E a) μ) g v
  have hinj : Function.Injective (toL2ₗ μ π'.V h'.finitePartMemL2) :=
    toL2ₗ_injective h'.finitePartMemL2 fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (π'.cusp ψ hψ).1.level
  filter_upwards [GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π,
    GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π',
    GlobalTheory.CuspRep.AeFix.eventually_mem_fixed E a π x0] with w hB hB' hw
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B', hB'⟩ := hB'
  refine ⟨B, hB, ?_⟩
  have hx0 : x0 ≠ 0 := fun e => hP0 (by rw [e, map_zero, map_zero])
  have h1 : IsSatVecGL w (π.locRep w) x0 B := hB.2 x0 hw hx0
  have h2 := h1.map ((H.starProjection : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) ∘ₗ toL2ₗ μ π.V hm)
    (ρ' := rhoL μ w) (fun g y => by
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [toL2ₗ_locRep, rhoL_apply, rhoL_apply, hc]) hP0
  have h2' : IsSatVecGL w (rhoL μ w) (toL2ₗ μ π'.V h'.finitePartMemL2 y0) B := by
    rw [hy0]; exact h2
  have h3 := IsSatVecGL.of_map (toL2ₗ μ π'.V h'.finitePartMemL2) (fun g y => toL2ₗ_locRep h'.finitePartMemL2 w g y) hinj h2'
  have e := h3.unique (hB'.2 y0 h3.2.1 h3.1)
  subst e
  exact hB'

theorem memL2_of_normalised_alt {π : CuspSub E a} (hπ : IsNormalised π) : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1 := by
  intro φ hφ
  obtain ⟨C, hC⟩ := GlobalTheory.Published.CuspFormsBoundedGL.of_invariant RfCs.cuspidalSpectrumGL.2.2 (π.cusp φ hφ) (hπ φ hφ)
  exact GlobalTheory.CompanionTheory.CuspInvariant.memL2_of_bounded_continuous_invariant μ (ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level)
    (leftInv_latticeGL (π.cusp φ hφ).1.left (hπ φ hφ)) hC

theorem sameSat_of_not_perp {π : CuspSub E a} (hπ : IsNormalised π) {H : Submodule ℂ (L2 (latticeGL E a) μ)}
    (hH : IsSubrep (R (latticeGL E a) μ) H) {π' : CuspSub E a} (h' : IsFinitePartOf μ π' H)
    (hne : ∃ F ∈ classes π.V μ, F ∉ Hᗮ) : SameSat π π' :=
  same_satake_of_projection (memL2_of_normalised_alt hπ) hH h' hne

end PositivityTheory.AdelicQuotientData.QORTX

end
