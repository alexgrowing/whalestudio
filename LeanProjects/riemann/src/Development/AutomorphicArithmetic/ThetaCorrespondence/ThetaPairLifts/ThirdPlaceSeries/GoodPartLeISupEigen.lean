import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.FormsStep
theorem goodPart_le_iSup_eigen_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          V0T D T S In.rho In.chi In.θ i j b ⊓
            ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i),
              Module.End.eigenspace (hkT D T S In i j b k P)
                (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b hj1 hj2
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b hj1 hj2
  have ha := descend_actL D T S In i j b hj1 hj2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  refine (GlobalTheory.T.V0T_le_span_image_goodL D S In T i j b hj1 hj2 (eIdem_all D) Φ hc ha he hw).trans (Submodule.span_le.mpr ?_)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [SetLike.mem_coe]
  refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ (In.span j hj1 hj2 hx) ?_ ?_ ?_
  · intro σ y hy
    refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ hy ?_ ?_ ?_
    · intro hσ z hz
      refine Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ ?_)
      rw [Submodule.mem_inf] at hz ⊢
      refine ⟨descend_mem_V0T D T S In i j b Φ hc ha he z hz.1, ?_⟩
      have hz2 := hz.2
      simp only [Submodule.mem_iInf] at hz2 ⊢
      intro k P hkP
      have hPb : P ∉ In.Sb := fun hP => hkP.2.2.2 (by
        rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
        exact Or.inr (Finset.mem_coe.mpr (hSb hP)))
      exact descend_mem_eigenspace D T S In i j b hj1 hj2 Φ hc hf k P _ z (hz2 k P ⟨hkP.1, hkP.2.1, hkP.2.2.1, hPb⟩)
    · rw [map_zero]; exact zero_mem _
    · intro y z hy hz; rw [map_add]; exact add_mem hy hz
  · rw [map_zero]; exact zero_mem _
  · intro y z hy hz; rw [map_add]; exact add_mem hy hz
end GlobalTheory.HeightCounting.FormsStep
end
end
