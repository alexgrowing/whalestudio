import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.ProvedMore
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesMore
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs
open GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.LocGL.SupportRing

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

open PositivityTheory.Rg.BcB.F

theorem zpr : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  PositivityTheory.Prw.zelevinskyPolynomialRing_of PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
    PositivityTheory.RgGu.segmentRepresentation
    (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg PositivityTheory.RgGu.segmentRepresentation)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem clsGL_smIrr {m : ℕ} (σ : SmIrr (GL (Fin m) k)) :
    ∀ h, clsGL σ.ρ h = Finsupp.single (IrrGL.of σ.ρ σ.smooth σ.irred) 1 :=
  fun h => clsGL_irr ⟨_, σ.ρ, σ.smooth, σ.irred⟩ h

end Local

theorem cls_locProd {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    {A : Type 1} [CommRing A] {Ψ : GrothGL (w.adicCompletion E) ≃+ A} (hΨ : IsProductIso (w.adicCompletion E) Ψ)
    (X : Pre E n) :
    ∃ hp, Ψ (clsGL (locProd X.h w (X.σ · w)) hp) = ∏ i, Ψ (Finsupp.single (X.cls i w) 1) := by
  obtain ⟨hp, ep⟩ := multiProd_cls hΨ X.h (fun i => (X.σ i w).ρ) (fun i => (X.σ i w).smooth)
    (fun i => (⟨_, (X.σ i w).ρ, (X.σ i w).smooth, (X.σ i w).irred⟩ : IrrRep _).hasFiniteLength)
  exact ⟨hp, ep.trans (Finset.prod_congr rfl fun i _ => congrArg Ψ (clsGL_smIrr _ _))⟩

theorem permSub : PermSub := by
  intro E _ _ _ n D D' e w he P hP
  obtain ⟨-, Ψ, -, hΨ, -⟩ := zpr (w.adicCompletion E)
  obtain ⟨h1, e1⟩ := cls_locProd w hΨ D
  obtain ⟨h2, e2⟩ := cls_locProd w hΨ D'
  have hc : clsGL (locProd D.h w (D.σ · w)) h1 = clsGL (locProd D'.h w (D'.σ · w)) h2 := by
    apply Ψ.injective
    rw [e1, e2]
    exact Fintype.prod_equiv e _ _ fun i => congrArg (fun x => Ψ (Finsupp.single x 1)) (he i)
  refine isSubquotient_of_clsGL_ne h1 P.smooth P.irred ?_
  rw [hc]
  exact (clsGL_of_pos h2 P.smooth P.irred hP).ne'

theorem sat_of_cls {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m m' : ℕ}
    (σ : SmIrr (GL (Fin m) (w.adicCompletion E))) (σ' : SmIrr (GL (Fin m') (w.adicCompletion E)))
    (h : IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.of σ'.ρ σ'.smooth σ'.irred) (b : Multiset ℂˣ)
    (hb : GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w m) ∧ GlobalTheory.LFun.HasSatGL w σ.ρ b) :
    GlobalTheory.LGrp.IsSpherical σ'.ρ (GlobalTheory.LFun.KGL w m') ∧ GlobalTheory.LFun.HasSatGL w σ'.ρ b := by
  have hm : m = m' := congrArg Sigma.fst h
  subst hm
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h
  have he : ∀ g x, φ.toLinearEquiv (σ.ρ g x) = σ'.ρ g (φ.toLinearEquiv x) :=
    fun g x => Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g x
  exact ⟨GlobalTheory.BaseChangeBridge.isSpherical_of_equiv φ.toLinearEquiv he hb.1,
    GlobalTheory.BaseChangeBridge.hasSatGL_of_equiv φ.toLinearEquiv he hb.2⟩

theorem permSat : PermSat := by
  intro E _ _ _ n D D' e w he B hB
  obtain ⟨b, hb, hs⟩ := hB
  refine ⟨fun j => b (e.symm j), fun j => sat_of_cls (D.σ (e.symm j) w) (D'.σ j w) ?_ _ (hb (e.symm j)), ?_⟩
  · have h := he (e.symm j)
    rw [e.apply_symm_apply] at h
    exact h
  · exact (Fintype.sum_equiv e.symm _ _ fun _ => rfl).trans hs

end PositivityTheory.Rg.BcB.F.Rig

end
