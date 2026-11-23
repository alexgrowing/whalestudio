import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsSha
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH1BijectiveOfInverse
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH2BijectiveOfInverse
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementD

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GroundTheory.ProfCoh CategoryTheory

namespace PositivityTheory.Lit1.PTN

theorem addEquiv_of_resCmp {R ι H C : Type} [CommRing R] [AddCommGroup H] [Module R H]
    [AddCommGroup C] {Hv Cv : ι → Type} [∀ v, AddCommGroup (Hv v)] [∀ v, AddCommGroup (Cv v)]
    (res : ∀ v, H →+ Hv v) (pres : ∀ v, C →+ Cv v) (E : H ≃+ C) (Ev : ∀ v, Hv v ≃+ Cv v)
    (h : ∀ v x, Ev v (res v x) = pres v (E x)) (U : Submodule R H) (T : AddSubgroup C)
    (hU : ∀ x, x ∈ U ↔ ∀ v, res v x = 0) (hT : ∀ y, y ∈ T ↔ ∀ v, pres v y = 0) :
    Nonempty (U ≃+ T) :=
  _root_.UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv.main res pres E Ev h U T hU hT

section FoundSide

attribute [local instance 2000] Rep.hV2

theorem mem_ptSha_iff' {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
    [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (A : Rep.{0} (ULift.{0} ℤ) G)
    [IsDiscreteRep A] (n : ℕ) (x : cohomology A n) : x ∈ ptSha φ A n ↔ ∀ v, ptRes φ A v n x = 0 := by
  rw [mem_ptSha, funext_iff]
  rfl

set_option maxHeartbeats 1000000 in
theorem shaIso_of_rep (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
    (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v))
    (hevc : ∀ v, Continuous (ev v) ∧ Continuous (ev v).symm)
    (hev : ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ)
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))))
    [IsDiscreteRep A] (eM : M ≃+ A.V) (hM : ∀ g m, eM (rho g m) = A.ρ (e g) (eM m)) :
    Nonempty (Sha1 rho (locFam S Av) (continuous_locFam S Av) ≃+
        ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 1) ∧
    Nonempty (Sha2 rho (locFam S Av) (continuous_locFam S Av) ≃+
        ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 2) := by
  have hT : ∀ n (y : cohomology A n), y ∈ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A n ↔
      ∀ v : S, ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v n y = 0 := by
    intro n y
    exact (mem_ptSha_iff' (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A n y).trans
      ⟨fun h v => h ⟨v.1, Finset.mem_coe.2 v.2⟩, fun h w => h ⟨w.1, Finset.mem_coe.1 w.2⟩⟩
  obtain ⟨E1, Ev1, h1⟩ := resCmp1' e (locFam S Av) (continuous_locFam S Av)
    (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) ev (fun v => (hevc v).1) (fun v => (hevc v).2) hev rho hc A eM hM
  obtain ⟨E2, Ev2, h2⟩ := resCmp2B e (locFam S Av) (continuous_locFam S Av)
    (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) ev (fun v => (hevc v).1) (fun v => (hevc v).2) hev rho hc A eM hM
  have hU1 : ∀ x, x ∈ Sha1 rho (locFam S Av) (continuous_locFam S Av) ↔
      ∀ v, (resH1 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom x = 0 := by
    intro x
    simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have hU2 : ∀ x, x ∈ Sha2 rho (locFam S Av) (continuous_locFam S Av) ↔
      ∀ v, (resH2 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom x = 0 := by
    intro x
    simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  exact ⟨addEquiv_of_resCmp
      (fun v => (resH1 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom)
      (fun v => ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v 1) E1 Ev1 h1 _ _ hU1 (hT 1),
    addEquiv_of_resCmp
      (fun v => (resH2 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom)
      (fun v => ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v 2) E2 Ev2 h2 _ _ hU2 (hT 2)⟩

end FoundSide

end PositivityTheory.Lit1.PTN
