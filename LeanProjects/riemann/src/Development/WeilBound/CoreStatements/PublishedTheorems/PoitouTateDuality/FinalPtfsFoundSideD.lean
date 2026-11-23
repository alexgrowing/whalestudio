import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsFoundSideC

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion PositivityTheory.LocalTateOrthogonality.Gcoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxSynthPendingDepth 1

theorem exists_cocycle_of_dn {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] (rho : Representation R G M) (e : M →+ A.V)
    (he : ∀ g m, e (rho g m) = A.ρ g (e m)) (f : (Fin 2 → G) → M)
    (hlc : IsLocallyConstant fun s => e (f s)) (hdn : ∀ s, dn rho 2 f s = 0) :
    ∃ x : cocycles A 2, ∀ s, cochainOf A (cocycleι A 2 x) s = e (f s) := by
  have hd0 : (inhomogeneousCochains.d A 2).hom (fun s => e (f s)) = 0 := by
    refine (d_comp_homF rho A e he 2 f).trans ?_
    funext s
    exact (congrArg e (hdn s)).trans (map_zero e)
  obtain ⟨x, hx⟩ := exists_coc A 2 _ hlc hd0
  exact ⟨x, fun s => congrFun hx s⟩

section Local

variable {Kf : FiniteSubfield} [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
  {S : Set (HeightOneSpectrum (𝓞 Kf.1))} [Fintype S] {l r : ℕ} [Fact l.Prime]
  {ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)}
  {v : S} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[(v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A}

set_option maxHeartbeats 1000000 in

theorem exists_root_of_unity_preimage
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (l ^ r))
    (u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))
    (hu : ((((u : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ)
    {y : AlgebraicClosure ℚ} (hy0 : y ≠ 0) (κ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hκ : ∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y)
    (χ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hχadd : ∀ σ τ : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[(v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)), χ (ev (σ * τ)) = χ (ev σ) + χ (ev τ))
    (hχlc : IsLocallyConstant fun σ : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[(v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) => χ (ev σ)) :
    ∃ x0 : cocycles (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) 2,
      ∀ s, cochainOf _ (cocycleι _ 2 x0) s = rvF S u (κ (ev (s 0)) * χ (ev (s 1))) := by
  let e : ZMod (l ^ r) →+ (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))).V := rvF S u
  have hlc : IsLocallyConstant fun s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[(v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) => e (κ (ev (s 0)) * χ (ev (s 1))) := by
    have h0 := (kummer_ev_isLocallyConstant hev hζ hy0 κ hκ).comp_continuous
      (continuous_apply (A := fun _ : Fin 2 => (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[(v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) 0)
    have h1 := hχlc.comp_continuous (continuous_apply (A := fun _ : Fin 2 => (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[(v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) 1)
    exact h0.comp₂ h1 (fun a b => e (a * b))
  let rhoV : Representation (ZMod (l ^ r)) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[(v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) (ZMod (l ^ r)) :=
    (muLoc Kf.1 l r A).comp ev.toMonoidHom
  have hrho : ∀ σ m, rhoV σ m = ((cycMod Kf.1 (AlgebraicClosure ℚ) l r ((ev σ : Dec (F := Kf.1) A) :
      G Kf.1 (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m := fun σ m => rfl
  have heq : ∀ σ m, e (rhoV σ m) = (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))).ρ σ (e m) := fun σ m =>
    (congrArg (rvF S u) (hrho σ m)).trans (rvF_act hev hζ u hu σ m)
  have hdn : ∀ s, dn rhoV 2 (fun t => κ (ev (t 0)) * χ (ev (t 1))) s = 0 := by
    intro s
    refine (dn_two rhoV (fun p => κ (ev p.1) * χ (ev p.2)) s).trans ?_
    have hκev : ∀ a b, κ (ev (a * b)) = κ (ev a) + ((cycMod Kf.1 (AlgebraicClosure ℚ) l r
        ((ev a : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
        κ (ev b) := fun a b => by
      rw [map_mul]; exact kummer_coc hζ hy0 κ hκ _ _
    simp only [hrho, hκev, hχadd]
    ring
  haveI : IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) := isDiscreteRep_res_gsRoots S ιs (l ^ r) v
  exact exists_cocycle_of_dn (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) rhoV e heq _ hlc hdn

end Local

end PositivityTheory.Lit1.PTN
