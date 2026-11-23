import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverRestrictionBaseChangeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PD GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

theorem sortSign_id' {ι : Type} [LinearOrder ι] (t : Finset ι) : sortSign (id : ι → ι) t = 1 := by
  unfold sortSign
  refine Finset.prod_eq_one fun a _ ↦ Finset.prod_eq_one fun b _ ↦ if_neg ?_
  rintro ⟨h₁, h₂⟩
  exact lt_asymm h₁ h₂

theorem cechHEquivCohOn_cechCubeMapOver {X Y : Scheme.{0}} (g : Y ⟶ X) (ι : Type) [LinearOrder ι]
    [Finite ι] (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] (S : Type) [CommRing S]
    [Algebra S Γ(Y, ⊤)] (σ : R →+* S)
    (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (V : X.Opens) (U : ι → X.Opens) (hc : V ≤ ⨆ i, U i) (hc' : g ⁻¹ᵁ V ≤ ⨆ i, g ⁻¹ᵁ U i)
    (F : X.Modules) (G : Y.Modules) (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)
    (hF : CechAcyclicMod V U F) (hG : CechAcyclicMod (g ⁻¹ᵁ V) (fun i ↦ g ⁻¹ᵁ U i) G) (n : ℕ)
    (y : cechH R F V U n) :
    cohOn.pull hσ φ (le_refl (g ⁻¹ᵁ V)) n (cechHEquivCohOn R hc hF n y) =
      cechHEquivCohOn S hc' hG n ((cechCubeMapOver V U hσ φ).homology n y) := by
  obtain ⟨z, rfl⟩ := cechClass_surjective (cechCube R F V U) n y
  have hτ : ∀ t : Finset ι, cechOpen (g ⁻¹ᵁ V) (fun i ↦ g ⁻¹ᵁ U i) t ≤
      g ⁻¹ᵁ cechOpen V U (t.image id) := fun t ↦ by
    rw [Finset.image_id]
    exact (preimage_cechOpen g V U t).ge
  have key : ∀ (t : {s : Finset ι // s.card = n + 1}) (u : Finset ι) (hu : u.card = n + 1)
      (h : cechOpen (g ⁻¹ᵁ V) (fun i ↦ g ⁻¹ᵁ U i) t.1 ≤ g ⁻¹ᵁ cechOpen V U u), u = t.1 →
      (((cechCubeMapOver V U hσ φ).cocycle (n + 1) z).1 t :
        sectionsOn G (cechOpen (g ⁻¹ᵁ V) (fun i ↦ g ⁻¹ᵁ U i) t.1)) =
        sectionsOn.res S G h (sectionsOn.mapOver hσ φ (cechOpen V U u)
          (z.1 ⟨u, hu⟩ : sectionsOn F (cechOpen V U u))) := by
    rintro ⟨t, ht⟩ u hu h rfl
    rfl
  refine Eq.trans ?_ (congrArg (cechHEquivCohOn S hc' hG n)
    ((cechCubeMapOver V U hσ φ).homology_cechClass n z)).symm
  refine (GlobalTheory.T.cover_restriction_base_change g ι ι R S σ hσ V (g ⁻¹ᵁ V) U (fun i ↦ g ⁻¹ᵁ U i) hc hc' le_rfl id hτ F G φ
    hF hG n z ((cechCubeMapOver V U hσ φ).cocycle (n + 1) z) (fun t ht ↦ ?_) (fun t ht ↦ ?_)).symm
  · rw [sortSign_id', one_smul]
    exact key t _ ht (hτ t.1) Finset.image_id
  · exact absurd (by rw [Finset.image_id]; exact t.2) ht

theorem cech_holds : P_cech := by
  intro k k' _ _ _ X X' s s' g hg a b _ _ n U hc hU hc' hU'
  letI := algΓ s
  letI := algΓ s'
  intro y
  exact cechHEquivCohOn_cechCubeMapOver g (Fin n) k k' (algebraMap k k') (appTop_algebraMapS hg) ⊤ U
    hc.ge hc'.ge (Omega s a) (Omega s' a) (omegaPullS hg a)
    (cechAcyclicMod_top_of_isAffineOpen hU _) (cechAcyclicMod_top_of_isAffineOpen hU' _) b y

end PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

end
