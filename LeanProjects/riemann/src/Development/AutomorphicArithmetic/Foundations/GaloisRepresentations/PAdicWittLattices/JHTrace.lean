import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.G3.HeckeTraceSheaves

section Two
variable {k k' : Type} [CommRing k] [CommRing k'] {φ : k →+* k'}

private theorem omegaPullS_app_toOm {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
    (hg : g ≫ s = s' ≫ spMap φ) (j : ℕ) (U : X.Opens) (x : OmU s U j) :
    (omegaPullS hg j).app U (toOm s j U x) = toOm s' j (g ⁻¹ᵁ U) (formPullS hg U j x) :=
  omegaPullS_toOmega hg j U x

private theorem formRes_formPullS_eq {X Y' : Scheme.{0}} {s : X ⟶ Sp k} {r' : Y' ⟶ Sp k'} {u v : Y' ⟶ X}
    (w : u = v) (hu : u ≫ s = r' ≫ spMap φ) (hv : v ≫ s = r' ≫ spMap φ) (U : X.Opens)
    (hle : v ⁻¹ᵁ U ≤ u ⁻¹ᵁ U) (j : ℕ) (x : OmU s U j) :
    formRes r' hle j (formPullS hu U j x) = formPullS hv U j x := by
  subst w
  have h := formRes_refl r' (u ⁻¹ᵁ U) (formPullS hu U j x)
  rw [h]

end Two

section Sheaf

variable {k k' : Type} [CommRing k] [CommRing k'] {φ : k →+* k'}
  {X X' Y Y' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
  {r : Y ⟶ Sp k} {r' : Y' ⟶ Sp k'} {e : Y' ⟶ Y} {f : Y ⟶ X} {f' : Y' ⟶ X'}

private def mid (he : e ≫ r = r' ≫ spMap φ) (w : e ≫ f = f' ≫ g) (a : ℕ) :
    (Scheme.Modules.pushforward f).obj (Omega r a) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f').obj (Omega r' a)) :=
  (Scheme.Modules.pushforward f).map (omegaPullS he a) ≫
    (Scheme.Modules.pushforwardComp e f).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr w).hom.app _ ≫
        (Scheme.Modules.pushforwardComp f' g).inv.app _

private theorem mid_app (he : e ≫ r = r' ≫ spMap φ) (w : e ≫ f = f' ≫ g) (a : ℕ) (U : X.Opens)
    (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U))
    (y : Γ((Scheme.Modules.pushforward f).obj (Omega r a), U)) :
    (mid he w a).app U y = (Omega r' a).presheaf.map (homOfLE hle).op
      ((omegaPullS he a).app (f ⁻¹ᵁ U) y) := by
  simp [mid]
  rfl

private theorem mid_form (hg : g ≫ s = s' ≫ spMap φ) (he : e ≫ r = r' ≫ spMap φ)
    (hf : f ≫ s = r) (hf' : f' ≫ s' = r') (w : e ≫ f = f' ≫ g) (a : ℕ) (U : X.Opens)
    (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b' : Sec r (f ⁻¹ᵁ U)) (x : OmU s U a) :
    (mid he w a).app U (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x)) =
      toOm r' a (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b') •
        formPull hf' (g ⁻¹ᵁ U) a (formPullS hg U a x)) := by
  have hu : (e ≫ f) ≫ s = r' ≫ spMap φ := by rw [Category.assoc, hf, he]
  have hu' : (f' ≫ g) ≫ s = r' ≫ spMap φ := by
    rw [Category.assoc, hg, ← Category.assoc, hf']
  have key : formRes r' hle a (formPullS he (f ⁻¹ᵁ U) a (formPull hf U a x)) =
      formPull hf' (g ⁻¹ᵁ U) a (formPullS hg U a x) :=
    ((congrArg (formRes r' hle a) (formPullS_formPull hf he hu U a x)).trans
      (formRes_formPullS_eq w hu hu' U hle a x)).trans (formPull_formPullS hg hf' hu' U a x).symm
  refine (mid_app he w a U hle _).trans ?_
  rw [omegaPullS_app_toOm, res_toOm, formPullS_smul, formRes_smul, key]

private theorem sheaf_lhs [IsFinite f] [Etale f] (hg : g ≫ s = s' ≫ spMap φ) (hf : f ≫ s = r)
    (a : ℕ) {U : X.Opens} (hU : IsAffineOpen U) (b' : Sec r (f ⁻¹ᵁ U)) (x : OmU s U a) :
    (omegaTrace hf a ≫ omegaPullS hg a).app U (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x)) =
      toOm s' a (g ⁻¹ᵁ U) (appSecS s s' g U (secTrace s r hU b') • formPullS hg U a x) := by
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaPullS hg a).app U
    ((omegaTrace hf a).app U (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x))) = _
  rw [omegaTrace_toOm_smul_formPull hf a hU, omegaPullS_app_toOm, formPullS_smul]

private theorem sheaf_rhs [IsFinite f'] [Etale f'] (hg : g ≫ s = s' ≫ spMap φ)
    (he : e ≫ r = r' ≫ spMap φ) (hf : f ≫ s = r) (hf' : f' ≫ s' = r') (w : e ≫ f = f' ≫ g)
    (a : ℕ) {U : X.Opens} (hV : IsAffineOpen (g ⁻¹ᵁ U))
    (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b' : Sec r (f ⁻¹ᵁ U)) (x : OmU s U a) :
    (mid he w a ≫ (Scheme.Modules.pushforward g).map (omegaTrace hf' a)).app U
        (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x)) =
      toOm s' a (g ⁻¹ᵁ U) (secTrace s' r' hV (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b')) •
        formPullS hg U a x) := by
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaTrace hf' a).app (g ⁻¹ᵁ U) ((mid he w a).app U
    (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x))) = _
  rw [mid_form hg he hf hf' w a U hle, omegaTrace_toOm_smul_formPull hf' a hV]

private theorem sheaf_id [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] [IsAffineHom g]
    (hg : g ≫ s = s' ≫ spMap φ) (he : e ≫ r = r' ≫ spMap φ) (hf : f ≫ s = r) (hf' : f' ≫ s' = r')
    (w : e ≫ f = f' ≫ g)
    (hT : ∀ (U : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U))
      (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)),
      appSecS s s' g U (secTrace s r hU b) =
        secTrace s' r' hV (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b))) (a : ℕ) :
    omegaTrace hf a ≫ omegaPullS hg a =
      mid he w a ≫ (Scheme.Modules.pushforward g).map (omegaTrace hf' a) := by
  refine hom_ext_affine fun U hU y ↦ ?_
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  have hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  obtain ⟨z, rfl⟩ := toOm_surjective (s := r) (j := a) (hU.preimage f) y
  refine formOm_induction (P := fun z ↦ (omegaTrace hf a ≫ omegaPullS hg a).app U
      (toOm r a (f ⁻¹ᵁ U) z) =
    (mid he w a ≫ (Scheme.Modules.pushforward g).map (omegaTrace hf' a)).app U
      (toOm r a (f ⁻¹ᵁ U) z)) hf hU ?_ (fun y z hy hz ↦ ?_) (fun b' x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz
  · rw [sheaf_lhs hg hf a hU, sheaf_rhs hg he hf hf' w a hV hle, hT U hU hV hle b']

end Sheaf

section Coh

private theorem pull_pull {X Y Z : Scheme.{0}} {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R Γ(X, ⊤)] [Algebra S Γ(Y, ⊤)] [Algebra T Γ(Z, ⊤)] {σ : R →+* S} {τ : S →+* T}
    {ρ : R →+* T} {u : Y ⟶ X} {v : Z ⟶ Y} {F : X.Modules} {G : Y.Modules} {L : Z.Modules}
    (hσ : ∀ r, u.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (hτ : ∀ r, v.appTop (algebraMap S Γ(Y, ⊤) r) = algebraMap T Γ(Z, ⊤) (τ r))
    (hρ : ∀ r, (v ≫ u).appTop (algebraMap R Γ(X, ⊤) r) = algebraMap T Γ(Z, ⊤) (ρ r))
    (Φ : F ⟶ (Scheme.Modules.pushforward u).obj G) (Ψ : G ⟶ (Scheme.Modules.pushforward v).obj L)
    (n : ℕ) (x : cohOn F ⊤ n) :
    cohOn.pull hτ Ψ (le_refl (v ⁻¹ᵁ ⊤)) n (cohOn.pull hσ Φ (le_refl (u ⁻¹ᵁ ⊤)) n x) =
      cohOn.pull hρ (Φ ≫ (Scheme.Modules.pushforward u).map Ψ ≫
        (Scheme.Modules.pushforwardComp v u).hom.app L) (le_refl ((v ≫ u) ⁻¹ᵁ ⊤)) n x := by
  apply (cohOn.toH' L _ n).injective
  refine (cohOn.toH'_pull hτ Ψ _ _).trans ?_
  refine Eq.trans ?_ (cohOn.toH'_pull hρ _ _ x).symm
  erw [cohOn.toH'_pull hσ Φ, SheafPull.pull_pull]
  rfl

private theorem comp_pushforwardCongr_rfl_hom_app {X Y : Scheme.{0}} {F : X.Modules} {G : Y.Modules}
    (u : Y ⟶ X) (Φ : F ⟶ (Scheme.Modules.pushforward u).obj G) :
    Φ ≫ (Scheme.Modules.pushforwardCongr (rfl : u = u)).hom.app G = Φ := by
  ext U x
  simp
  rfl

private theorem pull_congr {X Y : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
    [Algebra R Γ(X, ⊤)] [Algebra S Γ(Y, ⊤)] {σ : R →+* S} {F : X.Modules} {G : Y.Modules}
    {u v : Y ⟶ X} (w : u = v)
    (hu : ∀ r, u.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (hv : ∀ r, v.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (Φ : F ⟶ (Scheme.Modules.pushforward u).obj G) (n : ℕ) (x : cohOn F ⊤ n) :
    cohOn.pull hv (Φ ≫ (Scheme.Modules.pushforwardCongr w).hom.app G)
        (le_refl (v ⁻¹ᵁ ⊤)) n x = cohOn.pull hu Φ (le_refl (u ⁻¹ᵁ ⊤)) n x := by
  subst w
  rw [comp_pushforwardCongr_rfl_hom_app]

end Coh

end UpperTheory.Gal.G3.HeckeTraceSheaves

open UpperTheory.Gal.G3.HeckeTraceSheaves in
theorem UpperTheory.Gal.G3.jHTrace :
    (∀ (k k' : Type) [Field k] [Field k'] {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (f : Y ⟶ X) (f' : Y' ⟶ X') [IsFinite f] [Etale f] [IsFinite f'] [Etale f'], IsPullback e f' f g → ∀ (U : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen (g ⁻¹ᵁ U)) (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)), appSecS s s' g U (secTrace s r hU b) = secTrace s' r' hU' (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b))) → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → ∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k') {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ)) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (he : IsPullback e r' r (spMap φ)) (f : Y ⟶ X) (hf : f ≫ s = r) (f' : Y' ⟶ X') (hf' : f' ≫ s' = r'), e ≫ f = f' ≫ g → ∀ (a b : ℕ) [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] (y : hodgeH r a b), hodgePullS h.w a b (hodgeTrace hf a b y) = hodgeTrace hf' a b (hodgePullS he.w a b y) := by
  intro hT hP k k' _ _ φ X X' Y Y' s s' g h r r' e he f hf f' hf' w a b _ _ _ _ y
  haveI : IsAffineHom g := hP k k' φ X X' s s' g h
  have hpb : IsPullback e f' f g := by
    subst hf hf'
    exact IsPullback.of_bot he w h
  have hid := sheaf_id h.w he.w hf hf' w
    (fun U hU hV hle b => hT k k' s s' g r r' e f f' hpb U hU hV hle b) a
  letI := algΓ s
  letI := algΓ s'
  letI := algΓ r
  letI := algΓ r'
  obtain ⟨z, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b).surjective y
  change cohOn.pull (appTop_algebraMapS h.w) (omegaPullS h.w a) _ b
      (cohOn.map k (omegaTrace hf a) ⊤ b
        ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b).symm
          ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b) z))) =
    cohOn.map k' (omegaTrace hf' a) ⊤ b
      ((coh.pushforwardEquiv k' (appTop_algebraMap hf') (Omega r' a) b).symm
        (cohOn.pull (appTop_algebraMapS he.w) (omegaPullS he.w a) _ b
          ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b) z)))
  rw [LinearEquiv.symm_apply_apply]
  refine (cohOn.pull_map (appTop_algebraMapS h.w) (omegaPullS h.w a) (omegaTrace hf a) _ z).trans ?_
  rw [hid]
  refine (cohOn.map_pull (appTop_algebraMapS h.w) (mid he.w w a) (omegaTrace hf' a) _ z).symm.trans ?_
  congr 1
  rw [LinearEquiv.eq_symm_apply]
  have hu : (e ≫ f) ≫ s = r' ≫ spMap φ := by rw [Category.assoc, hf, he.w]
  have hu' : (f' ≫ g) ≫ s = r' ≫ spMap φ := by
    rw [Category.assoc, h.w, ← Category.assoc, hf']
  refine (pull_pull (appTop_algebraMapS h.w) (appTop_algebraMap hf') (appTop_algebraMapS hu')
    (mid he.w w a) (𝟙 _) b z).trans ?_
  refine Eq.trans ?_ (pull_pull (appTop_algebraMap hf) (appTop_algebraMapS he.w)
    (appTop_algebraMapS hu) (𝟙 _) (omegaPullS he.w a) b z).symm
  refine Eq.trans ?_ (pull_congr w (appTop_algebraMapS hu) (appTop_algebraMapS hu') _ b z)
  congr 1

end
