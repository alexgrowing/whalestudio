import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellPointEqOfBaseAndCellCoordinatesEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellPointBasicOpenAffineSpaceCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

noncomputable section

namespace GlobalTheory.LogPole.CellBir

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem isIso_spMap_of_inverse {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (h₁ : f.comp g = RingHom.id B) (h₂ : g.comp f = RingHom.id A) : IsIso (spMap f) :=
  inferInstanceAs (IsIso (Spec.map (RingEquiv.toCommRingCatIso (RingEquiv.ofRingHom f g h₁ h₂)).hom))

theorem isOpenImmersion_spMap_away {R : Type} [CommRing R] (g : R) :
    IsOpenImmersion (spMap (algebraMap R (Localization.Away g))) := IsOpenImmersion.of_isLocalization g

set_option maxHeartbeats 3000000 in

theorem exists_isOpenImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ V : (Spec (CommRingCat.of Γ(Y₀ TF.X Z, W))).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by

  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h hW
  obtain ⟨g, hnil, hU0, z, hz, hzU, hC, hX⟩ := GlobalTheory.T.exists_bigCell_point_basicOpen_affineSpace_coords E H Dw l Xo c TF Z hF U n e v hv W k L N h hW
  obtain ⟨φ, hφ⟩ : ∃ φ : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1) →+* Γ(Y₀ TF.X Z, W),
    φ = MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) := ⟨_, rfl⟩
  rw [← hφ] at hnil hU0 ⊢
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = ev z W hz := ⟨_, rfl⟩
  have hψφ : ψ.comp φ = algebraMap _ (Localization.Away g) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, hφ, MvPolynomial.eval₂Hom_C, hψ]
      exact hC r
    · intro i
      simp only [RingHom.comp_apply, hφ, MvPolynomial.eval₂Hom_X', hψ]
      exact hX i
  have hψu : IsUnit (ψ (φ g)) := by
    rw [← RingHom.comp_apply, hψφ]
    exact IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨ψ', hψ'c⟩ : ∃ ψ' : Localization.Away (φ g) →+* Localization.Away g, ψ'.comp (algebraMap _ _) = ψ :=
    ⟨_, IsLocalization.Away.lift_comp (φ g) hψu⟩
  obtain ⟨θ, hθc⟩ : ∃ θ : Localization.Away g →+* Localization.Away (φ g),
      θ.comp (algebraMap _ _) = (algebraMap _ (Localization.Away (φ g))).comp φ :=
    ⟨Localization.awayMap φ g, IsLocalization.map_comp _⟩

  have hz₀ : ⊤ ≤ (spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) ≫ GlobalTheory.FlagMod.tau h.1) ⁻¹ᵁ W :=
    GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le h.1 le_rfl)
  have ev₀ := GlobalTheory.FlagMod.ev_spMap_tau h.1 (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) hz₀
  have hz' : ⊤ ≤ (spMap θ ≫ z) ⁻¹ᵁ W := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have ev' : ev (spMap θ ≫ z) W hz' = θ.comp ψ := by rw [hψ]; exact GlobalTheory.FlagMod.ev_spMap θ z W hz hz'
  have hcomp : ∀ p, θ (ψ (φ p)) = algebraMap _ (Localization.Away (φ g)) (φ p) := fun p => by
    rw [← RingHom.comp_apply ψ φ, hψφ, ← RingHom.comp_apply θ, hθc, RingHom.comp_apply]
  have heq : spMap θ ≫ z = spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) ≫ GlobalTheory.FlagMod.tau h.1 := by
    refine GlobalTheory.T.bigCell_point_eq_of_base_and_cellCoordinates_eq E H Dw l Xo c TF Z hF U n e v hv W k L N h _ _ _ hz' hz₀
      (GlobalTheory.FlagMod.le_preimage_comp _ hzU) (hU0 _ _ hz₀ (by
        rw [ev₀]; exact IsLocalization.Away.algebraMap_isUnit _)) (fun r => ?_) (fun i => ?_)
    · have := hcomp (MvPolynomial.C r)
      simp only [hφ, MvPolynomial.eval₂Hom_C] at this
      rw [ev', ev₀, RingHom.comp_apply]
      exact this
    · have := hcomp (MvPolynomial.X i)
      simp only [hφ, MvPolynomial.eval₂Hom_X'] at this
      rw [ev', ev₀, RingHom.comp_apply]
      exact this
  have hθψ : θ.comp ψ = algebraMap _ (Localization.Away (φ g)) := by
    exact ev'.symm.trans ((GlobalTheory.FlagMod.ev_congr heq W hz' hz₀).trans ev₀)
  have h1 : ψ'.comp θ = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers g)
      ((congrArg (ψ'.comp ·) hθc).trans ((congrArg (·.comp φ) hψ'c).trans hψφ))
  have h2 : θ.comp ψ' = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (φ g)) ((congrArg (θ.comp ·) hψ'c).trans hθψ)
  haveI : Nontrivial (Localization.Away (φ g)) := OreLocalization.nontrivial_iff.mpr hnil
  haveI : IsOpenImmersion (spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))))))
  refine ⟨(spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).opensRange, ?_, ?_⟩
  · have x : Sp (Localization.Away (φ g)) :=
      (inferInstance : Nonempty (PrimeSpectrum (Localization.Away (φ g)))).some
    exact ⟨⟨_, Set.mem_range_self x⟩⟩
  · have key : ((spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).opensRange).ι =
        (spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).isoOpensRange.inv ≫
          spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) := by
      exact (Iso.eq_inv_comp _).2 (Scheme.Hom.isoOpensRange_hom_ι _)
    have hfac : spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g))) ≫ spMap φ =
        spMap θ ≫ spMap (algebraMap _ (Localization.Away g)) :=
      (spMap_comp_ringHom φ _).trans ((congrArg spMap hθc.symm).trans (spMap_comp_ringHom _ θ).symm)
    haveI : IsIso (spMap θ) := isIso_spMap_of_inverse θ ψ' h2 h1
    haveI := isOpenImmersion_spMap_away g
    have hoi : IsOpenImmersion ((spMap (algebraMap Γ(Y₀ TF.X Z, W) (Localization.Away (φ g)))).isoOpensRange.inv ≫
        spMap θ ≫ spMap (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g))) := inferInstance
    rw [← hfac, ← Category.assoc, ← key] at hoi
    exact hoi

end GlobalTheory.LogPole.CellBir
