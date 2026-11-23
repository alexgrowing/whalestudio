import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldBasisToroidalModelSncStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocallyFiniteFreeLocalizations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAwStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LogDerProj

namespace GlobalTheory.LogDerProj

theorem isLocalizedModule_res : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ J : Ideal R, IsLocalizedModule (Submonoid.powers f) (res (S := S) f φ J) := by
  intro k R S _ _ _ _ f _ φ hφ J
  refine IsLocalizedModule.mk (fun x => ?_) (GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway f φ hφ J) (GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq f φ hφ J _ _)
  have hu : IsUnit (algebraMap R S x) := IsLocalization.map_units S x
  rw [Module.End.isUnit_iff]
  constructor
  · intro n n' h
    have h' : algebraMap R S x • n.1 = algebraMap R S x • n'.1 := by
      simpa [algebraMap_smul] using congrArg Subtype.val h
    exact Subtype.ext ((hu.smul_left_cancel).1 h')
  · intro n
    refine ⟨⟨((hu.unit⁻¹ : Sˣ) : S) • n.1, (show _ ∈ logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S)) from
      Submodule.smul_mem _ _ n.2)⟩, Subtype.ext ?_⟩
    change (x : R) • (((hu.unit⁻¹ : Sˣ) : S) • n.1) = n.1
    rw [← algebraMap_smul S (x : R), smul_smul, IsUnit.mul_val_inv, one_smul]

theorem finrank_fibre : ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (f : R) (d : ℕ) (ϕ : M →ₗ[R] (Fin d → Localization.Away f)), IsLocalizedModule (Submonoid.powers f) ϕ → ∀ m : Ideal R, m.IsMaximal → f ∉ m → Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = d := by
  intro R M _ _ _ f d ϕ hϕ m hm hf
  letI := Ideal.Quotient.field m
  have hu : IsUnit (algebraMap R (R ⧸ m) f) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf
  letI : Algebra (Localization.Away f) (R ⧸ m) := (IsLocalization.Away.lift f hu).toAlgebra
  haveI : IsScalarTower R (Localization.Away f) (R ⧸ m) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hbc : IsBaseChange (Localization.Away f) ϕ := IsLocalizedModule.isBaseChange (Submonoid.powers f) _ ϕ
  let e1 := hbc.equiv
  let e2 := TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away f) (R ⧸ m) (R ⧸ m) M
  let e3 := LinearEquiv.baseChange (Localization.Away f) (R ⧸ m) _ _ e1
  rw [← e2.finrank_eq, e3.finrank_eq, Module.finrank_eq_card_basis
    (Algebra.TensorProduct.basis (R ⧸ m) (Pi.basisFun (Localization.Away f) (Fin d))), Fintype.card_fin]

end GlobalTheory.LogDerProj

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LogDerProj.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ U : Y.X.affineOpens, Module.Finite Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) ∧ Module.Projective Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U
  haveI : SmoothOfRelativeDimension Dw.dim Y.s := smooth_gen_iff.1 hsm
  haveI : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  set I := Scheme.IdealSheafData.vanishingIdeal (interior Y).compl with hI
  let φ : c.F →+* Γ(Y.X, U.1) := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.s U.1
  have hφ : φ.FiniteType := by
    have h1 : (Y.s.appLE ⊤ U.1 (by simp)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType Y.s inferInstance ⟨⊤, isAffineOpen_top _⟩ U _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.surjective)
  have hM : logDer Y.s I U = GlobalTheory.LogDerProj.logSub φ (I.ideal U) := rfl
  have loc : ∀ q : PrimeSpectrum Γ(Y.X, U.1), ∃ r ∉ q.asIdeal,
      ∃ ϕ : GlobalTheory.LogDerProj.logSub φ (I.ideal U) →ₗ[Γ(Y.X, U.1)] (Fin Dw.dim → Localization.Away r),
        IsLocalizedModule (Submonoid.powers r) ϕ := by
    intro q
    have hU : IsAffineOpen U.1 := U.2
    have hxU : hU.fromSpec q ∈ U.1 := by
      change _ ∈ (U.1 : Set Y.X)
      rw [← hU.range_fromSpec]
      exact ⟨q, rfl⟩
    have key := GlobalTheory.T.exists_logVectorField_basis_toroidalModel_snc E H Dw l Xo c Y h1 hsm hsnc U (hU.fromSpec q) hxU
    obtain ⟨f, W, hW, m, t, b, hxW, hWf, -⟩ := key
    have hq : f ∉ q.asIdeal := by
      have : q ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen f := by rw [← hWf]; exact hxW
      rw [hU.fromSpec_preimage_basicOpen] at this
      exact this
    letI : Algebra Γ(Y.X, U.1) Γ(Y.X, W.1) := (Y.X.presheaf.map (homOfLE hW).op).hom.toAlgebra
    have hloc : ∀ (V : Y.X.Opens) (hV : V ≤ U.1), V = Y.X.basicOpen f →
        letI := (Y.X.presheaf.map (homOfLE hV).op).hom.toAlgebra; IsLocalization.Away f Γ(Y.X, V) := by
      rintro V hV rfl
      exact U.2.isLocalization_basicOpen f
    haveI : IsLocalization.Away f Γ(Y.X, W.1) := hloc W.1 hW hWf
    have hc : ∀ a, algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1) (φ a) = constFn Y.s W.1 a :=
      fun a => congr(($(Scheme.Hom.appLE_map Y.s (U := ⊤) (V := U.1) (fun _ _ => trivial) (homOfLE hW).op)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a))
    have hid : (I.ideal U).map (algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1)) = I.ideal W := I.map_ideal (U := W) (V := U) hW
    have hN : logDer Y.s I W = GlobalTheory.LogDerProj.logSub
        ((algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1)).comp φ) ((I.ideal U).map (algebraMap _ _)) := by
      ext D
      rw [GlobalTheory.LogDerProj.mem_logSub, hid]
      simp only [RingHom.comp_apply, hc]
      rfl
    let b' := b.map (LinearEquiv.ofEq _ _ hN)
    let e := (b'.equivFun.restrictScalars Γ(Y.X, U.1)).trans (LinearEquiv.piCongrRight fun _ =>
      (IsLocalization.algEquiv (Submonoid.powers f) Γ(Y.X, W.1) (Localization.Away f)).toLinearEquiv)
    haveI := GlobalTheory.LogDerProj.isLocalizedModule_res (S := Γ(Y.X, W.1)) f φ hφ (I.ideal U)
    exact ⟨f, hq, e.toLinearMap ∘ₗ GlobalTheory.LogDerProj.res (S := Γ(Y.X, W.1)) f φ (I.ideal U),
      IsLocalizedModule.of_linearEquiv (Submonoid.powers f) (GlobalTheory.LogDerProj.res (S := Γ(Y.X, W.1)) f φ (I.ideal U)) e⟩
  rw [hM]
  obtain ⟨hfin, hproj⟩ := GlobalTheory.LocFreeProj.finite_projective_of_locally_free _ _ fun q => by
    obtain ⟨r, hr, ϕ, hϕ⟩ := loc q
    exact ⟨r, hr, Fin Dw.dim → Localization.Away r, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ϕ, hϕ⟩
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  obtain ⟨r, hr, ϕ, hϕ⟩ := loc ⟨m, hm.isPrime⟩
  exact GlobalTheory.LogDerProj.finrank_fibre r Dw.dim ϕ hϕ m hm hr
