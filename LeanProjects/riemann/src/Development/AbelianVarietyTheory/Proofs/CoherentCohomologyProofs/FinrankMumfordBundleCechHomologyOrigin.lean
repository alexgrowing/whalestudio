import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBallQuotientEqSumMulFdeg
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CokerDualMapEquivResidueFieldOfOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularLocalRingAndRingKrullDimEqOfPolAV

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.OriginCohom

theorem nonempty_extendScalars_equiv {R : Type} (O : Type) [CommRing R] [CommRing O]
    [inst : Algebra R O] (M : ModuleCat.{0} R) :
    Nonempty ((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).obj M ≃ₗ[O] O ⊗[R] M) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* O, inst = φ.toAlgebra :=
    ⟨algebraMap R O, Algebra.algebra_ext _ _ fun _ => rfl⟩
  exact ⟨LinearEquiv.refl _ _⟩

theorem nonempty_homology_extendScalars_equiv {R : Type} (O : Type) [CommRing R] [CommRing O]
    [Algebra R O] [Module.Flat R O] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
      C).homology n ≃ₗ[O] O ⊗[R] C.homology n) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
  have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
  obtain ⟨e⟩ := nonempty_extendScalars_equiv O (C.homology n)
  exact ⟨((C.sc n).mapHomologyIso
    (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩

theorem finrank_homology (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (χ₀ : R →ₐ[K] K) (O : Type) [CommRing O] [Algebra R O]
    [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)] [IsRegularLocalRing O]
    (g : ℕ) (hg : ringKrullDim O = g) (C : CochainComplex (ModuleCat.{0} R) ℕ)
    (hz : ∀ p, g < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p))
    (hsupp : ∀ χ : R →ₐ[K] K, χ ≠ χ₀ → ∀ p, ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology p, r • z = 0)
    (C' : CochainComplex (ModuleCat.{0} O) ℕ)
    (e : ((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj C ≅ C')
    (hq : ∀ (E : CochainComplex (ModuleCat.{0} O) ℕ) (φ : E ⟶ C'),
      (∀ p, Module.Free O (E.X p) ∧ Module.Finite O (E.X p)) →
      (∀ (R' : Type) [CommRing R'] [Algebra O R'], QuasiIso
        (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap O R')).mapHomologicalComplex _).map φ)) →
      Nonempty ((Module.Dual O (E.X 0) ⧸ LinearMap.range (E.d 0 1).hom.dualMap) ≃ₗ[O]
        IsLocalRing.ResidueField O)) (n : ℕ) :
    Module.Finite K ((ModuleCat.restrictScalars (algebraMap K R)).obj (C.homology n)) ∧
      Module.finrank K ((ModuleCat.restrictScalars (algebraMap K R)).obj (C.homology n)) =
        if n = g then 1 else 0 := by
  have : Module.Flat R O := IsLocalization.flat O (RingHom.ker χ₀).primeCompl
  have hX (p : ℕ) : Nonempty (C'.X p ≃ₗ[O] O ⊗[R] C.X p) := by
    obtain ⟨e₁⟩ := nonempty_extendScalars_equiv O (C.X p)
    exact ⟨((HomologicalComplex.eval _ _ p).mapIso e.symm).toLinearEquiv ≪≫ₗ e₁⟩
  have hH (p : ℕ) : Nonempty (C'.homology p ≃ₗ[O] O ⊗[R] C.homology p) := by
    obtain ⟨e₁⟩ := nonempty_homology_extendScalars_equiv O C p
    exact ⟨(HomologicalComplex.homologyMapIso e.symm p).toLinearEquiv ≪≫ₗ e₁⟩
  obtain ⟨E, φ, hE0, hEfin, -, hEproj, hφ, -, hφ'⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} C' g
      (fun p hp => by
        obtain ⟨e₁⟩ := hX p
        have := ModuleCat.isZero_iff_subsingleton.1 (hz p hp)
        exact ModuleCat.isZero_iff_subsingleton.2 e₁.toEquiv.subsingleton)
      (fun p => by
        obtain ⟨e₁⟩ := hX p
        have := hflat p
        exact Module.Flat.of_linearEquiv e₁)
      (fun p => by
        obtain ⟨e₁⟩ := hH p
        have := hfin p
        exact Module.Finite.equiv e₁.symm)
  have hfree (p : ℕ) : Module.Free O (E.X p) ∧ Module.Finite O (E.X p) := by
    have := hEfin p
    have := hEproj p
    exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
  have hEH (p : ℕ) : Nonempty (E.homology p ≃ₗ[O] O ⊗[R] C.homology p) := by
    obtain ⟨e₁⟩ := hH p
    exact ⟨(asIso (HomologicalComplex.homologyMap φ p)).toLinearEquiv ≪≫ₗ e₁⟩
  have hlen (p : ℕ) :=
    letI : Module K (C.homology p) := Module.compHom _ (algebraMap K R)
    haveI : IsScalarTower K R (C.homology p) :=
      ⟨fun a r z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
    haveI := hfin p
    PointSupport.finiteLength_and_finrank_eq_length K R χ₀ O (C.homology p)
      fun χ hχ => hsupp χ hχ p
  obtain ⟨h₁, h₂⟩ := homology_of_free_complex_of_isFiniteLength O g hg E hfree hE0
    (fun p => by
      obtain ⟨e₁⟩ := hEH p
      exact (hlen p).1.of_injective (f := e₁.toLinearMap) e₁.injective)
    (hq E φ hfree hφ')
  obtain ⟨e₁⟩ := hEH n
  obtain ⟨-, h₃, h₄⟩ := hlen n
  refine ⟨h₃, ?_⟩
  rw [← e₁.length_eq] at h₄
  split_ifs with hn
  · subst hn
    rw [h₂] at h₄
    exact_mod_cast h₄
  · have := ModuleCat.isZero_iff_subsingleton.1 (h₁ n hn)
    rw [Module.length_eq_zero] at h₄
    exact_mod_cast h₄

theorem nonempty_homology_restrictScalars_equiv {K R : Type} [CommRing K] [CommRing R]
    (a : K →+* R) {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R))
    (f₀ : Y ⟶ Spec (CommRingCat.of K)) (w : f₀ = f ≫ Spec.map (CommRingCat.ofHom a)) (M : LB Y)
    {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) (n : ℕ) :
    Nonempty ((cechLB f₀ M D).homology n ≃ₗ[K]
      (ModuleCat.restrictScalars a).obj ((cechLB f M D).homology n)) := by
  have hc (V : Y.Opens) (r : K) : cst f₀ V r = cst f V (a r) := by
    rw [← appLE_cst (π := 𝟙 Y) ((Category.id_comp f₀).trans w) (le_rfl : V ≤ 𝟙 Y ⁻¹ᵁ V) r]
    exact (rs_self le_rfl _).symm
  let e : secCube f₀ M D ≅ secCube f M D ⋙ ModuleCat.restrictScalars a :=
    Cube.isoMk (fun s =>
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun r x =>
          congrArg (fun u : Γ(Y, ⨅ i ∈ s, D i) => u • (id x : SecOn M (⨅ i ∈ s, D i)))
            (hc (⨅ i ∈ s, D i) r) }) fun _ _ => rfl
  exact ⟨(HomologicalComplex.homologyMapIso
    ((cechFunctor κ K).mapIso e ≪≫ (cechRestrictScalarsIso a (secCube f M D)).symm) n ≪≫
    ((cechLB f M D).sc n).mapHomologyIso (ModuleCat.restrictScalars a)).toLinearEquiv⟩

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem lbIso_pull_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : Y ⟶ X)
    (ψ : Z ⟶ Y) : LBIso ((L.pull φ).pull ψ) (L.pull (ψ ≫ φ)) :=
  LBIso.chartPull (chartPullLinComb L φ (fun _ : PUnit => ψ) (fun _ => ψ ≫ φ) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm) (chartPullId _)
    (PolBaseChange.lbIso_refl (pull_isLB hL _))

theorem finrank_cechLB_homology :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t → (∃ p q, t p = η[P.A].left q) → ∀ D : Fin (P.g + 1) → Y.Opens, (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, Module.Finite K ((cechLB (f ≫ t ≫ P.A.hom) ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology n) ∧ Module.finrank K ((cechLB (f ≫ t ≫ P.A.hom) ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology n) = if n = P.g then 1 else 0 := by
  intro K _ _ P R _ t Y π f H ht ⟨p, q, hpq⟩ D hD hc n
  have hsm : Smooth P.A.hom := P.isAb.smooth
  have hpr : IsProper P.A.hom := P.isAb.proper
  let φ : CommRingCat.of K ⟶ CommRingCat.of R := Spec.preimage (t ≫ P.A.hom)
  let _ : Algebra K R := φ.hom.toAlgebra
  have hφ : t ≫ P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap K R)) :=
    (Spec.map_preimage _).symm
  have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K R))) :=
    hφ ▸ inferInstance
  have : Algebra.FiniteType K R := RingHom.finiteType_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft)
  let o : Spec (CommRingCat.of K) ⟶ P.A.left := η[P.A].left
  have ho : o ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have hr : Set.range o ⊆ Set.range t := by
    rintro _ ⟨x, rfl⟩
    exact ⟨p, hpq.trans (congrArg o (Subsingleton.elim _ _))⟩
  let c : CommRingCat.of R ⟶ CommRingCat.of K := Spec.preimage (IsOpenImmersion.lift t o hr)
  have hco : Spec.map c ≫ t = o := by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hcφ : CommRingCat.ofHom (algebraMap K R) ≫ c = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hφ, ← Category.assoc, hco, ho, Spec.map_id]
  let χ₀ : R →ₐ[K] K := ⟨c.hom, fun r => congrArg (fun u => u.hom r) hcφ⟩
  have hmax : (RingHom.ker χ₀).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun r => ⟨algebraMap K R r, χ₀.commutes r⟩
  have hprime : (RingHom.ker c.hom).IsPrime := hmax.isPrime
  let O := Localization.AtPrime (RingHom.ker χ₀)
  have hloc : IsLocalization.AtPrime O (RingHom.ker c.hom) :=
    inferInstanceAs (IsLocalization.AtPrime O (RingHom.ker χ₀))
  obtain ⟨hreg, hdim⟩ :=
    isRegularLocalRing_and_ringKrullDim_eq_of_polAV K P R t (RingHom.ker χ₀) O ht
  obtain ⟨-, hflat, hfin, hsupp⟩ := MumfordSupport.cohomology_finite_and_vanishes_off_origin K P R t Y π f H ht _ D hD hc
  have hF : (translDiff P.A P.L (𝟙 P.A)).IsLB := LB.isLB_linComb P.isLB _ _
  have hsep₀ : IsSeparated (fst P.A P.A).left :=
    inferInstanceAs (IsSeparated (pullback.fst P.A.hom P.A.hom))
  have hsep : IsSeparated f := MorphismProperty.of_isPullback H hsep₀
  have : IsSeparated (terminal.from Y) := by
    rw [← terminal.comp_from f]
    infer_instance
  have hDs (s : Finset (Fin (P.g + 1))) (hs : s.Nonempty) : IsAffineOpen (⨅ i ∈ s, D i) :=
    IsAffineOpen.biInf _ (Finset.finite_toSet _) hs fun i _ => hD i
  let j := Spec.map (CommRingCat.ofHom (algebraMap R O))
  have H' := IsPullback.of_hasPullback f j
  obtain ⟨w, hw⟩ := lbIso_pull_pull_comp hF π (pullback.fst f j)
  let e := cechLBBaseChangeIso (LB.isLB_pull hF π) H' hDs ≪≫
    cechLBCongr _ _ (LB.isLB_pull (LB.isLB_pull hF π) _) (LB.isLB_pull hF _) w hw
  obtain ⟨h₁, h₂⟩ := finrank_homology K R χ₀ O P.g hdim _
    (fun p hp => isZero_cechLB_X _ _ _ (by rw [Fintype.card_fin]; exact hp)) hflat hfin
    (fun χ hχ => hsupp χ.toRingHom
      (by
        rw [Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext r
        exact χ.commutes r)
      (fun h => hχ (by
        have h' : CommRingCat.ofHom χ.toRingHom = c :=
          Spec.map_injective ((cancel_mono t).1 (h.trans hco.symm))
        ext r
        exact congrArg (fun u => u.hom r) h'))) _ e
    (fun E ψ hE hψ => GlobalTheory.MumfordLocal.coker_dualMap_equiv_residueField_of_origin K P R t c.hom O (j ≫ t) _ (pullback.fst f j ≫ π)
      (pullback.snd f j) (H'.paste_horiz H) ht hco rfl _ _ E ψ
      (fun i => isAffineOpen_preimage_of_isPullback H' (hD i))
      (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) hE hψ) n
  obtain ⟨e₀⟩ := nonempty_homology_restrictScalars_equiv (algebraMap K R) f (f ≫ t ≫ P.A.hom)
    (by rw [hφ]) ((translDiff P.A P.L (𝟙 P.A)).pull π) D n
  exact ⟨Module.Finite.equiv e₀.symm, e₀.finrank_eq.trans h₂⟩

end GlobalTheory.OriginCohom
