import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.CechPic

namespace GlobalTheory.FieldChangeInter

variable {X X' : Scheme.{0}}

def cechIso {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) :
    letI := algebraΓOfHom f
    cechLB f M D ≅ cech R (LB.toMod M) ⊤ D :=
  letI := algebraΓOfHom f
  (cechFunctor κ R).mapIso (Cube.isoMk (fun s => LinearEquiv.ofBijective
    (M := SecOnR f M (⨅ i ∈ s, D i)) (M₂ := sectionsOn (LB.toMod M) (⊤ ⊓ ⨅ i ∈ s, D i))
    (SecOnR.restrict f M (inf_le_right : ⊤ ⊓ (⨅ i ∈ s, D i) ≤ ⨅ i ∈ s, D i))
    (SecOnR.restrict_bijective f _ (le_inf le_top le_rfl)))
    fun {s t} h x => (SecOnR.restrict_restrict f _ inf_le_right x).trans
      (SecOnR.restrict_restrict f inf_le_right (cechOpen_anti ⊤ D h) x).symm)

theorem nonempty_homology_equiv {R : Type} (O : Type) [CommRing R] [CommRing O]
    [Algebra R O] [Module.Flat R O] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
      C).homology n ≃ₗ[O] O ⊗[R] C.homology n) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
  have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
  obtain ⟨e⟩ := Semicont.nonempty_extendScalars_obj_equiv O (C.homology n)
  exact ⟨((C.sc n).mapHomologyIso
    (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩

theorem nonempty_coh_equiv {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] [Finite κ] {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (n : ℕ) :
    letI := algebraΓOfHom f
    Nonempty ((cechLB f M D).homology n ≃ₗ[R] coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  haveI := LB.isQuasicoherent_toMod hM
  exact ⟨((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechIso f M D)).toLinearEquiv ≪≫ₗ
    cechHEquivCoh R hc hD (LB.toMod M) n ≪≫ₗ (cohOn.mapIso R ⊤ n (Twist.unitTwistIso M)).symm⟩

variable {k E : Type} [Field k] [Field E] [Algebra k E] {f : X ⟶ Spec (CommRingCat.of k)}
  {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X}

theorem hdim_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    hdim E (twist (structureModule X') (M.pull π)) n = hdim k (twist (structureModule X) M) n := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := nonempty_coh_equiv f hM hc hD' n
  obtain ⟨e₂⟩ := nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := nonempty_homology_equiv E (cechLB f M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv
  rw [hdim_def, hdim_def, ← e₁.finrank_eq, ← e₂.finrank_eq]
  exact e₄.finrank_eq.symm.trans (e₃.finrank_eq.trans Module.finrank_baseChange)

theorem interNum_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {ι : Type} [Fintype ι] {L : ι → LB X}
    (hL : ∀ i, (L i).IsLB) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    interNum E (structureModule X') (fun i => (L i).pull π) = interNum k (structureModule X) L := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have h : chiPic k (structureModule X) = chiPic E (structureModule X') ∘ pull π := by
    funext c
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    exact finsum_congr fun n => congrArg (fun a : ℕ => (-1 : ℤ) ^ n * a) (hdim_pull H hM n).symm
  rw [interNum_eq_multiDiff k _ hL, h, multiDiff_comap, Function.comp_apply, map_zero,
    interNum_eq_multiDiff E _ fun i ↦ pull_isLB (hL i) π]
  rfl

theorem del_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (S : LinSys k),
    IsProjOver S.str → (S.baseChange E).del = S.del := by
  intro k E _ _ _ S h
  have : IsProper S.str := by
    obtain ⟨N, i, hi, e⟩ := h
    have := isProper_str k N
    rw [← e]
    infer_instance
  exact interNum_pull (ι := Fin S.D) (L := fun _ => S.L) (S.isPullback_baseChange E) fun _ => S.isLB

end GlobalTheory.FieldChangeInter
