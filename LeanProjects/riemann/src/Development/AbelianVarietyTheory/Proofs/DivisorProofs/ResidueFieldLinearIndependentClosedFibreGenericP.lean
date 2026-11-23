import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvrStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutResidueLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainSectionsQuotMaximalIdealSmoothConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMapMaximalIdealOfRingKrullDimEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ResInj

theorem cst_eq_fnOf {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (V : X.Opens)
    (hV : genericPoint X ∈ V) (r : R) : GlobalTheory.Desc.cst p r = fnOf V hV (GlobalTheory.AbLaw.cst p V r) := by
  simp only [GlobalTheory.Desc.cst, GlobalTheory.AbLaw.cst, fnOf, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp]
  rw [TopCat.Presheaf.germ_res_apply]

theorem zeroAt_fnOf_iff {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} {x : X} (hx : x ∈ U) (b : Γ(X, U)) :
    ZeroAt x (fnOf U (gen_mem hx) b) ↔ (X.presheaf.germ U x hx).hom b ∈ maximalIdeal (X.presheaf.stalk x) := by
  refine ⟨fun ⟨a, ha, e⟩ => ?_, fun h => ⟨_, h, algebraMap_germ hx b⟩⟩
  rwa [IsFractionRing.injective (X.presheaf.stalk x) X.functionField (e.trans (algebraMap_germ hx b).symm)] at ha

theorem cst_zeroAt (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X)
    (hx : p x = closedPoint R) (r : R) (hr : r ∈ maximalIdeal R) : ZeroAt x (GlobalTheory.Desc.cst p r) := by
  have hreg : RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.ResInj

theorem GlobalTheory.Desc.ResInj.exists_affine_fnOf : ∀ (X : Scheme.{0}) [IsIntegral X] (x : X) (n : ℕ) (u : Fin n → X.functionField), (∀ i, GlobalTheory.Cartier.RegAt x (u i)) → ∃ (U : X.Opens) (hx : x ∈ U), IsAffineOpen U ∧ ∃ s : Fin n → Γ(X, U), ∀ i, GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem hx) (s i) = u i := by
  intro X _ x n u hu
  choose W hxW s hs using fun i => (hu i).exists_fnOf
  let W₀ : X.Opens := ⟨⋂ i, (W i : Set X), isOpen_iInter_of_finite fun i => (W i).isOpen⟩
  have hx₀ : x ∈ W₀ := Set.mem_iInter.2 hxW
  obtain ⟨U, hU, hxU, hUW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hx₀
  have hle : ∀ i, U ≤ W i := fun i z hz => Set.mem_iInter.1 (hUW hz) i
  refine ⟨U, hxU, hU, fun i => resG X (hle i) (s i), fun i => ?_⟩
  rw [fnOf_resG, hs]

theorem GlobalTheory.Desc.ResInj.mem_map_of_germ_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (G : Over (Sp R)) [IsIntegral G.left], Smooth G.hom → GeometricallyConnected G.hom → ∀ y : G.left, G.hom y = closedPoint R → ringKrullDim (G.left.presheaf.stalk y) = 1 → ∀ (U : G.left.Opens) (hy : y ∈ U), IsAffineOpen U → ∀ b : Γ(G.left, U), (G.left.presheaf.germ U y hy).hom b ∈ maximalIdeal (G.left.presheaf.stalk y) → b ∈ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
  intro R _ _ _ G _ hsm hgc y hy hdim U hyU hU b hb
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  letI : Algebra R Γ(G.left, U) := (GlobalTheory.AbLaw.cst G.hom U).toAlgebra
  haveI : Module.Flat R Γ(G.left, U) := GlobalTheory.AbLaw.flat_cst G.hom hU
  let p := hU.primeIdealOf ⟨y, hyU⟩
  letI : Algebra Γ(G.left, U) (G.left.presheaf.stalk y) := G.left.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI hloc := hU.isLocalization_stalk ⟨y, hyU⟩
  have hmem : ∀ c : Γ(G.left, U), (G.left.presheaf.germ U y hyU).hom c ∈ maximalIdeal (G.left.presheaf.stalk y) ↔ c ∈ p.asIdeal := by
    intro c
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (G.left.presheaf.stalk y) p.asIdeal c
  have hle : (maximalIdeal R).map (algebraMap R Γ(G.left, U)) ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap, ← hmem, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
    have := GlobalTheory.Desc.ResInj.cst_zeroAt R G.left G.hom y hy t ht
    rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf G.hom U (gen_mem hyU)] at this
  have hd : ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    rw [← hdim]
    exact ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) (G.left.presheaf.stalk y)).toRingEquiv
  have e := GlobalTheory.T.eq_map_maximalIdeal_of_ringKrullDim_eq_one' R Γ(G.left, U) p.asIdeal hle hd (GlobalTheory.T.isDomain_sections_quot_maximalIdeal_smooth_connected R G hsm hgc U hU y hyU hy)
  have : b ∈ p.asIdeal := (hmem b).1 hb
  rw [e] at this
  exact this

theorem GlobalTheory.Desc.ResInj.residue_linearIndependent : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ (n : ℕ) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) → (∀ c : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, GlobalTheory.Desc.cst H.hom (c i) * u i) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, GlobalTheory.Cartier.ZeroAt y' (∑ i, GlobalTheory.Desc.cst H'.hom (d i) * θ (u i)) → ∀ i, d i ∈ maximalIdeal D := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hpff y y' hy hy' hdy hdy' n u hu hind d hz
  have hπy : π y' = y := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb hpff y y' hy hy' hdy hdy'
  obtain ⟨U, hyU, hUa, x, hx⟩ := GlobalTheory.Desc.ResInj.exists_affine_fnOf H.left y n u hu
  set V : H'.left.Opens := π ⁻¹ᵁ U with hVdef
  have hy'V : y' ∈ V := by show π y' ∈ U; rw [hπy]; exact hyU
  have hgU : genericPoint H.left ∈ U := gen_mem hyU
  have hgV : genericPoint H'.left ∈ V := gen_mem hy'V
  letI : Algebra T D := a.toAlgebra
  letI : Algebra T Γ(H.left, U) := (GlobalTheory.AbLaw.cst H.hom U).toAlgebra
  letI : Algebra D Γ(H'.left, V) := (GlobalTheory.AbLaw.cst H'.hom V).toAlgebra
  letI : Algebra Γ(H.left, U) Γ(H'.left, V) := (π.app U).hom.toAlgebra
  letI : Algebra T Γ(H'.left, V) := ((GlobalTheory.AbLaw.cst H'.hom V).comp a).toAlgebra
  haveI : IsScalarTower T D Γ(H'.left, V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T Γ(H.left, U) Γ(H'.left, V) := .of_algebraMap_eq fun r => by
    have e := GlobalTheory.AbLaw.appLE_cst hpb.w (V := U) (V' := V) le_rfl r
    rw [Scheme.Hom.appLE_eq_app] at e
    exact e.symm
  haveI : Algebra.IsPushout T D Γ(H.left, U) Γ(H'.left, V) := by
    have po := GlobalTheory.AbLaw.isPushout_cst hpb hUa (V' := V) rfl
    rw [Scheme.Hom.appLE_eq_app] at po
    exact CommRingCat.isPushout_iff_isPushout.mp po
  have hsm : Smooth H'.hom := MorphismProperty.of_isPullback hpb hH.smooth
  have hgc : GeometricallyConnected H'.hom := MorphismProperty.of_isPullback hpb hH.geomConnected

  have hindA : ∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T Γ(H.left, U)) →
      ∀ i, c i ∈ maximalIdeal T := by
    intro c hc
    apply hind c
    have hle : (maximalIdeal T).map (algebraMap T Γ(H.left, U)) ≤
        Ideal.comap (H.left.presheaf.germ U y hyU).hom (maximalIdeal _) := by
      rw [Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
      have := GlobalTheory.Desc.ResInj.cst_zeroAt T H.left H.hom y hy t ht
      rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU] at this
    have h1 := hle hc
    rw [Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU] at h1
    convert h1 using 1
    simp only [map_sum, Algebra.smul_def, map_mul, hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU]
    rfl

  have hd := GlobalTheory.T.pushout_residue_linearIndependent' T D Γ(H.left, U) Γ(H'.left, V) hm n x hindA d
  apply hd
  apply GlobalTheory.Desc.ResInj.mem_map_of_germ_mem D H' hsm hgc y' hy' hdy' V hy'V (GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback hpb hUa)
  rw [← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hy'V]
  convert hz using 1
  simp only [map_sum, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hx i, ← GlobalTheory.Desc.fnOf_app_of_pff H.left H'.left π θ hpff U hgU hgV, GlobalTheory.Desc.ResInj.cst_eq_fnOf H'.hom V hgV]
  rfl
