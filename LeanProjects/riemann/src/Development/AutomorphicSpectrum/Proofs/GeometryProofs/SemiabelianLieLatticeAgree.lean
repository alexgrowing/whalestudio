import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieLatticeEqStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalRingFractionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOnePrimeDvrStalkStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDescendsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeRangeOfStalkStatement
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem exists_model (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    ∃ (Ep : Type) (_ : AddCommGroup Ep) (_ : Module (regAt ξ p) Ep) (Mp : LieModel G (regPt h p) Ep)
      (j : Ep →ₗ[regAt ξ p] E), IsBaseChange Ω j ∧
        ∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left := by
  obtain ⟨Ep, i1, i2, Mp, j, hb, hj⟩ := GlobalTheory.T.lie_model_descends_base_change X G (regAt ξ p) Ω (regPt h p) E
    (castPt (spMap_algebraMap_regPt h p).symm M)
  exact ⟨Ep, i1, i2, Mp, j, hb, fun e =>
    (castPt_pt_left (spMap_algebraMap_regPt h p).symm M (j e)).symm.trans (hj e)⟩

theorem lat_fin (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    Module.Finite (regAt ξ p) (M.lat p) ∧ Module.Projective (regAt ξ p) (M.lat p) ∧
      Submodule.span Ω (M.lat p : Set E) = ⊤ := by
  obtain ⟨Ep, i1, i2, Mp, j, hb, hj⟩ := exists_model h G M p
  have hr := GlobalTheory.T.lie_lattice_range_of_stalk X Ω ξ h G E M p Ep Mp j hj
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective X G (regAt ξ p) (regPt h p) Ep Mp
  haveI := GlobalTheory.T.regular_local_ring_fraction_field X Ω ξ h p
  have hl : IsLocalizedModule (nonZeroDivisors (regAt ξ p)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (regAt ξ p)) Ω j).mpr hb
  have hinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (regAt ξ p)) j).1 hm
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Ep) c.2
    exact hreg (show (c : regAt ξ p) • m = (c : regAt ξ p) • 0 by rw [smul_zero]; exact hc)
  have hMeq : M.lat p = LinearMap.range j := SetLike.coe_injective (hr.trans (LinearMap.coe_range j).symm)
  let e : Ep ≃ₗ[regAt ξ p] M.lat p := (LinearEquiv.ofInjective j hinj).trans (LinearEquiv.ofEq _ _ hMeq.symm)
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, ?_⟩
  rw [eq_top_iff]
  intro v _
  refine hb.inductionOn v (fun v => v ∈ Submodule.span Ω (M.lat p : Set E)) (zero_mem _) (fun m => ?_)
    (fun s n hn => Submodule.smul_mem _ s hn) (fun a b ha hb => add_mem ha hb)
  exact Submodule.subset_span (by rw [hr]; exact ⟨m, rfl⟩)

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap]

theorem lat_gen (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {p q : Cpt ξ} (hs : q.1 ⤳ p.1) :
    M.lat q = Submodule.span (regAt ξ q) (M.lat p : Set E) := by
  obtain ⟨Eq, i1, i2, Mq, jq, hbq, hjq⟩ := exists_model h G M q
  letI : Algebra (regAt ξ p) (regAt ξ q) := (regIncl hs).toAlgebra
  letI : Module (regAt ξ p) Eq := Module.compHom Eq (regIncl hs)
  haveI : IsScalarTower (regAt ξ p) (regAt ξ q) Eq := ⟨fun a b c => by
    change (regIncl hs a * b) • c = regIncl hs a • (b • c)
    rw [mul_smul]⟩
  obtain ⟨Ep, i3, i4, Mp, j, hb, hj⟩ := GlobalTheory.T.lie_model_descends_base_change X G (regAt ξ p) (regAt ξ q) (regPt h p) Eq
    (castPt (spMap_regIncl_regPt h hs).symm Mq)
  let jp : Ep →ₗ[regAt ξ p] E :=
    { toFun := fun e => jq (j e)
      map_add' := fun a b => by simp
      map_smul' := fun c e => by
        rw [map_smul]
        change jq (regIncl hs c • j e) = _
        rw [map_smul]
        rfl }
  have hjp : ∀ e, (M.pt (jp e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left := by
    intro e
    have h1 := hjq (j e)
    have h2 := (castPt_pt_left (spMap_regIncl_regPt h hs).symm Mq (j e)).symm.trans (hj e)
    have h3 : (dualMap (algebraMap (regAt ξ q) Ω)).comp (dualMap (algebraMap (regAt ξ p) (regAt ξ q))) =
        dualMap (algebraMap (regAt ξ p) Ω) := dualMap_comp _ _
    refine h1.trans ?_
    rw [h2, ← h3]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hrp := GlobalTheory.T.lie_lattice_range_of_stalk X Ω ξ h G E M p Ep Mp jp hjp
  have hrq := GlobalTheory.T.lie_lattice_range_of_stalk X Ω ξ h G E M q Eq Mq jq hjq
  have hMq : M.lat q = LinearMap.range jq := SetLike.coe_injective (hrq.trans (LinearMap.coe_range jq).symm)
  rw [hrp, hMq]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    refine hb.inductionOn w (fun w => jq w ∈ Submodule.span (regAt ξ q) (Set.range jp)) (by simp) (fun m => ?_)
      (fun s n hn => by rw [map_smul]; exact Submodule.smul_mem _ s hn)
      (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    exact Submodule.subset_span ⟨m, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨e, rfl⟩
    exact ⟨j e, rfl⟩

theorem mem_localizedIn_iff (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {p q : Cpt ξ} (hs : q.1 ⤳ p.1)
    (P : PrimeSpectrum (regAt ξ p)) (hu : ∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q)
    (hd : ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p) (v : E) :
    v ∈ GroundTheory.Heights₂.Heights.Model.localizedIn P.asIdeal (M.lat p) ↔ v ∈ M.lat q := by
  have hg := lat_gen h G M hs
  constructor
  · rintro ⟨s, hsP, hv⟩
    have h0 : (s : Ω) ≠ 0 := fun h0 => hsP (by
      have : s = 0 := Subtype.ext h0
      rw [this]; exact zero_mem _)
    have h1 : (s : Ω) • v ∈ M.lat q := by rw [hg]; exact Submodule.subset_span hv
    have h2 := (M.lat q).smul_mem (⟨_, hu s hsP⟩ : regAt ξ q) h1
    have h3 : (⟨_, hu s hsP⟩ : regAt ξ q) • (s : Ω) • v = v := by
      rw [Subring.smul_def, smul_smul]
      simp [h0]
    rwa [h3] at h2
  · intro hv
    rw [hg] at hv
    induction hv using Submodule.span_induction with
    | mem w hw => exact ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hw⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul a w _ hw =>
      obtain ⟨s, hsP, hsw⟩ := hw
      obtain ⟨t, htP, hta⟩ := hd a a.2
      refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim htP hsP, ?_⟩
      have e : (t * s) • a • w = (⟨_, hta⟩ : regAt ξ p) • s • w := by
        simp only [Subring.smul_def, smul_smul, Subring.coe_mul]
        congr 1
        ring
      rw [e]
      exact (M.lat p).smul_mem _ hsw

theorem lat_eq_of_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (M' : LieModel G' ξ E), (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left) → IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → M.lat = M'.lat := by
  intro X Ω _ ξ hξ G G' _ _ GΩ _ φ φ' hS hS' hP hP' E _ _ M M' hv hN hnorm
  funext p
  haveI := hS.comm
  haveI := hS.smooth
  haveI := hS'.comm
  haveI := hS'.smooth
  haveI := GlobalTheory.T.regular_local_ring_fraction_field X Ω ξ hξ p
  obtain ⟨hdom, hic⟩ := hnorm p.1
  haveI : IsDomain (regAt ξ p) := inferInstance
  haveI : IsNoetherianRing (X.presheaf.stalk p.1) := inferInstance
  haveI : IsNoetherianRing (regAt ξ p) := isNoetherianRing_of_ringEquiv _ (regIso hξ p)
  haveI : IsIntegrallyClosed (regAt ξ p) := IsIntegrallyClosed.of_equiv (regIso hξ p)
  haveI : FiniteDimensional Ω E := (GlobalTheory.T.lie_model_finite_projective X G Ω ξ E M).1
  obtain ⟨f1, p1, s1⟩ := lat_fin hξ G M p
  obtain ⟨f2, p2, s2⟩ := lat_fin hξ G' M' p
  refine GroundTheory.Heights₂.Heights.Model.LatticesAgree.proof GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.proof (regAt ξ p) Ω E (M.lat p) (M'.lat p) f1 p1 f2 p2 s1 s2 ?_
  intro P hP1
  obtain ⟨q, hs, hdvr, hu, hd⟩ := GlobalTheory.T.height_one_prime_dvr_stalk X Ω ξ hξ hN hnorm p P hP1
  have hq := GlobalTheory.T.semiabelian_lie_lattice_eq X Ω ξ hξ G G' GΩ φ φ' hS hS' hP hP' E M M' hv q hdvr
  ext v
  rw [mem_localizedIn_iff hξ G M hs P hu hd, mem_localizedIn_iff hξ G' M' hs P hu hd, hq]

end GlobalTheory.CompanionTheory.Ar.LieStalk
