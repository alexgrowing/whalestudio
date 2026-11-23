import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceSurjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.HodgeSubExists

private theorem mem_of_forall_dualAnnihilator {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] {W N : Submodule R M} (hWN : IsCompl W N) {c : M}
    (hc : ∀ φ ∈ W.dualAnnihilator, φ c = 0) : c ∈ W := by
  let q := N.projectionOnto W hWN.symm
  let p : M →ₗ[R] M := N.subtype ∘ₗ q
  have hp : ∀ x ∈ W, p x = 0 := fun x hx ↦ by
    have hq : q x = 0 := (Submodule.projectionOnto_apply_eq_zero_iff hWN.symm).2 hx
    simp only [p, LinearMap.comp_apply, hq, map_zero]
  have h0 : p c = 0 := (Module.forall_dual_apply_eq_zero_iff R (p c)).1 fun φ ↦
    hc (φ ∘ₗ p) ((Submodule.mem_dualAnnihilator _).2 fun x hx ↦ by simp [hp x hx])
  exact (Submodule.projectionOnto_apply_eq_zero_iff hWN.symm).1 (Subtype.ext h0)

section Affine

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

private theorem exists_class (hLie : LieExact G) [Module.Finite R (primDR G)]
    [Module.Projective R (primDR G)] {N : Submodule R (primDR G)} (hN : IsCompl (PrimitiveSubmodule G) N)
    (tv : ∀ v : epsR R ⟶ G, IsTangent v → R)
    (tv_mul : ∀ v v' hv hv' hvv, tv (v * v') hvv = tv v hv + tv v' hv')
    (tv_smul : ∀ (r : R) v hv hrv, tv (GlobalTheory.GrpTangent.epsScale r ≫ v) hrv = r * tv v hv) :
    ∃ c ∈ PrimitiveSubmodule G, ∀ v (h : HdR G) (e : IsLieImage h v), h c = tv v e.1 := by
  have tv_congr : ∀ (v v' : epsR R ⟶ G) (hv : IsTangent v) (hv' : IsTangent v'),
      v = v' → tv v hv = tv v' hv' := by
    rintro v _ hv hv' rfl; rfl
  choose vh hvh vh_eq using hLie.1
  have hl : ∀ h v (e : IsLieImage h v), tv (vh h) (hvh h).1 = tv v e.1 := fun h v e ↦
    tv_congr _ _ _ _ (vh_eq h v e).symm
  let l : Module.Dual R (HdR G) :=
    { toFun := fun h ↦ tv (vh h) (hvh h).1
      map_add' := fun h k ↦ (hl _ _ ((hvh h).add (hvh k))).trans (tv_mul _ _ _ _ _)
      map_smul' := fun r h ↦ (hl _ _ ((hvh h).smul r)).trans (tv_smul _ _ _ _) }
  obtain ⟨c, hc⟩ := (Module.evalEquiv R (primDR G)).surjective l
  have hc' : ∀ (h : HdR G) v (e : IsLieImage h v), h c = tv v e.1 := fun h v e ↦
    (LinearMap.congr_fun hc h).trans (hl h v e)
  refine ⟨c, mem_of_forall_dualAnnihilator hN fun φ hφ ↦ ?_, fun v h e ↦ hc' h v e⟩
  have e : IsLieImage φ 1 := isLieImage_one_iff.2 hφ
  have h1 : IsTangent (GlobalTheory.GrpTangent.epsScale (0 : R) ≫ (1 : epsR R ⟶ G)) := by
    rw [MonObj.comp_one]; exact e.1
  rw [hc' φ 1 e, tv_congr _ _ e.1 h1 (MonObj.comp_one _).symm, tv_smul _ _ e.1 h1, zero_mul]

private theorem exists_class_of_pullback {T : Scheme.{0}} {A : Over T} [GrpObj A] [QuasiSeparated A.hom]
    {b : Sp R ⟶ T} {φ : G.left ⟶ A.left} (hφ : IsGrpPullback G A b φ)
    (hLie : LieExact G) [Module.Finite R (primDR G)]
    [Module.Projective R (primDR G)] {N : Submodule R (primDR G)} (hN : IsCompl (PrimitiveSubmodule G) N)
    (t : Γ((Scheme.Modules.pullback b).obj (omega A), ⊤)) :
    ∃ c ∈ PrimitiveSubmodule G, ∀ (v : epsR R ⟶ G) (h : HdR G), IsLieImage h v →
      ∀ (w : (v.left ≫ φ) ≫ A.hom = (Pdiv.specO R (DualNumber R)).hom ≫ b)
        (we : sec (epsZero R) ≫ v.left ≫ φ = b ≫ unitSec A),
        h c = (Scheme.ΓSpecIso (.of R)).hom ((TanFibre.form w we).app ⊤ t) := by
  have : QuasiSeparated G.hom := MorphismProperty.of_isPullback hφ.1 ‹_›
  let u := toOmega G ((omegaBase hφ).app ⊤ t)
  obtain ⟨c, hc, H⟩ := exists_class hLie hN
    (fun v hv ↦ u.1 ⟨v, (HodgeSubSurj.isTangent_iff_ptMap v).1 hv⟩)
    (fun v v' hv hv' hvv ↦ u.2.1 ⟨v, (HodgeSubSurj.isTangent_iff_ptMap v).1 hv⟩
      ⟨v', (HodgeSubSurj.isTangent_iff_ptMap v').1 hv'⟩ _)
    (fun r v hv hrv ↦ u.2.2 r ⟨v, (HodgeSubSurj.isTangent_iff_ptMap v).1 hv⟩ _)
  refine ⟨c, hc, fun v h e w we ↦ (H v h e).trans ?_⟩
  let x : Pdiv.LieG G := ⟨v, (HodgeSubSurj.isTangent_iff_ptMap v).1 e.1⟩
  have E := HodgeSubSurj.form_eq hφ x w we
  refine (toOmega_apply _ x).trans
    (congrArg (fun a : Γ(Sp R, ⊤) => (Scheme.ΓSpecIso (.of R)).hom a) ?_)
  exact (congr(($E).app ⊤ t)).symm

end Affine

private theorem main : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V)),
      ∃ c, c ∈ PrimitiveSubmodule (onAff A hV) ∧ GlobalTheory.HodgeSub.Corr A hV s c := by
  intro P T A _ g hA hg V hV s
  have := hA.proper
  have hB := VB.isAbelianScheme_onAff A hA hV
  have hgB := VB.smooth_onAff A hg hV
  obtain ⟨hLie, ⟨N, hN⟩, -, -, -⟩ := P.p5.2.1 Γ(T, V) (onAff A hV) g hB hgB
  obtain ⟨hF, hP, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim P.p5.1 hB hgB
  have h : IsGrpPullback (onAff A hV) A hV.fromSpec (pullback.fst A.hom hV.fromSpec) :=
    isGrpPullback_pullback A hV.fromSpec
  exact exists_class_of_pullback h hLie hN (GlobalTheory.QCoh.pullbackSections hV.fromSpec (omega A)
    hV.fromSpec_preimage_self.ge s)

end GlobalTheory.HodgeSubExists

theorem _root_.GlobalTheory.T.hodge_subbundle_correspondent_exists : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V)),
      ∃ c, c ∈ PrimitiveSubmodule (onAff A hV) ∧ GlobalTheory.HodgeSub.Corr A hV s c := GlobalTheory.HodgeSubExists.main
