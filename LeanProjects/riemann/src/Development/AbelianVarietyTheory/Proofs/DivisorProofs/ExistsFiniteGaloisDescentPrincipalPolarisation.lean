import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionCls
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LbIsoDescendsToSubfieldContainingFinset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumDescent

theorem qc_qs_tensor {S : Scheme.{0}} (A : Over S) [IsProper A.hom] :
    QuasiCompact (A ⊗ A).hom ∧ QuasiSeparated (A ⊗ A).hom := by
  have e : (A ⊗ A).hom = pullback.fst A.hom A.hom ≫ A.hom := rfl
  rw [e]; exact ⟨inferInstance, inferInstance⟩

theorem exists_galois_polAV : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∀ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB → Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) → Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  intro K _ _ A _ _ hA PP hPP Ω _ _ _ _ κ hκ L hL hS hΛ hAmp hKT
  haveI := hA.proper
  haveI := hA.smooth
  let σΩ : K →+* Ω := algebraMap K Ω
  let AΩ := (Over.pullback (spMap σΩ)).obj A
  have hAΩ : IsAbelianScheme AΩ := isAbelianScheme_pullback_obj _ A hA
  have hpΩ : IsGrpPullback AΩ A (spMap σΩ) (pullback.fst A.hom (spMap σΩ)) := isGrpPullback_pullback A _

  obtain ⟨F, hF, H⟩ := GlobalTheory.LBDescent.exists_finite_subextension_cls K Ω A.left AΩ.left A.hom AΩ.hom
    (pullback.fst A.hom (spMap σΩ)) hpΩ.1 L hL
  let f : Sp F ⟶ Sp K := spMap (algebraMap K F)
  let AF := (Over.pullback f).obj A
  have hAF : IsAbelianScheme AF := isAbelianScheme_pullback_obj f A hA
  have hpF : IsGrpPullback AF A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  have hcomp : spMap (algebraMap F Ω) ≫ f = spMap σΩ := by
    simp only [f, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have w : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap F Ω)) ≫ f := by
    rw [Category.assoc, hcomp]
    exact hpΩ.1.w
  let jm : AΩ.left ⟶ AF.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap F Ω)) w
  have hjf : jm ≫ pullback.fst A.hom f = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjs : jm ≫ AF.hom = AΩ.hom ≫ spMap (algebraMap F Ω) := pullback.lift_snd _ _ _
  have hj : IsGrpPullback AΩ AF (spMap (algebraMap F Ω)) jm :=
    IsGrpPullback.cancel hpF (hpΩ.congr hcomp.symm hjf.symm) hjs
  obtain ⟨x, hx⟩ := H AF.left AF.hom (pullback.fst A.hom f) (IsPullback.of_hasPullback _ _) jm hjf hjs
  obtain ⟨L₁, hL₁, rfl⟩ := CechPic.cls_surj x
  have hw : LBIso L (L₁.pull jm) := by
    rw [← CechPic.cls_eq_iff hL (pull_isLB hL₁ jm), CechPic.cls_pull hL₁ jm (pull_isLB hL₁ jm)]
    exact hx.symm

  have hPPlb : PP.IsLB := hPP
  obtain ⟨κF, hκF⟩ : ∃ κF : (G2 AF).left ⟶ (G2 A).left, IsSquare (pullback.fst A.hom f) κF :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hpF.1.w⟩
  obtain ⟨jm₂, hjm₂⟩ : ∃ jm₂ : (G2 AΩ).left ⟶ (G2 AF).left, IsSquare jm jm₂ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hj.1.w⟩
  have hΛF : (abelian₂ AF L₁).IsLB := DVR.linComb_isLB _ hL₁ _ _
  have hΛΩ : (abelian₂ AΩ L).IsLB := DVR.linComb_isLB _ hL _ _
  have hNF : (PP.pull κF).IsLB := pull_isLB hPPlb κF
  have eΩ : κ = jm₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hjm₂ hκF
    rw [hjf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ h
  have isoΩ : LBIso ((abelian₂ AF L₁).pull jm₂) ((PP.pull κF).pull jm₂) :=
    LBIso.trans (pull_isLB hΛF _) hΛΩ (pull_isLB hNF _)
      (GlobalTheory.LamPull.lbIso_lam_pull hj hL₁ hL hw hjm₂).symm
      (LBIso.trans hΛΩ (pull_isLB hPPlb _) (pull_isLB hNF _) hΛ
        (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF jm₂ eΩ).symm)
  haveI := hAF.proper
  haveI := hAF.smooth
  have hqq := qc_qs_tensor AF
  obtain ⟨s, hs⟩ := GlobalTheory.lbIso_descends_to_subfield_containing_finset F Ω (algebraMap F Ω) (G2 AF) (G2 AΩ) jm₂
    (abelian₂ AF L₁) (PP.pull κF) (GlobalTheory.SiegelDescent.isPullback_square hj.1 jm₂ hjm₂) hqq.1 hqq.2 hΛF hNF isoΩ

  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let F' : IntermediateField K Ω := F ⊔ IntermediateField.adjoin K (s : Set Ω)
  haveI : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  haveI : FiniteDimensional K F' := IntermediateField.finiteDimensional_sup _ _
  let E : IntermediateField K Ω := IntermediateField.normalClosure K F' Ω
  haveI hEf : FiniteDimensional K E := normalClosure.is_finiteDimensional K F' Ω
  haveI hEg : IsGalois K E := by
    haveI : Normal K E := inferInstance
    exact IsGalois.mk
  have hFE : F ≤ E := le_sup_left.trans F'.le_normalClosure
  have hsE : (s : Set Ω) ⊆ E := fun y hy =>
    F'.le_normalClosure (le_sup_right (a := F) (IntermediateField.subset_adjoin K _ hy))
  let α : F →+* E := (IntermediateField.inclusion hFE).toRingHom
  let e : Sp E ⟶ Sp K := spMap (algebraMap K E)
  let AE := (Over.pullback e).obj A
  have hAE : IsAbelianScheme AE := isAbelianScheme_pullback_obj e A hA
  have hpE : IsGrpPullback AE A e (pullback.fst A.hom e) := isGrpPullback_pullback A e
  have hcα : spMap α ≫ f = e := by
    simp only [f, e, α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wE : pullback.fst A.hom e ≫ A.hom = (AE.hom ≫ spMap α) ≫ f := by
    rw [Category.assoc, hcα]
    exact hpE.1.w
  let χ : AE.left ⟶ AF.left := pullback.lift (pullback.fst A.hom e) (AE.hom ≫ spMap α) wE
  have hχf : χ ≫ pullback.fst A.hom f = pullback.fst A.hom e := pullback.lift_fst _ _ _
  have hχs : χ ≫ AF.hom = AE.hom ≫ spMap α := pullback.lift_snd _ _ _
  have hχ : IsGrpPullback AE AF (spMap α) χ := IsGrpPullback.cancel hpF (hpE.congr hcα.symm hχf.symm) hχs
  obtain ⟨χ₂, hχ₂⟩ : ∃ χ₂ : (G2 AE).left ⟶ (G2 AF).left, IsSquare χ χ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hχ.1.w⟩
  have isoE : LBIso ((abelian₂ AF L₁).pull χ₂) ((PP.pull κF).pull χ₂) :=
    hs E α (algebraMap E Ω) (RingHom.ext fun _ => rfl) (fun y hy => ⟨⟨y, hsE hy⟩, rfl⟩) (G2 AE) χ₂
      (GlobalTheory.SiegelDescent.isPullback_square hχ.1 χ₂ hχ₂)

  let LE : LB AE.left := L₁.pull χ
  have hLE : LE.IsLB := pull_isLB hL₁ χ
  have hcE : spMap (algebraMap E Ω) ≫ e = spMap σΩ := by
    simp only [e, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wΩ : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap E Ω)) ≫ e := by
    rw [Category.assoc, hcE]
    exact hpΩ.1.w
  let jE : AΩ.left ⟶ AE.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap E Ω)) wΩ
  have hjEf : jE ≫ pullback.fst A.hom e = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjEs : jE ≫ AE.hom = AΩ.hom ≫ spMap (algebraMap E Ω) := pullback.lift_snd _ _ _
  have hjE : IsGrpPullback AΩ AE (spMap (algebraMap E Ω)) jE :=
    IsGrpPullback.cancel hpE (hpΩ.congr hcE.symm hjEf.symm) hjEs
  have hαΩ : spMap (algebraMap E Ω) ≫ spMap α = spMap (algebraMap F Ω) := by
    simp only [α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have ejm : jm = jE ≫ χ := by
    apply pullback.hom_ext
    · rw [hjf, Category.assoc, hχf, hjEf]
    · show jm ≫ AF.hom = (jE ≫ χ) ≫ AF.hom
      rw [hjs, Category.assoc, hχs, ← Category.assoc, hjEs, Category.assoc, hαΩ]
  have hwE : LBIso L (LE.pull jE) :=
    LBIso.trans hL (pull_isLB hL₁ jm) (pull_isLB hLE jE) hw
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ jE ejm).symm
  have hd := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend E Ω (algebraMap E Ω) AE AΩ jE LE L hAE hjE hLE hL hwE
  haveI := hAE.proper
  haveI := hAE.smooth
  have ha := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension E Ω (algebraMap E Ω) AE AΩ jE hjE LE L hLE hL
    hwE hAΩ.proper hAmp hKT
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim E AE hAE
  have hrig : Out.Rigidified AE LE := by
    have : Subsingleton (𝟙_ (Over (Sp E))).left := inferInstanceAs (Subsingleton (PrimeSpectrum E))
    exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum E) (pull_isLB hLE _)
  let A₁ : Out.PolAV (Sp E) :=
    { A := AE, isAb := hAE, g := g, smoothDim := hg, L := LE, isLB := hLE, rigid := hrig,
      sym := hd.2.1 hS, ample := ha.2.1, ktriv := ha.2.2 }
  refine ⟨E, inferInstance, inferInstance, hEf, hEg, A₁, Iso.refl _, ?_, fun κ' hκ' => ?_⟩
  · show IsMonHom (𝟙 AE); infer_instance
  have e' : κ' = χ₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hχ₂ hκF
    rw [hχf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ' h
  have hLE' : (LE.pull (𝟙 AE.left)).IsLB := pull_isLB hLE _
  have k₁ : LBIso (abelian₂ AE (LE.pull (𝟙 AE.left))) ((abelian₂ AF L₁).pull χ₂) :=
    GlobalTheory.LamPull.lbIso_lam_pull hχ hL₁ hLE' (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ (𝟙 _) (Category.id_comp χ).symm) hχ₂
  have k₂ : LBIso ((PP.pull κF).pull χ₂) (PP.pull κ') := GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF χ₂ e'
  exact LBIso.trans (DVR.linComb_isLB _ hLE' _ _) (pull_isLB hΛF _) (pull_isLB hPPlb _) k₁
    (LBIso.trans (pull_isLB hΛF _) (pull_isLB hNF _) (pull_isLB hPPlb _) isoE k₂)

end GlobalTheory.MumDescent
