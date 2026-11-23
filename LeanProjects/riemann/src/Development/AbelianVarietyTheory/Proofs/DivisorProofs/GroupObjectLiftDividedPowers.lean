import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftDeRhamUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleLiftOfNilpotentDividedPowersThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftSymmetricOfSymmetricReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetFiniteLengthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftPullbackOneProdEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDifferentialUniqueStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RMDeform

theorem exists_lift_abelian (GD : GlobalTheory.Published.GrothendieckDeformation) (ADR : GlobalTheory.Published.AbelianDeRham)
    {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (κ : DividedPowers I) (hκ : IsNilDP κ) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) {g : ℕ}
    {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap π) i) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (E : Submodule R (Crys κ (spMap π) A₀)) (hE : ∃ N, IsCompl E N)
    (hF : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI A₀).Corr d y) :
    ∃ (A' : Over (Sp R)) (_ : GrpObj A') (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'),
      IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ liftFil κ h' = E := by
  obtain ⟨HC, HL, -⟩ := GD R I κ hκ R₀ π hπ hI
  have b := (HC g A₀ A i h hA hg).1
  have c := HC.crysToDR_bijective h hA hg
  obtain ⟨N, hN⟩ := hE
  have adm : GlobalTheory.Published.GrothendieckMessing.IsAdmissible h (E.map (crysToDR κ h)) := by
    refine ⟨⟨N.map (crysToDR κ h), (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).isCompl hN⟩,
      fun y ↦ ?_⟩
    rw [hF]
    constructor
    · rintro ⟨d, hd, e⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).2 e⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, e⟩
      exact ⟨d, hd, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).1 e⟩
  obtain ⟨A', _, i', h', hA', hg', e⟩ := HL g A₀ A i h hA hg _ adm
  exact ⟨A', inferInstance, i', h', hA', hg', by rw [e, Submodule.comap_map_eq_of_injective c.1]⟩

theorem lbIso_pull_square {X₀ X Y₀ Y : Scheme.{0}} {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB)
    {l : X₀ ⟶ X} (e : LBIso (P.pull l) P₀) (a₀ : Y₀ ⟶ X₀) (a : Y ⟶ X) (y : Y₀ ⟶ Y) (w : a₀ ≫ l = y ≫ a) :
    LBIso (P₀.pull a₀) ((P.pull a).pull y) := by
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull hP₀, ← (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP l) hP₀).2 e, GlobalTheory.CechPic.cls_pull hP,
    GlobalTheory.CechPic.cls_pull (pull_isLB hP a), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp,
    ← GlobalTheory.CechPic.pull_comp, w]

theorem exists_deform : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → ∀ (hI : RingHom.ker π = I)
    (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left), IsGrpPullback X₀.A A (spMap π) i →
    IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
    ∀ (E : Submodule R (Crys κ (spMap π) X₀.A)), (∃ N : Submodule R (Crys κ (spMap π) X₀.A), IsCompl E N) →
      (∀ y : HdR X₀.A, y ∈ Fil X₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI X₀.A).Corr d y) →
      (∀ (a : 𝓞 F), ∀ d ∈ E, act κ (spMap π) X₀.rm a d ∈ E) →
      (∀ (c : 𝔠.elt) (φ : Crys κ (spMap π) X₀.A →ₗ[R] Crys κ (spMap π) X₀.A →ₗ[R] R),
        GlobalTheory.AbDual.IsCorrForm κ (spMap π) X₀.A X₀.A (X₀.P c) φ → ∀ a ∈ E, ∀ b ∈ E, φ a b = 0) →
      ∃ (X' : Obj F 𝔠 (Sp R)) (i' : X₀.A.left ⟶ X'.A.left) (pull : X₀.IsPullBy X' (spMap π) i'), liftFil κ pull.grp = E := by
  intro GD ADR ADC F _ _ _ 𝔠 R R₀ _ _ I κ hκ π hπ hI X₀ A _ i h hA hg E hE hFil hstab hiso
  obtain ⟨A', _, i', h', hA', hg', rfl⟩ := exists_lift_abelian GD ADR κ hκ π hπ hI h hA hg E hE hFil
  haveI : IsCommMonObj A' := hA'.comm
  obtain ⟨rm', hrm'⟩ := GlobalTheory.T.abelian_lift_crystalline_comparison GD R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' (𝓞 F) X₀.rm hstab
  obtain ⟨l, l₁, l₂⟩ := GlobalTheory.AbDual.exists_prod_pullback h' h'
  have hsq : IsSquare i' l := ⟨l₁, l₂⟩
  obtain ⟨cp, hcp⟩ := fracId_exists_totPos F 𝔠
  have hdiag₀ : (X₀.diag cp).IsLB := pull_isLB (X₀.isLB cp) _
  have C := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ hI hA' hg' hA' hg' h' h'
  have hP : ∀ c : 𝔠.elt, ∃ P : LB (G2 A').left, P.IsLB ∧ HasGen (P.pull (lift (1 : A' ⟶ A') (𝟙 A')).left) ∧
      HasGen (P.pull (lift (𝟙 A') (1 : A' ⟶ A')).left) ∧ LBIso (P.pull l) (X₀.P c) := by
    intro c
    obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.AbDual.exists_isCorrForm C (X₀.isLB c) (X₀.rig₁ c) (X₀.rig₂ c)
    obtain ⟨P, hP, t₁, t₂, -, -, e⟩ := GlobalTheory.BirigidLift.exists_lift GD ADR ADC hκ hπ hI hA' hg' hA' hg' h' h' l₁ l₂
      hdiag₀ (X₀.pos cp hcp) hdiag₀ (X₀.pos cp hcp) (X₀.isLB c) (X₀.rig₁ c) (X₀.rig₂ c) hφ₀ (hiso c φ₀ hφ₀)
    exact ⟨P, hP, t₁, t₂, e⟩
  choose P' hP'LB hr₁ hr₂ hP'e using hP
  have wΔ : (lift (𝟙 X₀.A) (𝟙 X₀.A)).left ≫ l = i' ≫ (lift (𝟙 A') (𝟙 A')).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, l₁, Category.assoc, GlobalTheory.AbDual.lift_left_fst, ← Category.assoc, GlobalTheory.AbDual.lift_left_fst]
      simp
    · rw [Category.assoc, l₂, Category.assoc, GlobalTheory.AbDual.lift_left_snd, ← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
      simp
  have pos' : ∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A' ((P' c).pull (lift (𝟙 A') (𝟙 A')).left) := by
    intro c hc
    haveI := hA'.smooth
    exact GlobalTheory.T.relAmple_lift_of_nilpotentDividedPowers_thickening R R₀ I κ hκ π hπ hI A' X₀.A i' h'.1 inferInstance _ (X₀.diag c) (pull_isLB (hP'LB c) _)
      (pull_isLB (X₀.isLB c) _) (lbIso_pull_square (hP'LB c) (X₀.isLB c) (hP'e c) _ _ i' wΔ) (X₀.pos c hc)
  have hL := pull_isLB (hP'LB cp) (lift (𝟙 A') (𝟙 A')).left
  have symm' : ∀ c, LBIso (P' c) ((P' c).pull (lift (snd A' A') (fst A' A')).left) := fun c ↦
    GlobalTheory.T.birigidified_lift_symmetric_of_symmetric_reduction GD ADC R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' l hsq _ hL (pos' cp hcp) (X₀.P c) (X₀.isLB c)
      (X₀.symm c) (P' c) (hP'LB c) (hr₁ c) (hr₂ c) (hP'e c)
  have add' : ∀ c c', LBIso (P' c') (LB.div (P' (c + c')) (P' c)) := fun c c' ↦
    GlobalTheory.T.abelian_lift_de_rham_unique GD ADC R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' l hsq _ hL (pos' cp hcp) (X₀.P c) (X₀.P c')
      (X₀.P (c + c')) (X₀.isLB c) (X₀.isLB c') (X₀.isLB (c + c')) (X₀.add c c') (P' c) (P' c') (P' (c + c'))
      (hP'LB c) (hP'LB c') (hP'LB (c + c')) (hr₁ c) (hr₂ c) (hr₁ c') (hr₂ c') (hr₁ (c + c')) (hr₂ (c + c'))
      (hP'e c) (hP'e c') (hP'e (c + c'))
  have smul' : ∀ (a : 𝓞 F) c, LBIso (P' (a • c)) ((P' c).pull (lift (fst A' A') (snd A' A' ≫ rm'.act a)).left) :=
    fun a c ↦ by
      haveI := X₀.rm.hom a
      haveI := rm'.hom a
      exact GlobalTheory.T.birigidified_lift_pullback_one_prod_endomorphism GD ADC R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' l hsq _ hL (pos' cp hcp) (X₀.rm.act a)
        (rm'.act a) (hrm' a) (X₀.P c) (X₀.P (a • c)) (X₀.isLB c) (X₀.isLB (a • c)) (X₀.smul a c) (P' c) (P' (a • c))
        (hP'LB c) (hP'LB (a • c)) (hr₁ c) (hr₂ c) (hr₁ (a • c)) (hr₂ (a • c)) (hP'e c) (hP'e (a • c))
  have ker' := GlobalTheory.T.real_mult_lift_divided_powers GD ADR ADC F 𝔠 R R₀ I κ hκ π hπ hI X₀ A' i' h' hA' hg' rm' hrm' P' l hsq hP'LB hr₁ hr₂ hP'e
    symm' add' smul' pos'
  let X' : Obj F 𝔠 (Sp R) :=
    { A := A', ab := hA', dim := hg', rm := rm', P := P', isLB := hP'LB, rig₁ := hr₁, rig₂ := hr₂, symm := symm',
      add := add', smul := smul', pos := pos', ker := ker' }
  exact ⟨X', i', ⟨h', hrm', ⟨l, hsq, fun c ↦ (hP'e c).symm⟩⟩, rfl⟩

end GlobalTheory.RMDeform
