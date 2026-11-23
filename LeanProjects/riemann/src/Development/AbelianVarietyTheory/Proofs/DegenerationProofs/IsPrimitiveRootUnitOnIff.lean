import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.SymLevelDescent

open GlobalTheory.ThetaDescent

theorem hypS_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)} {A : Over (Sp K)}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A₀) {φ : A.left ⟶ A₀.left}
    (h : IsGrpPullback A A₀ (spMap i) φ) {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hb : LBIso L (L₀.pull φ)) {w wd : A ⟶ A} {w₀ wd₀ : A₀ ⟶ A₀} (e : φ ≫ w₀.left = w.left ≫ φ)
    (ed : φ ≫ wd₀.left = wd.left ≫ φ) (hw : IsMonHom w) (hwd : IsMonHom wd) (hs : w * wd = 𝟙 A)
    (hp : LBIso L (cubeLB A ![𝟙 A, w] L))
    (ha : LBIso (cubeLB A ![fst A A ≫ w, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ wd] L)) :
    GlobalTheory.ZH.HypS A₀ L₀ := by
  have F := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i
  have pa := fun {T : Over (Sp K)} (x : T ⟶ A) => GlobalTheory.SymSpread.pushPt_comp h e x
  have pd := fun {T : Over (Sp K)} (x : T ⟶ A) => GlobalTheory.SymSpread.pushPt_comp h ed x
  have hc : ∀ {T : Over (Sp K)} {n : ℕ} (x : Fin n → (T ⟶ A)), (cubeLB A x L).IsLB :=
    fun x => DVR.linComb_isLB _ hL _ _
  have hc₀ : ∀ {T : Over (Sp K₀)} {n : ℕ} (x : Fin n → (T ⟶ A₀)), (cubeLB A₀ x L₀).IsLB :=
    fun x => DVR.linComb_isLB _ hL₀ _ _
  refine ⟨w₀, wd₀, (F.2 A₀ A₀ A A φ φ w₀ w h h e).1 hw, (F.2 A₀ A₀ A A φ φ wd₀ wd h h ed).1 hwd, ?_, ?_, ?_⟩
  · let U := pushPt h.1.w (𝟙 A)
    have hU : U.left = φ := Category.id_comp _
    haveI : Epi U.left := hU ▸ (F.1 _ _ _ _ φ h.1).1
    apply preHom_injective U
    have b : pushPt h.1.w (w * wd) = pushPt h.1.w w * pushPt h.1.w wd := map_mul (pushHom h A) _ _
    have c := pa (𝟙 A)
    have d := pd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [hs, c, d, ← MonObj.comp_mul] at b
    exact b.symm.trans (Category.comp_id _).symm
  · let U := pushPt h.1.w (𝟙 A)
    have hU : U.left = φ := Category.id_comp _
    have h₁ := GlobalTheory.SymSpread.lbIso_cube h hL₀ hL hb ![𝟙 A₀, w₀] ![𝟙 A, w] U (fun i => by
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rw [hU] at h₁
    refine (lb_gen_iso_descend_field K₀ K i _ _ A₀.hom A.hom φ hA.smooth hA.proper hA.geomConnected h.1).2 _ _ hL₀
      (hc₀ _) ?_
    exact LBIso.trans (pull_isLB hL₀ _) hL (pull_isLB (hc₀ _) _) hb.symm
      (LBIso.trans hL (hc _) (pull_isLB (hc₀ _) _) hp h₁)
  · have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
    let U := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
    have h₁ := GlobalTheory.SymSpread.lbIso_cube h hL₀ hL hb ![fst A₀ A₀ ≫ w₀, snd A₀ A₀] ![fst A A ≫ w, snd A A] U (fun i => by
      fin_cases i
      · exact (pa _).trans (by simp [U])
      · simp [U])
    have h₂ := GlobalTheory.SymSpread.lbIso_cube h hL₀ hL hb ![fst A₀ A₀, snd A₀ A₀ ≫ wd₀] ![fst A A, snd A A ≫ wd] U (fun i => by
      fin_cases i
      · simp [U]
      · exact (pd _).trans (by simp [U]))
    refine (lb_gen_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom (A ⊗ A).hom U.left A₂.smooth A₂.proper A₂.geomConnected
      (GlobalTheory.SymSpread.isPullback_square h)).2 _ _ (hc₀ _) (hc₀ _) ?_
    exact LBIso.trans (pull_isLB (hc₀ _) _) (hc _) (pull_isLB (hc₀ _) _) h₁.symm
      (LBIso.trans (hc _) (hc _) (pull_isLB (hc₀ _) _) ha h₂)

theorem unitOn_zpow {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn u ^ n = unitOn (u ^ n) :=
  (map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom) _ n).symm

theorem isPrimitiveRoot_unitOn_iff {R : Type} [CommRing R] (u : Rˣ) (k : ℕ) :
    IsPrimitiveRoot (unitOn u) k ↔ IsPrimitiveRoot u k :=
  IsPrimitiveRoot.map_iff_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom)
    (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1)

theorem level_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (Q : Out.PolAV (Sp K))
    (A₀ : Over (Sp K₀)) [GrpObj A₀] (hab : IsAbelianScheme A₀) (hdim : SmoothOfRelativeDimension Q.g A₀.hom)
    (L₀ : LB A₀.left) (hL : L₀.IsLB) (hr : Out.Rigidified A₀ L₀) (hs : Out.Sym A₀ L₀) (hamp : Out.RelAmple A₀ L₀)
    (hk : Out.KTriv A₀ L₀) {φ : Q.A.left ⟶ A₀.left} (hp : IsGrpPullback Q.A A₀ (spMap i) φ)
    (hw : LBIso Q.L (L₀.pull φ)) (k : ℕ) (z : K₀ˣ) (t : Out.Level Q k (unitOn (Units.map i.toMonoidHom z)))
    (pt₀ : Fin (2 * Q.g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (hpt : ∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) :
    Nonempty (Out.Level ⟨A₀, hab, Q.g, hdim, L₀, hL, hr, hs, hamp, hk⟩ k (unitOn z)) := by
  let U : Over.mk ((Out.baseOver (Sp K)).hom ≫ spMap i) ⟶ Out.baseOver (Sp K₀) := Over.homMk (spMap i) (by simp)
  haveI : Epi U.left := epi_spMap i
  have hU : ∀ a, pushHom hp _ (t.pt a) = preHom U (pt₀ a) := fun a => Over.OverMorphism.ext (hpt a)
  have key : ∀ (K' : Type) [Field K'] (x : Sp K' ⟶ Sp K₀), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (s : Sp Ω ⟶ Sp K) (N : Type) (_ : Monoid N) (P : (Over.mk s ⟶ Q.A) →* N) (R : (Over.mk x ⟶ A₀) →* N),
      Function.Bijective P ∧ Function.Injective R ∧
      ∀ a, P ((Over.homMk s (by simp) : Over.mk s ⟶ Out.baseOver _) ≫ t.pt a) =
        R ((Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver _) ≫ pt₀ a) := by
    intro K' _ x
    obtain ⟨x', rfl⟩ := Spec.map_surjective x
    obtain ⟨Ω, _, _, j, j', hj⟩ := GlobalTheory.exists_algClosed_join_of_two_field_extensions K₀ K K' i x'.hom
    have hc : spMap j' ≫ Spec.map x' = spMap j ≫ spMap i := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hj.symm
    let V : Over.mk ((Over.mk (spMap j)).hom ≫ spMap i) ⟶ Over.mk (Spec.map x') := Over.homMk (spMap j') hc
    haveI : Epi V.left := epi_spMap j'
    refine ⟨Ω, inferInstance, inferInstance, spMap j, _, inferInstance, pushHom hp (Over.mk (spMap j)), preHom V,
      pushHom_bijective hp _, preHom_injective V, fun a => ?_⟩
    apply Over.OverMorphism.ext
    show (spMap j ≫ (t.pt a).left) ≫ φ = spMap j' ≫ Spec.map x' ≫ (pt₀ a).left
    rw [Category.assoc, hpt, ← Category.assoc, ← hc, Category.assoc]
  refine ⟨{ pt := pt₀, prim := ?_, torsion := fun a => ?_, indep := ?_, span := ?_, pairing := fun a a' => ?_ }⟩
  · exact (isPrimitiveRoot_unitOn_iff _ _).2 (((isPrimitiveRoot_unitOn_iff _ _).1 t.prim).of_map_of_injective
      (Units.map_injective i.injective))
  · apply preHom_injective U
    rw [map_pow, ← hU, ← map_pow, t.torsion, map_one, map_one]
  · intro K' _ _ x c c' hc
    obtain ⟨Ω, _, _, s, N, _, P, R, hP, hR, H⟩ := key K' x
    refine t.indep Ω s c c' (hP.1 ?_)
    have := congrArg R hc
    unfold Out.linComb at this ⊢
    rw [map_prod_pow, map_prod_pow] at this ⊢
    simpa only [H] using this
  · intro K' _ _ x y₀ hy
    obtain ⟨Ω, _, _, s, N, _, P, R, hP, hR, H⟩ := key K' x
    obtain ⟨y, hy'⟩ := hP.2 (R y₀)
    obtain ⟨c, hc⟩ := t.span Ω s y (hP.1 (by rw [map_pow, hy', ← map_pow, hy, map_one, map_one]))
    refine ⟨c, hR ?_⟩
    have := (congrArg P hc).trans hy'
    unfold Out.linComb at this ⊢
    rw [map_prod_pow] at this ⊢
    simpa only [H] using this
  · haveI := hab.comm
    have h₁ := (GlobalTheory.weilIs_grpPullback_of_comm _ _ A₀ Q.A (spMap i) φ L₀ Q.L hL Q.isLB hp hw _ k (t.pt a) (t.pt a')
      (U ≫ pt₀ a) (U ≫ pt₀ a') _ (hpt a).symm (hpt a').symm).1 (t.pairing a a')
    rw [unitOn_zpow] at h₁ ⊢
    refine (GlobalTheory.T.weilPairing_fieldExtension_iff _ A₀ K₀ K i (𝟙 _) L₀ k (pt₀ a) (pt₀ a') _ hab hL).1 ?_
    rw [map_zpow]
    exact (weilIs_congr (by simp) L₀ k _ _ _ _ rfl rfl _).1 h₁

theorem exists_fg_subalgebra {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) :
    letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
    ∃ R₀ : Subalgebra o (gen β s), R₀.FG ∧ ∀ x : gen β s, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b := by
  letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
  let s₀ : Set (gen β s) := (gen β s).subtype ⁻¹' (s : Set K)
  have hfin : s₀.Finite := s.finite_toSet.preimage (gen β s).subtype.injective.injOn
  refine ⟨Algebra.adjoin o s₀, Subalgebra.fg_def.2 ⟨s₀, hfin, rfl⟩, fun x => ?_⟩
  have hle : Subring.closure (Set.range β ∪ (s : Set K)) ≤
      (Algebra.adjoin o s₀).toSubring.map (gen β s).subtype := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨a, rfl⟩ | hy)
    · exact ⟨algebraMap o _ a, Subalgebra.algebraMap_mem _ a, rfl⟩
    · exact ⟨⟨y, subset_gen β le_rfl hy⟩, Algebra.subset_adjoin hy, rfl⟩
  obtain ⟨a, ha, b, hb, e⟩ := Subfield.mem_closure_iff.1 x.2
  obtain ⟨a, ha', rfl⟩ := hle ha
  obtain ⟨b, hb', rfl⟩ := hle hb
  exact ⟨a, ha', b, hb', Subtype.ext e.symm⟩

theorem descends_to_fg_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Q : Out.PolAV (Sp Ω)) (M : ℕ) (ze : oˣ), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) → Nonempty (Out.Level Q M (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze))) → ∃ (Ω₀ : Type) (_ : Field Ω₀) (_ : Algebra o Ω₀) (j : Ω₀ →ₐ[o] Ω) (R₀ : Subalgebra o Ω₀) (Q₀ : Out.PolAV (Sp Ω₀)) (φ : Q.A.left ⟶ Q₀.A.left), R₀.FG ∧ (∀ x : Ω₀, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) ∧ Q₀.g = Q.g ∧ IsGrpPullback Q.A Q₀.A (spMap j.toRingHom) φ ∧ (letI := Q₀.isAb.comm; GlobalTheory.ZH.HypS Q₀.A Q₀.L) ∧ Nonempty (Out.Level Q₀ M (unitOn (Units.map (algebraMap o Ω₀).toMonoidHom ze))) := by
  intro o K _ _ _ t M ze ⟨w, wd, hw, hwd, hsum, hpol, hadj⟩ ⟨lev⟩
  classical
  let β : o →+* K := algebraMap o K
  let act : Bool → (t.A ⟶ t.A) := fun j => cond j w wd
  obtain ⟨s₀, H₀⟩ := GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.T.exists_lineBundle_descent_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ Bool (fun j => (act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K (gen β s₀) (Sp (gen β s₀)) (Sp K) (𝟙 _) (𝟙 _) (spMap (gen β s₀).subtype) X₀ p₀
    (Fin (2 * t.g)) (fun a => (lev.pt a).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun a => by
      have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) (Sp (gen β s)) (𝟙 _) inc
    (spMap (gen β s).subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype h) (by simp)
  let act₁ : Bool → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : Fin (2 * t.g) → (Out.baseOver (Sp (gen β s)) ⟶ A₁) := fun a =>
    Over.homMk (sq₁.lift (x₁ a) (𝟙 _) (by rw [(hx₁ a).2]; simp)) (sq₁.lift_snd _ _ _)
  have hpt : ∀ a, (lev.pt a).left ≫ ψ = spMap (gen β s).subtype ≫ (pt₁ a).left := fun a => by
    have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
    have e₁ : (pt₁ a).left ≫ φ₁ = x₁ a := sq₁.lift_fst _ _ _
    have e₂ : (pt₁ a).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁]
      exact ((hx₁ a).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, hψ₂, ← Category.assoc, e]
      refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      exact ((congrArg _ e₂).trans (Category.comp_id _)).symm
  have hact : ∀ j, (act j).left ≫ ψ = ψ ≫ (act₁ j).left := fun j => by
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_scheme_descent_smooth_dimension _ K (gen β s).subtype A₁ t.A ψ hG t.isAb
  obtain ⟨hr, hs, hk⟩ := GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
    t.ample
  letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
  obtain ⟨R₀, hfg, hfrac⟩ := exists_fg_subalgebra β s
  refine ⟨gen β s, inferInstance, inferInstance, ⟨(gen β s).subtype, fun _ => rfl⟩, R₀,
    ⟨A₁, hab, t.g, hdim _ t.smoothDim, L₁, hL₁, hr t.rigid, hs t.sym, hamp, hk t.ktriv⟩, ψ, hfg, hfrac, rfl, hG, ?_, ?_⟩
  · have := t.isAb.comm
    have := hab.comm
    exact hypS_descend (gen β s).subtype hab hG hL₁ t.isLB hL (hact true).symm (hact false).symm hw hwd hsum hpol hadj
  · exact level_descend (gen β s).subtype t A₁ hab _ L₁ hL₁ _ _ _ _ hG hL M _ lev pt₁ hpt

end GlobalTheory.SymLevelDescent
