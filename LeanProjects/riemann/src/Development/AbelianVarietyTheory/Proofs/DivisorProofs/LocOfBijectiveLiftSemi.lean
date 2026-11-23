import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEquivResM
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineGlueSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineCoverSectionsGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearLiftBijectiveLocalizationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

def bcProj {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) :
    (onAff A hV').left ⟶ (onAff A hV).left :=
  pullback.lift (pullback.fst A.hom hV'.fromSpec)
    (pullback.snd A.hom hV'.fromSpec ≫ Spec.map (T.presheaf.map (homOfLE h).op))
    (by rw [pullback.condition, Category.assoc, hV.map_fromSpec hV' (homOfLE h).op])

@[reassoc (attr := simp)] theorem bcProj_fst {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ V) : bcProj A hV hV' h ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem bcProj_snd {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ V) : bcProj A hV hV' h ≫ pullback.snd A.hom hV.fromSpec =
      pullback.snd A.hom hV'.fromSpec ≫ Spec.map (T.presheaf.map (homOfLE h).op) :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_bcProj {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ V) : letI := resAlg h
    IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) (bcProj A hV hV' h) := by
  letI := resAlg h
  letI : GrpObj ((Over.pullback hV.fromSpec).obj A) := inferInstanceAs (GrpObj (onAff A hV))
  letI : GrpObj ((Over.pullback hV'.fromSpec).obj A) := inferInstanceAs (GrpObj (onAff A hV'))
  have n := isGrpPullback_pullback A hV'.fromSpec
  refine (isGrpPullback_pullback A hV.fromSpec).cancel ?_ ?_
  · refine IsGrpPullback.congr n ?_ ?_
    · exact (hV.map_fromSpec hV' (homOfLE h).op).symm
    · exact (bcProj_fst A hV hV' h).symm
  · exact bcProj_snd A hV hV' h

theorem eq_bcProj {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (φ : (onAff A hV').left ⟶ (onAff A hV).left)
    (hφ : φ ≫ (onAff A hV).hom = (onAff A hV').hom ≫ Spec.map (T.presheaf.map (homOfLE h).op))
    (hf : φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec) :
    φ = bcProj A hV hV' h := by
  apply pullback.hom_ext
  · rw [hf, bcProj_fst]
  · exact hφ.trans (bcProj_snd A hV hV' h).symm

theorem bcProj_self {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ V) : bcProj A hV hV h = 𝟙 _ := by
  symm
  apply eq_bcProj
  · rw [Category.id_comp, show (homOfLE h).op = 𝟙 (Opposite.op V) from rfl, T.presheaf.map_id,
      Spec.map_id]
    exact (Category.comp_id _).symm
  · exact Category.id_comp _

theorem bcProj_comp {V V' V'' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hV'' : IsAffineOpen V'') (h : V' ≤ V) (h' : V'' ≤ V') :
    bcProj A hV' hV'' h' ≫ bcProj A hV hV' h = bcProj A hV hV'' (h'.trans h) := by
  apply eq_bcProj
  · change (bcProj A hV' hV'' h' ≫ bcProj A hV hV' h) ≫ pullback.snd A.hom hV.fromSpec = _
    rw [Category.assoc, bcProj_snd, bcProj_snd_assoc, ← Spec.map_comp, ← T.presheaf.map_comp]
    rfl
  · rw [Category.assoc, bcProj_fst, bcProj_fst]

theorem pull_eq_self {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {σ : R →+* R}
    {b : Sp R ⟶ Sp R} {φ : A.left ⟶ A.left}
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A σ b φ) (hσ : σ = RingHom.id R) (hφ : φ = 𝟙 _)
    (c : primDR A) : m.pull c = c := by
  subst hσ hφ
  exact Subtype.ext (IsMor.pullCohomologyOne_id m.isMor c.1)

theorem loc_of_bijective_liftSemi {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    [IsLocalization.Away f R'] {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R' M'] (ρ : M →ₛₗ[algebraMap R R'] M') (hρ : Function.Bijective (liftSemi ρ)) :
    (∀ m' : M', ∃ (n : ℕ) (x : M), algebraMap R R' f ^ n • m' = ρ x) ∧
      ∀ x : M, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0 :=
  GlobalTheory.T.semilinear_lift_bijective_localization f ρ hρ

section Data

variable {A} (H : GlobalTheory.Published.AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
  (hg : SmoothOfRelativeDimension g A.hom)

include hA in
theorem isAbelianScheme_onAff {V : T.Opens} (hV : IsAffineOpen V) : IsAbelianScheme (onAff A hV) :=
  isAbelianScheme_pullback_obj hV.fromSpec A hA

include hg in
theorem smooth_onAff {V : T.Opens} (hV : IsAffineOpen V) :
    SmoothOfRelativeDimension g (onAff A hV).hom :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback A.hom hV.fromSpec) hg

include H hA hg in
theorem small_primDR {V : T.Opens} (hV : IsAffineOpen V) : Small.{0} (primDR (onAff A hV)) := by
  obtain ⟨hf, -, -⟩ := H.1.prim (isAbelianScheme_onAff hA hV) (smooth_onAff hg hV)
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' Γ(T, V) (primDR (onAff A hV))
  exact small_of_surjective hf

def modV {V : T.Opens} (hV : IsAffineOpen V) : Type :=
  @Shrink.{0} (primDR (onAff A hV)) (small_primDR H hA hg hV)

instance {V : T.Opens} (hV : IsAffineOpen V) : AddCommGroup (modV H hA hg hV) := by
  letI := small_primDR H hA hg hV
  unfold modV
  infer_instance

instance {V : T.Opens} (hV : IsAffineOpen V) : Module Γ(T, V) (modV H hA hg hV) := by
  letI := small_primDR H hA hg hV
  unfold modV
  infer_instance

def shEquiv {V : T.Opens} (hV : IsAffineOpen V) : modV H hA hg hV ≃ₗ[Γ(T, V)] primDR (onAff A hV) := by
  letI := small_primDR H hA hg hV
  exact Shrink.linearEquiv Γ(T, V) (primDR (onAff A hV))

def rho {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) :
    modV H hA hg hV →+ modV H hA hg hV' :=
  letI := resAlg h
  { toFun := fun x => (shEquiv H hA hg hV').symm
      ((GlobalTheory.Published.AbelianDeRham.bcMor (isGrpPullback_bcProj A hV hV' h)).pull (shEquiv H hA hg hV x))
    map_zero' := by simp
    map_add' := fun x y => by simp }

theorem shEquiv_rho {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (x : modV H hA hg hV) : letI := resAlg h
    shEquiv H hA hg hV' (rho H hA hg hV hV' h x) =
      (GlobalTheory.Published.AbelianDeRham.bcMor (isGrpPullback_bcProj A hV hV' h)).pull (shEquiv H hA hg hV x) :=
  LinearEquiv.apply_symm_apply _ _

def data : Data T where
  M V hV := modV H hA hg hV
  grp V hV := inferInstance
  mod V hV := inferInstance
  ρ hV hV' h := rho H hA hg hV hV' h
  ρ_smul := by
    intro V V' hV hV' h a x
    letI := resAlg h
    apply (shEquiv H hA hg hV').injective
    rw [shEquiv_rho, map_smul, LinearMap.map_smulₛₗ, map_smul, shEquiv_rho]
    rfl
  ρ_self := by
    intro V hV h x
    apply (shEquiv H hA hg hV).injective
    rw [shEquiv_rho]
    refine pull_eq_self _ ?_ (bcProj_self A hV h) _
    ext a
    change (T.presheaf.map (homOfLE h).op).hom a = a
    rw [show (homOfLE h).op = 𝟙 (Opposite.op V) from rfl, T.presheaf.map_id]
    rfl
  ρ_ρ := by
    intro V V' V'' hV hV' hV'' h h' x
    apply (shEquiv H hA hg hV'').injective
    rw [shEquiv_rho, shEquiv_rho, shEquiv_rho]
    exact GrpMor.pull_pull _ _ _ (fun r => resG_resG' h h' (h'.trans h) r) (bcProj_comp A hV hV' hV'' h h') _
  loc_surj := by
    intro V hV f hD m
    letI := resAlg (T.basicOpen_le f)
    haveI : IsLocalization.Away f Γ(T, T.basicOpen f) := hV.isLocalization_basicOpen f
    have hbc := (H.2.2.1 _ (onAff A hV) g (isAbelianScheme_onAff hA hV) (smooth_onAff hg hV) _
      (onAff A hD) (bcProj A hV hD _) (isGrpPullback_bcProj A hV hD _)).1
    obtain ⟨n, x, hx⟩ := (loc_of_bijective_liftSemi f _ hbc).1 (shEquiv H hA hg hD m)
    refine ⟨n, (shEquiv H hA hg hV).symm x, (shEquiv H hA hg hD).injective ?_⟩
    rw [shEquiv_rho, LinearEquiv.apply_symm_apply, ← hx, map_smul]
    rfl
  loc_inj := by
    intro V hV f hD x hx
    letI := resAlg (T.basicOpen_le f)
    haveI : IsLocalization.Away f Γ(T, T.basicOpen f) := hV.isLocalization_basicOpen f
    have hbc := (H.2.2.1 _ (onAff A hV) g (isAbelianScheme_onAff hA hV) (smooth_onAff hg hV) _
      (onAff A hD) (bcProj A hV hD _) (isGrpPullback_bcProj A hV hD _)).1
    have hx' : rho H hA hg hV hD (T.basicOpen_le f) x = 0 := hx
    have h0 : (GlobalTheory.Published.AbelianDeRham.bcMor (isGrpPullback_bcProj A hV hD (T.basicOpen_le f))).pull
        (shEquiv H hA hg hV x) = 0 := by
      rw [← shEquiv_rho, hx', map_zero]
    obtain ⟨n, hn⟩ := (loc_of_bijective_liftSemi f _ hbc).2 (shEquiv H hA hg hV x) h0
    refine ⟨n, ?_⟩
    change (f ^ n • x : modV H hA hg hV) = 0
    apply (shEquiv H hA hg hV).injective
    rw [LinearEquiv.map_smul, hn, LinearEquiv.map_zero]

end Data

end GlobalTheory.DeRhamSheaf

namespace GlobalTheory.AffGlue

variable {T : Scheme.{0}}

theorem sep (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V) (hc : V ≤ ⨆ i, W i) (x : D.M V hV)
    (hx : ∀ i, D.ρ hV (hW i) (hWV i) x = 0) : x = 0 :=
  GlobalTheory.T.affine_glue_separated D hV W hW hWV hc x hx

theorem glue (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V) (hc : V ≤ ⨆ i, W i)
    (m : ∀ i, D.M (W i) (hW i))
    (hm : ∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j),
      D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) :
    ∃ x : D.M V hV, ∀ i, D.ρ hV (hW i) (hWV i) x = m i :=
  GlobalTheory.T.affine_cover_sections_glue D hV W hW hWV hc m hm

theorem isSheaf_famPresheaf (D : Data T) : (famPresheaf D).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ U sf hsf
  let s : ∀ k, fam D (U k) := sf
  have key : ∀ (k l : κ) (O : T.Opens) (hO : IsAffineOpen O) (hk : O ≤ U k) (hl : O ≤ U l),
      (s k).1 ⟨O, hO, hk⟩ = (s l).1 ⟨O, hO, hl⟩ := fun k l O hO hk hl =>
    congrFun (congrArg Subtype.val (hsf k l)) ⟨O, hO, le_inf hk hl⟩
  have cov : ∀ W : T.Opens, W ≤ iSup U → W ≤ ⨆ p : Σ k, AffIn (W ⊓ U k), p.2.1 := by
    intro W hW x hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hW hx)
    obtain ⟨O, hO, hxO, hOW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens)
      (show x ∈ W ⊓ U k from ⟨hx, hk⟩)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, O, hO, hOW⟩, hxO⟩
  have hle : ∀ (W : T.Opens) (p : Σ k, AffIn (W ⊓ U k)), p.2.1 ≤ W :=
    fun W p => p.2.2.2.trans inf_le_left
  have hleU : ∀ (W : T.Opens) (p : Σ k, AffIn (W ⊓ U k)), p.2.1 ≤ U p.1 :=
    fun W p => p.2.2.2.trans inf_le_right
  let val : ∀ (W : T.Opens) (p : Σ k, AffIn (W ⊓ U k)), D.M p.2.1 p.2.2.1 :=
    fun W p => (s p.1).1 ⟨p.2.1, p.2.2.1, hleU W p⟩
  have compat : ∀ (W : T.Opens) (p q : Σ k, AffIn (W ⊓ U k)) (O : T.Opens) (hO : IsAffineOpen O)
      (hp : O ≤ p.2.1) (hq : O ≤ q.2.1),
      D.ρ p.2.2.1 hO hp (val W p) = D.ρ q.2.2.1 hO hq (val W q) := by
    intro W p q O hO hp hq
    rw [fam_rel D (s p.1) ⟨p.2.1, p.2.2.1, hleU W p⟩ ⟨O, hO, hp.trans (hleU W p)⟩ hp,
      fam_rel D (s q.1) ⟨q.2.1, q.2.2.1, hleU W q⟩ ⟨O, hO, hq.trans (hleU W q)⟩ hq]
    exact key p.1 q.1 O hO (hp.trans (hleU W p)) (hq.trans (hleU W q))
  have ex : ∀ (W : T.Opens) (hW : IsAffineOpen W) (_ : W ≤ iSup U), ∃ x : D.M W hW,
      ∀ p : Σ k, AffIn (W ⊓ U k), D.ρ hW p.2.2.1 (hle W p) x = val W p := by
    intro W hW hWU
    exact glue D hW (fun p : Σ k, AffIn (W ⊓ U k) => p.2.1) (fun p => p.2.2.1) (hle W) (cov W hWU)
      (val W) (compat W)
  choose x hx using ex
  have uniq : ∀ (W : T.Opens) (hW : IsAffineOpen W) (_ : W ≤ iSup U) (y z : D.M W hW),
      (∀ p : Σ k, AffIn (W ⊓ U k), D.ρ hW p.2.2.1 (hle W p) y = D.ρ hW p.2.2.1 (hle W p) z) →
        y = z := by
    intro W hW hWU y z h
    rw [← sub_eq_zero]
    exact sep D hW (fun p : Σ k, AffIn (W ⊓ U k) => p.2.1) (fun p => p.2.2.1) (hle W) (cov W hWU) _
      (fun p => by rw [map_sub, h, sub_self])
  let t : fam D (iSup U) := ⟨fun W => x W.1 W.2.1 W.2.2, fun W W' h => by
    apply uniq W'.1 W'.2.1 W'.2.2
    intro p
    rw [D.ρ_ρ, hx]
    exact hx W.1 W.2.1 W.2.2 ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.trans (inf_le_inf_right _ h)⟩⟩
  refine ⟨t, fun k => ?_, fun y hy => ?_⟩
  · apply Subtype.ext
    funext O
    have := hx O.1 O.2.1 (O.2.2.trans (le_iSup U k)) ⟨k, O.1, O.2.1, le_inf le_rfl O.2.2⟩
    rw [D.ρ_self] at this
    exact this
  · have hy' : ∀ k (O : AffIn (U k)), (show fam D (iSup U) from y).1 ⟨O.1, O.2.1, O.2.2.trans (le_iSup U k)⟩ =
        (s k).1 O := fun k O => congrFun (congrArg Subtype.val (hy k)) O
    apply Subtype.ext
    funext W
    apply uniq W.1 W.2.1 W.2.2
    intro p
    rw [fam_rel D (show fam D (iSup U) from y) W ⟨p.2.1, p.2.2.1, (hle W.1 p).trans W.2.2⟩ (hle W.1 p), hx]
    exact hy' p.1 ⟨p.2.1, p.2.2.1, hleU W.1 p⟩

end GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

theorem exists_isDeRhamSheaf : GlobalTheory.Published.AbelianDeRham → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ H : T.Modules, IsDeRhamSheaf A H := by
  intro H T A _ g hA hg
  have hS := isSheaf_famPresheaf (data H hA hg)
  refine ⟨toModules (data H hA hg) hS, fun V hV => (secEquiv hS hV).trans (shEquiv H hA hg hV), ?_⟩
  intro V V' hV hV' h φ hφ hf s
  have e := eq_bcProj A hV hV' h φ (by exact hφ.1.w) hf
  subst e
  change shEquiv H hA hg hV' (secEquiv hS hV' (GlobalTheory.Twist.resM _ h s)) = _
  rw [secEquiv_resM]
  exact shEquiv_rho H hA hg hV hV' h _

end GlobalTheory.DeRhamSheaf
