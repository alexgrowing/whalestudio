import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationIntegersRankOneStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HenselianAlgClosedResidueStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenericPointOpenImmersionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SectionThroughClosedPointStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardMayerVietorisExtendStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericFibreInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericTrivialNearSpecialStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfSamePolarizationStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.SymB

theorem pic_inj {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R] [IsDomain R] [ValuationRing R]
    [Ring.DimensionLEOne R] [Algebra R C] [IsFractionRing R C] {X XK : Scheme.{0}} {f : X ⟶ Sp R} {j : XK ⟶ X}
    {fK : XK ⟶ Sp C} (H : IsPullback j fK f (spMap (algebraMap R C))) (h₁ : Smooth f) (h₂ : QuasiCompact f)
    (h₃ : GeometricallyIntegral f) (q : Pic X) (h : pull j q = 0) : q = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj q
  exact (cls_eq_zero_iff hM).2 (GlobalTheory.ValGenExtend.triv_of_triv_generic R C X XK f j fK H h₁ h₂ h₃ M hM
    ((cls_eq_zero_iff (pull_isLB hM j)).1 h))

theorem pull_sq_lam {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) (p : Pic A.left) :
    pull (sqToBase A s) (lam p (fst A A) (snd A A)) =
      lam (pull (pullback.fst A.hom s) p) (fst _ _) (snd _ _) := by
  have h := isGrpPullback_pullback A s
  rw [sqToBase, pull_lam, lift_fst, lift_snd, lam_pull_of_isGrpPullback h]
  rfl

theorem sq_fst {S S' : Scheme.{0}} (A : Over S) (s : S' ⟶ S) : sqToBase A s ≫ (fst A A).left =
    (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z ↦ z.left) (lift_fst (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

theorem sq_snd {S S' : Scheme.{0}} (A : Over S) (s : S' ⟶ S) : sqToBase A s ≫ (snd A A).left =
    (snd ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z ↦ z.left) (lift_snd (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

theorem isPullback_sq {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) :
    IsPullback (sqToBase A s) ((Over.pullback s).obj A ⊗ (Over.pullback s).obj A).hom (A ⊗ A).hom s :=
  have hg := isGrpPullback_pullback A s
  isPullback_prod hg.1 hg.1 (sq_fst A s) (sq_snd A s)

theorem inv_pull {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) :
    pullback.fst A.hom s ≫ (GrpObj.inv : A ⟶ A).left =
      (GrpObj.inv : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A).left ≫ pullback.fst A.hom s := by
  have h := isGrpPullback_pullback A s
  have e := map_inv (pushHom h ((Over.pullback s).obj A)) (𝟙 _)
  have e' := congrArg (fun q ↦ q.left) e
  simpa [pushHom, Hom.inv_def, pushPt] using e'.symm

abbrev jj {S S' : Scheme.{0}} (A : Over S) (s : S' ⟶ S) : ((Over.pullback s).obj A).left ⟶ A.left := pullback.fst A.hom s

theorem transl_id {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) (hS : ∀ c : Pic S', c = 0)
    (c : Pic (A ⊗ A).left) (l : Pic ((Over.pullback s).obj A).left)
    (h : pull (sqToBase A s) c = lam l (fst _ _) (snd _ _)) (d : 𝟙_ (Over S) ⟶ A) :
    ∃ τ : ((Over.pullback s).obj A).left ⟶ ((Over.pullback s).obj A).left,
      τ ≫ jj A s = jj A s ≫ (GlobalTheory.PolTranslate.transl d).left ∧
      l = pull τ l - pull (jj A s) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) := by
  have hg := isGrpPullback_pullback A s
  let B := (Over.pullback s).obj A
  let j : B.left ⟶ A.left := pullback.fst A.hom s
  have sq : (s ≫ d.left) ≫ A.hom = 𝟙 S' ≫ s := by
    have := Over.w d
    simp only [Category.assoc, Category.id_comp]
    rw [show d.left ≫ A.hom = (𝟙_ (Over S)).hom from this]
    exact Category.comp_id s
  let u : S' ⟶ B.left := hg.1.lift (s ≫ d.left) (𝟙 S') sq
  have hu₂ : u ≫ B.hom = 𝟙 S' := hg.1.lift_snd _ _ sq
  let t : B ⟶ B := Over.homMk (B.hom ≫ u) (by rw [Category.assoc, hu₂, Category.comp_id])
  have ht : t.left ≫ j = j ≫ (toUnit A ≫ d).left := by
    have e : (toUnit A ≫ d).left = A.hom ≫ d.left := rfl
    have e₀ : t.left = B.hom ≫ u := rfl
    have e₁ : u ≫ j = s ≫ d.left := hg.1.lift_fst _ _ sq
    rw [e, e₀, Category.assoc, e₁, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ d.left) (hg.1.w).symm
  let x₀ : Over.mk (B.hom ≫ s) ⟶ A := Over.homMk j hg.1.w
  let y₀ : Over.mk (B.hom ≫ s) ⟶ A := Over.homMk (j ≫ (toUnit A ≫ d).left) (by
    rw [Category.assoc, Over.w]; exact hg.1.w)
  have hτ : (𝟙 B * t).left ≫ j = j ≫ (GlobalTheory.PolTranslate.transl d).left := by
    have e := hg.2 B (𝟙 B) t x₀ y₀ (by simp [x₀, j]) (by simp only [y₀, Over.homMk_left]; exact ht.symm)
    rw [← e]
    have : x₀ * y₀ = x₀ ≫ GlobalTheory.PolTranslate.transl d := by
      rw [GlobalTheory.PolTranslate.transl, MonObj.comp_mul, Category.comp_id]
      congr 1
    rw [this]
    rfl
  refine ⟨(𝟙 B * t).left, hτ, ?_⟩
  have hlift : (lift (𝟙 B) t).left ≫ sqToBase A s = j ≫ (lift (𝟙 A) (toUnit A ≫ d)).left := by
    have a₁ : (lift (𝟙 B) t).left ≫ (fst B B).left = 𝟙 _ := congrArg (fun q ↦ q.left) (lift_fst (𝟙 B) t)
    have a₂ : (lift (𝟙 B) t).left ≫ (snd B B).left = t.left := congrArg (fun q ↦ q.left) (lift_snd (𝟙 B) t)
    have b₁ : (lift (𝟙 A) (toUnit A ≫ d)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun q ↦ q.left) (lift_fst (𝟙 A) (toUnit A ≫ d))
    have b₂ : (lift (𝟙 A) (toUnit A ≫ d)).left ≫ (snd A A).left = (toUnit A ≫ d).left :=
      congrArg (fun q ↦ q.left) (lift_snd (𝟙 A) (toUnit A ≫ d))
    refine pullback.hom_ext ?_ ?_
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, Category.assoc, b₁, sq_fst, ← Category.assoc, a₁]
      simp [j]
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, Category.assoc, b₂, sq_snd, ← Category.assoc, a₂]
      exact ht
  have h₀ : ∀ u : S' ⟶ B.left, pull (B.hom ≫ u) l = 0 := fun u ↦ by
    rw [pull_comp, hS (pull u l), map_zero]
  have e₁ : pull t.left l = 0 := h₀ u
  have e₂ : pull (1 : B ⟶ B).left l = 0 := by
    have : (1 : B ⟶ B).left = B.hom ≫ (η[B]).left := by rw [Hom.one_def]; rfl
    rw [this]; exact h₀ _
  have e₃ : pull (jj A s) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) = lam l (𝟙 B) t := by
    rw [← pull_comp]
    have : jj A s ≫ (lift (𝟙 A) (toUnit A ≫ d)).left = (lift (𝟙 B) t).left ≫ sqToBase A s := hlift.symm
    rw [this, pull_comp, h, pull_lam, lift_fst, lift_snd]
  rw [e₃, lam, e₁, e₂, Over.id_left, pull_id]
  abel

theorem near : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic (A ⊗ A).left)
    (l : Pic ((Over.pullback (spMap (algebraMap R C))).obj A).left),
    pull (sqToBase A (spMap (algebraMap R C))) c = lam l (fst _ _) (snd _ _) →
    ∀ y : A.left, IsClosed {y} → A.hom y = IsLocalRing.closedPoint R →
      ∃ V : A.left.Opens, y ∈ V ∧ pull (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0 := by
  intro C _ _ R _ _ _ _ _ _ A _ hA c l h y hy hyc
  obtain ⟨hH, hk⟩ := GlobalTheory.T.henselian_alg_closed_residue C R
  haveI := hA.comm
  have hs₀ := hA.smooth
  obtain ⟨V₀, hV₀, e₀⟩ := GlobalTheory.T.picard_generic_trivial_near_special C R A hA l
  obtain ⟨b₀, hb₀⟩ := (GlobalTheory.T.section_through_closed_point R A hs₀).2 V₀ hV₀
  obtain ⟨b, hb⟩ := (GlobalTheory.T.section_through_closed_point R A hs₀).1 y hy hyc
  let d : 𝟙_ (Over (Sp R)) ⟶ A := b⁻¹ * b₀
  obtain ⟨τ, hτ, hl⟩ := transl_id A (spMap (algebraMap R C)) (fun c ↦ GlobalTheory.ThetaExtend.pic_local c) c l h d
  have hbd : b ≫ GlobalTheory.PolTranslate.transl d = b₀ := by
    rw [GlobalTheory.PolTranslate.transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      toUnit_unique (b ≫ toUnit A) (𝟙 _), Category.id_comp, mul_inv_cancel_left]
  obtain ⟨V₂, hy₂, e₂⟩ := exists_pull_eq_zero (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) y
  refine ⟨(GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂, ⟨?_, hy₂⟩, ?_⟩
  · show (GlobalTheory.PolTranslate.transl d).left y ∈ V₀
    have e : (GlobalTheory.PolTranslate.transl d).left (b.left (IsLocalRing.closedPoint R)) =
        (b ≫ GlobalTheory.PolTranslate.transl d).left (IsLocalRing.closedPoint R) := by
      rw [Over.comp_left]; rfl
    rw [← hb, e, hbd]
    exact hb₀
  · set W := jj A (spMap (algebraMap R C)) ⁻¹ᵁ ((GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂) with hW
    have t₁ : pull W.ι (pull τ l) = 0 := by
      rw [← pull_comp]
      refine pull_eq_zero_of_mem (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V₀) (W.ι ≫ τ) (fun z ↦ ?_) e₀
      show jj A (spMap (algebraMap R C)) ((W.ι ≫ τ) z) ∈ V₀
      rw [← Scheme.Hom.comp_apply, Category.assoc, hτ, ← Category.assoc, Scheme.Hom.comp_apply]
      exact (show _ ∈ (GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂ from z.2).1
    have t₂ : pull W.ι (pull (jj A (spMap (algebraMap R C))) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c)) = 0 := by
      rw [← pull_comp]
      exact pull_eq_zero_of_mem V₂ (W.ι ≫ jj A (spMap (algebraMap R C)))
        (fun z ↦ (show _ ∈ (GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂ from z.2).2) e₂
    calc pull W.ι l = pull W.ι (pull τ l - pull (jj A (spMap (algebraMap R C)))
          (pull (lift (𝟙 A) (toUnit A ≫ d)).left c)) := congrArg _ hl
      _ = 0 := by rw [map_sub, t₁, t₂, sub_zero]

theorem extend : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ l : Pic ((Over.pullback (spMap (algebraMap R C))).obj A).left,
    (∀ y : A.left, IsClosed {y} → A.hom y = IsLocalRing.closedPoint R →
      ∃ V : A.left.Opens, y ∈ V ∧ pull (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0) →
    ∃ p : Pic A.left, pull (jj A (spMap (algebraMap R C))) p = l := by
  intro C _ _ R _ _ _ _ _ _ A _ hA l hn
  have hp₀ := hA.proper
  have hio := GlobalTheory.T.generic_point_open_immersion C R
  let j := jj A (spMap (algebraMap R C))
  have hjo : IsOpenImmersion j := by
    show IsOpenImmersion (pullback.fst A.hom (spMap (algebraMap R C)))
    infer_instance
  let U₀ : A.left.Opens := j.opensRange
  let Q : A.left.Opens → Prop := fun W ↦ IsCompact (W : Set A.left) ∧
    ∃ (r : ((Over.pullback (spMap (algebraMap R C))).obj A).left ⟶ W.toScheme) (p : Pic W.toScheme), r ≫ W.ι = j ∧ pull r p = l
  have hcA : CompactSpace A.left := by
    exact QuasiCompact.compactSpace_of_compactSpace A.hom
  have hcK : CompactSpace ((Over.pullback (spMap (algebraMap R C))).obj A).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd A.hom (spMap (algebraMap R C)))
  have hqs : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  have base : Q U₀ := by
    refine ⟨?_, j.isoOpensRange.hom, pull j.isoOpensRange.inv l, by simp [U₀], ?_⟩
    · have : (U₀ : Set A.left) = Set.range j := Scheme.Hom.coe_opensRange j
      rw [this]
      exact isCompact_range j.continuous
    · rw [← pull_comp, Iso.hom_inv_id, pull_id]
  have step : ∀ (W V : A.left.Opens), Q W → IsCompact (V : Set A.left) → pull (j ⁻¹ᵁ V).ι l = 0 → Q (W ⊔ V) := by
    rintro W V ⟨hW, r, p, hr, hp⟩ hV hl
    have hz : pull (A.left.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0 := by
      refine GlobalTheory.T.picard_generic_fibre_injective C R A hA (W ⊓ V) ?_ _ ?_
      · exact QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hW V.isOpen hV
      · have e : (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ (W ⊓ V)) ≫ A.left.homOfLE (inf_le_left : W ⊓ V ≤ W) =
            (j ⁻¹ᵁ (W ⊓ V)).ι ≫ r := by
          rw [← cancel_mono W.ι, Category.assoc, Category.assoc, hr, Scheme.homOfLE_ι]
          exact morphismRestrict_ι _ _
        rw [← pull_comp, e, pull_comp, hp]
        exact pull_eq_zero_of_mem (j ⁻¹ᵁ V) (j ⁻¹ᵁ (W ⊓ V)).ι (fun z ↦ (show _ ∈ W ⊓ V from z.2).2) hl
    obtain ⟨q, hq⟩ := GlobalTheory.T.picard_mayer_vietoris_extend A.left W V p hz
    refine ⟨hW.union hV, r ≫ A.left.homOfLE le_sup_left, q, by simp [hr], ?_⟩
    rw [pull_comp, hq, hp]
  have hN : ∀ z : A.left, ∃ N : A.left.Opens, z ∈ N ∧ ∀ W, Q W → Q (W ⊔ N) := fun z ↦ by
    obtain ⟨y, hyz, hy⟩ := (isClosed_closure (s := {z})).exists_closed_singleton ⟨z, subset_closure rfl⟩
    have hyc : A.hom y = IsLocalRing.closedPoint R := by
      have h₁ := A.hom.isClosedMap _ hy
      rw [Set.image_singleton] at h₁
      have h₂ := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 h₁
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal h₂)
    obtain ⟨V, hyV, hV⟩ := hn y hy hyc
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
    replace hU : IsAffineOpen U := hU
    refine ⟨U, (specializes_iff_mem_closure.2 hyz).mem_open U.isOpen hyU, fun W hW ↦ step W U hW hU.isCompact ?_⟩
    exact pull_eq_zero_of_mem (j ⁻¹ᵁ V) (j ⁻¹ᵁ U).ι (fun z ↦ hUV z.2) hV
  choose N hz hN using hN
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun z ↦ (N z : Set A.left)) (fun z ↦ (N z).isOpen.mem_nhds (hz z))
  have key : ∀ t : Finset A.left, Q (U₀ ⊔ t.sup N) := fun t ↦ by
    classical
    induction t using Finset.induction_on with
    | empty => simpa using base
    | insert a s _ ih =>
      have := hN a _ ih
      rwa [Finset.sup_insert, sup_comm (N a), ← sup_assoc]
  have htop : U₀ ⊔ t.sup N = ⊤ := by
    refine top_le_iff.1 fun z _ ↦ ?_
    have hz' : z ∈ ⋃ x ∈ t, (N x : Set A.left) := by rw [ht]; trivial
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 hz'
    exact Or.inr (Finset.le_sup (f := N) hx hzx)
  have hQ := key t
  rw [htop] at hQ
  obtain ⟨-, r, p, hr, hp⟩ := hQ
  refine ⟨pull A.left.topIso.inv p, ?_⟩
  have e : j ≫ A.left.topIso.inv = r := by
    rw [← hr, Category.assoc]
    have : (⊤ : A.left.Opens).ι = A.left.topIso.hom := rfl
    rw [this, Iso.hom_inv_id, Category.comp_id]
  rw [← pull_comp]
  exact (congrArg (fun q ↦ pull q p) e).trans hp

theorem relAmple_of_cls {K : Type} [CommRing K] (B : Over (Sp K)) {M N : LB B.left} (hM : M.IsLB) (hN : N.IsLB)
    (e : cls M hM = cls N hN) (h : Out.RelAmple B N) : Out.RelAmple B M := by
  obtain ⟨w, hw⟩ := (cls_eq_iff hM (pull_isLB hN (𝟙 _))).1 (e.trans (by rw [cls_pull hN, pull_id]))
  exact relAmple_pull (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) hN hM
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ ↦ trivial) h

theorem symmetricBundle (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem) : SymmetricBundleSt := by
  intro C _ _ v R _ _ hv A _ hA c hc
  obtain ⟨_, _, _, _⟩ := GlobalTheory.T.valuation_integers_rank_one C v R hv
  obtain ⟨hH, hk⟩ := GlobalTheory.T.henselian_alg_closed_residue C R
  haveI := hA.comm
  have hs₀ := hA.smooth
  have hp₀ := hA.proper
  have hc₀ := hA.geomConnected
  have hg := isGrpPullback_pullback A (spMap (algebraMap R C))
  have hB := PolPull.isAbelianScheme_of_isGrpPullback hA hg
  obtain ⟨L₀, hL₀, ha₀, hk₀, e₀⟩ := hc.2.2 C (spMap (algebraMap R C))
  obtain ⟨L', hL', -, hs', ha', -, hl'⟩ := RiemannExists.exists_sym_translate C _ hB L₀ hL₀ ha₀ hk₀
  have eK : pull (sqToBase A (spMap (algebraMap R C))) c = lam (cls L' hL') (fst _ _) (snd _ _) := e₀.trans hl'.symm
  obtain ⟨p, hp⟩ := extend C R A hA (cls L' hL') (near C R A hA c (cls L' hL') eK)
  obtain ⟨L, hL, rfl⟩ := cls_surj p

  have s₂ : Smooth (A ⊗ A).hom := by
    change Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have p₂ : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have c₂ : GeometricallyConnected (A ⊗ A).hom := by
    change GeometricallyConnected (pullback.fst A.hom A.hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hsq := isPullback_sq A (spMap (algebraMap R C))
  have hlam : lam (cls L hL) (fst A A) (snd A A) = c := by
    rw [← sub_eq_zero]
    refine pic_inj hsq s₂ inferInstance (gi _ _ _ s₂ c₂) _ ?_
    rw [map_sub, pull_sq_lam, hp, eK, sub_self]
  have hsym : Out.Sym A L := by
    refine GlobalTheory.RigSymSubring.sym_of_cls hL ?_
    rw [← sub_eq_zero]
    refine pic_inj hg.1 hs₀ inferInstance (gi _ _ _ hs₀ hc₀) _ ?_
    have e := inv_pull A (spMap (algebraMap R C))
    rw [map_sub, ← pull_comp, e, pull_comp, hp, GlobalTheory.RigSymSubring.cls_of_sym hL' hs', sub_self]
  obtain ⟨P, hP, ePc, hPd⟩ := GlobalTheory.AbDual.principalPol_selfDual hD hC _ A hA c hc
  have hkt : Out.KTriv A L := by
    refine GlobalTheory.ThetaExtend.kTriv_of_lam hL hP (ePc.trans hlam.symm) fun T x hx ↦ ?_
    have ev : ∀ {Y : Over (Sp R)} (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun a b ↦ by
      rw [evc, ePc, ← hlam, pull_lam, lift_fst, lift_snd]
    refine hPd.eq_one x ((triv_ev_iff hP _ _).2 ?_)
    rw [ev, lam_comm, ← ev]
    exact (triv_ev_iff hP _ _).1 hx
  refine ⟨L, hL, (GlobalTheory.RigSymSubring.rigidified_iff hL).2 (GlobalTheory.ThetaExtend.pic_local _), hsym, ?_, hkt, hlam.symm⟩
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  refine GlobalTheory.FibreAmple.relAmple_of_fibres hLaws R C A hA L hL ?_ ?_
  · exact relAmple_of_cls _ (pull_isLB hL _) hL' ((cls_pull hL _ _).trans hp) ha'
  · obtain ⟨L₁, hL₁, a₁, k₁, e₁⟩ := hc.2.2 (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R))
    have hB' := PolPull.isAbelianScheme_of_isGrpPullback hA (isGrpPullback_pullback A (spMap (IsLocalRing.residue R)))
    refine GlobalTheory.T.rel_ample_of_same_polarization _ _ hB' _ L₁ (pull_isLB hL _) hL₁ a₁ k₁ ?_
    rw [cls_pull hL, ← pull_sq_lam, hlam, e₁]

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.SymB
