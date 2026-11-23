import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqCompSectionOfSurjectiveAppTop
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SurjectiveAppOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExtOfForallQuotient
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GroupRingHomConstOfLaurent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiRigid

open SplitTorus

section Affine

noncomputable def aug (R X : Type) [CommRing R] [AddCommGroup X] : AddMonoidAlgebra R X →+* R :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id R) 1 fun _ _ ↦ Commute.all _ _

theorem aug_single {R X : Type} [CommRing R] [AddCommGroup X] (a : X) (c : R) :
    aug R X (AddMonoidAlgebra.single a c) = c := by
  simp [aug]

theorem aug_comp (R X : Type) [CommRing R] [AddCommGroup X] :
    (aug R X).comp (algebraMap R _) = RingHom.id R :=
  RingHom.ext fun c ↦ aug_single 0 c

theorem unit_eq_one {R L X : Type} [CommRing R] [IsDomain R] [CommRing L] [Nontrivial L]
    [AddCommGroup X] [Module.Free ℤ X] (ρ : R →+* L) {u : AddMonoidAlgebra R X} (hu : IsUnit u)
    (h₁ : aug R X u = 1) (h₂ : AddMonoidAlgebra.mapRingHom X ρ u = 1) : u = 1 := by
  obtain ⟨a, c, -, rfl⟩ := isUnit_eq_single hu
  rw [aug_single] at h₁
  subst h₁
  rw [AddMonoidAlgebra.mapRingHom_single, map_one, AddMonoidAlgebra.one_def] at h₂
  rw [single_one_injective h₂, AddMonoidAlgebra.one_def]

variable {S : Scheme.{0}}

noncomputable def sp {A C : CommRingCat.{0}} (ψ : A ⟶ C) {s : Spec A ⟶ S} {s' : Spec C ⟶ S}
    (h : Spec.map ψ ≫ s = s') : Over.mk s' ⟶ Over.mk s := Over.homMk (Spec.map ψ) h

theorem pull_sp {A C : CommRingCat.{0}} (ψ : A ⟶ C) {s : Spec A ⟶ S} {s' : Spec C ⟶ S}
    (h : Spec.map ψ ≫ s = s') {Y : Type} [AddCommGroup Y] (g : Over.mk s ⟶ splitTorus S Y)
    (u : Γ((splitTorus S Y).left, ⊤)) : pull (sp ψ h ≫ g) u = ψ.hom (pull g u) := by
  let p : Spec A ⟶ (splitTorus S Y).left := g.left
  change (Scheme.ΓSpecIso C).hom.hom ((Spec.map ψ ≫ p).appTop.hom u) =
    ψ.hom ((Scheme.ΓSpecIso A).hom.hom (p.appTop.hom u))
  rw [appTop_comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

variable {R : CommRingCat.{0}} (X : Type) [AddCommGroup X] (t : Spec R ⟶ S)

noncomputable abbrev grpSpec : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (torusRing R X))) ≫ t)

noncomputable def unitSec : Over.mk t ⟶ grpSpec X t :=
  sp (A := torusRing R X) (CommRingCat.ofHom (aug R X)) (by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, aug_comp]; simp)

theorem unitSec_univPt : unitSec X t ≫ univPt X t = 1 :=
  pull_ext fun a ↦ by
    rw [pull_one_chi, unitSec, pull_sp]
    exact (congrArg (aug R X) (ev_chi t a)).trans (aug_single _ _)

theorem unitSec_left : (unitSec X t).left ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (torusRing R X))) = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, aug_comp]
  exact Spec.map_id R

theorem isPullback_univPt : IsPullback (univPt X t).left
    (Spec.map (CommRingCat.ofHom (algebraMap R (torusRing R X)))) (splitTorus S X).hom t := by
  refine IsPullback.of_right ?_ (Over.w _) (Diag.isPullback_torusFst S X)
  rw [show t ≫ toZ S = toZ _ from specULiftZIsTerminal.hom_ext _ _]
  have h := coord_ofCoord (T := grpSpec X t) (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X
    ((Int.castRingHom R).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom)) ≫
      (Scheme.ΓSpecIso (torusRing R X)).inv)
  have e : (univPt X t).left ≫ torusFst S X = _ :=
    ext_of_isAffine ((Iso.cancel_iso_inv_left (Scheme.ΓSpecIso _) _ _).1
      (h.trans (Scheme.ΓSpecIso_inv_naturality _)))
  rw [e]
  exact Diag.isPullback_groupRing R X

variable [Module.Free ℤ X] [Module.Finite ℤ X] [IsDomain R]

theorem exists_const (B : Over S) [GrpObj B] [IsProper B.hom] (d : grpSpec X t ⟶ B) :
    ∃ k : Spec R ⟶ B.left,
      d.left = Spec.map (CommRingCat.ofHom (algebraMap R (torusRing R X))) ≫ k :=
  groupRing_hom_const_of_laurent B.hom (laurent_point_const B) R X t d.left (Over.w d)

theorem affine_eq_one {H B : Over S} [GrpObj H] [GrpObj B] [IsProper B.hom] {Y : Type}
    [AddCommGroup Y] (i : splitTorus S Y ⟶ H) (q : H ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) (d : grpSpec X t ⟶ H) (h₁ : unitSec X t ≫ d = 1)
    {L : CommRingCat.{0}} [Nontrivial L] (ρ : R ⟶ L) {s : Spec (torusRing L X) ⟶ S}
    (hs : Spec.map (CommRingCat.ofHom (R := torusRing R X) (S := torusRing L X)
      (AddMonoidAlgebra.mapRingHom X ρ.hom)) ≫ (grpSpec X t).hom = s)
    (h₂ : sp _ hs ≫ d = 1) : d = 1 := by
  have hq : d ≫ q = toUnit _ ≫ η[B] := by
    obtain ⟨k, e⟩ := exists_const X t B (d ≫ q)
    have h : unitSec X t ≫ d ≫ q = 1 := by rw [reassoc_of% h₁, MonObj.one_comp]
    have h' := congrArg (·.left) h
    simp only [Over.comp_left _ _ _ (unitSec X t), e, reassoc_of% (unitSec_left X t)] at h'
    apply Over.OverMorphism.ext
    rw [e, h', Hom.one_def, Over.comp_left, Over.comp_left, ← Category.assoc]
    rfl
  have : Mono i := hk.flip.mono_snd_of_mono
  obtain ⟨d', rfl⟩ : ∃ d', d' ≫ i = d := ⟨hk.lift d _ hq, hk.lift_fst _ _ _⟩
  have e₁ : unitSec X t ≫ d' = 1 := by
    rw [← cancel_mono i, Category.assoc, h₁, MonObj.one_comp]
  have e₂ : sp _ hs ≫ d' = 1 := by
    rw [← cancel_mono i, Category.assoc, h₂, MonObj.one_comp]
  have : d' = 1 := pull_ext fun a ↦ by
    rw [pull_one_chi]
    refine unit_eq_one ρ.hom ((isUnit_chi Y a).map _) ?_ ?_
    · exact (pull_sp _ _ d' _).symm.trans
        ((congrArg (pull · (chi Y a)) e₁).trans (pull_one_chi a))
    · exact (pull_sp _ _ d' _).symm.trans
        ((congrArg (pull · (chi Y a)) e₂).trans (pull_one_chi a))
  rw [this, MonObj.one_comp]

end Affine

section Field

variable {K : Type} [Field K]

theorem torus_tensor_eq_one {H : Over (Spec (.of K))} [GrpObj H] (E : TorusExtension H)
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (W : Over (Spec (.of K))) [IsIntegral W.left] (w : 𝟙_ _ ⟶ W)
    (d : splitTorus (Spec (.of K)) X ⊗ W ⟶ H) (h₁ : lift 1 (𝟙 W) ≫ d = 1)
    (h₂ : lift (𝟙 _) (toUnit _ ≫ w) ≫ d = 1) : d = 1 := by
  letI := E.addCommGroup
  letI := E.grpB
  have := E.i_hom
  have := E.q_hom
  have := E.isAbelian.proper
  have := (torusExtension_smooth_geometricallyConnected H E).2.2.2.2
  let w' : Spec (.of K) ⟶ W.left := w.left
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := W.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (w' default)) isOpen_univ
  replace hV : IsAffineOpen V := hV
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  obtain ⟨ρ, hρ⟩ := exists_specMap_fromSpec_eq w' hV (by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z default])
  let t := hV.fromSpec ≫ W.hom
  let j : Over.mk t ⟶ W := Over.homMk hV.fromSpec rfl
  let a : grpSpec X t ⟶ Over.mk t := Over.homMk (Spec.map _) rfl
  let m : grpSpec X t ⟶ splitTorus (Spec (.of K)) X ⊗ W := lift (univPt X t) (a ≫ j)
  have hm : IsPullback m.left a.left (snd _ W).left hV.fromSpec := by
    refine IsPullback.of_right ?_ (congrArg (·.left) (lift_snd (univPt X t) (a ≫ j)))
      (IsPullback.of_hasPullback (splitTorus (Spec (.of K)) X).hom W.hom)
    rw [show m.left ≫ pullback.fst _ _ = (univPt X t).left from
      congrArg (·.left) (lift_fst (univPt X t) (a ≫ j))]
    exact isPullback_univPt X t
  have : IsOpenImmersion m.left := MorphismProperty.of_isPullback hm.flip inferInstance
  have : IsIntegral (splitTorus (Spec (.of K)) X ⊗ W).left :=
    isIntegral_pullback_of_smooth (splitTorus (Spec (.of K)) X).hom W.hom
  have : IsDominant m.left := ⟨m.left.isOpenEmbedding.isOpen_range.dense
    ⟨_, (unitSec X t).left (Classical.arbitrary (PrimeSpectrum Γ(W.left, V))), rfl⟩⟩
  have hw : w' ≫ W.hom = 𝟙 _ := Over.w w
  have hc : Spec.map (CommRingCat.ofHom (R := torusRing Γ(W.left, V) X) (S := torusRing (.of K) X)
      (AddMonoidAlgebra.mapRingHom X ρ.hom)) ≫ a.left =
      Spec.map (CommRingCat.ofHom (algebraMap K _)) ≫ Spec.map ρ := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun c ↦ AddMonoidAlgebra.mapRingHom_single _ _ _
  have key : m ≫ d = 1 := by
    refine affine_eq_one X t E.i E.q E.isKernel (m ≫ d) ?_ ρ rfl ?_
    · have : unitSec X t ≫ m = j ≫ lift 1 (𝟙 W) := by
        have ha : unitSec X t ≫ a = 𝟙 _ := Over.OverMorphism.ext (unitSec_left X t)
        simp only [m, comp_lift, unitSec_univPt, reassoc_of% ha, MonObj.comp_one, Category.comp_id]
      rw [reassoc_of% this, h₁, MonObj.comp_one]
    · have : ∀ {Z : Over (Spec (.of K))} (n : Z ⟶ grpSpec X t), n ≫ a ≫ j = toUnit _ ≫ w →
          n ≫ m ≫ d = 1 := fun n hn ↦ by
        rw [← MonObj.comp_one (n ≫ univPt X t), ← h₂, comp_lift_assoc, comp_lift_assoc, hn,
          Category.comp_id, comp_toUnit_assoc]
      refine this _ (Over.OverMorphism.ext ?_)
      change Spec.map _ ≫ a.left ≫ hV.fromSpec = (Spec.map _ ≫ a.left ≫ hV.fromSpec ≫ W.hom) ≫ w'
      rw [reassoc_of% hc, reassoc_of% hc, reassoc_of% hρ, hρ, hw, Category.comp_id]
  apply Over.OverMorphism.ext
  refine ext_of_isDominant_of_isSeparated H.hom ((Over.w d).trans (Over.w _).symm) m.left ?_
  rw [← Over.comp_left, key, ← Over.comp_left, MonObj.comp_one]

end Field

section Descent

variable {S : Scheme.{0}}

theorem exists_desc {G B Y : Over S} (p : G ⟶ B) [Flat p.left] [Surjective p.left]
    [QuasiCompact p.left] (f : G ⟶ Y)
    (H : ∀ (Z : Over S) (a b : Z ⟶ G), a ≫ p = b ≫ p → a ≫ f = b ≫ f) : ∃ g, p ≫ g = f := by
  have H' : ∀ {Z : Scheme.{0}} (a b : Z ⟶ G.left), a ≫ p.left = b ≫ p.left →
      a ≫ f.left = b ≫ f.left := fun {Z} a b h ↦
    congrArg (·.left) (H (Over.mk (a ≫ G.hom)) (Over.homMk a rfl) (Over.homMk b (by
      change b ≫ G.hom = a ≫ G.hom
      rw [← Over.w p, reassoc_of% h])) (Over.OverMorphism.ext h))
  have e := EffectiveEpi.fac p.left f.left H'
  refine ⟨Over.homMk (EffectiveEpi.desc p.left f.left H') ?_, Over.OverMorphism.ext e⟩
  rw [← cancel_epi p.left, reassoc_of% e, Over.w, Over.w]

theorem epi_of_fpqc {G B : Over S} (p : G ⟶ B) [Flat p.left] [Surjective p.left]
    [QuasiCompact p.left] : Epi p := Over.epi_of_epi_left p

theorem isPullback_whiskerRight {G B : Over S} (p : G ⟶ B) (W : Over S) :
    IsPullback (fst G W).left (p ▷ W).left p.left (fst B W).left := by
  refine IsPullback.of_bot ?_ (congrArg (·.left) (whiskerRight_fst p W).symm)
    (IsPullback.of_hasPullback B.hom W.hom)
  rw [show (p ▷ W).left ≫ pullback.snd B.hom W.hom = (snd G W).left from
    congrArg (·.left) (whiskerRight_snd p W), Over.w]
  exact IsPullback.of_hasPullback G.hom W.hom

instance {G B : Over S} (p : G ⟶ B) (W : Over S) [Flat p.left] : Flat (p ▷ W).left :=
  MorphismProperty.of_isPullback (isPullback_whiskerRight p W) ‹_›

instance {G B : Over S} (p : G ⟶ B) (W : Over S) [Surjective p.left] : Surjective (p ▷ W).left :=
  MorphismProperty.of_isPullback (isPullback_whiskerRight p W) ‹_›

instance {G B : Over S} (p : G ⟶ B) (W : Over S) [QuasiCompact p.left] :
    QuasiCompact (p ▷ W).left :=
  MorphismProperty.of_isPullback (isPullback_whiskerRight p W) ‹_›

theorem exists_eq_mul {T G B Z : Over S} [GrpObj G] [GrpObj B] {i : T ⟶ G} {q : G ⟶ B}
    [IsMonHom q] (hk : IsPullback i (toUnit _) q η[B]) {a b : Z ⟶ G} (h : a ≫ q = b ≫ q) :
    ∃ τ : Z ⟶ T, a = (τ ≫ i) * b :=
  ⟨hk.lift (a * b⁻¹) (toUnit _) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, h, mul_inv_cancel]; rfl),
    by rw [hk.lift_fst, inv_mul_cancel_right]⟩

theorem globalFns : Out.GlobalFnsSt :=
  GlobalFunctions.globalFns_of (fun _ _ f _ _ ↦ geometricallyIntegral_of_smooth f)
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

end Descent

section Main

variable {K : Type} [Field K]

theorem abelian_tensor_eq_one {B H : Over (Spec (.of K))} [GrpObj B] [GrpObj H]
    (hB : IsAbelianScheme B) [IsSeparated H.hom] (W : Over (Spec (.of K))) [ConnectedSpace W.left]
    (w : 𝟙_ _ ⟶ W) (g : B ⊗ W ⟶ H) (h₁ : lift 1 (𝟙 W) ≫ g = 1)
    (h₂ : lift (𝟙 B) (toUnit _ ≫ w) ≫ g = 1) : g = 1 := by
  have := hB.smooth
  have := hB.proper
  let ε : W ⟶ B ⊗ W := lift 1 (𝟙 W)
  let j : B ⟶ B ⊗ W := lift (𝟙 B) (toUnit _ ≫ w)
  have hεp : ε.left ≫ (snd B W).left = 𝟙 W.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hsm : Smooth (snd B W).left := by
    change Smooth (pullback.snd B.hom W.hom); infer_instance
  have huc : UniversallyClosed (snd B W).left := by
    change UniversallyClosed (pullback.snd B.hom W.hom); infer_instance
  have hsurj : ∀ V : W.left.Opens, Function.Surjective ((snd B W).left.app V).hom := fun V ↦
    surjective_app_of_isAbelianScheme globalFns _ (Out.TLinPf.isAb_pullback W.hom B hB) V
  have hw : w.left ≫ W.hom = 𝟙 _ := Over.w w
  have hpb : IsPullback j.left B.hom (snd B W).left w.left := by
    have hr : IsPullback (fst B W).left (snd B W).left B.hom W.hom := .of_hasPullback B.hom W.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : j.left ≫ (fst B W).left = 𝟙 B.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hw]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Over.comp_left]
      rfl
  have key : g.left = (snd B W).left ≫ ε.left ≫ g.left := by
    refine eq_comp_section_of_local_rigidity (snd B W).left ε.left g.left W.hom H.hom hεp
      ((Over.w g).trans (Over.w (snd B W)).symm) (snd B W).left.isOpenMap
      (local_rigidity _ _ _ _ _ _ hεp huc hsurj) (fun s ↦ ?_) ?_
    · have : W.hom ⁻¹' {s} = Set.univ := Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
      rw [this]
      exact isPreconnected_univ
    intro s
    refine ⟨w.left s, (η[H] : 𝟙_ _ ⟶ H).left s, Subsingleton.elim _ _, ?_⟩
    intro x hx
    obtain ⟨z, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback hpb x s hx
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h₂, Hom.one_def, Over.comp_left,
      Scheme.Hom.comp_apply]
    rfl
  have key' : g = snd B W ≫ ε ≫ g := Over.OverMorphism.ext key
  rw [key', h₁, MonObj.comp_one]

theorem tensor_eq_one {G H : Over (Spec (.of K))} [GrpObj G] [GrpObj H] (D : TorusExtension G)
    (E : TorusExtension H) (W : Over (Spec (.of K))) [IsIntegral W.left] (w : 𝟙_ _ ⟶ W)
    (f : G ⊗ W ⟶ H) (h₁ : lift 1 (𝟙 W) ≫ f = 1) (h₂ : lift (𝟙 G) (toUnit _ ≫ w) ≫ f = 1) :
    f = 1 := by
  letI := D.addCommGroup
  letI := D.grpB
  have := D.free
  have := D.finite
  have := D.i_hom
  have := D.q_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_quasiCompact
  obtain ⟨-, -, _, _, -⟩ := torusExtension_smooth_geometricallyConnected G D
  have := (torusExtension_smooth_geometricallyConnected H E).2.2.2.2
  have : IsIntegral (G ⊗ W).left := isIntegral_pullback_of_smooth G.hom W.hom
  let T := splitTorus (Spec (.of K)) D.X
  let act : T ⊗ (G ⊗ W) ⟶ G ⊗ W :=
    lift ((fst T _ ≫ D.i) * (snd T _ ≫ fst _ _)) (snd _ _ ≫ snd _ _)
  have hax : ∀ {Z : Over (Spec (.of K))} (x : Z ⟶ G), lift x (toUnit _ ≫ w) ≫ f = 1 := fun x ↦ by
    rw [← MonObj.comp_one x, ← h₂, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  have hact : ∀ {Z : Over (Spec (.of K))} (τ : Z ⟶ T) (b : Z ⟶ G ⊗ W),
      lift τ b ≫ act = lift ((τ ≫ D.i) * (b ≫ fst _ _)) (b ≫ snd _ _) := fun τ b ↦ by
    simp only [act, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have hinv : act ≫ f = snd _ _ ≫ f := by
    rw [← mul_inv_eq_one]
    refine torus_tensor_eq_one E D.X (G ⊗ W) (lift η w) _ ?_ ?_
    · rw [MonObj.comp_mul, GrpObj.comp_inv, reassoc_of% hact, lift_snd_assoc, MonObj.one_comp,
        _root_.one_mul, ← comp_lift, lift_fst_snd, Category.comp_id, mul_inv_cancel]
    · rw [MonObj.comp_mul, GrpObj.comp_inv, reassoc_of% hact, lift_snd_assoc, comp_lift, lift_snd,
        hax, hax, inv_one, _root_.mul_one]
  obtain ⟨g, rfl⟩ := exists_desc (D.q ▷ W) f fun Z a b h ↦ by
    have e₁ := h =≫ fst _ _
    have e₂ := h =≫ snd _ _
    simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd] at e₁ e₂
    obtain ⟨τ, hτ⟩ := exists_eq_mul D.isKernel (a := a ≫ fst _ _) (b := b ≫ fst _ _)
      (by simpa using e₁)
    have : a = lift τ b ≫ act := by rw [hact, ← hτ, ← e₂, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [this, Category.assoc, hinv, lift_snd_assoc]
  have := epi_of_fpqc D.q
  have : g = 1 := by
    refine abelian_tensor_eq_one D.isAbelian W w g ?_ ?_
    · rw [← h₁, lift_whiskerRight_assoc, MonObj.one_comp]
    · rw [← cancel_epi D.q, MonObj.comp_one, ← h₂, lift_whiskerRight_assoc, comp_lift_assoc,
        Category.comp_id, Category.id_comp, comp_toUnit_assoc]
  rw [this, MonObj.comp_one]

theorem isMonHom_of_axes {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
    (h : ∀ f : G ⊗ G ⟶ H, lift (𝟙 G) 1 ≫ f = 1 → lift 1 (𝟙 G) ≫ f = 1 → f = 1)
    (φ : G ⟶ H) (hφ : η[G] ≫ φ = η[H]) : IsMonHom φ := by
  have h1 : (1 : G ⟶ G) ≫ φ = 1 := by
    rw [Hom.one_def, Category.assoc, hφ, Hom.one_def]
  have := h (((fst G G * snd G G) ≫ φ) * ((fst G G ≫ φ) * (snd G G ≫ φ))⁻¹)
    (by simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1,
      _root_.mul_one, mul_inv_cancel])
    (by simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1,
      _root_.one_mul, mul_inv_cancel])
  rw [mul_inv_eq_one, Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
  refine ⟨hφ, ?_⟩
  rw [this]
  congr 1

theorem square_eq_one {G H : Over (Spec (.of K))} [GrpObj G] [GrpObj H] (D : TorusExtension G)
    (E : TorusExtension H) (f : G ⊗ G ⟶ H) (h₁ : lift (𝟙 G) 1 ≫ f = 1)
    (h₂ : lift 1 (𝟙 G) ≫ f = 1) : f = 1 := by
  obtain ⟨-, -, _, _, -⟩ := torusExtension_smooth_geometricallyConnected G D
  have : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  exact tensor_eq_one D E G η f h₂ h₁

theorem torus_const (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (.of K))) [GrpObj B] [IsProper B.hom] (f : splitTorus (Spec (.of K)) X ⟶ B) :
    f = toUnit _ ≫ η ≫ f := by
  obtain ⟨k, e⟩ := groupRing_hom_const_of_laurent B.hom (laurent_point_const B) K X (𝟙 _)
    ((torusIso K X).hom ≫ f.left) (by rw [Category.assoc, Over.w, torusIso_hom_hom, Category.comp_id])
  rw [← torusIso_hom_hom, Category.assoc, cancel_epi] at e
  have hη : (η : 𝟙_ _ ⟶ splitTorus (Spec (.of K)) X).left ≫ (splitTorus (Spec (.of K)) X).hom =
    𝟙 _ := Over.w _
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, e, reassoc_of% hη]
  rfl

theorem torus_hom_eq_one (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (.of K))) [GrpObj B] [IsProper B.hom] (f : splitTorus (Spec (.of K)) X ⟶ B)
    [IsMonHom f] : f = 1 := by
  rw [torus_const X B f, IsMonHom.one_hom, Hom.one_def]

theorem exists_torus_and_quotient_hom {G H : Over (Spec (.of K))} [GrpObj G] [GrpObj H]
    (D : TorusExtension G) (E : TorusExtension H) (φ : G ⟶ H) [IsMonHom φ] :
    letI := D.addCommGroup; letI := E.addCommGroup; letI := D.grpB; letI := E.grpB
    (∃! α : splitTorus (Spec (.of K)) D.X ⟶ splitTorus (Spec (.of K)) E.X,
      IsMonHom α ∧ α ≫ E.i = D.i ≫ φ) ∧
    (∃! β : D.B ⟶ E.B, IsMonHom β ∧ D.q ≫ β = φ ≫ E.q) := by
  letI := D.addCommGroup; letI := E.addCommGroup; letI := D.grpB; letI := E.grpB
  have := D.free
  have := D.finite
  have := D.i_hom
  have := D.q_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_quasiCompact
  have := E.i_hom
  have := E.q_hom
  have := E.isAbelian.proper
  have h0 : D.i ≫ φ ≫ E.q = 1 := torus_hom_eq_one D.X E.B _
  have : Mono E.i := E.isKernel.flip.mono_snd_of_mono
  have := epi_of_fpqc D.q
  constructor
  · obtain ⟨α, hα⟩ : ∃ α, α ≫ E.i = D.i ≫ φ :=
      ⟨E.isKernel.lift (D.i ≫ φ) (toUnit _) (by rw [Category.assoc, h0]; rfl),
        E.isKernel.lift_fst _ _ _⟩
    refine ⟨α, ⟨⟨?_, ?_⟩, hα⟩, fun α' h ↦ by rw [← cancel_mono E.i, h.2, hα]⟩
    · rw [← cancel_mono E.i, Category.assoc, hα, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono E.i, Category.assoc, hα, IsMonHom.mul_hom, Category.assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hα]
  · obtain ⟨β, hβ⟩ := exists_desc D.q (φ ≫ E.q) fun Z a b h ↦ by
      obtain ⟨τ, rfl⟩ := exists_eq_mul D.isKernel h
      rw [MonObj.mul_comp, Category.assoc, h0, MonObj.comp_one, _root_.one_mul]
    refine ⟨β, ⟨⟨?_, ?_⟩, hβ⟩, fun β' h ↦ by rw [← cancel_epi D.q, h.2, hβ]⟩
    · rw [← IsMonHom.one_hom D.q, Category.assoc, hβ, IsMonHom.one_hom]
    · have : Epi (D.B ◁ D.q) := by
        have := epi_of_fpqc (D.q ▷ D.B)
        rw [show D.B ◁ D.q = (β_ _ _).hom ≫ D.q ▷ D.B ≫ (β_ _ _).hom by simp]
        infer_instance
      have := epi_of_fpqc (D.q ▷ G)
      have : Epi (D.q ⊗ₘ D.q) := by rw [MonoidalCategory.tensorHom_def]; infer_instance
      rw [← cancel_epi (D.q ⊗ₘ D.q), ← IsMonHom.mul_hom_assoc, hβ, tensorHom_comp_tensorHom_assoc,
        hβ, IsMonHom.mul_hom]

end Main

section Family

variable {S : Scheme.{0}}

theorem ext_of_geometric_fibres {Z Y : Over S} [IsReduced Z.left] [IsSeparated Y.hom] {f g : Z ⟶ Y}
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S),
      (Over.pullback p).map f = (Over.pullback p).map g) : f = g := by
  have : Surjective (equalizer.ι f.left g.left) := ⟨fun z ↦ by
    let k := S.residueField (Z.hom z)
    let p : Spec (.of (AlgebraicClosure k)) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫
        S.fromSpecResidueField (Z.hom z)
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback Z.hom p) z
      default (Scheme.fromSpecResidueField_apply (Z.hom z) _).symm
    refine range_subset_range_equalizer_ι (pullback.fst Z.hom p) ?_ ⟨y, hy⟩
    have := congrArg (·.left ≫ pullback.fst Y.hom p) (h _ p)
    exact (pullback.lift_fst _ _ _).symm.trans (this.trans (pullback.lift_fst _ _ _))⟩
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Y.hom
    ((Over.w f).trans (Over.w g).symm) (equalizer.ι f.left g.left) (equalizer.condition _ _))

theorem family_square_eq_one [IsReduced S] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : G ⊗ G ⟶ H) (h₁ : lift (𝟙 G) 1 ≫ f = 1)
    (h₂ : lift 1 (𝟙 G) ≫ f = 1) : f = 1 := by
  have := hG.smooth
  have := hH.separated
  have := smooth_tensorObj_hom G G
  have : IsReduced (G ⊗ G).left := isReduced_of_smooth_of_isReduced (G ⊗ G).hom
  refine ext_of_geometric_fibres fun Ω _ _ p ↦ ?_
  obtain ⟨D⟩ := hG.fibres Ω p
  obtain ⟨E⟩ := hH.fibres Ω p
  let F := Over.pullback p
  have := square_eq_one D E (Functor.LaxMonoidal.μ F G G ≫ F.map f)
    (by rw [← F.map_id, ← F.map_one, Functor.Monoidal.lift_μ_assoc, ← F.map_comp, h₁, F.map_one])
    (by rw [← F.map_id, ← F.map_one, Functor.Monoidal.lift_μ_assoc, ← F.map_comp, h₂, F.map_one])
  rw [← cancel_epi (Functor.LaxMonoidal.μ F G G), this, F.map_one, MonObj.comp_one]

end Family

end GlobalTheory.SemiRigid

namespace GlobalTheory

open SemiRigid

theorem semiAbelian_rigidity :
    (∀ (K : Type) [Field K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B →
      ∀ f : splitTorus (Spec (CommRingCat.of K)) X ⟶ B,
        (∃ b : 𝟙_ _ ⟶ B, f = toUnit _ ≫ b) ∧ (IsMonHom f → f = toUnit _ ≫ η[B])) ∧
    (∀ (K : Type) [Field K] (G H : Over (Spec (CommRingCat.of K))) [GrpObj G] [GrpObj H],
      Nonempty (TorusExtension G) → Nonempty (TorusExtension H) →
      (∀ f : G ⊗ G ⟶ H, lift (𝟙 G) (toUnit G ≫ η[G]) ≫ f = toUnit G ≫ η[H] →
        lift (toUnit G ≫ η[G]) (𝟙 G) ≫ f = toUnit G ≫ η[H] → f = toUnit _ ≫ η[H]) ∧
      ∀ φ : G ⟶ H, η[G] ≫ φ = η[H] → IsMonHom φ) ∧
    (∀ (S : Scheme.{0}) [IsReduced S] (G H : Over S) [GrpObj G] [GrpObj H],
      IsSemiAbelian G → IsSemiAbelian H →
      (∀ f : G ⊗ G ⟶ H, lift (𝟙 G) (toUnit G ≫ η[G]) ≫ f = toUnit G ≫ η[H] →
        lift (toUnit G ≫ η[G]) (𝟙 G) ≫ f = toUnit G ≫ η[H] → f = toUnit _ ≫ η[H]) ∧
      ∀ φ : G ⟶ H, η[G] ≫ φ = η[H] → IsMonHom φ) ∧
    (∀ (K : Type) [Field K] (G H : Over (Spec (CommRingCat.of K))) [GrpObj G] [GrpObj H]
      (D : TorusExtension G) (E : TorusExtension H) (φ : G ⟶ H), IsMonHom φ →
      letI := D.addCommGroup; letI := E.addCommGroup; letI := D.grpB; letI := E.grpB
      (∃! α : splitTorus (Spec (CommRingCat.of K)) D.X ⟶ splitTorus (Spec (CommRingCat.of K)) E.X,
        IsMonHom α ∧ α ≫ E.i = D.i ≫ φ) ∧
      (∃! β : D.B ⟶ E.B, IsMonHom β ∧ D.q ≫ β = φ ≫ E.q)) := by
  refine ⟨fun K _ X _ _ _ B _ hB f ↦ ?_, fun K _ G H _ _ ⟨D⟩ ⟨E⟩ ↦ ?_, fun S _ G H _ _ hG hH ↦ ?_,
    fun K _ G H _ _ D E φ _ ↦ exists_torus_and_quotient_hom D E φ⟩
  · have := hB.proper
    exact ⟨⟨_, torus_const X B f⟩, fun _ ↦ torus_hom_eq_one X B f⟩
  · exact ⟨square_eq_one D E, isMonHom_of_axes (square_eq_one D E)⟩
  · exact ⟨family_square_eq_one hG hH, isMonHom_of_axes (family_square_eq_one hG hH)⟩

theorem isMonHom_of_isSemiAbelian {S : Scheme.{0}} [IsReduced S] {G H : Over S} [GrpObj G]
    [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (φ : G ⟶ H) (hφ : η[G] ≫ φ = η[H]) :
    IsMonHom φ :=
  isMonHom_of_axes (family_square_eq_one hG hH) φ hφ

theorem mul_eq_of_isSemiAbelian {S : Scheme.{0}} [IsReduced S] {G : Over S} (m₁ m₂ : GrpObj G)
    (h₁ : @IsSemiAbelian S G m₁) (h₂ : @IsSemiAbelian S G m₂)
    (h : m₁.toMonObj.one = m₂.toMonObj.one) : m₁.toMonObj.mul = m₂.toMonObj.mul := by
  have := @IsMonHom.mul_hom _ _ _ G G m₁.toMonObj m₂.toMonObj (𝟙 G)
    (@isMonHom_of_isSemiAbelian S _ G G m₁ m₂ h₁ h₂ (𝟙 G) ((Category.comp_id _).trans h))
  simpa using this

end GlobalTheory
