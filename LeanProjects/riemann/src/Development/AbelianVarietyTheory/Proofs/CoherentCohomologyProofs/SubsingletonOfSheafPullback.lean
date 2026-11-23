import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoToInterAppPushforwardInclusion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Topology

universe u

noncomputable section

namespace GlobalTheory
namespace AffineVanishing

section Restriction

variable {X Y : TopCat.{u}} {j : Y ⟶ X} (hj : IsOpenEmbedding j)

lemma shortExact_map_sheafPullback {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) [(hj.sheafPullback AddCommGrpCat.{u}).PreservesZeroMorphisms] :
    (S.map (hj.sheafPullback AddCommGrpCat.{u})).ShortExact := by
  have h₁ : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} j) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map j) AddCommGrpCat.{u} _ _
  have h₂ : PreservesFiniteLimits (hj.sheafPullback AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso (hj.sheafPullbackIso _)
  have h₃ : PreservesFiniteColimits (hj.sheafPullback AddCommGrpCat.{u}) :=
    preservesFiniteColimits_of_natIso (hj.sheafPullbackIso _)
  exact hS.map_of_exact _

lemma subsingleton_of_sheafPullback (V : Opens Y) (n : ℕ) (F : X.Sheaf AddCommGrpCat.{u})
    (h : Subsingleton (Sheaf.H'.{u} ((hj.sheafPullback AddCommGrpCat.{u}).obj F) (n + 1) V)) :
    Subsingleton (Sheaf.H'.{u} F (n + 1) (hj.functor.obj V)) := by
  haveI : (hj.sheafPullback AddCommGrpCat.{u}).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  induction n generalizing F with
  | zero =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    exact SheafLES.subsingleton₁_one_of_sections_surjective.{u} hS _
      (SheafLES.sections_surjective_of_subsingleton.{u} (shortExact_map_sheafPullback hj hS) V h)
      (Flasque.subsingleton_H'_of_isFlasque _ 0 _)
  | succ n ih =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    have hI : (Flasque.injectiveShortComplex F).X₂.IsFlasque := inferInstance
    have hI' : ((hj.sheafPullback AddCommGrpCat.{u}).obj
        (Flasque.injectiveShortComplex F).X₂).IsFlasque := ⟨fun _ ↦ hI.epi _⟩
    exact SheafLES.subsingleton₁.{u} hS (n + 1) _
      (ih _ (SheafLES.subsingleton₃.{u} (shortExact_map_sheafPullback hj hS) (n + 1) V
        (Flasque.subsingleton_H'_of_isFlasque _ (hF := hI') n V) h))
      (Flasque.subsingleton_H'_of_isFlasque _ (n + 1) _)

end Restriction

variable {X Y : Scheme.{u}}

lemma subsingleton_of_restrict (j : Y ⟶ X) [IsOpenImmersion j] (F : X.Modules) (V : Y.Opens)
    (n : ℕ) (h : Subsingleton (cohOn (F.restrict j) V (n + 1))) :
    Subsingleton (cohOn F (j ''ᵁ V) (n + 1)) :=
  subsingleton_of_sheafPullback j.isOpenEmbedding V n ((toAbSheaf X).obj F) h

abbrev interModule (F : X.Modules) (W : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward W.ι).obj (F.restrict W.ι)

abbrev toInterModule (F : X.Modules) (W : X.Opens) : F ⟶ interModule F W :=
  (Scheme.Modules.restrictAdjunction W.ι).unit.app F

lemma map_toInterModule_eq_zero (F : X.Modules) (W V : X.Opens) (n : ℕ) (α : cohOn F V n)
    (h : SheafLES.map.{u} ((Kempf.toInter AddCommGrpCat.{u} W).app ((toAbSheaf X).obj F)) n V
      (cohOn.toH' F V n α) = 0) :
    cohOn.map ℤ (toInterModule F W) V n α = 0 :=
  haveI : IsIso ((Kempf.toInter AddCommGrpCat.{u} W).app ((toAbSheaf X).obj (interModule F W))) :=
    Kempf.isIso_toInter_app_pushforward (A := AddCommGrpCat.{u}) W.ι.base W (fun y ↦ y.2)
      ((toAbSheaf W).obj (F.restrict W.ι))
  Kempf.map_eq_zero_of_map_toInter_eq_zero.{u} ((toAbSheaf X).map (toInterModule F W)) h

lemma mono_lift_toInterModule (F : X.Modules) {ι : Type u} [Finite ι] (W : ι → X.Opens)
    (hW : ⊤ ≤ iSup W) : Mono (Pi.lift fun i ↦ toInterModule F (W i)) := by
  refine ⟨fun {Z} a b hab ↦ ?_⟩
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  refine QCoh.section_eq_of_cover F (fun i ↦ (W i).ι ''ᵁ ((W i).ι ⁻¹ᵁ U))
    (fun i ↦ (W i).ι.image_preimage_le U) (fun x hx ↦ ?_) _ _ fun i ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hW (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨i, ⟨x, hi⟩, hx, rfl⟩
  · have h : a ≫ toInterModule F (W i) = b ≫ toInterModule F (W i) := by
      simpa using hab =≫ Pi.π _ i
    exact congr(($h).app U s)

lemma subsingleton_top [IsAffine X] (n : ℕ)
    (ih : ∀ q, 0 < q → q < n + 1 → ∀ (G : X.Modules) [G.IsQuasicoherent] (U : X.Opens),
      IsAffineOpen U → Subsingleton (cohOn G U q))
    (F : X.Modules) [F.IsQuasicoherent] : Subsingleton (cohOn F ⊤ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun α ↦ ?_
  obtain ⟨𝔘, h𝔘, hfin, hsup, h0⟩ := Kempf.exists_finite_cover_map_toInter_eq_zero.{u}
    (X := X) (𝔅 := X.affineOpens) X.isBasis_affineOpens
    (fun B hB B' hB' ↦ IsAffineOpen.inf hB hB') ((toAbSheaf X).obj F) ⊤
    (isAffineOpen_top X).isCompact (Nat.le_add_left 1 n)
    (fun q hq hqn B hB ↦ ih q hq hqn F B hB) (cohOn.toH' F ⊤ (n + 1) α)
  haveI : Finite 𝔘 := hfin
  haveI (W : 𝔘) : IsAffine W.1 := h𝔘 W.2
  let φ : F ⟶ ∏ᶜ (fun W : 𝔘 ↦ interModule F W.1) := Pi.lift fun W ↦ toInterModule F W.1
  haveI : Mono φ := mono_lift_toInterModule F (fun W : 𝔘 ↦ W.1) (by
    rw [← sSup_eq_iSup', hsup])
  have hα : cohOn.map ℤ φ ⊤ (n + 1) α = 0 := by
    apply (cohOn.piEquiv ℤ ⊤ (n + 1) _).injective
    ext W
    rw [cohOn.piEquiv_apply, cohOn.map_map, map_zero, Pi.zero_apply, Pi.lift_π]
    exact map_toInterModule_eq_zero F W.1 ⊤ (n + 1) α (h0 W.1 W.2)
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    { exact := ShortComplex.exact_cokernel φ }
  have hT := SheafLES.shortExact_map_toAbSheaf hS
  have hinj : Function.Injective (SheafLES.map.{u} ((toAbSheaf X).map φ) (n + 1) ⊤) := by
    cases n with
    | zero =>
      exact SheafLES.map_f_one_injective_of_sections_surjective.{u} hT ⊤
        (QCoh.surjective_cokernel_π_app φ (isAffineOpen_top X))
    | succ n =>
      refine SheafLES.map_f_injective_of_surjective.{u} hT (n + 1) ⊤ fun y ↦ ⟨0, ?_⟩
      exact @Subsingleton.elim _ (ih (n + 1) n.succ_pos (by omega) (cokernel φ) ⊤
        (isAffineOpen_top X)) _ _
  exact (cohOn.toH' F ⊤ (n + 1)).injective (hinj (hα.trans (by
    rw [map_zero]; exact (map_zero _).symm)))

end AffineVanishing

open AffineVanishing

theorem cohOn.subsingleton_of_isAffineOpen {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (hn : 0 < n) : Subsingleton (cohOn F U n) := by
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
    haveI : IsAffine U := hU
    have h := subsingleton_of_restrict U.ι F ⊤ n
      (subsingleton_top n (fun q hq hqn G _ V hV ↦ ih q hqn G hV hq) (F.restrict U.ι))
    rwa [Scheme.Opens.ι_image_top] at h

theorem coh.subsingleton_of_isAffine {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : 0 < n) : Subsingleton (coh F n) :=
  cohOn.subsingleton_of_isAffineOpen F (isAffineOpen_top X) hn

instance coh.subsingleton_succ_of_isAffine {X : Scheme.{u}} [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) : Subsingleton (coh F (n + 1)) :=
  coh.subsingleton_of_isAffine F n.succ_pos

end GlobalTheory
