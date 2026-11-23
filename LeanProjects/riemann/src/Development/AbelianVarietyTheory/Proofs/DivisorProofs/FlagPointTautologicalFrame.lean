import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res)
open GlobalTheory.Twist (resM resM_resM app_resM resM_self)

namespace GlobalTheory.FlagZ.LocTaut

variable {S T Y Z : Scheme.{0}}

def compIso (j : S ⟶ T) [IsOpenImmersion j] (f : T ⟶ Y) :
    Scheme.Modules.pullback (j ≫ f) ≅ Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor j :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp j f).symm).leftAdjointUniq
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j))

theorem compIso_app_pullbackSections (j : S ⟶ T) [IsOpenImmersion j] (f : T ⟶ Y) (G : Y.Modules)
    (h : ⊤ ≤ (j ≫ f) ⁻¹ᵁ ⊤) (h' : j ''ᵁ ⊤ ≤ f ⁻¹ᵁ ⊤) (s : Γ(G, ⊤)) :
    ((compIso j f).hom.app G).app ⊤ (pullbackSections (j ≫ f) G h s) = pullbackSections f G h' s := by
  have := Adjunction.unit_leftAdjointUniq_hom_app
    ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp j f).symm)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j)) G
  have H := congr(($this).app ⊤ s)
  refine Eq.trans ?_ H
  exact congrArg _ (QCoh.res_self _ le_rfl _)

theorem pullbackComp_hom_app (b : S ⟶ Y) (a : Y ⟶ Z) (E : Z.Modules) {U : Z.Opens} {V : Y.Opens}
    {W : S.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : W ≤ b ⁻¹ᵁ V) (h : W ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app E).app W
      (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) = pullbackSections (b ≫ a) E h s := by
  rw [← Vert.DivPull.pullbackComp_inv_app b a E h₁ h₂ h]
  exact congr(($((Scheme.Modules.pullbackComp b a).inv_hom_id_app E)).app W _)

theorem exists_frame_image (j : S ⟶ T) [IsOpenImmersion j] (f : T ⟶ Y) (p : S ⟶ Y) (hp : p = j ≫ f) (q : Y ⟶ Z)
    (E : Z.Modules) (F : Y.Modules) (i : F ⟶ (Scheme.Modules.pullback q).obj E) {κ μ : Type} [Fintype κ] [Fintype μ]
    (e : μ → Γ(E, ⊤)) (c : κ → μ → Γ(S, ⊤)) (s : κ → Γ((Scheme.Modules.pullback p).obj F, ⊤)) (hs : IsFrame s)
    (h₀ : ⊤ ≤ (p ≫ q) ⁻¹ᵁ ⊤)
    (h : ∀ k, ((Scheme.Modules.pullback p).map i ≫ (Scheme.Modules.pullbackComp p q).hom.app E).app ⊤ (s k) =
      ∑ m, c k m • pullbackSections (p ≫ q) E h₀ (e m))
    (V : T.Opens) (hV : V ≤ j ''ᵁ ⊤) (h₁ : V ≤ (f ≫ q) ⁻¹ᵁ ⊤) :
    ∃ t : κ → Γ((Scheme.Modules.pullback f).obj F, V), IsFrame t ∧ ∀ k,
      ((Scheme.Modules.pullback f).map i ≫ (Scheme.Modules.pullbackComp f q).hom.app E).app V (t k) =
        ∑ m, resG T hV ((j.appIso ⊤).inv (c k m)) • pullbackSections (f ≫ q) E h₁ (e m) := by
  subst hp
  let t : κ → Γ((Scheme.Modules.pullback f).obj F, j ''ᵁ ⊤) := fun k => ((compIso j f).hom.app F).app ⊤ (s k)
  have ht : IsFrame t := (isFrame_restrict_iff j t).1 (hs.map_iso ((compIso j f).hom.app F))
  refine ⟨_, ht.res hV, fun k => ?_⟩
  have h2 : ((Scheme.Modules.pullback (j ≫ f)).map i).app ⊤ (s k) =
      ∑ m, c k m • pullbackSections (j ≫ f) _ (V := ⊤) le_top (pullbackSections q E (U := ⊤) le_top (e m)) := by
    refine (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullbackComp (j ≫ f) q).hom.app E).app ⊤)).1 ((h k).trans ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Scheme.Modules.Hom.app_smul, pullbackComp_hom_app]
  have h3 : ((Scheme.Modules.pullback f).map i).app (j ''ᵁ ⊤) (t k) =
      ∑ m, (j.appIso ⊤).inv (c k m) • pullbackSections f _ (V := ⊤) le_top (pullbackSections q E (U := ⊤) le_top (e m)) := by
    have hn := congr(($((compIso j f).hom.naturality i)).app ⊤ (s k))
    refine hn.symm.trans ?_
    refine (congrArg (((compIso j f).hom.app _).app ⊤) h2).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Scheme.Modules.Hom.app_smul, compIso_app_pullbackSections j f _ _ le_top]
    rfl
  refine (app_resM _ hV _).trans ?_
  refine (congrArg (fun x => resM _ hV (((Scheme.Modules.pullbackComp f q).hom.app E).app _ x)) h3).trans ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Scheme.Modules.Hom.app_smul, pullbackComp_hom_app f q E _ _ le_top, Twist.resM_smul]
  exact congrArg _ (res_pullbackSections _ _ _ _ _)

theorem exists_frame_pullback_taut : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N), Taut.IsTaut ι N fl →
    ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (g' : T ⟶ Fl ι N) (w : g' ≫ flStr ι N = g) (V : T.Opens) (hV : IsAffineOpen V)
    (G : ι → GL (Fin N) Γ(T, V)), V.ι ≫ g' = hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G →
    ∀ (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback g').obj ((fl a).F l), V), IsFrame s ∧ ∀ j,
      ((Scheme.Modules.pullback g').map ((fl a).ι l) ≫
        (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app (Taut.stdE N) ≫
          (Scheme.Modules.pullbackCongr w).hom.app (Taut.stdE N)).app V (s j) =
        Loc.colSecOn g V (G a).1 (Fin.castLE l.is_le j) := by
  intro ι _ N fl hfl T g g' w V hV G hG a l
  subst w
  obtain ⟨s, hs, h⟩ := hfl Γ(T, V) G a l
  have hp : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G = hV.fromSpec ≫ g' := by
    rw [IsAffineOpen.fromSpec, Category.assoc, hG]
    exact (hV.isoSpec.inv_hom_id_assoc _).symm
  obtain ⟨t, ht, h'⟩ := exists_frame_image hV.fromSpec g' _ hp (flStr ι N) (Taut.stdE N) _ ((fl a).ι l)
    (freeFrame (Sp ℤ) (Fin N)) _ s hs _ h V (QCoh.fromSpec_image_top hV).ge le_top
  refine ⟨t, ht, fun k => (h' k).trans (Finset.sum_congr rfl fun m _ => ?_)⟩
  congr 1
  have := QCoh.fromSpec_appIso_inv_res hV ⊤ ((G a).1 m (Fin.castLE l.is_le k))
  rw [show ∀ x, (Spec Γ(T, V)).presheaf.map (⊤ : (Spec Γ(T, V)).Opens).leTop.op x = x from
    QCoh.res_self_ring (X := Spec Γ(T, V)) le_rfl] at this
  refine (congrArg (resG T _) this).trans ?_
  exact (LB.resG_resG _ _ _).trans (LB.resG_self _ _)

end GlobalTheory.FlagZ.LocTaut
