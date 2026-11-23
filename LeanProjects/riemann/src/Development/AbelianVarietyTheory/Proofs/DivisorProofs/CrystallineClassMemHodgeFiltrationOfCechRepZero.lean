import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCoverStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechKS

theorem Pt.nonempty_affHom_of_in {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s) (h : P.In U.1) :
    Nonempty ((Pt.aff s U).Hom P) := by
  let φ := GlobalTheory.Points.valMap P.x U.1 h
  have hc : ∀ r : R, φ.hom (algebraMap R (CechDR.Sec s U.1) r) = algebraMap R P.B r := by
    intro r
    change φ.hom ((s.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [← GlobalTheory.Points.valR_eq P.x U.1 h, GlobalTheory.Points.valR_appLE P.x s le_top h, P.w,
      GlobalTheory.Points.valR_specMap]
    rfl
  refine ⟨⟨{ φ.hom with commutes' := hc }, ?_⟩⟩
  exact GlobalTheory.Points.specMap_valMap_fromSpec U.2 P.x h

theorem Pt.affHom_ρ_eq_valR {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a : (Pt.aff s U).Hom P) (b : Γ(X, U.1)) : a.ρ b = valR P.x U.1 b := by
  have hpre : ⊤ ≤ (CechDR.affPt s U) ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have hid : valR (CechDR.affPt s U) U.1 b = b := by
    rw [GlobalTheory.Points.valR_eq _ _ hpre]
    have h1 : Spec.map (𝟙 Γ(X, U.1)) ≫ U.2.fromSpec = CechDR.affPt s U := by
      rw [Spec.map_id, Category.id_comp]; rfl
    have h2 := GlobalTheory.Points.valMap_specMap_fromSpec U.2 (𝟙 Γ(X, U.1)) (h1 ▸ hpre)
    have h3 : GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre = 𝟙 _ := by
      have key : ∀ (x : Spec Γ(X, U.1) ⟶ X) (hx : x = CechDR.affPt s U) (h : ⊤ ≤ x ⁻¹ᵁ U.1),
          GlobalTheory.Points.valMap x U.1 h = GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre := by
        rintro _ rfl _; rfl
      exact (key _ h1 _).symm.trans h2
    rw [h3]; rfl
  rw [← a.pt, GlobalTheory.Points.valR_spMap_comp _ _ _ hpre, hid]
  rfl

theorem eq_of_valR_eq_on_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {J : Type} (W : J → X.Opens)
    (hW : ⨆ j, W j = ⊤) (V : X.Opens) (f g : Γ(X, V))
    (h : ∀ (P : Pt s) (j : J), P.In V → P.In (W j) → valR P.x V f = valR P.x V g) : f = g := by
  refine TopCat.Presheaf.section_ext X.sheaf V f g fun x hx ↦ ?_
  have hxW : x ∈ ⨆ j, W j := by rw [hW]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxW
  obtain ⟨U', hU', hxU', hsub⟩ := exists_isAffineOpen_mem_and_subset (U := V ⊓ W j) ⟨hx, hj⟩
  have hle : U' ≤ V ⊓ W j := hsub
  have hleV : U' ≤ V := hle.trans inf_le_left
  let Ua : X.affineOpens := ⟨U', hU'⟩
  have hPU : (Pt.aff s Ua).In U' := hU'.fromSpec_preimage_self.ge
  have hv := h (Pt.aff s Ua) j (hPU.mono hleV) (hPU.mono (hle.trans inf_le_right))
  have key : ∀ b : Γ(X, V), valR (Pt.aff s Ua).x V b = (X.presheaf.map (homOfLE hleV).op).hom b := by
    intro b
    rw [← GlobalTheory.Points.valR_res (Pt.aff s Ua).x hleV hPU b]
    exact (Pt.affHom_ρ_eq_valR s Ua (Pt.aff s Ua) (Pt.Hom.id _) _).symm
  rw [key, key] at hv
  have := congrArg (X.presheaf.germ U' x hxU') hv
  rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this

theorem Pt.affHom_subsingleton {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a a' : (Pt.aff s U).Hom P) : a = a' := by
  obtain ⟨ρ, e⟩ := a
  obtain ⟨ρ', e'⟩ := a'
  have : ρ = ρ' := AlgHom.ext fun b ↦ (Pt.affHom_ρ_eq_valR s U P ⟨ρ, e⟩ b).trans (Pt.affHom_ρ_eq_valR s U P ⟨ρ', e'⟩ b).symm
  subst this; rfl

theorem Pt.Hom.comp_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {P Q T : Pt s}
    (φ : P.Hom Q) (ψ : Q.Hom T) : (φ.comp ψ).triv = φ.triv ≫ ψ.triv :=
  Thick.hom_ext fun _ ↦ rfl

theorem h1_mk_mem_f1_of_isRep_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens), ⨆ j, W j = ⊤ → ∀ c : Z1 (O (dp0 R) s), IsRep W c 0 → H1.mk _ c ∈ F1 s := by
  intro R _ X s J W hW c hc
  obtain ⟨G, hG1, hG2⟩ := hc
  have hG : ∀ j j' (P : Pt s), P.In (W j) → P.In (W j') → G j P = G j' P := fun j j' P h h' ↦
    sub_eq_zero.1 (hG2 j j' P h h')
  change toH1O s (H1.mk _ c) = 0
  apply GlobalTheory.CechDR.cmpO_injective R X s
  rw [map_zero, ← GlobalTheory.CechDR.structureSheaf_comparison_comm, GlobalTheory.CechDR.comparison_mk]
  refine H1.mk_eq_zero.2 ?_
  classical
  let aP : ∀ (U : X.affineOpens) (P : Pt s), P.In U.1 → (Pt.aff s U).Hom P :=
    fun U P h ↦ (Pt.nonempty_affHom_of_in s U P h).some
  let FU : X.affineOpens → PtFn s := fun U P ↦
    if h : P.In U.1 ∧ ∃ j, P.In (W j) then G h.2.choose P - ev c (aP U P h.1).triv else 0
  have FU_eq : ∀ U (P : Pt s) j (hU : P.In U.1), P.In (W j) → FU U P = G j P - ev c (aP U P hU).triv := by
    intro U P j hU hj
    have h : P.In U.1 ∧ ∃ j, P.In (W j) := ⟨hU, j, hj⟩
    simp only [FU, dif_pos h]
    rw [hG _ j P h.2.choose_spec hj]
  have ex : ∀ U : X.affineOpens, ∃ f : Γ(X, U.1), ∀ (j : J) (P : Pt s), P.In (U.1 ⊓ W j) →
      FU U P = valR P.x U.1 f := by
    intro U
    refine GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover R X s J (fun j ↦ U.1 ⊓ W j) U.1 (fun j ↦ inf_le_left) ?_ (FU U) ?_
    · rw [← inf_iSup_eq, hW, inf_top_eq]
    · intro j P Q φ hP
      have hU : P.In U.1 := hP.mono inf_le_left
      have hj : P.In (W j) := hP.mono inf_le_right
      rw [FU_eq U P j hU hj, FU_eq U Q j (hU.map φ) (hj.map φ),
        Pt.affHom_subsingleton s U Q (aP U Q (hU.map φ)) ((aP U P hU).comp φ), Pt.Hom.comp_triv, ev_comp,
        hG1 j P Q φ hj, map_sub]
      have e : φ.triv.φ (ev c (aP U P hU).triv) = φ.ρ (ev c (aP U P hU).triv) := rfl
      rw [e]; ring
  choose f hf using ex
  refine ⟨fun U ↦ f U.unop, ?_⟩
  funext U V a
  have hle : V.unop.1 ≤ U.unop.1 := leOfHom a.unop
  refine eq_of_valR_eq_on_cover s W hW V.unop.1 _ _ fun P j hV hj ↦ ?_
  change valR P.x V.unop.1 (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
    (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) = valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv)
  have hU : P.In U.unop.1 := hV.mono hle
  set b := aP V.unop P hV
  have e1 : valR P.x V.unop.1 (f V.unop) = FU V.unop P := (hf V.unop j P (hV.inf hj)).symm
  have e2 : valR P.x V.unop.1 (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) = FU U.unop P :=
    (GlobalTheory.Points.valR_res P.x hle hV (f U.unop)).trans (hf U.unop j P (hU.inf hj)).symm
  have e3 : aP U.unop P hU = (Pt.affHom s hle).comp b := Pt.affHom_subsingleton s _ P _ _
  have e4 : ev c (aP U.unop P hU).triv = b.ρ (ev c (Pt.affHom s hle).triv) + ev c b.triv := by
    rw [e3, Pt.Hom.comp_triv, ev_comp]; rfl
  have e5 : valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv) = b.ρ (ev c (Pt.affHom s hle).triv) :=
    (Pt.affHom_ρ_eq_valR s V.unop P b _).symm
  have e6 : b.ρ (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
      (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) =
      b.ρ (f V.unop) - b.ρ (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) := map_sub b.ρ _ _
  rw [e5, ← Pt.affHom_ρ_eq_valR s V.unop P b, e6, Pt.affHom_ρ_eq_valR s V.unop P b (f V.unop),
    Pt.affHom_ρ_eq_valR s V.unop P b (GlobalTheory.CechDR.Sec.res s hle (f U.unop)), e1, e2,
    FU_eq V.unop P j hV hj, FU_eq U.unop P j hU hj, e4]
  ring

end GlobalTheory.CechKS
