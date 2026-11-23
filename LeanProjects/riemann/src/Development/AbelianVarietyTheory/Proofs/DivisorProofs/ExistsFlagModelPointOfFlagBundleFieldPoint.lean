import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelPointCarriesUniqueFlagBundlePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedPointOverOfLieEigenspaceFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open GlobalTheory.Toroidal (gen genι genStr)

theorem exists_rel_of_mem_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → ∃ z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hbar K _ p hp

  obtain ⟨yF, hyF, hcar⟩ := GlobalTheory.Mean4O.CompModel.exists_flagPt C p

  haveI := Y.jQ_open
  have hr : Set.range (p ≫ C.π) ⊆ Set.range Y.jQ := by
    rintro _ ⟨s, rfl⟩
    exact hp s
  let y := IsOpenImmersion.lift Y.jQ (p ≫ C.π) hr
  have hy : y ≫ Y.jQ = p ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hys : y ≫ pullback.snd _ _ = spMap yF.fK := by
    rw [← Y.jQ_over, ← Category.assoc, hy, hyF]
    exact yF.y_over

  obtain ⟨P, hPy, hPw⟩ := GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) Y K yF.fK y
    (yF.y ≫ genι Y) yF.frame hys (by rw [← Category.assoc, hy, hyF])
  letI : Algebra c.F K := yF.fK.toAlgebra
  have hPX : GlobalTheory.FlagMod.frX P = y := hPy
  have hl := X.lies_ptY P
  have hxg : X.ptY P ≫ X.π = yF.y ≫ genι Y := by
    rw [hl.1, hPX, Model.j, ← Category.assoc, hy, hyF]

  have hr₀ : Set.range (X.ptY P) ⊆ Set.range (GlobalTheory.CompHS.inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    show X.π (X.ptY P s) ∈ GlobalTheory.CompHS.barComp Y Z
    have e : X.π (X.ptY P s) = genι Y (j (f (p s))) := by
      rw [← Scheme.Hom.comp_apply, hxg, ← hyF, hπ]
      rfl
    rw [e]
    exact (hbar _).2 ⟨f (p s), rfl⟩
  let z := IsOpenImmersion.lift (GlobalTheory.CompHS.inc₀ X Z) (X.ptY P) hr₀
  have hz : z ≫ GlobalTheory.CompHS.inc₀ X Z = X.ptY P := IsOpenImmersion.lift_fac _ _ _
  refine ⟨z, ?_⟩
  rw [hz]

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY P)
  have hφ : X.ptY P ≫ X.π ≫ Y.s = spMap yF.fK := GlobalTheory.CompHS.ptY_str X P
  obtain ⟨g₂, hg₂⟩ := hFE K yF.fK (X.ptY P) k hk hφ
  refine ⟨yF.fK, k, hk, g₂, hφ, hg₂, ?_⟩

  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd P) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  have ht' := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).2.2.1 _ _ _ ht
  have hPx : GlobalTheory.FlagMod.frX P ≫ Y.j = X.ptY P ≫ X.π := hl.1.symm
  choose b hb hdiag hsum using fun τ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (X.F.M k).toMChart) (X.F.inM hk rfl) hPx hQ.over ht' τ

  have hgv : ∀ τ i, yF.frame.v τ i = (tv (GlobalTheory.FlagMod.frVec Y P hPx τ i)).left := by
    intro τ i
    obtain ⟨w, hw1, hw2, hw3⟩ := hPw τ i
    rw [← hPX] at hw1
    have hL : w = GlobalTheory.FlagMod.liftTan Y (GlobalTheory.FlagMod.frX P) ((GlobalTheory.FlagMod.frX_fst P).symm ▸ P.tan τ i) :=
      Y.m0.cart.1.hom_ext (hw2.trans (GlobalTheory.FlagMod.liftTan_univ _ _).symm)
        (hw1.trans (GlobalTheory.FlagMod.liftTan_over _ _).symm)
    show yF.frame.v τ i = _
    rw [← hw3, hL]
    rfl
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
  have hd : yF.frame.Tri (RingHom.id K) g₂ (fun τ i => (t⁻¹) (some ⟨τ, i⟩)) := by
    refine ⟨by rw [h2, Category.id_comp, hxg], rfl, fun τ i => ⟨fun m => b τ m i, hdiag τ i,
      fun m hm => hb τ hm, ?_⟩⟩
    simp only [h1, Category.id_comp]
    have e : (fun m => yF.frame.v τ m) = fun m => (tv (GlobalTheory.FlagMod.frVec Y P hPx τ m)).left := funext (hgv τ)
    rw [e, hg₂ τ i, GlobalTheory.LieMet.isComb_iff, ← hQ.frVec_eq rfl hQ.over τ]
    exact hsum τ i
  exact carries_of_tri C hd hcar

end GlobalTheory.VarFlag
