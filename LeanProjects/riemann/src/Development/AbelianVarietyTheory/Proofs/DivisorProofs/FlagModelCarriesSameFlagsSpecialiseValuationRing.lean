import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlagSpec

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt stalkPt genericPt constF)
open GlobalTheory.VarFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv TanM)

theorem sp_comp_sp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (ψ : S →+* T) (φ : R →+* S) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

theorem eq_spMap_of_comp {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {ι : R →+* R'}
    (hι : Function.Injective ι) {h : Sp R ⟶ Sp S} {φ : S →+* R} (e : spMap ι ≫ h = spMap (ι.comp φ)) :
    h = spMap φ := by
  obtain ⟨p, rfl⟩ := Spec.map_surjective h
  have h1 : ι.comp p.hom = ι.comp φ := by
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← e, ← sp_comp_sp]; rfl
  have hp : p.hom = φ := RingHom.ext fun a => hι (RingHom.congr_fun h1 a)
  rw [← hp]; rfl

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genericPt_genStr {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F]
    {e : F ≃+* c.F} (C : FlagCpt Z e) :
    genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genStr Z = spMap (constF e C.Y) := by
  letI := (constF e C.Y).toAlgebra
  rw [← Category.assoc, ← C.y0_x, Category.assoc, GlobalTheory.Toroidal.genStr, Z.jQ_over]
  exact GlobalTheory.ShFam.ptF_snd _

theorem flagSpaceComponent_stalkPoint_over_coefficientField {Y : Model Xo c (RingHom.id c.F)} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Y e) (y : C.Y.X)
    {φ : c.F →+* C.Y.X.presheaf.stalk y} {f : EigFrame Y φ (stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y)}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (h : f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t) :
    stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y ≫ Y.s = spMap φ := by
  have hg : GlobalTheory.Toroidal.genι Y ≫ Y.s = GlobalTheory.Toroidal.genStr Y := by
    rw [GlobalTheory.Toroidal.genι, GlobalTheory.Toroidal.genStr, pullback.condition]
    exact (congrArg (pullback.snd Y.s (spMap (RingHom.id c.F)) ≫ ·) (spMap_id' _)).trans (Category.comp_id _)
  refine eq_spMap_of_comp (IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField) ?_
  rw [← h.2.1, ← genericPt_genStr C, ← hg]
  have h1 := congrArg (· ≫ Y.s) h.1
  simp only [Category.assoc] at h1
  exact h1.symm

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [dualMap]

theorem isFrameAt_map {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {z : Sp R ⟶ Z} {k : F.J} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k}
    {g : EigFrame Y φ (z ≫ π)} (hg : IsFrameAt F z k hz g) (ψ : R →+* R') {φ' : c.F →+* R'}
    {g' : EigFrame Y φ' ((spMap ψ ≫ z) ≫ π)} (hg' : g.IsMap ψ g') :
    IsFrameAt F (spMap ψ ≫ z) k (GlobalTheory.FlagMod.le_preimage_comp _ hz) g' := by
  intro σ i
  rw [hg' σ i, hg σ i, ← GlobalTheory.FlagMod.tanPull_left ψ (Category.assoc _ _ _).symm,
    F.tanPull_vecAt k ψ z hz _ rfl rfl]

theorem co_of_isFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {R : Type} [CommRing R] {φ : c.F →+* R} (z : Sp R ⟶ Z) (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k') {g g' : EigFrame Y φ (z ≫ π)} (hg : IsFrameAt F z k hz g)
    (hg' : IsFrameAt F z k' hz' g') (τ : E →+* ℂ) :
    (g.co g' τ).BlockTriangular id ∧ ∀ i, IsUnit (g.co g' τ i i) := by
  have hh := GlobalTheory.FlagMod.le_preimage_inf hz hz'
  have e : g.co g' τ = (F.B k k' τ).map (GlobalTheory.FlagMod.ev z _ hh) := by
    refine GlobalTheory.ShFam.EigFrame.co_eq fun i => ?_
    rw [funext (hg τ), hg' τ i, GlobalTheory.LieMet.isComb_iff]
    exact F.vecAt_eq_sum k k' z hz hz' hh rfl τ i
  rw [e]
  exact ⟨F.B_map_tri k k' τ _, fun i => (F.isUnit_B_diag k k' τ i).map (GlobalTheory.FlagMod.ev z _ hh)⟩

end GlobalTheory.VarFlagSpec

open GlobalTheory.VarFlagSpec GlobalTheory.ShFam in

theorem GlobalTheory.VarFlag.rel_specialise : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y),
    GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C →
    ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ X.YY) (v : Sp A ⟶ C.Y.X),
    u ≫ X.π = v ≫ C.π ≫ GlobalTheory.Toroidal.genι Y →
    GlobalTheory.VarFlag.Rel X.F C (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) →
    GlobalTheory.VarFlag.Rel X.F C (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v) := by
  intro E _ _ _ H Dw l Xo c Y X hFE C hCT A _ _ _ u v huv hL
  set ι := algebraMap A (FractionRing A) with hι_def
  have hι : Function.Injective ι := IsFractionRing.injective A (FractionRing A)
  set ρ := IsLocalRing.residue A with hρ_def

  set y := v (IsLocalRing.closedPoint A) with hy_def
  let ψA : C.Y.X.presheaf.stalk y →+* A := (Scheme.stalkClosedPointTo v).hom
  have hv : v = spMap ψA ≫ stalkPt C.Y y := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk v).symm
  obtain ⟨φ₁, f, t, hf0, -⟩ := C.gr_spec y
  have hxA : u ≫ X.π = spMap ψA ≫ (stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y) := by
    rw [huv, hv, Category.assoc]
  have hsA : u ≫ X.π ≫ Y.s = spMap (ψA.comp φ₁) := by
    rw [← Category.assoc, hxA]
    simp only [Category.assoc]
    rw [flagSpaceComponent_stalkPoint_over_coefficientField C y hf0, sp_comp_sp]

  obtain ⟨kk, hkk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover u
  obtain ⟨gA, hgA⟩ := hFE A (ψA.comp φ₁) u kk hkk hsA
  obtain ⟨fA, hfA⟩ := f.exists_isMap ψA (φ' := ψA.comp φ₁) (x' := u ≫ X.π) rfl hxA

  obtain ⟨φL, k0, hz0, gL, hsL, hgL, hcL⟩ := hL
  obtain rfl : φL = ι.comp (ψA.comp φ₁) := GlobalTheory.ShFam.EigLoc.spMap_inj (by
    rw [← hsL, Category.assoc, hsA, sp_comp_sp])
  have hxL : (spMap ι ≫ u) ≫ X.π = spMap ι ≫ (u ≫ X.π) := Category.assoc _ _ _
  obtain ⟨fL, hfL⟩ := fA.exists_isMap ι (φ' := ι.comp (ψA.comp φ₁)) rfl hxL
  obtain ⟨gL', hgL'⟩ := gA.exists_isMap ι (φ' := ι.comp (ψA.comp φ₁)) rfl hxL
  have hgL'fr := isFrameAt_map X.F hgA ι hgL'
  have hfLf : f.IsMap (ι.comp ψA) fL := fun τ i => by
    rw [hfL τ i, hfA τ i, GlobalTheory.GradedPieces.dual_comp]
  have hcF : C.Carries (spMap ι ≫ v) fL :=
    ⟨y, ι.comp ψA, φ₁, f, t, 1, by rw [hv, ← Category.assoc, sp_comp_sp], hf0,
      hfLf.tri rfl (by rw [hxL, hxA, ← Category.assoc, sp_comp_sp])⟩
  obtain ⟨t1, ht1⟩ := hCT (FractionRing A) _ _ _ _ fL gL hcF hcL
  have hfLid : fL.IsMap (RingHom.id _) fL := fun τ i => by rw [spMap_dualMap_id, Category.id_comp]

  have key : ∀ τ, (fA.co gA τ).BlockTriangular id ∧ ∀ i, IsUnit (fA.co gA τ i i) := by
    intro τ
    have h1 := ht1.co τ hfLid
    have h2 := co_of_isFrameAt X.F _ k0 kk hz0 _ hgL hgL'fr τ
    have hm : fL.co gL' τ = (fA.co gA τ).map ι := hfL.co τ hgL' hxL
    have hT1 : (fL.co gL τ).BlockTriangular id := fun a i h => h1.1 a i h
    have htri : (fL.co gL' τ).BlockTriangular id := by
      rw [← fL.co_mul gL gL' τ]; exact hT1.mul h2.1
    have hMt : (fA.co gA τ).BlockTriangular id := fun a i h => hι (by
      have := htri h
      rw [hm, Matrix.map_apply] at this
      rw [this, map_zero])
    refine ⟨hMt, fun i => ?_⟩
    have hdet := fA.isUnit_det_co gA τ
    rw [Matrix.det_of_upperTriangular hMt] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => fA.co gA τ j j) (Finset.mem_univ i)) hdet

  have hxk : (spMap ρ ≫ u) ≫ X.π = spMap ρ ≫ (u ≫ X.π) := Category.assoc _ _ _
  obtain ⟨fk, hfk⟩ := fA.exists_isMap ρ (φ' := ρ.comp (ψA.comp φ₁)) rfl hxk
  obtain ⟨gk, hgk⟩ := gA.exists_isMap ρ (φ' := ρ.comp (ψA.comp φ₁)) rfl hxk
  have hfkf : f.IsMap (ρ.comp ψA) fk := fun τ i => by
    rw [hfk τ i, hfA τ i, GlobalTheory.GradedPieces.dual_comp]
  have hmk : ∀ τ, fk.co gk τ = (fA.co gA τ).map ρ := fun τ => hfk.co τ hgk hxk
  refine ⟨ρ.comp (ψA.comp φ₁), kk, GlobalTheory.FlagMod.le_preimage_comp _ hkk, gk, ?_, isFrameAt_map X.F hgA ρ hgk, ?_⟩
  · rw [Category.assoc, hsA, sp_comp_sp]
  · refine ⟨y, ρ.comp ψA, φ₁, f, t, fun τ i => (((key τ).2 i).map ρ).unit,
      by rw [hv, ← Category.assoc, sp_comp_sp], hf0,
      by rw [hxk, hxA, ← Category.assoc, sp_comp_sp], rfl, fun τ i => ⟨fun a => fk.co gk τ a i, ?_, ?_, ?_⟩⟩
    · rw [hmk]; beta_reduce; rw [Matrix.map_apply, IsUnit.unit_spec]
    · intro a ha
      rw [hmk]; beta_reduce; rw [Matrix.map_apply, (key τ).1 ha, map_zero]
    · rw [← funext (hfkf τ)]
      exact fk.co_spec gk τ i
