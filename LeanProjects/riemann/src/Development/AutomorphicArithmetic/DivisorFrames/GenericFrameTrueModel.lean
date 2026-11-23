import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.FrameGenericComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationInvariant
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

set_option autoImplicit false

namespace UpperTheory.BaseMatrixDescent

private noncomputable def mat {r : ℕ} (dual : Bool) (M : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ := cond dual M⁻¹ Mᵀ

private theorem mat_posDef {r : ℕ} (dual : Bool) {M : Matrix (Fin r) (Fin r) ℂ} (h : M.PosDef) : (mat dual M).PosDef := by
  cases dual
  · exact h.transpose
  · exact h.inv

private theorem mat_chg {r : ℕ} (dual : Bool) (M : Matrix (Fin r) (Fin r) ℂ) {T : Matrix (Fin r) (Fin r) ℂ}
    (hT : IsUnit T.det) : mat dual ((lieMat dual T)ᴴ * M * lieMat dual T) = HermFrame.chg T (mat dual M) := by
  cases dual
  · simp only [mat, lieMat, cond_false, HermFrame.chg, transpose_mul, Matrix.mul_assoc]
  · simp only [mat, lieMat, cond_true, HermFrame.chg, Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [← conjTranspose_nonsing_inv, ← transpose_nonsing_inv, nonsing_inv_nonsing_inv _ hT]
    rfl

private theorem mat_conj {r : ℕ} (dual : Bool) (M : Matrix (Fin r) (Fin r) ℂ) :
    mat dual (M.map (starRingEnd ℂ)) = (mat dual M).map star := by
  cases dual
  · rfl
  · show Mᵀᴴ⁻¹ = M⁻¹ᵀᴴ
    rw [← conjTranspose_nonsing_inv, transpose_nonsing_inv]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : Var F}
  {ρ : Y.X ⟶ gen Z} {g₀ : GenFrame e ρ} {τ : E →+* ℂ}

omit [NumberField F] in
private theorem spMap_ev {σ : F →+* ℂ} (p : Pts Y σ) : spMap (Var.evStalk p) ≫ stalkPt Y (Var.base p) = p.1 :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk p.1

omit [NumberField F] in
private theorem emb_eq {σ : F →+* ℂ} (p : Pts Y σ) {φ : c.F →+* Y.X.presheaf.stalk (Var.base p)}
    (hφ : constF e Y = (toFn (Var.base p)).comp φ) : embOf e σ = (Var.evStalk p).comp φ := RingHom.ext fun a => by
  have h3 : φ a = algebraMap F _ (e.symm a) := toFn_injective _
    ((RingHom.congr_fun hφ a).symm.trans ((Y.stalkIncl (Var.base p)).commutes _).symm)
  rw [RingHom.comp_apply, RingHom.comp_apply, h3]
  exact ((Var.evStalk_germ (U := ⊤) trivial _).trans (CxPts.ev_algX CxPts.mem_ptsIn_top _)).symm

omit [NumberField F] in
private theorem pt_eq {σ : F →+* ℂ} (p : Pts Y σ) {yc : CxPts (genStr Z) (embOf e σ)} (h : yc.1 = p.1 ≫ ρ) :
    yc.1 ≫ genι Z = spMap (Var.evStalk p) ≫ stalkPt Y (Var.base p) ≫ ρ ≫ genι Z := by
  rw [← Category.assoc, spMap_ev, h, Category.assoc]

private noncomputable def down (hρ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) {σ : F →+* ℂ} (p : Pts Y σ) :
    CxPts (genStr Z) (embOf e σ) :=
  ⟨p.1 ≫ ρ, by
    have h1 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext e.apply_symm_apply))
    have h2 : ρ ≫ genStr Z = Y.str ≫ spMap e.symm.toRingHom := by
      rw [← hρ, Category.assoc, Category.assoc, h1, Category.comp_id]
    rw [Category.assoc, h2, ← Category.assoc, p.2, ← Spec.map_comp]; rfl⟩

omit [NumberField F] in

private theorem rule {X : Scheme.{0}} {j : Y.X ⟶ X} {M : X.Modules} {dual : Bool}
    {A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn} (hA : IsCo (genericPt Y ≫ j) A)
    {σ : F →+* ℂ} (G : EigMet Z (embOf e σ)) (p : Pts Y σ) {ch ch' : Chart M (Dw.mult τ)}
    (h : j (Var.base p) ∈ ch.U) (h' : j (Var.base p) ∈ ch'.U) {φ φ'} {f : StalkFrame ρ (Var.base p) φ}
    {f' : StalkFrame ρ (Var.base p) φ'} (hf : Fits g₀ τ (Var.base p) φ f (lieMat dual (A ch)))
    (hf' : Fits g₀ τ (Var.base p) φ' f' (lieMat dual (A ch'))) {yc : CxPts (genStr Z) (embOf e σ)}
    (hy : yc.1 = p.1 ≫ ρ) {g g' : EigFrame Z (embOf e σ) (yc.1 ≫ genι Z)} (hg : f.IsMap (Var.evStalk p) g)
    (hg' : f'.IsMap (Var.evStalk p) g') :
    mat dual (G.gram yc g' τ) = HermFrame.chg (trAt (p.1 ≫ j) ch ch') (mat dual (G.gram yc g τ)) := by
  obtain rfl := hf.φ_eq hf'
  have hu := isUnit_det_trAt ch ch' (stalk_le j h) (stalk_le j h')
  rw [hA.2 ch ch' (gen_le j h) (gen_le j h'), lieMat_mul, trAt_gen j ch ch' h h', lieMat_map _ _ hu] at hf'
  have e1 := hf.co_eq hf'
  have e2 : trAt (p.1 ≫ j) ch ch' = (trAt (stalkPt Y (Var.base p) ≫ j) ch ch').map (Var.evStalk p) := by
    rw [← trAt_spMap _ ch ch' (stalk_le j h) (stalk_le j h'), ← Category.assoc, spMap_ev]
  have hu' : IsUnit (trAt (p.1 ≫ j) ch ch').det := by
    rw [e2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hu.map _
  rw [G.change yc g g', hg.co τ hg' (pt_eq p hy), e1, ← lieMat_map _ _ hu, ← e2, mat_chg _ _ hu']

open GlobalTheory.TrueGeo.ModelMetric

private theorem mem_base {N : GlobalTheory.TrueGeo.Model Y} {σ₀ : 𝓞 F →+* ℂ} {σ : F →+* ℂ} {p : Pts Y σ} {z : CxPts N.p σ₀}
    (hz : z.1 = p.1 ≫ N.j) {U : N.X.Opens} (h : z ∈ CxPts.ptsIn N.p σ₀ U) : N.j (Var.base p) ∈ U := by
  have := CxPts.mem_ptsIn.1 h
  rw [hz] at this
  exact this

private theorem exists_met (hρ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (N : GlobalTheory.TrueGeo.Model Y) {M : N.X.Modules}
    (hM : IsVB M (Dw.mult τ)) {dual : Bool}
    {A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn} (G : ∀ σ : c.F →+* ℂ, EigMet Z σ)
    (hA : IsLie g₀ τ N.j dual A) (σ₀ : 𝓞 F →+* ℂ) : ∃ m : Met N.p σ₀ M (Dw.mult τ),
      ∀ (σ : F →+* ℂ), σ.comp (algebraMap (𝓞 F) F) = σ₀ → ∀ (p : Pts Y σ) (z : CxPts N.p σ₀), z.1 = p.1 ≫ N.j →
      ∀ ch : Chart M (Dw.mult τ), z ∈ CxPts.ptsIn N.p _ ch.U → ∀ y : Y.X, Var.base p = y →
      ∀ ψ : Y.X.presheaf.stalk y →+* ℂ, spMap ψ ≫ stalkPt Y y = p.1 →
      ∀ φ f, Fits g₀ τ y φ f (lieMat dual (A ch)) →
      ∀ (yc : CxPts (genStr Z) (embOf e σ)), yc.1 = p.1 ≫ ρ → ∀ g : EigFrame Z (embOf e σ) (yc.1 ≫ genι Z),
        f.IsMap ψ g → m.G ch z = mat dual ((G _).gram yc g τ) := by
  have key : ∀ z : CxPts N.p σ₀, ∃ φ f, Fits g₀ τ (Var.base (toY z)) φ f (lieMat dual (A (hM.pick z))) ∧
      ∃ g : EigFrame Z (embOf e (extEmb σ₀)) ((down hρ (toY z)).1 ≫ genι Z), f.IsMap (Var.evStalk (toY z)) g := fun z => by
    obtain ⟨φ, f, hf⟩ := hA.2 (hM.pick z) _ (mem_base (toY_j z).symm (hM.mem_pick z))
    exact ⟨φ, f, hf, f.exists_isMap _ (emb_eq _ hf.1) (pt_eq _ rfl)⟩
  choose φ₀ f₀ hf₀ g₁ hg₁ using key
  refine ⟨Met.ofPt hM hM.pick hM.mem_pick (fun z => mat dual ((G _).gram _ (g₁ z) τ))
    fun z => mat_posDef dual ((G _).pos _ _ _), ?_⟩
  intro σ hσ p z hz ch hch y hy ψ hψ φ f hf yc hyc g hg
  obtain rfl := extEmb_eq hσ
  obtain rfl : p = toY z := Subtype.ext (N.pb.hom_ext (hz.symm.trans (toY_j z).symm) (p.2.trans (toY z).2.symm))
  subst hy
  obtain rfl : ψ = Var.evStalk (toY z) := EigLoc.spMap_inj ((cancel_mono (Y.X.fromSpecStalk _)).1
    (hψ.trans (spMap_ev _).symm))
  obtain rfl : yc = down hρ (toY z) := Subtype.ext hyc
  rw [rule hA.1 (G _) (toY z) (mem_base hz (hM.mem_pick z)) (mem_base hz hch) (hf₀ z) hf hyc (hg₁ z) hg, ← hz,
    trAt_cx z _ _ (hM.mem_pick z) hch]
  rfl

end UpperTheory.BaseMatrixDescent

open UpperTheory.BaseMatrixDescent GlobalTheory.TrueGeo.ModelMetric in
theorem UpperTheory.generic_frame_true_model :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : Var F) (ρ : Y.X ⟶ gen Z) (_ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ) (N : GlobalTheory.TrueGeo.Model Y) (M : N.X.Modules) (hM : IsVB M (Dw.mult τ)) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn) (G : ∀ σ : c.F →+* ℂ, EigMet Z σ), IsLie g₀ τ N.j dual A → (∀ (σ σ' : c.F →+* ℂ) (y : CxPts (genStr Z) σ) (y' : CxPts (genStr Z) σ') (g : EigFrame Z σ (y.1 ≫ genι Z)) (g' : EigFrame Z σ' (y'.1 ≫ genι Z)), σ' = (starRingEnd ℂ).comp σ → y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → g.IsMap (starRingEnd ℂ) g' → (G σ').gram y' g' τ = ((G σ).gram y g τ).map (starRingEnd ℂ)) → ∃ h : VMetric N.p M (Dw.mult τ), IsMet g₀ τ N.j dual A G h := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y ρ hρ g₀ τ N M hM dual A G hA hG
  choose m hm using exists_met hρ N hM G hA
  refine ⟨⟨hM, m, fun σ σ' => Met.isConj_of_exists fun z z' hz => ⟨hM.pick z, hM.mem_pick z, ?_⟩⟩, ?_⟩
  · have hσ := CxPts.eq_conj_of_conj hz
    have he : extEmb σ' = (starRingEnd ℂ).comp (extEmb σ) :=
      extEmb_eq (by rw [RingHom.comp_assoc, extEmb_comp, hσ])
    have hp : (toY z').1 = spMap (starRingEnd ℂ) ≫ (toY z).1 := by
      refine N.pb.hom_ext ?_ ?_
      · rw [toY_j, Category.assoc, toY_j]
        exact hz
      · rw [(toY z').2, Category.assoc, (toY z).2, ModelMetric.spMap_comp_spMap, he]
    have he' : embOf e (extEmb σ') = (starRingEnd ℂ).comp (embOf e (extEmb σ)) := by rw [he]; rfl
    have hd : (down hρ (toY z')).1 = spMap (starRingEnd ℂ) ≫ (down hρ (toY z)).1 :=
      (congrArg (· ≫ ρ) hp).trans (Category.assoc _ _ _)
    obtain ⟨φ, f, hf⟩ := hA.2 (hM.pick z) _ (mem_base (toY_j z).symm (hM.mem_pick z))
    obtain ⟨g, hg⟩ := f.exists_isMap _ (emb_eq _ hf.1) (pt_eq (yc := down hρ (toY z)) _ rfl)
    obtain ⟨g', hg'⟩ := g.exists_isMap (starRingEnd ℂ) (x' := (down hρ (toY z')).1 ≫ genι Z) he'
      (by rw [hd, Category.assoc])
    have hfg : f.IsMap ((starRingEnd ℂ).comp (Var.evStalk (toY z))) g' := fun τ i => by
      rw [hg', hg, GlobalTheory.GradedPieces.dual_comp]
    rw [hm σ _ (extEmb_comp σ) (toY z) z (toY_j z).symm _ (hM.mem_pick z) _ rfl _ (spMap_ev _) φ f hf _ rfl g hg,
      hm σ' _ (extEmb_comp σ') (toY z') z' (toY_j z').symm _ ((CxPts.mem_ptsIn_iff_of_conj hz).2 (hM.mem_pick z)) _
        (base_conj hp) _ (by rw [← ModelMetric.spMap_comp_spMap, Category.assoc, spMap_ev, hp]) φ f hf _ rfl g' hfg,
      hG _ _ _ _ g g' he' hd hg', mat_conj]
  · intro ch σ p z hz hch φ f hf yc hyc g hg
    exact hm _ σ rfl p z hz ch hch _ rfl _ (spMap_ev p) φ f hf yc hyc g hg
