import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

open scoped ComplexOrder Matrix

namespace GlobalTheory.ArLieBase.MetOfEig

section Emb

variable {F : Type} [Field F] [NumberField F]

theorem exists_comp_eq (σ₀ : 𝓞 F →+* ℂ) : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = σ₀ := by
  have hk : RingHom.ker σ₀ = ⊥ := by
    have h0 : Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker σ₀) = ⊥ := by
      rw [RingHom.comap_ker]
      have e : σ₀.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom ℂ := RingHom.ext_int _ _
      rw [e]
      exact (RingHom.injective_iff_ker_eq_bot _).1 Int.cast_injective
    exact Ideal.eq_bot_of_comap_eq_bot h0
  have hinj : Function.Injective σ₀ := (RingHom.injective_iff_ker_eq_bot _).2 hk
  refine ⟨IsFractionRing.lift (K := F) hinj, ?_⟩
  ext x
  exact IsFractionRing.lift_algebraMap (K := F) hinj x

def extEmb (σ₀ : 𝓞 F →+* ℂ) : F →+* ℂ := (exists_comp_eq σ₀).choose

theorem extEmb_comp (σ₀ : 𝓞 F →+* ℂ) : (extEmb σ₀).comp (algebraMap (𝓞 F) F) = σ₀ :=
  (exists_comp_eq σ₀).choose_spec

theorem eq_extEmb {σ₀ : 𝓞 F →+* ℂ} {σ : F →+* ℂ} (h : σ.comp (algebraMap (𝓞 F) F) = σ₀) : σ = extEmb σ₀ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (h.trans (extEmb_comp σ₀).symm)

end Emb

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp]; rfl

theorem eq_of_spMap_eq {R R' : Type} [CommRing R] [CommRing R'] {a b : R →+* R'} (h : spMap a = spMap b) : a = b :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem evalPt_congr {R : Type} [CommRing R] {Y : Scheme.{0}} {x x' : Sp R ⟶ Y} (e : x = x') (U : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (f : Γ(Y, U)) :
    TangentOrigin.evalPt x U h f = TangentOrigin.evalPt x' U h' f := by
  subst e; rfl

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

section Frames

variable {σ' : c.F →+* ℂ}

open Classical in

def gramOf (G : EigMet Z σ') (y : CxPts (genStr Z) σ') (τ : E →+* ℂ)
    (u : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)) : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
  if h : ∃ g : EigFrame Z σ' (y.1 ≫ genι Z), g.v τ = u then G.gram y h.choose τ else 1

theorem gramOf_eq (G : EigMet Z σ') {y : CxPts (genStr Z) σ'} {τ : E →+* ℂ}
    {u : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)} (g : EigFrame Z σ' (y.1 ≫ genι Z)) (hg : g.v τ = u) :
    gramOf G y τ u = G.gram y g τ := by
  have h : ∃ g : EigFrame Z σ' (y.1 ≫ genι Z), g.v τ = u := ⟨g, hg⟩
  have hco : h.choose.co g τ = 1 := EigFrame.co_eq fun i => by
    rw [h.choose_spec, ← hg]
    convert isCombAtG_single Z.t _ (g.tan τ) i using 1
    funext a
    simp [Matrix.one_apply, Pi.single_apply]
  rw [gramOf, dif_pos h, G.change y h.choose g τ, hco]
  simp

theorem gramOf_posDef (G : EigMet Z σ') (y : CxPts (genStr Z) σ') (τ : E →+* ℂ)
    (u : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)) : (gramOf G y τ u).PosDef := by
  unfold gramOf
  split_ifs
  exacts [G.pos _ _ _, Matrix.PosDef.one]

open Classical in

def withPart {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} (g₀ : EigFrame Z φ x) (τ : E →+* ℂ)
    (u : Fin (Dw.mult τ) → (Sp (DualNumber K) ⟶ Z.t.G.left)) (hu : IsEigBasis Z φ x τ u) : EigFrame Z φ x where
  v := Function.update g₀.v τ u
  tan τ' i := by
    by_cases h : τ' = τ
    · subst h; simpa using (hu.1 i).1
    · rw [Function.update_of_ne h]; exact g₀.tan τ' i
  eig τ' i a := by
    by_cases h : τ' = τ
    · subst h; simpa using (hu.1 i).2 a
    · rw [Function.update_of_ne h]; exact g₀.eig τ' i a
  basis τ' w hw he := by
    by_cases h : τ' = τ
    · subst h; simpa using hu.2 w ⟨hw, he⟩
    · rw [Function.update_of_ne h]; exact g₀.basis τ' w hw he

theorem exists_frame_part (y : CxPts (genStr Z) σ') {τ : E →+* ℂ}
    {u : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)} (hu : IsEigBasis Z σ' (y.1 ≫ genι Z) τ u) :
    ∃ g : EigFrame Z σ' (y.1 ≫ genι Z), g.v τ = u := by
  obtain ⟨g₀⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c Oz β Z ℂ σ' y.1 y.2
  exact ⟨withPart g₀ τ u hu, by simp [withPart]⟩

end Frames

section Points

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X}
  {πB : W ⟶ gen Z}
  (hpb : IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)))

include hpb in

def ptG {σ₀ : 𝓞 F →+* ℂ} (z : CxPts q σ₀) : Sp ℂ ⟶ W :=
  hpb.lift z.1 (spMap (extEmb σ₀)) (by rw [z.2, spMap_comp, extEmb_comp])

theorem ptG_fst {σ₀ : 𝓞 F →+* ℂ} (z : CxPts q σ₀) : ptG hpb z ≫ jB = z.1 := hpb.lift_fst _ _ _

theorem ptG_snd {σ₀ : 𝓞 F →+* ℂ} (z : CxPts q σ₀) :
    ptG hpb z ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (extEmb σ₀) := hpb.lift_snd _ _ _

omit [NumberField F] in
theorem spMap_e : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
  rw [spMap_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext e.apply_symm_apply))

omit [NumberField F] in
theorem genStr_of {x : Sp ℂ ⟶ W} {σ : F →+* ℂ} (h : x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap σ) :
    (x ≫ πB) ≫ genStr Z = spMap (σ.comp e.symm.toRingHom) := by
  rw [← spMap_comp, ← h]
  simp only [Category.assoc, spMap_e, Category.comp_id]

omit [NumberField F] in
theorem of_genStr {x : Sp ℂ ⟶ W} {σ : F →+* ℂ} (h : (x ≫ πB) ≫ genStr Z = spMap (σ.comp e.symm.toRingHom)) :
    x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap σ := by
  rw [← Category.assoc, ← Category.assoc, h, spMap_comp]
  congr 1
  ext a
  simp

def ptY {σ₀ : 𝓞 F →+* ℂ} (z : CxPts q σ₀) : CxPts (genStr Z) ((extEmb σ₀).comp e.symm.toRingHom) :=
  ⟨ptG hpb z ≫ πB, genStr_of (ptG_snd hpb z)⟩

theorem eq_ptG {σ₀ : 𝓞 F →+* ℂ} {z : CxPts q σ₀} {σ : F →+* ℂ} (hσ : σ.comp (algebraMap (𝓞 F) F) = σ₀)
    {zg : Sp ℂ ⟶ W} (h₁ : zg ≫ jB = z.1) (h₂ : (zg ≫ πB) ≫ genStr Z = spMap (σ.comp e.symm.toRingHom)) :
    zg = ptG hpb z :=
  hpb.hom_ext (h₁.trans (ptG_fst hpb z).symm) (by rw [ptG_snd, of_genStr h₂, eq_extEmb hσ])

end Points

section Metric

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X}
  {πB : W ⟶ gen Z}
  (hpb : IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)))
  {M : X.Modules} {τ : E →+* ℂ} (dual : Bool) (uu : FrAssign Z M (Dw.mult τ) jB) (Gm : ∀ σ', EigMet Z σ')

def uvec (ch : Chart M (Dw.mult τ)) {σ₀ : 𝓞 F →+* ℂ} (z : CxPts q σ₀) (hz : z ∈ CxPts.ptsIn q σ₀ ch.U) :
    Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Z.t.G.left) :=
  uu ch.U ch.e ch.isFrame ℂ (ptG hpb z) (by rw [ptG_fst]; exact hz)

open Classical in

def lieGram (σ₀ : 𝓞 F →+* ℂ) (ch : Chart M (Dw.mult τ)) (z : CxPts q σ₀) :
    Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
  if hz : z ∈ CxPts.ptsIn q σ₀ ch.U then
    cond dual (gramOf (Gm _) (ptY hpb z) τ (uvec hpb uu ch z hz))⁻¹
      (gramOf (Gm _) (ptY hpb z) τ (uvec hpb uu ch z hz))ᵀ
  else 0

theorem lieGram_spec {σ₀ : 𝓞 F →+* ℂ} (z : CxPts q σ₀) (σ : F →+* ℂ) (hσ : σ.comp (algebraMap (𝓞 F) F) = σ₀)
    (zg : Sp ℂ ⟶ W) (hzg : zg ≫ jB = z.1) (yc : CxPts (genStr Z) (σ.comp e.symm.toRingHom)) (hyc : yc.1 = zg ≫ πB)
    (ch : Chart M (Dw.mult τ)) (hx : ⊤ ≤ (zg ≫ jB) ⁻¹ᵁ ch.U)
    (g : EigFrame Z (σ.comp e.symm.toRingHom) (yc.1 ≫ genι Z))
    (hg : ∀ i, g.v τ i = uu ch.U ch.e ch.isFrame ℂ zg hx i) :
    lieGram hpb dual uu Gm σ₀ ch z = cond dual ((Gm _).gram yc g τ)⁻¹ ((Gm _).gram yc g τ)ᵀ := by
  obtain rfl := eq_extEmb hσ
  obtain rfl : zg = ptG hpb z := eq_ptG hpb hσ hzg (by rw [← hyc]; exact yc.2)
  obtain rfl : yc = ptY hpb z := Subtype.ext hyc
  have hz : z ∈ CxPts.ptsIn q σ₀ ch.U := by have := hx; rwa [hzg] at this
  have hg' : g.v τ = uvec hpb uu ch z hz := funext hg
  rw [lieGram, dif_pos hz, gramOf_eq (Gm _) g hg']

theorem trEntry {r : ℕ} {σ₀ : 𝓞 F →+* ℂ} (ch ch' : Chart M r) (y : CxPts q σ₀) (hy : y ∈ CxPts.ptsIn q σ₀ ch.U)
    (hy' : y ∈ CxPts.ptsIn q σ₀ ch'.U) (x : Sp ℂ ⟶ X) (hxy : x = y.1) (hxx : ⊤ ≤ x ⁻¹ᵁ (ch.U ⊓ ch'.U))
    (a b : Fin r) :
    ch.tr q σ₀ ch' y a b = TangentOrigin.evalPt x (ch.U ⊓ ch'.U) hxx (trCo ch.isFrame ch'.e a b) := by
  have hW : y ∈ CxPts.ptsIn q σ₀ (ch.U ⊓ ch'.U) := CxPts.mem_ptsIn_inf.2 ⟨hy, hy'⟩
  rw [VB.Chart.tr, Matrix.of_apply, ch.crd_eq (ch'.e b) inf_le_right inf_le_left hW a, CxPts.ev_eq hW,
    CxPts.evHom_eq_evalPt]
  exact evalPt_congr hxy.symm _ _ _ _

theorem inv_chg_transpose_conj {n : ℕ} (T M : Matrix (Fin n) (Fin n) ℂ) (hT : IsUnit T) :
    M⁻¹ = HermFrame.chg T ((Tᵀ)ᴴ * M * Tᵀ)⁻¹ := by
  have h1 : IsUnit Tᵀ.det := by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 hT
  have h2 : IsUnit (Tᵀ)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact h1.star
  have e : Tᴴᵀ = (Tᵀ)ᴴ := by ext; simp
  rw [HermFrame.chg, Matrix.mul_inv_rev, Matrix.mul_inv_rev, e]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h2, Matrix.mul_one]

theorem lieGram_trans (hLF : IsLieFrames Z e jB πB M (Dw.mult τ) τ dual uu) {σ₀ : 𝓞 F →+* ℂ}
    (ch ch' : Chart M (Dw.mult τ)) (y : CxPts q σ₀) (hy : y ∈ CxPts.ptsIn q σ₀ ch.U) :
    lieGram hpb dual uu Gm σ₀ ch' y = HermFrame.chg (ch.tr q σ₀ ch' y) (lieGram hpb dual uu Gm σ₀ ch y) := by
  by_cases hy' : y ∈ CxPts.ptsIn q σ₀ ch'.U
  swap
  · rw [lieGram, dif_neg hy', VB.Chart.tr_of_notMem ch ch' hy', HermFrame.chg_zero]
  have hx : ⊤ ≤ (ptG hpb y ≫ jB) ⁻¹ᵁ ch.U := by rw [ptG_fst]; exact hy
  have hx' : ⊤ ≤ (ptG hpb y ≫ jB) ⁻¹ᵁ ch'.U := by rw [ptG_fst]; exact hy'
  have hxx : ⊤ ≤ (ptG hpb y ≫ jB) ⁻¹ᵁ (ch.U ⊓ ch'.U) := by
    rw [ptG_fst]; exact CxPts.mem_ptsIn_inf.2 ⟨hy, hy'⟩
  have hb : ∀ (ch₁ : Chart M (Dw.mult τ)) (h₁ : ⊤ ≤ (ptG hpb y ≫ jB) ⁻¹ᵁ ch₁.U),
      IsEigBasis Z ((extEmb σ₀).comp e.symm.toRingHom) ((ptY hpb y).1 ≫ genι Z) τ
        (uu ch₁.U ch₁.e ch₁.isFrame ℂ (ptG hpb y) h₁) := fun ch₁ h₁ => by
    have := hLF.1 ch₁.U ch₁.e ch₁.isFrame ℂ (ptG hpb y) h₁ (extEmb σ₀) (ptG_snd hpb y)
    simpa only [ptY, Category.assoc] using this
  obtain ⟨g, hg⟩ := exists_frame_part (ptY hpb y) (hb ch hx)
  obtain ⟨g', hg'⟩ := exists_frame_part (ptY hpb y) (hb ch' hx')
  have hg₁ : g.v τ = uvec hpb uu ch y hy := hg
  have hg₁' : g'.v τ = uvec hpb uu ch' y hy' := hg'
  have hpt : (ptY hpb y).1 ≫ genι Z = ptG hpb y ≫ πB ≫ genι Z := Category.assoc _ _ _
  have hT := ch.isUnit_tr ch' hy hy'
  rw [lieGram, lieGram, dif_pos hy, dif_pos hy', gramOf_eq _ g hg₁, gramOf_eq _ g' hg₁']
  cases dual
  · have hco : g.co g' τ = ch.tr q σ₀ ch' y := EigFrame.co_eq fun i => by
      have := hLF.2.1 ch.U ch'.U ch.e ch'.e ch.isFrame ch'.isFrame ℂ (ptG hpb y) hx hx' hxx i
      simp only [cond] at this
      have hcf : (fun a => ch.tr q σ₀ ch' y a i) = fun b =>
          TangentOrigin.evalPt (ptG hpb y ≫ jB) (ch.U ⊓ ch'.U) hxx (trCo ch.isFrame ch'.e b i) :=
        funext fun b => trEntry ch ch' y hy hy' _ (ptG_fst hpb y) hxx b i
      rw [hg, hg', hpt, hcf]
      exact this
    rw [(Gm _).change (ptY hpb y) g g' τ, hco]
    simp only [cond, HermFrame.chg, Matrix.transpose_mul, Matrix.mul_assoc]
  · have hco : g'.co g τ = (ch.tr q σ₀ ch' y)ᵀ := EigFrame.co_eq fun i => by
      have := hLF.2.1 ch.U ch'.U ch.e ch'.e ch.isFrame ch'.isFrame ℂ (ptG hpb y) hx hx' hxx i
      simp only [cond] at this
      have hcf : (fun a => (ch.tr q σ₀ ch' y)ᵀ a i) = fun a =>
          TangentOrigin.evalPt (ptG hpb y ≫ jB) (ch.U ⊓ ch'.U) hxx (trCo ch.isFrame ch'.e i a) :=
        funext fun a => trEntry ch ch' y hy hy' _ (ptG_fst hpb y) hxx i a
      rw [hg, hg', hpt, hcf]
      exact this
    rw [(Gm _).change (ptY hpb y) g' g τ, hco]
    exact inv_chg_transpose_conj _ _ hT

theorem inv_map_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : (A.map (starRingEnd ℂ))⁻¹ = A⁻¹.map star := by
  have h : A.map (starRingEnd ℂ) = Aᴴᵀ := by ext; simp
  rw [h, ← Matrix.transpose_nonsing_inv, ← Matrix.conjTranspose_nonsing_inv]
  ext; simp

theorem lieGram_conj (hLF : IsLieFrames Z e jB πB M (Dw.mult τ) τ dual uu) (hEC : EigConj Z Gm)
    {σ₀ σ₀' : 𝓞 F →+* ℂ} (ch : Chart M (Dw.mult τ)) (y : CxPts q σ₀) (y' : CxPts q σ₀')
    (hyy : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    lieGram hpb dual uu Gm σ₀' ch y' = (lieGram hpb dual uu Gm σ₀ ch y).map star := by
  by_cases hy : y ∈ CxPts.ptsIn q σ₀ ch.U
  swap
  · have hy' : y' ∉ CxPts.ptsIn q σ₀' ch.U := fun h => hy ((CxPts.mem_ptsIn_iff_of_conj hyy).1 h)
    rw [lieGram, lieGram, dif_neg hy, dif_neg hy']
    ext; simp
  have hy' : y' ∈ CxPts.ptsIn q σ₀' ch.U := (CxPts.mem_ptsIn_iff_of_conj hyy).2 hy
  have hσ : (starRingEnd ℂ).comp σ₀ = σ₀' :=
    eq_of_spMap_eq (by rw [← spMap_comp, ← y.2, ← y'.2, hyy, Category.assoc])
  have hσ' : extEmb σ₀' = (starRingEnd ℂ).comp (extEmb σ₀) :=
    (eq_extEmb (by rw [RingHom.comp_assoc, extEmb_comp, hσ])).symm
  have hzg : ptG hpb y' = spMap (starRingEnd ℂ) ≫ ptG hpb y :=
    hpb.hom_ext (by rw [ptG_fst, Category.assoc, ptG_fst, hyy])
      (by rw [ptG_snd, Category.assoc, ptG_snd, spMap_comp, hσ'])
  have hx : ⊤ ≤ (ptG hpb y ≫ jB) ⁻¹ᵁ ch.U := by rw [ptG_fst]; exact hy
  have hb := hLF.1 ch.U ch.e ch.isFrame ℂ (ptG hpb y) hx (extEmb σ₀) (ptG_snd hpb y)
  obtain ⟨g, hg⟩ := exists_frame_part (ptY hpb y) (by simpa only [ptY, Category.assoc] using hb)
  have hg₁ : g.v τ = uvec hpb uu ch y hy := hg
  have hφ : (extEmb σ₀').comp e.symm.toRingHom = (starRingEnd ℂ).comp ((extEmb σ₀).comp e.symm.toRingHom) := by
    rw [hσ']; rfl
  have hyc : (ptY hpb y').1 = spMap (starRingEnd ℂ) ≫ (ptY hpb y).1 := by
    simp only [ptY, hzg, Category.assoc]
  have hpt : (ptY hpb y').1 ≫ genι Z = spMap (starRingEnd ℂ) ≫ ((ptY hpb y).1 ≫ genι Z) := by
    rw [hyc, Category.assoc]
  obtain ⟨g', hg'⟩ := EigFrame.exists_isMap (φ' := (extEmb σ₀').comp e.symm.toRingHom)
    (x' := (ptY hpb y').1 ≫ genι Z) g (starRingEnd ℂ) hφ hpt
  have key : ∀ (x₁ x₂ : Sp ℂ ⟶ W) (_ : x₁ = x₂) (h₁ : ⊤ ≤ (x₁ ≫ jB) ⁻¹ᵁ ch.U) (h₂ : ⊤ ≤ (x₂ ≫ jB) ⁻¹ᵁ ch.U),
      uu ch.U ch.e ch.isFrame ℂ x₁ h₁ = uu ch.U ch.e ch.isFrame ℂ x₂ h₂ := by
    intro x₁ x₂ ex _ _; subst ex; rfl
  have hx₂ : ⊤ ≤ ((spMap (starRingEnd ℂ) ≫ ptG hpb y) ≫ jB) ⁻¹ᵁ ch.U := by
    rw [← hzg, ptG_fst]; exact hy'
  have hv : g'.v τ = uvec hpb uu ch y' hy' := funext fun i => by
    rw [hg' τ, hg₁]
    unfold uvec
    rw [key _ _ hzg _ hx₂]
    exact (hLF.2.2 ch.U ch.e ch.isFrame ℂ ℂ (starRingEnd ℂ) (ptG hpb y) _ hx₂ i).symm
  have hgram := hEC _ _ (ptY hpb y) (ptY hpb y') g g' τ hφ hyc hg'
  rw [lieGram, lieGram, dif_pos hy, dif_pos hy', gramOf_eq _ g hg₁, gramOf_eq _ g' hv, hgram]
  cases dual
  · ext a b; simp
  · simp only [cond]; exact inv_map_conj _

open Classical in

def met (hVB : IsVB M (Dw.mult τ)) (hLF : IsLieFrames Z e jB πB M (Dw.mult τ) τ dual uu) (σ₀ : 𝓞 F →+* ℂ) :
    Met q σ₀ M (Dw.mult τ) where
  isVB := hVB
  G := lieGram hpb dual uu Gm σ₀
  posDef ch y hy := by
    rw [lieGram, dif_pos hy]
    cases dual
    exacts [(gramOf_posDef _ _ _ _).transpose, (gramOf_posDef _ _ _ _).inv]
  trans ch ch' y hy := lieGram_trans hpb dual uu Gm hLF ch ch' y hy

def vmet (hVB : IsVB M (Dw.mult τ)) (hLF : IsLieFrames Z e jB πB M (Dw.mult τ) τ dual uu) (hEC : EigConj Z Gm) :
    VMetric q M (Dw.mult τ) :=
  ⟨hVB, met hpb dual uu Gm hVB hLF, fun _ _ ch y y' hyy => lieGram_conj hpb dual uu Gm hLF hEC ch y y' hyy⟩

end Metric

end Model

end GlobalTheory.ArLieBase.MetOfEig

namespace GlobalTheory.ArLieBase

open MetOfEig in

theorem exists_isLieMet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F)
    (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ gen Z),
    IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) →
    ∀ (M : X.Modules) (r : ℕ) (τ : E →+* ℂ) (dual : Bool) (hr : r = Dw.mult τ) (uu : FrAssign Z M r jB)
      (G : ∀ σ', EigMet Z σ'), IsVB M r → IsLieFrames Z e jB πB M r τ dual uu → EigConj Z G →
      ∃ h : VMetric q M r, IsLieMet Z e q jB πB M r τ dual hr G h uu := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB hpb M r τ dual hr uu G hVB hLF hEC
  subst hr
  refine ⟨vmet hpb dual uu G hVB hLF hEC, ?_⟩
  intro σ z zg yc hzg hyc ch hx g hg
  have e₁ : ∀ i, g.v τ i = uu ch.U ch.e ch.isFrame ℂ zg hx i := fun i => by simpa using hg i
  have := lieGram_spec hpb dual uu G z σ rfl zg hzg yc hyc ch hx g e₁
  simpa [vmet, met] using this

end GlobalTheory.ArLieBase
