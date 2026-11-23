import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleGenericFibreData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarSectionsCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetQuotGramRe
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCovWeight

open GlobalTheory.GradedNorm GlobalTheory.FlagCovDivCore Matrix

theorem grSq_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) : grSq Mᵀ i = grSq M i := by
  have e (k) : ReciprocityTheory.ChartRestriction.G.FD.lminor Mᵀ k = ReciprocityTheory.ChartRestriction.G.FD.lminor M k := det_transpose _
  rw [grSq, grSq, e, e]

theorem grSq_block {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) :
    grSq (M.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt) : Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ) (Fin.last i) =
      grSq M i := rfl

theorem top_le_fromSpecStalk {G : Scheme.{0}} {x : G} {U : G.Opens} (hU : x ∈ U) : ⊤ ≤ G.fromSpecStalk x ⁻¹ᵁ U :=
  fun w _ => by
    have : G.fromSpecStalk x w ∈ Set.range (G.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := G.fromSpecStalk x w) this U.isOpen hU

theorem ratVal_stalk {k : Type} [CommRing k] {σ : k →+* ℂ} {G : Scheme.{0}} [IsIntegral G] {q : G ⟶ Sp k} (z : CxPts q σ)
    {χ : G.presheaf.stalk (under z) →+* ℂ} (hχ : spMap χ ≫ G.fromSpecStalk (under z) = z.1)
    (a : G.presheaf.stalk (under z)) : ratVal (algebraMap _ G.functionField a) z = χ a := by
  obtain ⟨U, hU, b, rfl⟩ := G.presheaf.germ_exist a
  have hz : z ∈ ptsIn q σ U := mem_ptsIn.2 hU
  have hη : genericPoint G ∈ U := (genericPoint_specializes (under z)).mem_open U.isOpen hU
  have e : algebraMap _ G.functionField (G.presheaf.germ U (under z) hU b) = fnOf U hη b :=
    GlobalTheory.Cartier.algebraMap_germ hU b
  have hs : ⊤ ≤ G.fromSpecStalk (under z) ⁻¹ᵁ U := top_le_fromSpecStalk hU
  have key : ∀ (y : Sp ℂ ⟶ G) (hy : ⊤ ≤ y ⁻¹ᵁ U), y = spMap χ ≫ G.fromSpecStalk (under z) →
      TangentOrigin.evalPt y U hy b = χ (TangentOrigin.evalPt (G.fromSpecStalk (under z)) U hs b) := by
    rintro y hy rfl
    exact TangentOrigin.evalPt_spMap_comp χ _ U hs hy b
  rw [e, ratVal_fnOf hz, ev_eq hz, evHom_eq_evalPt]
  refine (key _ hz hχ.symm).trans (congrArg χ ?_)
  have e2 : (G.fromSpecStalk (under z)).appLE U ⊤ hs ≫ (Scheme.ΓSpecIso _).hom = G.presheaf.germ U (under z) hU := by
    rw [Scheme.Hom.appLE]
    rw [Scheme.fromSpecStalk_app hU]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc (Spec _).presheaf, Subsingleton.elim (_ ≫ _) (𝟙 (Opposite.op ⊤))]
    simp
  exact congrArg (fun f => f.hom b) e2

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem prod_zpow_single {M : Type} [DivisionCommMonoid M] (F : Pad.Letter Dw → M) (n : Pad.Letter Dw → ℤ)
    (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (hn : ∀ z, n z = if τ = z.1 ∧ (k : ℕ) = z.2 then 1 else 0) :
    ∏ z, F z ^ n z = F ⟨τ, k⟩ := by
  rw [Finset.prod_eq_single ⟨τ, k⟩ (fun b _ hb => ?_) (by simp), hn, if_pos ⟨rfl, rfl⟩, zpow_one]
  obtain ⟨τ', k'⟩ := b
  rw [hn, if_neg, zpow_zero]
  rintro ⟨rfl, h⟩
  exact hb (congrArg _ (Fin.ext h.symm))

theorem grSq_of_tri {R K : Type} [CommRing R] [Field K] {ψ : R →+* K} (hψ : Function.Injective ψ) {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} {φ' : c.F →+* K} {x' : Sp K ⟶ Z.X} {f : EigFrame Z φ x} {v : EigFrame Z φ' x'}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (hf : f.Tri ψ v t) {τ : E →+* ℂ} {m : ℕ} (hr : m = Dw.mult τ)
    {u : Fin m → (Sp (DualNumber R) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) {A : Matrix (Fin m) (Fin m) R}
    (hA : IsUnit A.det) (ρ : Fin m → Kˣ)
    (h : ∀ i, ∃ (w : Sp (DualNumber K) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → K),
      IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) (fun b => ψ (A b i)) w ∧ IsCombAtG Z.t x' (v.v τ) cf w ∧
        cf (Fin.cast hr i) = ((ρ i)⁻¹ : Kˣ) ∧ ∀ k, Fin.cast hr i < k → cf k = 0)
    {σ : c.F →+* ℂ} (Gm : EigMet Z σ) {yc : CxPts (genStr Z) σ} {g : EigFrame Z σ (yc.1 ≫ genι Z)} {χ : R →+* ℂ}
    (hg : f.Tri χ g 1) {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : ∀ g' : EigFrame Z σ (yc.1 ≫ genι Z), (∀ i, g'.v τ (Fin.cast hr i) = spMap (dualMap χ) ≫ u i) →
      M = (Gm.gram yc g' τ)ᵀ.submatrix (Fin.cast hr) (Fin.cast hr)) (i : Fin m) :
    ∃ a : R, IsUnit a ∧ ψ a = t τ (Fin.cast hr i) * ((ρ i)⁻¹ : Kˣ) ∧
      grSq (HermFrame.chg (A.map χ) M) i = ‖χ a‖ ^ 2 * grSq (Gm.gram yc g τ) (Fin.cast hr i) := by
  subst hr
  obtain ⟨k, rfl⟩ := exists_frame_of_basis f hu
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨k', hk'⟩ := k.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨f₁, hf₁⟩ := f.exists_isMap χ hg.2.1 hg.1
  obtain ⟨k₁, hk₁⟩ := k.exists_isMap χ hg.2.1 hg.1
  choose w cf h1 h2 h3 h4 using h
  obtain ⟨T1, T2⟩ := hf.co τ hf'
  obtain ⟨U1, U2⟩ := hg.co τ hf₁
  have hC : (Matrix.of fun a i => cf i a).BlockTriangular id := fun a i h => h4 i a h
  have hT : (f'.co v τ).BlockTriangular id := fun a i h => T1 a i h
  have e : (f.co k τ * A).map ψ = f'.co v τ * Matrix.of fun a i => cf i a := by
    rw [Matrix.map_mul, ← hf'.co τ hk' hf.1]
    ext a i
    rw [← funext (hk' τ)] at h1
    exact congrFun (co_mulVec f' k' v τ (h1 i) (h2 i)) a
  have hS : ((f.co k τ * A).map ψ).BlockTriangular id := e ▸ hT.mul hC
  have hd := isUnit_diag hψ (S := f.co k τ * A) (by rw [Matrix.det_mul]; exact (f.isUnit_det_co k τ).mul hA) hS
  refine ⟨_, hd i, ?_, ?_⟩
  · refine (congrFun (congrFun e i) i).trans ((diag_mul hT hC i).trans ?_)
    rw [T2]
    exact congrArg _ (h3 i)
  · have e1 : HermFrame.chg (A.map χ) M =
        (((f.co k τ * A).map χ)ᴴ * Gm.gram yc f₁ τ * (f.co k τ * A).map χ)ᵀ := by
      rw [hM k₁ (hk₁ τ), Gm.change yc f₁ k₁, Matrix.map_mul, ← hf₁.co τ hk₁ hg.1]
      simp only [HermFrame.chg, transpose_mul, conjTranspose_mul, Matrix.mul_assoc, Fin.cast_refl, submatrix_id_id]
    have e2 := grSq_tri (Gm.gram yc f₁ τ) U1 (fun a => U2 a ▸ Units.ne_zero _) i
    rw [← Gm.change, U2] at e2
    rw [e1, grSq_transpose, grSq_tri _ (T := (f.co k τ * A).map χ) (fun a b hab => (congrArg χ (hψ ((hS hab).trans (map_zero _).symm))).trans
      (map_zero _)) (fun a => ((hd a).map χ).ne_zero)]
    simp only [Pi.one_apply, Units.val_one, norm_one, one_pow, one_mul] at e2
    exact congrArg₂ (· * ·) rfl e2.symm

variable {F : Type} [Field F] {e : F ≃+* c.F}

theorem exists_frame_pull (C : FlagCpt Z e) {G : Scheme.{0}} [IsIntegral G] (p : G ⟶ C.Y.X)
    (φ : C.Y.Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ p = spMap φ ≫ C.Y.X.fromSpecStalk (genericPoint C.Y.X)) (x : G)
    {xR : Sp (G.presheaf.stalk x) ⟶ Z.X} (hxR : xR = G.fromSpecStalk x ≫ p ≫ C.π ≫ genι Z)
    {xK : Sp G.functionField ⟶ Z.X} (hxK : xK = G.fromSpecStalk (genericPoint G) ≫ p ≫ C.π ≫ genι Z)
    {y : C.Y.X} (hy : y = p x) {φy : c.F →+* C.Y.X.presheaf.stalk y}
    {fy : EigFrame Z φy (stalkPt C.Y y ≫ C.π ≫ genι Z)} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (h1 : fy.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t)
    {k : Type} [CommRing k] {χ : G.presheaf.stalk x →+* k} {χy : C.Y.X.presheaf.stalk y →+* k}
    (hχ : spMap χy ≫ stalkPt C.Y y = spMap χ ≫ G.fromSpecStalk x ≫ p) {φ' : c.F →+* k} {x' : Sp k ⟶ Z.X}
    {g : EigFrame Z φ' x'} {t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ} (h2 : fy.Tri χy g t') :
    ∃ (ψ₀ : F →+* G.presheaf.stalk x) (f : EigFrame Z (ψ₀.comp e.symm.toRingHom) xR)
      (v : EigFrame Z (φ.comp (constF e C.Y)) xK),
      G.fromSpecStalk x ≫ p ≫ C.Y.str = spMap ψ₀ ∧ C.f0.IsMap φ v ∧
      f.Tri (algebraMap (G.presheaf.stalk x) G.functionField) v (fun τ i => Units.map φ.toMonoidHom (t τ i)) ∧
      f.Tri χ g t' := by
  subst hy
  have hs := comp_stalkMap p φ φs x
  have h0 : spMap (p.stalkMap x).hom ≫ stalkPt C.Y (p x) = G.fromSpecStalk x ≫ p :=
    Scheme.SpecMap_stalkMap_fromSpecStalk p
  have hc : χy = χ.comp (p.stalkMap x).hom := EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk (p x))).1 (by
    rw [spMap_trans, Category.assoc]
    exact hχ.trans (congrArg _ h0.symm)))
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : F →+* G.presheaf.stalk x, G.fromSpecStalk x ≫ p ≫ C.Y.str = spMap ψ₀ :=
    ⟨(Spec.preimage (G.fromSpecStalk x ≫ p ≫ C.Y.str)).hom, (Spec.map_preimage _).symm⟩
  have hg : genericPt C.Y ≫ C.Y.str = spMap (algebraMap F C.Y.Fn) := (GlobalTheory.FlagBundle.ratOf C.Y).pt_s
  have e1 : (algebraMap (G.presheaf.stalk x) G.functionField).comp ψ₀ = φ.comp (algebraMap F C.Y.Fn) := by
    refine EigLoc.spMap_inj ?_
    rw [spMap_trans, spMap_trans, ← hψ₀, ← hg, ← Category.assoc, spMap_fromSpecStalk,
      ← Category.assoc, φs, Category.assoc]
    rfl
  have e2 : φ.comp (constF e C.Y) =
      (algebraMap (G.presheaf.stalk x) G.functionField).comp (ψ₀.comp e.symm.toRingHom) := by
    rw [← RingHom.comp_assoc, e1]; rfl
  have e3 : ψ₀.comp e.symm.toRingHom = (p.stalkMap x).hom.comp φy := RingHom.ext fun a =>
    IsFractionRing.injective (G.presheaf.stalk x) G.functionField ((RingHom.congr_fun e2 a).symm.trans
      ((congrArg φ (RingHom.congr_fun h1.2.1 a)).trans (RingHom.congr_fun hs (φy a)).symm))
  have hK : xK = spMap φ ≫ genericPt C.Y ≫ C.π ≫ genι Z := by
    rw [hxK, ← Category.assoc, φs, Category.assoc]; rfl
  have hR : xR = spMap (p.stalkMap x).hom ≫ stalkPt C.Y (p x) ≫ C.π ≫ genι Z := by
    rw [hxR, ← Category.assoc (spMap _), h0, Category.assoc]
  obtain ⟨f, hf⟩ := fy.exists_isMap (p.stalkMap x).hom e3 hR
  obtain ⟨v, hv⟩ := C.f0.exists_isMap φ rfl hK
  refine ⟨ψ₀, f, v, hψ₀, hv, ⟨by rw [hxK, hxR, ← Category.assoc (spMap _), spMap_fromSpecStalk], e2, fun τ i => ?_⟩,
    by rw [h2.1, hR, hc, spMap_trans, Category.assoc], by rw [h2.2.1, e3, hc]; rfl, fun τ i => ?_⟩
  · obtain ⟨cf, c1, c2, c3⟩ := h1.2.2 τ i
    refine ⟨fun k => φ (cf k), congrArg φ c1, fun k hk => (congrArg φ (c2 k hk)).trans (map_zero _), ?_⟩
    have := GlobalTheory.GradedPieces.comb_map φ hK.symm c3
    simp only [GlobalTheory.GradedPieces.dual_comp] at this
    simp only [hv τ, hf τ, GlobalTheory.GradedPieces.dual_comp, hs]
    exact this
  · simpa only [hf τ, GlobalTheory.GradedPieces.dual_comp, ← hc] using h2.2.2 τ i

end Frames

set_option maxHeartbeats 1600000 in

theorem weight_lie : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Bs : Scheme.{0}) (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (E : D.what₂.Tau × Bool → Bs.Modules) (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (_ : GlobalTheory.BcRead.LieGen O c q E jB πB u)
    (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (_ : ∀ a, ∃ hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a),
      IsLieMet O.s.T.Z O.κ.e q jB πB (E a) _ (embB D a) (!a.2) hr Gm (h a) (u a))
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (_ : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀)
    (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X)
    (_ : IsPullback j (πG ≫ (O.var c).str) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πG] [Surjective πG] (φ : (O.var c).Fn →+* G.functionField)
    (_ : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ)
    (_ : GlobalTheory.FlagCov.FlagCover (fun a => (h a).isVB) jB πB u π₀ fl₀ j πG φ jG r)
    (a : D.what₂.Tau × Bool), a.2 = true → ∀ (i : Fin (rkB D.what₂.Tau O.N O.j a))
    (σ : D.what₂.LL →+* ℂ) (z : CxPts (πG ≫ (O.var c).str) σ) (y : Pts (O.var c) σ)
    (y' : CxPts (π₀ ≫ q) (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) (ch : (((fl₀ a).root i).pull j).ι)
    (t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → (O.var c).Fnˣ) (g : (O.Φ.C c).FrameAt y),
    (O.Φ.C c).Adapted y t g 1 → y.1 = z.1 ≫ πG → y'.1 = z.1 ≫ j → under z ∈ (((fl₀ a).root i).pull j).U ch →
    UnitAt (under z) ((((r a i ch)⁻¹ : G.functionFieldˣ) : G.functionField) *
        φ ((prodPow t (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) : (O.var c).Fnˣ) : (O.var c).Fn)) ∧
      Real.exp (-((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).φ (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))).φ
          (ch PUnit.unit) y') =
        ‖ratVal ((((r a i ch)⁻¹ : G.functionFieldˣ) : G.functionField) *
          φ ((prodPow t (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) : (O.var c).Fnˣ) : (O.var c).Fn)) z‖ ^ 2 *
          (O.Φ.C c).genSq (Gm (embOf O.κ.e σ)) (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) g := by
  intro D O c Bs q E h H Bg jB πB u hL Gm lm Y₀ _ π₀ fl₀ _ G _ j πG _ _ _ φ φs jG r hc a ha i σ z y y' ch t g had ey ey' hx
  obtain ⟨-, -, -, frB⟩ := hL
  obtain ⟨c1, c2, c3⟩ := hc
  obtain ⟨hr, lm⟩ := lm a
  have hqc := (h a).isVB.isQuasicoherent
  set x := under z with hxz

  obtain ⟨cc, hci, hcc⟩ : ∃ cc : ∀ k, (((fl₀ a).root k).pull j).ι, cc i = ch ∧
      ∀ k, j x ∈ (cc k PUnit.unit).U := by
    choose U e hU he using fun k => (fl₀ a).isVB_gr k (j x)
    let c₀ : ∀ k, (((fl₀ a).root k).pull j).ι := fun k _ => ⟨U k, e k, he k⟩
    refine ⟨Function.update c₀ i ch, Function.update_self _ _ _, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self]
      exact LB.pull_U_le j ch hx
    · rw [Function.update_of_ne hk]
      exact hU k
  subst hci
  obtain ⟨V, f, hV, hf⟩ := (h a).isVB (π₀ (j x))
  obtain ⟨W, hWV, hW, s, hxW, hs, hfr⟩ := exists_lifts_isFrame (fl₀ a) (fun k => cc k PUnit.unit) hcc
    (U := π₀ ⁻¹ᵁ V) hV
  let ψ := algebraMap (G.presheaf.stalk x) G.functionField
  have hψ : Function.Injective ψ := IsFractionRing.injective _ _
  obtain ⟨χ, hχ⟩ : ∃ χ : G.presheaf.stalk x →+* ℂ, spMap χ ≫ G.fromSpecStalk x = z.1 :=
    ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1⟩
  have hg : FlagCov.genPt G = spMap ψ ≫ G.fromSpecStalk x := (spMap_fromSpecStalk G x).symm
  have hRW : ⊤ ≤ (G.fromSpecStalk x ≫ j) ⁻¹ᵁ W := top_le_fromSpecStalk (U := j ⁻¹ᵁ W) hxW
  have hRV : ⊤ ≤ ((G.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, c1]
    exact top_le_fromSpecStalk (U := (j ≫ π₀) ⁻¹ᵁ V) hV
  have hKW : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W := by
    rw [hg, Category.assoc]
    exact fun w _ => hRW (x := spMap ψ w) trivial
  have hV' {K : Type} [CommRing K] (ρ : G.presheaf.stalk x →+* K) {w : Sp K ⟶ Bg}
      (hw : w = spMap ρ ≫ G.fromSpecStalk x ≫ jG) : ∃ hw' : ⊤ ≤ (w ≫ jB) ⁻¹ᵁ V,
        u a V f hf K w hw' = fun b => spMap (dualMap ρ) ≫ u a V f hf _ (G.fromSpecStalk x ≫ jG) hRV b := by
    subst hw
    refine ⟨?_, funext ((frB a).2.2 V f hf _ _ ρ _ hRV _)⟩
    rw [Category.assoc]
    exact fun w _ => hRV (x := spMap ρ w) trivial
  obtain ⟨hKV, hu'⟩ := hV' ψ (w := FlagCov.genPt G ≫ jG) (by rw [hg, Category.assoc])
  obtain ⟨hCV, hu''⟩ := hV' χ (w := z.1 ≫ jG) (by rw [← Category.assoc, hχ])
  obtain ⟨φy, fy, a1, a2⟩ := had
  obtain ⟨ψ₀, fR, v, e1, e2, e3, e4⟩ := exists_frame_pull (O.Φ.C c) πG φ φs x
    (xR := (G.fromSpecStalk x ≫ jG) ≫ πB ≫ genι O.s.T.Z)
    (by rw [Category.assoc, ← Category.assoc jG, c2, Category.assoc])
    (xK := FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (by rw [← Category.assoc jG, c2, Category.assoc]; rfl)
    (show Var.base y = πG x by rw [Var.base, ey]; rfl) a1 (χ := χ)
    (by rw [FlagCpt.spMap_evStalk, ← Category.assoc, hχ, ey]) a2
  have hu := (frB a).1 V f hf _ (G.fromSpecStalk x ≫ jG) hRV ψ₀ (by
    refine Eq.trans ?_ e1
    refine (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).symm.trans ?_))
    rw [c2]
    exact (Category.assoc _ _ _).trans (congrArg _ (O.Φ.C c).π_str))
  let A₀ := ((hf.pullback π₀).basis hWV).toMatrix fun k => ((fl₀ a).ι k.succ).app W (s k)
  have hA₀ : IsUnit A₀.det := by
    have := ((hf.pullback π₀).detUnit hfr hWV le_rfl).isUnit
    simpa only [IsFrame.val_detUnit, Twist.resM_self, Module.Basis.det_apply] using this
  let A := A₀.map (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW)
  have hA : IsUnit A.det := by
    have := hA₀.map (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW)
    rwa [RingHom.map_det] at this
  have hev {K : Type} [CommRing K] (ρ : G.presheaf.stalk x →+* K) {w : Sp K ⟶ Y₀} (hw' : ⊤ ≤ w ⁻¹ᵁ W)
      (hw : w = spMap ρ ≫ G.fromSpecStalk x ≫ j) (k) : (fun b => TangentOrigin.evalPt w W hw'
      (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k.succ).app W (s k)) b)) = fun b => ρ (A b k) := by
    subst hw
    exact funext fun b => TangentOrigin.evalPt_spMap_comp ρ _ W hRW hw' _
  have hsec (k) := c3 a k hr (cc k) V f hf W (hW k) hWV (s k) (hs k) hKW hKV
  have hv : (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) k) = v.v (embB D a) := (funext (e2 _)).symm
  have hy'W : y' ∈ ptsIn (π₀ ≫ q) _ W := mem_ptsIn.2 (by rw [ey']; exact hxW)
  have hy'V : y' ∈ ptsIn (π₀ ≫ q) _ (π₀ ⁻¹ᵁ V) := mem_ptsIn.2 (hWV (mem_ptsIn.1 hy'W))
  let cV : Chart (E a) _ := ⟨V, f, hf⟩
  have hM := lm σ (Points.PtsOver.map π₀ rfl _ y') (z.1 ≫ jG) ((O.Φ.C c).down y)
    (by rw [Category.assoc, c1, ← Category.assoc, ← ey']; rfl)
    (by rw [Category.assoc, c2, ← Category.assoc, ← ey]; rfl) cV hCV
  have hgram : (((h a).pull π₀ rfl).met _).gram (fun k => ((fl₀ a).ι k.succ).app W (s k)) y' =
      HermFrame.chg (A.map χ) (((h a).met _).G cV (Points.PtsOver.map π₀ rfl _ y')) := by
    rw [Met.gram_eq _ (cV.pull (h a).isVB π₀) hy'V _ hy'W]
    refine congrArg₂ _ ?_ (Met.pull_G _ π₀ rfl cV hy'V)
    ext b k
    refine (Chart.crd_eq _ _ le_rfl hWV hy'W b).trans ?_
    rw [ev_eq hy'W, evHom_eq_evalPt, Twist.resM_self]
    exact congrFun (hev χ _ (by rw [ey', ← Category.assoc, hχ]) k) b
  have hw := GlobalTheory.GradedWeight.exp_neg_grLB_φ ((h a).pull π₀ rfl) ((H a).pull π₀ rfl) (fl₀ a) i _ y' W hy'W (fun k => cc k PUnit.unit)
    (fun k _ => hW k) s fun k _ => hs k
  replace hw := hw.trans ((grSq_block _ i).trans (congrArg (grSq · i) hgram))
  obtain ⟨τ, b⟩ := a
  subst ha
  obtain ⟨d, hd, ed, en⟩ := grSq_of_tri hψ e3 hr hu hA (fun k => r _ k (cc k)) (fun k => by
    have := hsec k
    simp only [cond_true] at this
    rw [hu', hv, hev ψ _ (by rw [hg, Category.assoc])] at this
    exact this) (Gm (embOf O.κ.e σ)) e4 (fun g' hg' => hM g' fun k => (hg' k).trans (congrFun hu'' k).symm) i
  have hn (w) : rootEx O.S.Dw (DV.tauEmb D τ) (0 + i) w =
      if DV.tauEmb D τ = w.1 ∧ ((Fin.cast hr i : Fin _) : ℕ) = w.2 then 1 else 0 := by
    rw [Link.ApproxSec.rootEx_apply, zero_add, if_pos (lt_of_lt_of_eq i.2 O.S.p_eq.symm)]
    rfl
  have ep : prodPow t (rootEx O.S.Dw (DV.tauEmb D τ) (0 + i)) = t _ (Fin.cast hr i) :=
    prod_zpow_single (fun w => t w.1 w.2) _ _ _ hn
  have eg : (O.Φ.C c).genSq (Gm (embOf O.κ.e σ)) (rootEx O.S.Dw (DV.tauEmb D τ) (0 + i)) g =
      grSq ((Gm (embOf O.κ.e σ)).gram _ g _) (Fin.cast hr i) :=
    prod_zpow_single (fun w => grSq ((Gm (embOf O.κ.e σ)).gram _ g w.1) w.2) _ _ _ hn
  have ed' : (((r (τ, true) i (cc i))⁻¹ : G.functionFieldˣ) : G.functionField) *
      φ ((prodPow t (rootEx O.S.Dw (DV.tauEmb D τ) (0 + i)) : (O.var c).Fnˣ) : (O.var c).Fn) = ψ d := by
    rw [ep, ed, mul_comm]
    rfl
  refine ⟨⟨d, hd, ed'.symm⟩, hw.trans (en.trans ?_)⟩
  exact congrArg₂ (fun s t => ‖s‖ ^ 2 * t) ((ratVal_stalk z hχ d).symm.trans (congrArg (ratVal · z) ed'.symm)) eg.symm

end GlobalTheory.FlagCovWeight

end
