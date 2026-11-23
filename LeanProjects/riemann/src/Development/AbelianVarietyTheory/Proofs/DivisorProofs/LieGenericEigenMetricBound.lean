import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleGenericFibreData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetQuotGramRe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarSectionsCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSqInverseTransposeRev
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCovDualNorm

open GlobalTheory.FlagCovDivCore GlobalTheory.GradedNorm

section Matrices

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

theorem grSq_castLE (K : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    grSq (K.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)) (Fin.last i) = grSq K i := rfl

theorem grSq_dual {M P A N : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) (hP : IsUnit P.det)
    (e : Aᵀ.submatrix Fin.revPerm id * P = N) (hN : N.BlockTriangular id) (hd : ∀ k, N k k ≠ 0) (i : Fin n) :
    grSq (HermFrame.chg A M⁻¹) i = ‖N i.rev i.rev‖ ^ 2 * (grSq (Pᴴ * M * P) i.rev)⁻¹ := by
  have hP' : IsUnit Pᴴ.det := by rw [det_conjTranspose]; exact hP.star
  have hQ : (Pᴴ * M * P).PosDef :=
    hM.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 hP))
  have h1 := GlobalTheory.grSq_inv_transpose_rev (Pᴴ * M * P)ᵀ hQ.transpose i.rev
  have h2 : (Pᴴ * M * P)ᵀ = (Pᴴ * M * P).map (starRingEnd ℂ) := by
    ext a b
    exact (hQ.1.apply b a).symm
  rw [Fin.rev_rev, transpose_nonsing_inv, transpose_transpose, h2, grSq_map_conj] at h1
  have h3 := grSq_tri ((Pᴴ * M * P)⁻¹.submatrix Fin.rev Fin.rev) (T := (N.submatrix Fin.rev Fin.rev)ᴴ)
    (fun a c h => by
      have : N c.rev a.rev = 0 := hN (Fin.rev_lt_rev.2 h)
      simp [this]) (fun a => by simpa using hd a.rev) i
  have h4 : N * (Pᴴ * M * P)⁻¹ * Nᴴ = (HermFrame.chg A M⁻¹).submatrix Fin.rev Fin.rev := by
    rw [← e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, conjTranspose_mul]
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hP, nonsing_inv_mul_cancel_left _ _ hP']
    ext a b
    simp [HermFrame.chg, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have h5 : (N.submatrix Fin.rev Fin.rev)ᴴᴴ * (Pᴴ * M * P)⁻¹.submatrix Fin.rev Fin.rev * (N.submatrix Fin.rev Fin.rev)ᴴ =
      HermFrame.chg A M⁻¹ := by
    have := congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X.submatrix Fin.revPerm Fin.revPerm) h4
    simp only [← submatrix_mul_equiv (e₂ := Fin.revPerm)] at this
    rw [conjTranspose_conjTranspose, conjTranspose_submatrix]
    refine Eq.trans this ?_
    ext a b
    simp
  rw [h5, h1] at h3
  rw [h3]
  simp

end Matrices

section Frames

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {R K : Type} [CommRing R] [Field K]

theorem norm_of_tri_dual {ψ : R →+* K} (hψ : Function.Injective ψ) {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {φ' : c.F →+* K}
    {x' : Sp K ⟶ Z.X} {f : EigFrame Z φ x} {v : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (hf : f.Tri ψ v t) {τ : E →+* ℂ} {m : ℕ} (hr : m = Dw.mult τ) {u : Fin m → (Sp (DualNumber R) ⟶ Z.t.G.left)}
    (hu : IsEigBasis Z φ x τ u) {A : Matrix (Fin m) (Fin m) R} (hA : IsUnit A.det) (ρ : Fin m → Kˣ)
    (h : ∀ (i : Fin m) (k : Fin (Dw.mult τ)) (d : Fin m → K),
      IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) d (v.v τ k) →
        ((k : ℕ) + i + 1 < m → ∑ b, ψ (A b i) * d b = 0) ∧
        ((k : ℕ) + i + 1 = m → ∑ b, ψ (A b i) * d b = ((ρ i)⁻¹ : Kˣ)))
    {σ : c.F →+* ℂ} (G : EigMet Z σ) {y : CxPts (genStr Z) σ} {g : EigFrame Z σ (y.1 ≫ genι Z)} {χ : R →+* ℂ}
    (hg : f.Tri χ g 1) (i : Fin m) :
    ∃ (k : EigFrame Z σ (y.1 ≫ genι Z)) (a : R), (∀ b, k.v τ (Fin.cast hr b) = spMap (dualMap χ) ≫ u b) ∧ IsUnit a ∧
      ψ a * t τ (Fin.cast hr i.rev) = ((ρ i)⁻¹ : Kˣ) ∧
      grSq (HermFrame.chg (A.map χ) ((G.gram y k τ)⁻¹.submatrix (Fin.cast hr) (Fin.cast hr))) i =
        ‖χ a‖ ^ 2 * (grSq (G.gram y g τ) (Fin.cast hr i.rev))⁻¹ := by
  subst hr
  obtain ⟨w, rfl⟩ := exists_frame_of_basis f hu
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨w', hw'⟩ := w.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨f₁, hf₁⟩ := f.exists_isMap χ hg.2.1 hg.1
  obtain ⟨w₁, hw₁⟩ := w.exists_isMap χ hg.2.1 hg.1
  obtain ⟨T1, T2⟩ := hf.co τ hf'
  obtain ⟨T3, T4⟩ := hg.co τ hf₁
  have hT : (f'.co v τ).BlockTriangular id := fun a i h => T1 a i h
  have hT₁ : (f₁.co g τ).BlockTriangular id := fun a i h => T3 a i h
  rw [← funext (hw' τ)] at h
  let A' : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R := A.transpose.submatrix Fin.revPerm id
  have hA' : IsUnit A'.det := by
    rw [Matrix.det_permute, Matrix.det_transpose]
    exact ((Equiv.Perm.sign _).isUnit.map (Int.castRingHom R)).mul hA
  have e : (A' * w.co f τ).map ψ * f'.co v τ = A'.map ψ * w'.co v τ := by
    rw [Matrix.map_mul, ← hw'.co τ hf' hf.1, Matrix.mul_assoc, EigFrame.co_mul]
  have e₁ : (A.map χ)ᵀ.submatrix Fin.revPerm id * w₁.co g τ = (A' * w.co f τ).map χ * f₁.co g τ := by
    rw [Matrix.map_mul, ← hw₁.co τ hf₁ hg.1, Matrix.mul_assoc, EigFrame.co_mul]
    rfl
  have hN : (A'.map ψ * w'.co v τ).BlockTriangular id := fun a k hk =>
    (h a.rev k _ (w'.co_spec v τ k)).1 (by have : (k : ℕ) < a := hk; have := a.2; rw [Fin.val_rev]; omega)
  have hS := tri_of_mul hT (fun i => T2 i ▸ Units.ne_zero _) hN e
  have hS₁ : ((A' * w.co f τ).map χ).BlockTriangular id := fun a b hab => by
    have : (A' * w.co f τ) a b = 0 := hψ ((hS hab).trans (map_zero _).symm)
    rw [Matrix.map_apply, this, map_zero]
  have hU := isUnit_diag hψ (S := A' * w.co f τ) (by rw [Matrix.det_mul]; exact hA'.mul (w.isUnit_det_co f τ)) hS
  have hd (k) : ((A' * w.co f τ).map χ * f₁.co g τ) k k = χ ((A' * w.co f τ) k k) := by
    rw [diag_mul hS₁ hT₁, T4]; exact mul_one _
  refine ⟨w₁, _, fun b => hw₁ τ b, hU i.rev, ?_, ?_⟩
  · have e2 := congrFun (congrFun e i.rev) i.rev
    rw [diag_mul hS hT, T2] at e2
    refine e2.trans ?_
    have e3 := (h i i.rev _ (w'.co_spec v τ i.rev)).2 (by have := i.2; rw [Fin.val_rev]; omega)
    refine Eq.trans ?_ e3
    simp only [Matrix.mul_apply, A', Matrix.map_apply, Matrix.submatrix_apply, Fin.revPerm_apply, Fin.rev_rev,
      Matrix.transpose_apply, id]
  · have := grSq_dual (G.pos y w₁ τ) (w₁.isUnit_det_co g τ) e₁ (hS₁.mul hT₁)
      (fun k => by rw [hd]; exact ((hU k).map χ).ne_zero) i
    rw [hd, ← G.change] at this
    exact this

variable {F : Type} [Field F] {e : F ≃+* c.F}

theorem exists_frame_pull (C : FlagCpt Z e) {G : Scheme.{0}} [IsIntegral G] (p : G ⟶ C.Y.X)
    (φ : C.Y.Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ p = spMap φ ≫ C.Y.X.fromSpecStalk (genericPoint C.Y.X)) (x : G)
    {xR : Sp (G.presheaf.stalk x) ⟶ Z.X} (hxR : xR = G.fromSpecStalk x ≫ p ≫ C.π ≫ genι Z)
    {xK : Sp G.functionField ⟶ Z.X} (hxK : xK = G.fromSpecStalk (genericPoint G) ≫ p ≫ C.π ≫ genι Z)
    {y : C.Y.X} (hy : y = p x) {φy : c.F →+* C.Y.X.presheaf.stalk y} {fy : EigFrame Z φy (stalkPt C.Y y ≫ C.π ≫ genι Z)}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (h1 : fy.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t)
    {χ₀ : C.Y.X.presheaf.stalk y →+* K} {χ : G.presheaf.stalk x →+* K}
    (hχ : spMap χ₀ ≫ stalkPt C.Y y = spMap χ ≫ G.fromSpecStalk x ≫ p) {φ' : c.F →+* K} {x' : Sp K ⟶ Z.X}
    {g : EigFrame Z φ' x'} {t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (h2 : fy.Tri χ₀ g t') :
    ∃ (ψ₀ : F →+* G.presheaf.stalk x) (f : EigFrame Z (ψ₀.comp e.symm.toRingHom) xR)
      (v : EigFrame Z (φ.comp (constF e C.Y)) xK),
      G.fromSpecStalk x ≫ p ≫ C.Y.str = spMap ψ₀ ∧ C.f0.IsMap φ v ∧
      f.Tri (algebraMap (G.presheaf.stalk x) G.functionField) v (fun τ i => Units.map φ.toMonoidHom (t τ i)) ∧
      f.Tri χ g t' := by
  subst hy
  have hs := comp_stalkMap p φ φs x
  have h0 : spMap (p.stalkMap x).hom ≫ stalkPt C.Y (p x) = G.fromSpecStalk x ≫ p :=
    Scheme.SpecMap_stalkMap_fromSpecStalk p
  have hc : χ₀ = χ.comp (p.stalkMap x).hom := EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk (p x))).1 (by
    refine hχ.trans ?_
    rw [← h0, spMap_trans, Category.assoc]; rfl))
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
  obtain ⟨f, hf⟩ := fy.exists_isMap (p.stalkMap x).hom e3 (x' := xR)
    (by rw [hxR, ← Category.assoc (spMap _), h0, Category.assoc])
  obtain ⟨v, hv⟩ := C.f0.exists_isMap φ rfl hK
  refine ⟨ψ₀, f, v, hψ₀, hv, ⟨by rw [hxK, hxR, ← Category.assoc (spMap _), spMap_fromSpecStalk], e2, fun τ i => ?_⟩,
    ⟨?_, ?_, fun τ i => ?_⟩⟩
  · obtain ⟨cf, c1, c2, c3⟩ := h1.2.2 τ i
    refine ⟨fun k => φ (cf k), congrArg φ c1, fun k hk => (congrArg φ (c2 k hk)).trans (map_zero _), ?_⟩
    have := GlobalTheory.GradedPieces.comb_map φ hK.symm c3
    simp only [GlobalTheory.GradedPieces.dual_comp] at this
    simp only [hv τ, hf τ, GlobalTheory.GradedPieces.dual_comp, hs]
    exact this
  · rw [h2.1, hxR, ← Category.assoc, hχ]
    simp only [Category.assoc]
  · rw [h2.2.1, e3, hc]; rfl
  · simp only [hf τ, GlobalTheory.GradedPieces.dual_comp, ← hc]
    exact h2.2.2 τ i

end Frames

theorem prod_zpow_neg_single {ι G : Type} [Fintype ι] [DivisionCommMonoid G] (f : ι → G) {n : ι → ℤ} (z : ι)
    (h1 : n z = -1) (h0 : ∀ w, w ≠ z → n w = 0) : ∏ w, f w ^ n w = (f z)⁻¹ := by
  rw [Finset.prod_eq_single z (fun w _ hw => by rw [h0 w hw, zpow_zero]) (by simp), h1, zpow_neg_one]

set_option maxHeartbeats 400000 in

theorem weight_dual : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Bs : Scheme.{0}) (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
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
    (a : D.what₂.Tau × Bool), a.2 = false → ∀ (i : Fin (rkB D.what₂.Tau O.N O.j a))
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
  intro D O c Bs q E h H Bg jB πB u hG Gm hM Y₀ _ π₀ fl₀ hfb G _ j πG pb _ _ φ φs jG r hc a ha i σ z y y' ch t g had
    ey ey' hx
  obtain ⟨τ, b₀⟩ := a
  obtain rfl : b₀ = false := ha
  let a : D.what₂.Tau × Bool := (τ, false)
  obtain ⟨hr, hMet⟩ := hM a
  obtain ⟨-, -, -, frB⟩ := hG
  obtain ⟨c1, c2, c3⟩ := hc
  obtain ⟨φy, fy, t1, t2⟩ := had
  have hqc := (h a).isVB.isQuasicoherent
  let x : G := under z
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
  let χ : G.presheaf.stalk x →+* ℂ := (Scheme.stalkClosedPointTo z.1).hom
  have hχ : spMap χ ≫ G.fromSpecStalk x = z.1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1
  have hg : FlagCov.genPt G = spMap ψ ≫ G.fromSpecStalk x := (spMap_fromSpecStalk G x).symm
  have hst {U : G.Opens} (hU : x ∈ U) : ⊤ ≤ G.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : G.fromSpecStalk x w ∈ Set.range (G.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := G.fromSpecStalk x w) this U.isOpen hU
  have hRW : ⊤ ≤ (G.fromSpecStalk x ≫ j) ⁻¹ᵁ W := hst (U := j ⁻¹ᵁ W) hxW
  have hRV : ⊤ ≤ ((G.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, c1]
    exact hst (U := (j ≫ π₀) ⁻¹ᵁ V) hV
  have hKW : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W := by
    rw [hg, Category.assoc]
    exact fun w _ => hRW (x := spMap ψ w) trivial
  have hKV' : ⊤ ≤ ((spMap ψ ≫ G.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc]
    exact fun w _ => hRV (x := spMap ψ w) trivial
  have hgj : FlagCov.genPt G ≫ jG = spMap ψ ≫ G.fromSpecStalk x ≫ jG := by rw [hg, Category.assoc]
  have hKV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V := hgj ▸ hKV'
  have hCV : ⊤ ≤ ((spMap χ ≫ G.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc]
    exact fun w _ => hRV (x := spMap χ w) trivial
  have ey₁ : y'.1 = spMap χ ≫ G.fromSpecStalk x ≫ j := by rw [ey', ← hχ, Category.assoc]
  have hCW : y' ∈ ptsIn _ _ W := by
    change ⊤ ≤ y'.1 ⁻¹ᵁ W
    rw [ey₁]
    exact fun w _ => hRW (x := spMap χ w) trivial
  obtain ⟨ψ₀, fR, v, e1, e2, e3, e4⟩ := exists_frame_pull (O.Φ.C c) πG φ φs x
    (xR := (G.fromSpecStalk x ≫ jG) ≫ πB ≫ genι O.s.T.Z)
    (by rw [Category.assoc, ← Category.assoc jG, c2, Category.assoc])
    (xK := FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (by rw [← Category.assoc jG, c2, Category.assoc]; rfl)
    (y := Var.base y) (by change y.1 _ = _; rw [ey]; rfl) t1 (χ := χ)
    (by rw [(O.Φ.C c).spMap_evStalk y, ey, ← Category.assoc, hχ]) t2
  have hu := (frB a).1 V f hf _ (G.fromSpecStalk x ≫ jG) hRV ψ₀ (by
    refine Eq.trans ?_ e1
    refine (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).symm.trans ?_))
    rw [c2]
    exact (Category.assoc _ _ _).trans (congrArg _ (O.Φ.C c).π_str))
  have hu' : u a V f hf G.functionField (FlagCov.genPt G ≫ jG) hKV =
      fun b => spMap (dualMap ψ) ≫ u a V f hf _ (G.fromSpecStalk x ≫ jG) hRV b := by
    have key : ∀ (y : Sp G.functionField ⟶ Bg) (hy : ⊤ ≤ (y ≫ jB) ⁻¹ᵁ V), y = spMap ψ ≫ G.fromSpecStalk x ≫ jG →
        u a V f hf G.functionField y hy = fun b => spMap (dualMap ψ) ≫ u a V f hf _ (G.fromSpecStalk x ≫ jG) hRV b := by
      rintro y hy rfl
      exact funext ((frB a).2.2 V f hf _ _ ψ _ hRV hy)
    exact key _ _ hgj
  let A₀ := ((hf.pullback π₀).basis hWV).toMatrix fun k => ((fl₀ a).ι k.succ).app W (s k)
  have hA₀ : IsUnit A₀.det := by
    have := ((hf.pullback π₀).detUnit hfr hWV le_rfl).isUnit
    simpa only [IsFrame.val_detUnit, Twist.resM_self, Module.Basis.det_apply] using this
  let A := A₀.map (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW)
  have hA : IsUnit A.det := by
    have := hA₀.map (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW)
    rwa [RingHom.map_det] at this
  have key {K : Type} [CommRing K] (ψ : G.presheaf.stalk x →+* K) : ∀ (y : Sp K ⟶ Y₀) (hy : ⊤ ≤ y ⁻¹ᵁ W),
      y = spMap ψ ≫ G.fromSpecStalk x ≫ j → ∀ z,
      TangentOrigin.evalPt y W hy z = ψ (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW z) := by
    rintro y hy rfl z
    exact TangentOrigin.evalPt_spMap_comp ψ _ W hRW hy z
  have hev (k) : (fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hKW
      (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k.succ).app W (s k)) b)) = fun b => ψ (A b k) :=
    funext fun b => key ψ _ _ (by rw [hg, Category.assoc]) _
  have hsec (k) := c3 a k hr (cc k) V f hf W (hW k) hWV (s k) (hs k) hKW hKV
  have hv : (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) k) = v.v (embB D a) := (funext (e2 _)).symm
  obtain ⟨k, d, hk, hd, ed, en⟩ := norm_of_tri_dual hψ e3 hr hu hA (fun k => r _ k (cc k)) (fun k k' d hd => by
      have := hsec k k' d (by rw [hu', hv]; exact hd)
      simpa only [fun b => congrFun (hev k) b] using this) (Gm (embOf O.κ.e σ)) (y := (O.Φ.C c).down y) e4 i

  have hx1 : rootEx O.S.Dw (DV.tauEmb D τ) (O.j + i) ⟨embB D a, Fin.cast hr i.rev⟩ = -1 ∧
      ∀ w, w ≠ ⟨embB D a, Fin.cast hr i.rev⟩ → rootEx O.S.Dw (DV.tauEmb D τ) (O.j + i) w = 0 := by
    have h1 := O.S.p_eq
    have h2 := O.S.rank_eq
    have h3 : (i : ℕ) < O.N - O.j := i.2
    have h4 : ((Fin.cast hr i.rev : Fin _) : ℕ) = O.N - O.j - (i + 1) := rfl
    refine ⟨?_, fun w hw => ?_⟩
    · rw [GlobalTheory.CovHt.Link.ApproxSec.rootEx_apply, if_neg (by omega), if_pos ⟨rfl, by simp only [h4]; omega⟩]
    · rw [GlobalTheory.CovHt.Link.ApproxSec.rootEx_apply, if_neg (by omega), if_neg, neg_zero]
      obtain ⟨w1, w2⟩ := w
      rintro ⟨rfl, h5⟩
      exact hw (congrArg (Sigma.mk _) (Fin.ext (by simp only [h4] at h5 ⊢; omega)))
  have hp := prod_zpow_neg_single (fun w : Letter O.S.Dw => t w.1 w.2) _ hx1.1 hx1.2
  have hq := prod_zpow_neg_single
    (fun w : Letter O.S.Dw => grSq ((Gm (embOf O.κ.e σ)).gram ((O.Φ.C c).down y) g w.1) w.2) _ hx1.1 hx1.2
  have hfun : (((r a i (cc i))⁻¹ : G.functionFieldˣ) : G.functionField) *
      φ ((prodPow t (rootEx O.S.Dw (DV.tauEmb D τ) (O.j + i)) : (O.var c).Fnˣ) : (O.var c).Fn) = ψ d := by
    rw [prodPow, hp, ← ed, Units.val_inv_eq_inv_val (t _ _), map_inv₀]
    exact mul_inv_cancel_right₀ ((map_ne_zero φ).2 (Units.ne_zero _)) _
  have hval : ratVal (ψ d) z = χ d :=
    (GlobalTheory.TrueGeo.Res.ratVal_eq_valAt z ⟨d, rfl⟩).trans (GlobalTheory.TrueGeo.Res.valAt_algebraMap (y := z.1) d)
  simp only [cond_false]
  rw [hfun, hval, FlagCpt.genSq, hq, ← en]
  refine ⟨⟨d, hd, rfl⟩, ?_⟩

  have hw := GlobalTheory.GradedWeight.exp_neg_grLB_φ ((h a).pull π₀ rfl) ((H a).pull π₀ rfl) (fl₀ a) i _ y' W hCW (fun k => cc k PUnit.unit)
    (fun l _ => hW l) s (fun l _ => hs l)
  refine hw.trans ((grSq_castLE ((((h a).pull π₀ rfl).met _).gram (fun l => ((fl₀ a).ι l.succ).app W (s l)) y') i).trans
    (congrArg (grSq · i) ?_))
  let cE : Chart (E a) (rkB D.what₂.Tau O.N O.j a) := ⟨V, f, hf⟩
  have hyV : y' ∈ ptsIn _ _ (π₀ ⁻¹ᵁ V) := le_trans hCW (Scheme.Hom.preimage_mono _ hWV)
  have hGm := hMet σ (Points.PtsOver.map π₀ rfl _ y') (spMap χ ≫ G.fromSpecStalk x ≫ jG) ((O.Φ.C c).down y)
    (by change _ = y'.1 ≫ π₀; rw [ey₁]; simp only [Category.assoc, c1])
    (by change y.1 ≫ _ = _; rw [ey, ← hχ]; simp only [Category.assoc, c2]) cE hCV k
    (fun b => (hk b).trans ((frB a).2.2 V f hf _ _ χ _ hRV hCV b).symm)
  rw [Met.gram_eq _ (cE.pull (h a).isVB π₀) hyV _ hCW]
  refine congrArg₂ HermFrame.chg ?_ ((((h a).met _).pull_G π₀ rfl cE hyV).trans hGm)
  ext b l
  rw [Matrix.of_apply, Chart.crd_eq _ _ le_rfl hWV hCW, Twist.resM_self, ev_eq hCW]
  exact key χ _ hCW ey₁ _

end GlobalTheory.FlagCovDualNorm

end
