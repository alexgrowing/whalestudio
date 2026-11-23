import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCovDivCore

section Matrices

variable {R K : Type} [CommRing R] [Field K] {n : ℕ}

theorem isUnit_diag {ψ : R →+* K} (hψ : Function.Injective ψ) {S : Matrix (Fin n) (Fin n) R} (hS : IsUnit S.det)
    (h : (S.map ψ).BlockTriangular id) (i : Fin n) : IsUnit (S i i) := by
  rw [Matrix.det_of_upperTriangular (M := S) fun a b hab => hψ ((h hab).trans (map_zero _).symm)] at hS
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => S i i) (Finset.mem_univ i)) hS

theorem diag_mul {A B : Matrix (Fin n) (Fin n) K} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i :=
  Finset.sum_eq_single (s := Finset.univ) (f := fun a => A i a * B a i) i
    (fun a _ ha => ha.lt_or_gt.elim (fun h => by rw [hA h, zero_mul]) fun h => by rw [hB h, mul_zero]) (by simp)

theorem tri_of_mul {S T N : Matrix (Fin n) (Fin n) K} (hT : T.BlockTriangular id) (hd : ∀ i, T i i ≠ 0)
    (hN : N.BlockTriangular id) (e : S * T = N) : S.BlockTriangular id := by
  have hu : IsUnit T.det := by
    rw [Matrix.det_of_upperTriangular hT]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have := Matrix.invertibleOfIsUnitDet T hu
  have hi : T⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hT
  have : S = N * T⁻¹ := by rw [← e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  rw [this]
  exact hN.mul hi

end Matrices

section FlagFrame

open GlobalTheory.Twist (resM resM_resM app_resM)

theorem isFrame_of_lifts {X : Scheme.{0}} {M : X.Modules} {N : ℕ} (fl : Vert.Flag M N) {W : X.Opens}
    (t : ∀ k : Fin N, Γ(fl.F k.succ, W)) (ht : ∀ k, VB.IsFrame fun _ : Fin 1 => (fl.π k).app W (t k)) :
    VB.IsFrame fun k => (fl.ι k.succ).app W (t k) := by
  have key (l : Fin (N + 1)) : ∃ s : Fin l → Γ(fl.F l, W), VB.IsFrame s ∧
      ∀ j, (fl.ι l).app W (s j) = (fl.ι (Fin.castLE l.is_le j).succ).app W (t (Fin.castLE l.is_le j)) := by
    induction l using Fin.induction with
    | zero =>
      have z := VB.isVB_zero_iff.1 (fl.isVB 0)
      refine ⟨_, (VB.isFrame_freeFrame X (Fin 0)).map_iso ((VB.isVB_zero_iff.1
        (VB.isVB_freeModule_fin X 0)).iso z).hom |>.res le_top, fun j => j.elim0⟩
    | succ i ih =>
      obtain ⟨s, hs, es⟩ := ih
      have h := (VBExt.isFrame_sumElim (S := .mk (fl.step i) (Limits.cokernel.π _) (Limits.cokernel.condition _))
        { exact := ShortComplex.exact_cokernel _ } (t := fun _ : Fin 1 => t i) hs (ht i)).comp_equiv
        finSumFinEquiv.symm
      refine ⟨_, h, fun j => ?_⟩
      refine Fin.addCases (m := i) (n := 1) (fun j => ?_) (fun j => ?_) j
      · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
        refine Eq.trans ?_ (es j)
        rw [← fl.step_ι i]
        rfl
      · obtain rfl : j = 0 := Subsingleton.elim _ _
        exact congrArg (fun z => (fl.ι i.succ).app W (Sum.elim (fun j => (fl.step i).app W (s j)) (fun _ => t i) z))
          (finSumFinEquiv_symm_apply_natAdd (m := i) (n := 1) 0)
  obtain ⟨s, hs, es⟩ := key (Fin.last N)
  have := hs.map_iso (fl.ι (Fin.last N))
  rw [funext es] at this
  exact this

theorem exists_lifts_isFrame {X : Scheme.{0}} {M : X.Modules} {N : ℕ} (fl : Vert.Flag M N)
    (c : ∀ k, Chart (fl.gr k) 1) {y : X} (hy : ∀ k, y ∈ (c k).U) {U : X.Opens} (hU : y ∈ U) :
    ∃ (W : X.Opens) (_ : W ≤ U) (hW : ∀ k, W ≤ (c k).U) (t : ∀ k : Fin N, Γ(fl.F k.succ, W)), y ∈ W ∧
      (∀ k, (fl.π k).app W (t k) = resM _ (hW k) ((c k).e 0)) ∧ VB.IsFrame fun k => (fl.ι k.succ).app W (t k) := by
  choose W hW hyW t ht using fun k => VBExt.exists_lifts (fl.π k) (c k).e (hy k)
  have hV (k : Fin N) : U ⊓ Finset.univ.inf W ≤ W k :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ k))
  have e (k : Fin N) : (fl.π k).app _ (resM _ (hV k) (t k 0)) = resM _ ((hV k).trans (hW k)) ((c k).e 0) := by
    rw [app_resM, ht, resM_resM]
  refine ⟨U ⊓ Finset.univ.inf W, inf_le_left, fun k => (hV k).trans (hW k), fun k => resM _ (hV k) (t k 0), ⟨hU, by
    rw [TopologicalSpace.Opens.coe_finset_inf]; simpa using hyW⟩, e, isFrame_of_lifts fl _ fun k => ?_⟩
  have := (c k).isFrame.res ((hV k).trans (hW k))
  rw [e]
  convert this using 3 with i
  exact congrArg _ (Subsingleton.elim _ _)

end FlagFrame

section Frames

open GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {R K : Type} [CommRing R] [Field K]

theorem exists_frame_of_basis {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) {τ : E →+* ℂ}
    {u : Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) :
    ∃ g : EigFrame Z φ x, g.v τ = u := by
  refine ⟨⟨Function.update f.v τ u, fun τ' i => ?_, fun τ' i => ?_, fun τ' => ?_⟩, Function.update_self τ u f.v⟩ <;>
    by_cases h : τ' = τ
  · subst h; rw [Function.update_self]; exact (hu.1 i).1
  · rw [Function.update_of_ne h]; exact f.tan τ' i
  · subst h; rw [Function.update_self]; exact (hu.1 i).2
  · rw [Function.update_of_ne h]; exact f.eig τ' i
  · subst h; rw [Function.update_self]; exact fun w h1 h2 => hu.2 w ⟨h1, h2⟩
  · rw [Function.update_of_ne h]; exact f.basis τ'

theorem comb_unique {X : Scheme.{0}} {t : SAB H X} {x : Sp R ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    {a : Fin m → R} {w w' : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x v a w) (h' : IsCombAtG t x v a w') :
    w = w' := by
  obtain ⟨p, hp, e⟩ := h
  obtain ⟨p', hp', e'⟩ := h'
  have hpp : p = p' := funext fun i => Over.OverMorphism.ext (by rw [hp i, hp' i])
  rw [hpp] at e
  exact e.symm.trans e'

theorem co_mulVec {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f g k : EigFrame Z φ x) (τ : E →+* ℂ)
    {a b : Fin (Dw.mult τ) → R} {w : Sp (DualNumber R) ⟶ Z.t.G.left} (ha : IsCombAtG Z.t x (g.v τ) a w)
    (hb : IsCombAtG Z.t x (k.v τ) b w) : (f.co g τ).mulVec a = (f.co k τ).mulVec b := by
  have h1 (g : EigFrame Z φ x) (a : Fin (Dw.mult τ) → R) :
      IsCombAtG Z.t x (g.v τ) a (tv (∑ i, a i • g.vec τ i)).left :=
    (LieMet.isComb_iff (g.vec τ) a (∑ i, a i • g.vec τ i)).2 rfl
  have h2 : ∑ i, a i • g.vec τ i = ∑ i, b i • k.vec τ i :=
    tan_ext ((comb_unique (h1 g a) ha).trans (comb_unique hb (h1 k b)))
  have e (g : EigFrame Z φ x) (a : Fin (Dw.mult τ) → R) :
      ∑ i, a i • g.vec τ i = ∑ d, (f.co g τ).mulVec a d • f.vec τ d := by
    simp only [f.vec_eq g τ, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul, mul_comm]
    exact Finset.sum_comm
  rw [e g a, e k b] at h2
  exact funext (Fintype.linearIndependent_iffₛ.1 (f.linearIndependent_vec τ) _ _ h2)

variable {ψ : R →+* K} (hψ : Function.Injective ψ) {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {φ' : c.F →+* K} {x' : Sp K ⟶ Z.X}
  {f : EigFrame Z φ x} {v : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (hf : f.Tri ψ v t)
  {τ : E →+* ℂ} {m : ℕ} (hr : m = Dw.mult τ) {u : Fin m → (Sp (DualNumber R) ⟶ Z.t.G.left)}
  (hu : IsEigBasis Z φ x τ u) {A : Matrix (Fin m) (Fin m) R} (hA : IsUnit A.det) (ρ : Fin m → Kˣ)

include hψ hf hu hA

theorem unit_of_tri
    (h : ∀ i, ∃ (w : Sp (DualNumber K) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → K),
      IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) (fun b => ψ (A b i)) w ∧ IsCombAtG Z.t x' (v.v τ) cf w ∧
        cf (Fin.cast hr i) = ((ρ i)⁻¹ : Kˣ) ∧ ∀ k, Fin.cast hr i < k → cf k = 0) (i : Fin m) :
    ∃ a : R, IsUnit a ∧ ψ a = t τ (Fin.cast hr i) * ((ρ i)⁻¹ : Kˣ) := by
  subst hr
  obtain ⟨g, rfl⟩ := exists_frame_of_basis f hu
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨g', hg'⟩ := g.exists_isMap ψ hf.2.1 hf.1
  choose w cf h1 h2 h3 h4 using h
  obtain ⟨T1, T2⟩ := hf.co τ hf'
  have hC : (Matrix.of fun a i => cf i a).BlockTriangular id := fun a i h => h4 i a h
  have hT : (f'.co v τ).BlockTriangular id := fun a i h => T1 a i h
  have e : (f.co g τ * A).map ψ = f'.co v τ * Matrix.of fun a i => cf i a := by
    rw [Matrix.map_mul, ← hf'.co τ hg' hf.1]
    ext a i
    rw [← funext (hg' τ)] at h1
    exact congrFun (co_mulVec f' g' v τ (h1 i) (h2 i)) a
  refine ⟨_, isUnit_diag hψ (S := f.co g τ * A) (by rw [Matrix.det_mul]; exact (f.isUnit_det_co g τ).mul hA)
    (e ▸ hT.mul hC) i, ?_⟩
  refine (congrFun (congrFun e i) i).trans ((diag_mul hT hC i).trans ?_)
  rw [T2]
  exact congrArg _ (h3 i)

theorem unit_of_tri_dual
    (h : ∀ (i : Fin m) (k : Fin (Dw.mult τ)) (d : Fin m → K),
      IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) d (v.v τ k) →
        ((k : ℕ) + i + 1 < m → ∑ b, ψ (A b i) * d b = 0) ∧
        ((k : ℕ) + i + 1 = m → ∑ b, ψ (A b i) * d b = ((ρ i)⁻¹ : Kˣ))) (i : Fin m) :
    ∃ a : R, IsUnit a ∧ ψ a * t τ (Fin.cast hr i.rev) = ((ρ i)⁻¹ : Kˣ) := by
  subst hr
  obtain ⟨g, rfl⟩ := exists_frame_of_basis f hu
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨g', hg'⟩ := g.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨T1, T2⟩ := hf.co τ hf'
  have hT : (f'.co v τ).BlockTriangular id := fun a i h => T1 a i h
  rw [← funext (hg' τ)] at h
  let A' : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R := A.transpose.submatrix Fin.revPerm id
  have hA' : IsUnit A'.det := by
    rw [Matrix.det_permute, Matrix.det_transpose]
    exact ((Equiv.Perm.sign _).isUnit.map (Int.castRingHom R)).mul hA
  have e : (A' * g.co f τ).map ψ * f'.co v τ = A'.map ψ * g'.co v τ := by
    rw [Matrix.map_mul, ← hg'.co τ hf' hf.1, Matrix.mul_assoc, EigFrame.co_mul]
  have hN : (A'.map ψ * g'.co v τ).BlockTriangular id := fun a k hk =>
    (h a.rev k _ (g'.co_spec v τ k)).1 (by have : (k : ℕ) < a := hk; have := a.2; rw [Fin.val_rev]; omega)
  have hS := tri_of_mul hT (fun i => T2 i ▸ Units.ne_zero _) hN e
  refine ⟨_, isUnit_diag hψ (S := A' * g.co f τ) (by rw [Matrix.det_mul]; exact hA'.mul (g.isUnit_det_co f τ))
    hS i.rev, ?_⟩
  have e2 := congrFun (congrFun e i.rev) i.rev
  rw [diag_mul hS hT, T2] at e2
  refine e2.trans ?_
  have e3 := (h i i.rev _ (g'.co_spec v τ i.rev)).2 (by have := i.2; rw [Fin.val_rev]; omega)
  refine Eq.trans ?_ e3
  simp only [Matrix.mul_apply, A', Matrix.map_apply, Matrix.submatrix_apply, Fin.revPerm_apply, Fin.rev_rev,
    Matrix.transpose_apply, id]

end Frames

section Stalk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem spMap_trans {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_fromSpecStalk (G : Scheme.{0}) [IsIntegral G] (x : G) :
    spMap (algebraMap (G.presheaf.stalk x) G.functionField) ≫ G.fromSpecStalk x = G.fromSpecStalk (genericPoint G) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

theorem comp_stalkMap {G Y : Scheme.{0}} [IsIntegral G] [IsIntegral Y] (p : G ⟶ Y) (φ : Y.functionField →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ p = spMap φ ≫ Y.fromSpecStalk (genericPoint Y)) (x : G) :
    (algebraMap (G.presheaf.stalk x) G.functionField).comp (p.stalkMap x).hom =
      φ.comp (algebraMap (Y.presheaf.stalk (p x)) Y.functionField) := by
  refine EigLoc.spMap_inj ((cancel_mono (Y.fromSpecStalk (p x))).1 ?_)
  have h1 : spMap (p.stalkMap x).hom ≫ Y.fromSpecStalk (p x) = G.fromSpecStalk x ≫ p :=
    Scheme.SpecMap_stalkMap_fromSpecStalk p
  rw [spMap_trans, spMap_trans, Category.assoc, Category.assoc, h1, ← Category.assoc,
    spMap_fromSpecStalk, spMap_fromSpecStalk, φs]

theorem exists_frame (C : FlagCpt Z e) {G : Scheme.{0}} [IsIntegral G] (p : G ⟶ C.Y.X) (φ : C.Y.Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ p = spMap φ ≫ C.Y.X.fromSpecStalk (genericPoint C.Y.X)) (x : G)
    {xR : Sp (G.presheaf.stalk x) ⟶ Z.X} (hxR : xR = G.fromSpecStalk x ≫ p ≫ C.π ≫ genι Z)
    {xK : Sp G.functionField ⟶ Z.X} (hxK : xK = G.fromSpecStalk (genericPoint G) ≫ p ≫ C.π ≫ genι Z) :
    ∃ (ψ₀ : F →+* G.presheaf.stalk x) (f : EigFrame Z (ψ₀.comp e.symm.toRingHom) xR)
      (v : EigFrame Z (φ.comp (constF e C.Y)) xK) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ),
      G.fromSpecStalk x ≫ p ≫ C.Y.str = spMap ψ₀ ∧ C.f0.IsMap φ v ∧
      f.Tri (algebraMap (G.presheaf.stalk x) G.functionField) v (fun τ i => Units.map φ.toMonoidHom (t τ i)) ∧
      ∀ τ i, (C.gr τ i).IsEqn (p x) (t τ i) := by
  obtain ⟨φy, fy, t, h1, h2⟩ := C.gr_spec (p x)
  have hs := comp_stalkMap p φ φs x
  have h0 : spMap (p.stalkMap x).hom ≫ stalkPt C.Y (p x) = G.fromSpecStalk x ≫ p :=
    Scheme.SpecMap_stalkMap_fromSpecStalk p
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
  obtain ⟨f, hf⟩ := fy.exists_isMap (p.stalkMap x).hom e3 (x' := xR) (by rw [hxR, ← Category.assoc (spMap _), h0, Category.assoc])
  obtain ⟨v, hv⟩ := C.f0.exists_isMap φ rfl hK
  refine ⟨ψ₀, f, v, t, hψ₀, hv, ⟨by rw [hxK, hxR, ← Category.assoc (spMap _), spMap_fromSpecStalk], e2, fun τ i => ?_⟩, h2⟩
  obtain ⟨cf, c1, c2, c3⟩ := h1.2.2 τ i
  refine ⟨fun k => φ (cf k), congrArg φ c1, fun k hk => (congrArg φ (c2 k hk)).trans (map_zero _), ?_⟩
  have := GlobalTheory.GradedPieces.comb_map φ hK.symm c3
  simp only [GlobalTheory.GradedPieces.dual_comp] at this
  simp only [hv τ, hf τ, GlobalTheory.GradedPieces.dual_comp, hs]
  exact this

end Stalk

theorem unitAt_frameSec : ∀ (D : D7) (O : Setup D) (hO : O.Core) (B : ℝ) (hB : 2 ≤ B) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (hL : GlobalTheory.FlagCov.LieWit O B R c q E h jB πB u Gm)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X)
    (pb : IsPullback j (πG ≫ (O.var c).str) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πG] [Surjective πG] (φ : (O.var c).Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ)
    (hc : GlobalTheory.FlagCov.FlagCover (fun a => (h a).isVB) jB πB u π₀ fl₀ j πG φ jG r)
    (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a)) (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
    ∀ ch, ∀ x ∈ (((fl₀ a).root i).pull j).U ch, ∀ t : (O.var c).Fnˣ,
      ((O.Φ.C c).gr (embB D a) (Fin.cast hr (cond a.2 i i.rev))).IsEqn (πG x) t →
      UnitAt x (φ (t : (O.var c).Fn) ^ (cond a.2 (-1 : ℤ) 1) * (r a i ch : G.functionField)) := by
  intro D O hO B hB R hR c Bs _ q arq nBs E h H Bg jB πB u Gm hL Y₀ _ π₀ fl₀ hfb ar₀ n₀ G _ j πG pb _ _ φ φs jG r hc
    a i hr ch x hx t ht
  obtain ⟨-, -, -, frB, -⟩ := hL
  obtain ⟨c1, c2, c3⟩ := hc
  have hqc := (h a).isVB.isQuasicoherent

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
  obtain ⟨ψ₀, fR, v, tY, e1, e2, e3, e4⟩ := exists_frame (O.Φ.C c) πG φ φs x
    (xR := (G.fromSpecStalk x ≫ jG) ≫ πB ≫ genι O.s.T.Z)
    (by rw [Category.assoc, ← Category.assoc jG, c2, Category.assoc])
    (xK := FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (by rw [← Category.assoc jG, c2, Category.assoc]; rfl)
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
  have hev (k) : (fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hKW
      (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k.succ).app W (s k)) b)) = fun b => ψ (A b k) := by
    have key : ∀ (y : Sp G.functionField ⟶ Y₀) (hy : ⊤ ≤ y ⁻¹ᵁ W), y = spMap ψ ≫ G.fromSpecStalk x ≫ j → ∀ z,
        TangentOrigin.evalPt y W hy z = ψ (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW z) := by
      rintro y hy rfl z
      exact TangentOrigin.evalPt_spMap_comp ψ _ W hRW hy z
    exact funext fun b => key _ _ (by rw [hg, Category.assoc]) _
  have hsec (k) := c3 a k hr (cc k) V f hf W (hW k) hWV (s k) (hs k) hKW hKV
  have hv : (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) k) = v.v (embB D a) := (funext (e2 _)).symm
  obtain ⟨b, hb, eb⟩ := (e4 _ _).iff_unitAt.1 ht
  have hb' : UnitAt x (φ (t : (O.var c).Fn) / φ (tY (embB D a) (Fin.cast hr (cond a.2 i i.rev)))) :=
    ⟨_, hb.map (πG.stalkMap x).hom, (RingHom.congr_fun (comp_stalkMap πG φ φs x) b).trans
      ((congrArg φ eb).trans (map_div₀ φ _ _))⟩
  have ht0 : φ (t : (O.var c).Fn) ≠ 0 := (map_ne_zero φ).2 t.ne_zero
  have ht1 (τ k) : φ (tY τ k : (O.var c).Fn) ≠ 0 := (map_ne_zero φ).2 (tY τ k).ne_zero
  have hr0 : (r a i (cc i) : G.functionField) ≠ 0 := Units.ne_zero _
  obtain ⟨τ, _ | _⟩ := a
  · obtain ⟨d, hd, ed⟩ := unit_of_tri_dual hψ e3 hr hu hA (fun k => r _ k (cc k)) (fun k k' d hd => by
      have := hsec k k' d (by rw [hu', hv]; exact hd)
      simpa only [fun b => congrFun (hev k) b] using this) i
    have h1 : UnitAt x (ψ d) := ⟨d, hd, rfl⟩
    convert hb'.mul h1.inv using 1
    have ed' : ψ d * φ (tY (embB D (τ, false)) (Fin.cast hr i.rev)) = (r (τ, false) i (cc i) : G.functionField)⁻¹ :=
      ed.trans (Units.val_inv_eq_inv_val _)
    simp only [cond_false, zpow_one]
    rw [div_eq_mul_inv, mul_assoc, ← mul_inv, mul_comm _ (ψ d), ed', inv_inv]
  · obtain ⟨d, hd, ed⟩ := unit_of_tri hψ e3 hr hu hA (fun k => r _ k (cc k)) (fun k => by
      have := hsec k
      simp only [cond_true] at this
      rw [hu', hv, hev] at this
      exact this) i
    have h1 : UnitAt x (ψ d) := ⟨d, hd, rfl⟩
    convert hb'.inv.mul h1.inv using 1
    have ed' : ψ d = φ (tY (embB D (τ, true)) (Fin.cast hr i)) * (r (τ, true) i (cc i) : G.functionField)⁻¹ :=
      ed.trans (congrArg _ (Units.val_inv_eq_inv_val _))
    have := ht1 (embB D (τ, true)) (Fin.cast hr i)
    simp only [cond_true, zpow_neg, zpow_one]
    rw [ed']
    field_simp

end GlobalTheory.FlagCovDivCore

end
