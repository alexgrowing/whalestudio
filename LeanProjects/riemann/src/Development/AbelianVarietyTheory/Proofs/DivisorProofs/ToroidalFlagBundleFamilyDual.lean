import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixUniqueUpToTriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleRankDualStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls.BaseChange

theorem isUnit_det_of_lieMat {dual : Bool} {r : ℕ} {K : Type} [CommRing K] {d : Matrix (Fin r) (Fin r) K}
    (h : IsUnit (lieMat dual d).det) : IsUnit d.det := by
  cases dual
  · exact h
  · have e : (lieMat true d).det = _ := Matrix.det_permute Fin.revPerm (Matrix.transpose d⁻¹)
    rw [e, Matrix.det_transpose] at h
    exact Matrix.isUnit_nonsing_inv_det_iff.1 (isUnit_of_mul_isUnit_right h)

theorem lieMat_tri (dual : Bool) {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (ψ : K →+* K')
    {d : Matrix (Fin r) (Fin r) K} (hd : IsUnit d.det) {C : Matrix (Fin r) (Fin r) K'} (hC : IsUnit C.det)
    (hC' : ∀ i j, i < j → C i j = 0) :
    ∃ T : Matrix (Fin r) (Fin r) K', IsUnit T.det ∧ (∀ i j, i < j → T i j = 0) ∧
      lieMat dual (C * d.map ψ) = T * (lieMat dual d).map ψ := by
  cases dual
  · exact ⟨C, hC, hC', rfl⟩
  · have := C.invertibleOfIsUnitDet hC
    have hb : C.BlockTriangular OrderDual.toDual := fun a b hab => hC' a b hab
    have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
    have hm : (d.map ψ)⁻¹ = d⁻¹.map ψ := Matrix.inv_eq_right_inv (by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hd, Matrix.map_one _ (map_zero ψ) (map_one ψ)])
    refine ⟨(Matrix.transpose C⁻¹).submatrix Fin.revPerm Fin.revPerm, ?_, fun i j hij => ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
      exact Matrix.isUnit_nonsing_inv_det C hC
    · exact hi (show OrderDual.toDual (Fin.rev i) < OrderDual.toDual (Fin.rev j) from Fin.rev_lt_rev.2 hij)
    · show (Matrix.transpose (C * d.map ψ)⁻¹).submatrix Fin.rev id = _
      rw [Matrix.mul_inv_rev, Matrix.transpose_mul, hm]
      exact Matrix.submatrix_mul _ _ _ Fin.rev _ Fin.revPerm.bijective

theorem sum_chain {K N : Type} [CommRing K] [AddCommMonoid N] [Module K N] {r : ℕ} {u v : Fin r → N} {w : N}
    (A : Matrix (Fin r) (Fin r) K) (b : Fin r → K) (h1 : ∀ i, v i = ∑ a, A i a • u a) (h2 : w = ∑ i, b i • v i) :
    w = ∑ a, (∑ i, b i * A i a) • u a := by
  simp only [h2, h1, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

attribute [local instance] Over.cartesianMonoidalCategory in
open MonoidalCategory CartesianMonoidalCategory MonObj in

theorem comb_chain {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {T : Scheme.{0}} (t : SAB H T) {K : Type} [CommRing K] (x : Sp K ⟶ T) {r : ℕ}
    {u v : Fin r → (Sp (DualNumber K) ⟶ t.G.left)} {w : Sp (DualNumber K) ⟶ t.G.left}
    (hu : ∀ i, IsTanAtG t x (u i)) (hv : ∀ i, IsTanAtG t x (v i)) (hw : IsTanAtG t x w)
    (A : Matrix (Fin r) (Fin r) K) (b : Fin r → K) (hA : ∀ i, IsCombAtG t x u (A i) (v i))
    (hb : IsCombAtG t x v b w) : IsCombAtG t x u (fun a => ∑ i, b i * A i a) w := by
  have h1 := fun i => (LieMet.isComb_iff (fun a => LieMet.tanOf (hu a)) _ (LieMet.tanOf (hv i))).1 (hA i)
  have h2 := (LieMet.isComb_iff (fun a => LieMet.tanOf (hv a)) _ (LieMet.tanOf hw)).1 hb
  refine (LieMet.isComb_iff (fun a => LieMet.tanOf (hu a)) _ (LieMet.tanOf hw)).2 ?_
  exact sum_chain (N := ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G) (u := fun a => LieMet.tanOf (hu a))
    (v := fun a => LieMet.tanOf (hv a)) A b h1 h2

theorem agreeAt_tri {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] (e : F ≃+* c.F) {r : ℕ}
    {τ : E →+* ℂ} (dual : Bool) (hr : r = Dw.mult τ) {Bs Bg Y : Scheme.{0}} {M : Bs.Modules} (hM : IsVB M r)
    (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z) (u : FrAssign Z M r jB) (π : Y ⟶ Bs)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (hu : IsLieFrames Z e jB πB M r τ dual u)
    {K : Type} [CommRing K] [IsLocalRing K] {y : Sp K ⟶ Y} {xb : Sp K ⟶ Bg} {χ : c.F →+* K}
    (g : EigFrame Z χ (xb ≫ πB ≫ genι Z)) {K' : Type} [CommRing K'] {ψ : K →+* K'}
    (g' : EigFrame Z (ψ.comp χ) (spMap ψ ≫ xb ≫ πB ≫ genι Z)) {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K'ˣ}
    (h1 : y ≫ π = xb ≫ jB) (h3 : xb ≫ πB ≫ genStr Z = spMap χ)
    (h : AgreeAt Z hM jB u π fl dual y xb (xb ≫ πB ≫ genι Z) fun i => g.v τ (Fin.cast hr i)) (ht : g.Tri ψ g' t) :
    AgreeAt Z hM jB u π fl dual (spMap ψ ≫ y) (spMap ψ ≫ xb) (spMap ψ ≫ xb ≫ πB ≫ genι Z)
      fun i => g'.v τ (Fin.cast hr i) := by
  subst hr
  obtain ⟨V, f, hV, hf⟩ := hM ((xb ≫ jB) (IsLocalRing.closedPoint K))
  have hx : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ V := fun w _ =>
    (IsLocalRing.specializes_closedPoint (R := K) w).mem_open ((xb ≫ jB) ⁻¹ᵁ V).isOpen hV
  have hx' : ⊤ ≤ ((spMap ψ ≫ xb) ≫ jB) ⁻¹ᵁ V := fun w _ => by
    rw [Category.assoc]; exact hx (Set.mem_univ (spMap ψ w))
  have h3' : (spMap ψ ≫ xb) ≫ πB ≫ genStr Z = spMap (ψ.comp χ) := by
    rw [Category.assoc, h3, ← Spec.map_comp]; rfl
  have key : ∀ {L : Type} [CommRing L] (z : Sp L ⟶ Bg) (ρ : c.F →+* L) (hz : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ V),
      z ≫ πB ≫ genStr Z = spMap ρ → IsEigBasis Z ρ (z ≫ πB ≫ genι Z) τ (u V f hf L z hz) := by
    intro L _ z ρ hz hρ
    have hb := hu.1 V f hf L z hz (ρ.comp e.toRingHom) (by
      rw [reassoc_of% hρ, ← Spec.map_comp]; rfl)
    have e1 : (ρ.comp e.toRingHom).comp e.symm.toRingHom = ρ := RingHom.ext fun a => by simp
    rwa [e1] at hb
  have hb := key xb χ hx h3
  have hb' := key (spMap ψ ≫ xb) (ψ.comp χ) hx' h3'
  choose d hd using fun i => (hb.2 (g.v τ i) ⟨g.tan τ i, g.eig τ i⟩).exists
  have hA : FlagMat hM π fl hf y (lieMat dual (Matrix.of d)) := h V f hf hx (Matrix.of d) hd
  have hdu := isUnit_det_of_lieMat hA.1
  have hA' := (GlobalTheory.T.flag_matrix_unique_up_to_triangular Bs Y M _ hM π fl V f hf K y (by rw [h1]; exact hx)).2.2 K' ψ _ hA
  choose C hC1 hC2 hC3 using ht.2.2 τ
  have hCu : IsUnit (Matrix.of C).det := by
    rw [Matrix.det_of_lowerTriangular (Matrix.of C) (fun a b hab => hC2 a b hab)]
    exact IsUnit.prod_univ_iff.2 fun i => by rw [Matrix.of_apply, hC1]; exact Units.isUnit _
  obtain ⟨T, hT, hT', eT⟩ := lieMat_tri dual ψ hdu hCu hC2
  obtain ⟨g₀, hg₀⟩ := g.exists_isMap ψ (φ' := ψ.comp χ) (x' := spMap ψ ≫ xb ≫ πB ≫ genι Z) rfl rfl
  have ex : (spMap ψ ≫ xb) ≫ πB ≫ genι Z = spMap ψ ≫ xb ≫ πB ≫ genι Z := Category.assoc _ _ _
  have := GlobalTheory.T.toroidal_flag_bundle_rank_dual E H Dw l Xo c Oz β Z F e _ τ dual Bs Bg Y M hM jB πB u π fl hu K' (spMap ψ ≫ y) (spMap ψ ≫ xb)
    (ψ.comp χ) (by rw [Category.assoc, h1, Category.assoc]) h3' (g'.v τ) V f hf hx' (Matrix.of C * (Matrix.of d).map ψ)
    (by
      rw [Matrix.det_mul]
      exact hCu.mul (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hdu.map ψ))
    (fun i => by
      rw [ex] at hb' ⊢
      refine comb_chain Z.t _ (v := g₀.v τ) (fun a => (hb'.1 a).1) (g₀.tan τ) (g'.tan τ i) ((Matrix.of d).map ψ) (C i)
        (fun k => ?_) ?_
      · rw [funext (hu.2.2 V f hf K K' ψ xb hx hx'), hg₀ τ k]
        exact GlobalTheory.GradedPieces.comb_map ψ rfl (hd k)
      · rw [funext (hg₀ τ)]; exact hC3 i)
    (by rw [eT]; exact hA'.mul hT hT')
  rw [ex] at this
  exact this

theorem bears_tri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (ι : Type) (rk : ι → ℕ) (emb : ι → (E →+* ℂ)) (dual : ι → Bool) (hr : ∀ a, rk a = Dw.mult (emb a)) (Bs Bg Y : Scheme.{0}) (M : ι → Bs.Modules) (hM : ∀ a, IsVB (M a) (rk a)) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z) (u : ∀ a, FrAssign Z (M a) (rk a) jB) (π : Y ⟶ Bs) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (rk a)), (∀ a, IsLieFrames Z e jB πB (M a) (rk a) (emb a) (dual a) (u a)) → ∀ (K : Type) [CommRing K] [IsLocalRing K] (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z χ x) (K' : Type) [CommRing K'] (ψ : K →+* K') (χ' : c.F →+* K') (x' : Sp K' ⟶ Z.X) (g' : EigFrame Z χ' x') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K'ˣ), Bears Z emb dual hr hM jB πB u π fl y xb g → g.Tri ψ g' t → Bears Z emb dual hr hM jB πB u π fl (spMap ψ ≫ y) (spMap ψ ≫ xb) g' := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e ι rk emb dual hr Bs Bg Y M hM jB πB u π fl hu K _ _ y xb χ x g K' _ ψ χ' x'
    g' t hB ht
  obtain ⟨h1, rfl, h3, h4⟩ := hB
  obtain rfl := ht.1
  obtain rfl := ht.2.1
  refine ⟨by rw [Category.assoc, h1, Category.assoc], (Category.assoc _ _ _).symm, ?_, fun a =>
    agreeAt_tri Z e (dual a) (hr a) (hM a) jB πB (u a) π (fl a) (hu a) g g' h1 h3 (h4 a) ht⟩
  rw [Category.assoc, h3, ← Spec.map_comp]; rfl

end GlobalTheory.FlagCls.BaseChange

end
