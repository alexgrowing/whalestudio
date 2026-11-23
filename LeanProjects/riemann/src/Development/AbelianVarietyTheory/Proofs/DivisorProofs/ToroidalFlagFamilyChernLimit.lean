import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixUniqueUpToTriangularStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls.BorneUnique

theorem isUnit_diag {K : Type} [CommRing K] {r : ℕ} {S : Matrix (Fin r) (Fin r) K} (hS : IsUnit S.det)
    (hl : ∀ i j, i < j → S i j = 0) (i : Fin r) : IsUnit (S i i) := by
  have hb : S.BlockTriangular OrderDual.toDual := fun a b hab => hl a b hab
  rw [Matrix.det_of_lowerTriangular S hb] at hS
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => S j j) (Finset.mem_univ i)) hS

theorem exists_lower_of_lieMat {K : Type} [CommRing K] {r : ℕ} (dual : Bool) {d d' T : Matrix (Fin r) (Fin r) K}
    (hd : IsUnit (lieMat dual d).det) (hd' : IsUnit (lieMat dual d').det) (hT : IsUnit T.det)
    (hl : ∀ i j, i < j → T i j = 0) (h : lieMat dual d' = T * lieMat dual d) :
    ∃ S : Matrix (Fin r) (Fin r) K, IsUnit S.det ∧ (∀ i j, i < j → S i j = 0) ∧ d' = S * d := by
  cases dual
  · exact ⟨T, hT, hl, h⟩
  have hu : ∀ A : Matrix (Fin r) (Fin r) K, IsUnit (lieMat true A).det → IsUnit A.det := fun A hA => by
    have e : (lieMat true A).det = Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r)) * (Matrix.transpose A⁻¹).det :=
      Matrix.det_permute Fin.revPerm _
    rw [e, Matrix.det_transpose] at hA
    exact Matrix.isUnit_nonsing_inv_det_iff.1 (isUnit_of_mul_isUnit_right hA)
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin r) (Fin r) K, U = Matrix.transpose (T.submatrix Fin.rev Fin.rev) := ⟨_, rfl⟩
  have hUd : IsUnit U.det := by
    have e : (T.submatrix Fin.rev Fin.rev).det = T.det := Matrix.det_submatrix_equiv_self Fin.revPerm T
    rwa [hU, Matrix.det_transpose, e]
  have hb : U.BlockTriangular OrderDual.toDual := fun a b hab => by
    rw [hU]
    exact hl _ _ (Fin.rev_lt_rev.2 hab)
  have hm : d'⁻¹ = d⁻¹ * U := by
    ext a b
    have h1 := congrFun (congrFun h (Fin.rev b)) a
    simp only [lieMat, cond_true, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.rev_rev,
      id] at h1
    rw [h1, hU, Matrix.mul_apply]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_
    simp [mul_comm]
  have := U.invertibleOfIsUnitDet hUd
  refine ⟨U⁻¹, Matrix.isUnit_nonsing_inv_det _ hUd,
    fun i j hij => Matrix.blockTriangular_inv_of_blockTriangular hb hij, ?_⟩
  rw [← Matrix.nonsing_inv_nonsing_inv d' (hu _ hd'), hm, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv d (hu _ hd)]

attribute [local instance] Over.cartesianMonoidalCategory in
open MonoidalCategory CartesianMonoidalCategory MonObj in

theorem isCombAtG_of_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {T : Scheme.{0}} (t : SAB H T) {K : Type} [CommRing K] (x : Sp K ⟶ T) {r : ℕ}
    {u v : Fin r → (Sp (DualNumber K) ⟶ t.G.left)} {w : Sp (DualNumber K) ⟶ t.G.left}
    (hu : ∀ i, IsTanAtG t x (u i)) (hv : ∀ i, IsTanAtG t x (v i)) (hw : IsTanAtG t x w)
    (d : Matrix (Fin r) (Fin r) K) (b : Fin r → K) (hd : ∀ i, IsCombAtG t x u (d i) (v i))
    (hb : IsCombAtG t x u (fun a => ∑ i, b i * d i a) w) : IsCombAtG t x v b w := by
  have h1 := fun i => (LieMet.isComb_iff (fun a => LieMet.tanOf (hu a)) _ (LieMet.tanOf (hv i))).1 (hd i)
  have h2 := (LieMet.isComb_iff (fun a => LieMet.tanOf (hu a)) _ (LieMet.tanOf hw)).1 hb
  refine (LieMet.isComb_iff (fun a => LieMet.tanOf (hv a)) _ (LieMet.tanOf hw)).2 ?_
  rw [h2]
  simp only [h1, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem exists_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {T : Scheme.{0}} (t : SAB H T) {K : Type} [CommRing K] (x : Sp K ⟶ T) {r m : ℕ} (h : r = m)
    {u : Fin r → (Sp (DualNumber K) ⟶ t.G.left)} {v v' : Fin m → (Sp (DualNumber K) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t x (u i)) (hv : ∀ i, IsTanAtG t x (v i)) (hv' : ∀ i, IsTanAtG t x (v' i))
    {d S : Matrix (Fin r) (Fin r) K} (hS : IsUnit S.det) (hl : ∀ i j, i < j → S i j = 0)
    (hd : ∀ i, IsCombAtG t x u (d i) (v (Fin.cast h i)))
    (hd' : ∀ i, IsCombAtG t x u ((S * d) i) (v' (Fin.cast h i))) (i : Fin m) :
    ∃ cf : Fin m → K, IsUnit (cf i) ∧ (∀ k, i < k → cf k = 0) ∧ IsCombAtG t x v cf (v' i) := by
  subst h
  exact ⟨S i, isUnit_diag hS hl i, hl i, isCombAtG_of_mul t x hu hv (hv' i) d (S i) hd (hd' i)⟩

theorem tri_of_bears : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (ι : Type) (rk : ι → ℕ) (emb : ι → (E →+* ℂ)) (dual : ι → Bool) (hr : ∀ a, rk a = Dw.mult (emb a)) (Bs Bg Y : Scheme.{0}) (M : ι → Bs.Modules) (hM : ∀ a, IsVB (M a) (rk a)) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z) (u : ∀ a, FrAssign Z (M a) (rk a) jB) (π : Y ⟶ Bs) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (rk a)), (∀ a, IsLieFrames Z e jB πB (M a) (rk a) (emb a) (dual a) (u a)) → Function.Surjective emb → ∀ (K : Type) [CommRing K] [IsLocalRing K] (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g g' : EigFrame Z χ x), Bears Z emb dual hr hM jB πB u π fl y xb g → Bears Z emb dual hr hM jB πB u π fl y xb g' → ∃ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ, g.Tri (RingHom.id K) g' t := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e ι rk emb dual hr Bs Bg Y M hM jB πB u π fl hu hemb K _ _ y xb χ x g g'
    hg hg'
  obtain ⟨hy, rfl, hχ, hg⟩ := hg
  have key : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → K, IsUnit (cf i) ∧
      (∀ k, i < k → cf k = 0) ∧ IsCombAtG Z.t (xb ≫ πB ≫ genι Z) (g.v τ) cf (g'.v τ i) := by
    intro τ
    obtain ⟨a, rfl⟩ := hemb τ
    obtain ⟨V, f, hV, hf⟩ := hM a ((xb ≫ jB) (IsLocalRing.closedPoint K))
    have hx : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ V := fun p _ =>
      ((IsLocalRing.specializes_closedPoint p).map (xb ≫ jB).continuous).mem_open V.isOpen hV
    have hψ : xb ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (χ.comp e.toRingHom) := by
      rw [reassoc_of% hχ, ← Spec.map_comp]
      rfl
    have hb := (hu a).1 V f hf K xb hx _ hψ
    have hc : (χ.comp e.toRingHom).comp e.symm.toRingHom = χ := RingHom.ext fun z => by simp
    rw [hc] at hb
    choose d hd using fun i => (hb.2 (g.v (emb a) (Fin.cast (hr a) i)) ⟨g.tan _ _, g.eig _ _⟩).exists
    choose d' hd' using fun i => (hb.2 (g'.v (emb a) (Fin.cast (hr a) i)) ⟨g'.tan _ _, g'.eig _ _⟩).exists
    have h1 := hg a V f hf hx (Matrix.of d) hd
    have h2 := hg'.2.2.2 a V f hf hx (Matrix.of d') hd'
    obtain ⟨T, hT, hTl, hTe⟩ := (GlobalTheory.T.flag_matrix_unique_up_to_triangular Bs Y (M a) (rk a) (hM a) π (fl a) V f hf K y (hy ▸ hx)).2.1 _ _ h1 h2
    obtain ⟨S, hS, hSl, hSe⟩ := exists_lower_of_lieMat (dual a) h1.1 h2.1 hT hTl hTe
    exact exists_coeff Z.t _ (hr a) (fun i => (hb.1 i).1) (g.tan _) (g'.tan _) hS hSl (d := Matrix.of d) hd
      (hSe ▸ hd')
  choose cf h1 h2 h3 using key
  have e1 : spMap (Formalism.L2.Pj.dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [Formalism.L2.Pj.dualMap]
  have e2 : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
  refine ⟨fun τ i => (h1 τ i).unit, by rw [e2, Category.id_comp], rfl, fun τ i => ⟨cf τ i, rfl, h2 τ i, ?_⟩⟩
  simp only [e1, Category.id_comp]
  exact h3 τ i

end GlobalTheory.FlagCls.BorneUnique

end
