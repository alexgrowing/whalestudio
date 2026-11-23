import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixGradedQuotientStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

open ReciprocityTheory.ChartRestriction.G.PullbackSections MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem exists_comb_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {K : Type} [CommRing K] (x : Sp K ⟶ X) {r m : ℕ} (hr : r = m)
    {uu : Fin r → (Sp (DualNumber K) ⟶ t.G.left)} {v : Fin m → (Sp (DualNumber K) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t x (uu i)) (hv : ∀ i, IsTanAtG t x (v i)) {d : Matrix (Fin r) (Fin r) K}
    (hd : ∀ i, IsCombAtG t x uu (d i) (v (Fin.cast hr i))) (cf : Fin r → K) :
    ∃ w, IsCombAtG t x uu (Matrix.vecMul cf d) w ∧ IsCombAtG t x v (fun l => cf (Fin.cast hr.symm l)) w := by
  subst hr
  have h (i) : GlobalTheory.LieMet.tanOf (hv i) = ∑ b, d i b • GlobalTheory.LieMet.tanOf (hu b) :=
    (GlobalTheory.LieMet.isComb_iff (fun b => GlobalTheory.LieMet.tanOf (hu b)) _ (GlobalTheory.LieMet.tanOf (hv i))).1 (hd i)
  refine ⟨_, (GlobalTheory.LieMet.isComb_iff (fun b => GlobalTheory.LieMet.tanOf (hu b)) _ _).2 ?_,
    (GlobalTheory.LieMet.isComb_iff (fun b => GlobalTheory.LieMet.tanOf (hv b)) cf _).2 rfl⟩
  simp only [h, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

theorem sum_vecMul_lieMat {K : Type} [Field K] {r : ℕ} {d : Matrix (Fin r) (Fin r) K}
    (h : IsUnit (lieMat true d).det) (cf : Fin r → K) (l : Fin r) :
    ∑ b, Matrix.vecMul cf (lieMat true d) b * d l b = cf l.rev := by
  have hd : IsUnit d.det := by
    by_contra hd
    refine h.ne_zero (Matrix.det_eq_zero_of_row_eq_zero l fun j => ?_)
    simp [lieMat, Matrix.nonsing_inv_apply_not_isUnit _ hd]
  have e (m : Fin r) : ∑ b, d l b * d⁻¹ b m = if l = m then 1 else 0 := by
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hd, Matrix.one_apply]
  simp only [lieMat, cond_true, Matrix.vecMul, dotProduct, Finset.sum_mul, Matrix.submatrix_apply,
    Matrix.transpose_apply, id]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, mul_comm (d⁻¹ _ _), e]
  rw [Finset.sum_eq_single l.rev (fun m _ hm => by
    rw [if_neg (fun h => hm (by rw [h, Fin.rev_rev])), mul_zero]) (by simp), Fin.rev_rev, if_pos rfl, mul_one]

theorem flagAgree_of_bears : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Bs : Scheme.{0}) (E : D.what₂.Tau × Bool → Bs.Modules) (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB), (∀ a, IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a)) → ∀ (hr : ∀ a, rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)) (Y₀ : Scheme.{0}) (π₀ : Y₀ ⟶ Bs) (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a)) (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (jG : G ⟶ Bg) (φ : (O.var c).Fn →+* G.functionField) (χ : O.κ.c.F →+* G.functionField) (x : Sp G.functionField ⟶ O.s.T.Z.X) (g : EigFrame O.s.T.Z χ x), (O.Φ.C c).f0.IsMap φ g → Bears O.s.T.Z (embB D) (fun a => !a.2) hr hE jB πB u π₀ fl₀ (GlobalTheory.FlagCov.genPt G ≫ j) (GlobalTheory.FlagCov.genPt G ≫ jG) g → ∀ a, GlobalTheory.FlagCov.FlagAgree hE jB πB u π₀ fl₀ j φ jG a (hr a) := by
  intro D O c Bs E hE Bg jB πB u hu hr Y₀ π₀ fl₀ G _ j jG φ χ x g hg hb a
  obtain ⟨-, hx, hχ, hA⟩ := hb
  have hx' : x = GlobalTheory.FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z := hx.trans (Category.assoc _ _ _)
  have hv : (fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) l) = g.v (embB D a) :=
    funext fun l => (hg _ l).symm
  have key (V : Bs.Opens) (f : Fin (rkB D.what₂.Tau O.N O.j a) → Γ(E a, V)) (hf : IsFrame f)
      (hxV : ⊤ ≤ ((GlobalTheory.FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V) :
      ∃ d : Matrix (Fin (rkB D.what₂.Tau O.N O.j a)) (Fin (rkB D.what₂.Tau O.N O.j a)) G.functionField,
        (∀ i, IsTanAtG O.s.T.Z.t x (u a V f hf G.functionField (GlobalTheory.FlagCov.genPt G ≫ jG) hxV i)) ∧
        (∀ i, IsCombAtG O.s.T.Z.t x (u a V f hf G.functionField (GlobalTheory.FlagCov.genPt G ≫ jG) hxV) (d i)
          (g.v (embB D a) (Fin.cast (hr a) i))) ∧
        (∀ l d', IsCombAtG O.s.T.Z.t x (u a V f hf G.functionField (GlobalTheory.FlagCov.genPt G ≫ jG) hxV) d'
          (g.v (embB D a) l) → d' = d (Fin.cast (hr a).symm l)) ∧
        FlagMat (hE a) π₀ (fl₀ a) hf (GlobalTheory.FlagCov.genPt G ≫ j) (lieMat (!a.2) d) := by
    have h1 := (hu a).1 V f hf G.functionField (GlobalTheory.FlagCov.genPt G ≫ jG) hxV (χ.comp O.κ.e.toRingHom) (by
      rw [← Category.assoc πB, ← Category.assoc, hχ, ← Spec.map_comp]; rfl)
    have h2 : (χ.comp O.κ.e.toRingHom).comp O.κ.e.symm.toRingHom = χ :=
      RingHom.ext fun z => congrArg χ (O.κ.e.apply_symm_apply z)
    rw [h2, ← hx] at h1
    choose d hd hd' using fun l => h1.2 (g.v (embB D a) l) ⟨g.tan _ l, g.eig _ l⟩
    exact ⟨Matrix.of fun i => d (Fin.cast (hr a) i), fun i => (h1.1 i).1, fun i => hd _, fun l d' h => hd' l d' h,
      hA a V f hf hxV _ fun i => hd _⟩
  refine ⟨fun k V f hf W hWV t hy hxV => ?_, fun i ch V f hf W hW hWV t ht hy hxV => ?_⟩
  · obtain ⟨d, h1, h2, h3, h4⟩ := key V f hf hxV
    obtain ⟨cf, hc1, hc2⟩ := h4.2 k W hWV t hy
    intro aG uu v x'
    have haG : aG = Matrix.vecMul cf (lieMat (!a.2) d) := hc2
    have hv' : v = g.v (embB D a) := hv
    have hx'' : x' = x := hx'.symm
    rw [haG, hv', hx'']
    obtain ⟨τ, b⟩ := a
    cases b
    · intro l d' hd' hl
      rw [h3 l d' hd']
      refine (sum_vecMul_lieMat h4.1 cf _).trans (hc1 _ ?_)
      rw [Fin.val_rev, Fin.val_cast]; omega
    · obtain ⟨w, hw1, hw2⟩ := exists_comb_comb _ x (hr _) h1 (g.tan _) h2 cf
      exact ⟨w, _, hw1, hw2, fun l hl => hc1 _ hl⟩
  · obtain ⟨d, h1, h2, h3, h4⟩ := key V f hf hxV
    obtain ⟨cf, -, hc2⟩ := h4.2 i.succ W hWV t hy
    have hc1 := GlobalTheory.T.flag_matrix_graded_quotient _ _ _ _ (hE a) π₀ (fl₀ a) V f hf _ _ _ h4 i (ch PUnit.unit) W hW hWV t ht hy cf hc2
    intro aG uu v x'
    have haG : aG = Matrix.vecMul cf (lieMat (!a.2) d) := hc2
    have hv' : v = g.v (embB D a) := hv
    have hx'' : x' = x := hx'.symm
    rw [haG, hv', hx'']
    obtain ⟨τ, b⟩ := a
    cases b
    · intro l d' hd' hl
      rw [h3 l d' hd']
      refine (sum_vecMul_lieMat h4.1 cf _).trans_ne ?_
      rwa [show (Fin.cast (hr _).symm l).rev = i from Fin.ext (by rw [Fin.val_rev, Fin.val_cast]; omega)]
    · obtain ⟨w, hw1, hw2⟩ := exists_comb_comb _ x (hr _) h1 (g.tan _) h2 cf
      exact ⟨w, _, hw1, hw2, hc1⟩

end GlobalTheory.FlagCls

end
