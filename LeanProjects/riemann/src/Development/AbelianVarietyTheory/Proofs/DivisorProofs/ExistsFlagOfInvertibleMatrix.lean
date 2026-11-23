import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (freeModule)

namespace GlobalTheory.FlagCls

section

variable {X : Scheme.{0}} {N : X.Modules} {r : ℕ}

theorem isFrame_sum_smul_of_isUnit_det {U : X.Opens} {g : Fin r → Γ(N, U)} (hg : VB.IsFrame g)
    (A : Matrix (Fin r) (Fin r) Γ(X, U)) (hA : IsUnit A.det) : VB.IsFrame fun i => ∑ b, A i b • g b := by
  refine isFrame_iff.2 fun W h => ?_
  have key : IsUnit ((hg.basis h).det fun i => resM N h (∑ b, A i b • g b)) := by
    have e : (hg.basis h).toMatrix (fun i => resM N h (∑ b, A i b • g b)) =
        ((resG X h).mapMatrix A).transpose := by
      ext b i
      simp only [Module.Basis.toMatrix_apply, map_sum, resM_smul, ← hg.basis_apply h]
      rw [← map_sum, Module.Basis.repr_sum_self]
      rfl
    rw [Module.Basis.det_apply, e, Matrix.det_transpose, ← RingHom.map_det]
    exact hA.map _
  have := (Module.Basis.is_basis_iff_det (hg.basis h)).2 key
  exact ⟨this.1, this.2.ge⟩

theorem exists_flag_of_isFrame_top {s : Fin r → Γ(N, ⊤)} (hs : VB.IsFrame s) :
    ∃ fl : Vert.Flag N r, ∀ (k : Fin (r + 1)) (t : Γ(fl.F k, ⊤)) (l : Fin r), (k : ℕ) ≤ l →
      (hs.basis le_rfl).repr ((fl.ι k).app ⊤ t) l = 0 := by
  refine ⟨(FlagSurj.freeFlag X r).ofIso ((isFrame_freeFrame X (Fin r)).iso hs), fun k t l hl => ?_⟩
  have hk : (k : ℕ) ≤ r := Nat.lt_succ_iff.mp k.2
  have h1 (i : Fin k) : (((FlagSurj.freeFlag X r).ofIso ((isFrame_freeFrame X (Fin r)).iso hs)).ι k).app ⊤
      (freeFrame X (Fin k) i) = (hs.basis le_rfl) (Fin.castLE hk i) := by
    rw [IsFrame.basis_apply, resM_self, ← (isFrame_freeFrame X (Fin r)).iso_hom_app hs]
    refine (QCoh.app_app _ _ _ _).symm.trans (congrArg _ ?_)
    refine (QCoh.app_app _ _ _ _).trans ?_
    erw [SheafOfModules.ιFree_freeMap]
    rfl
  revert t h1
  generalize hφ : ((FlagSurj.freeFlag X r).ofIso ((isFrame_freeFrame X (Fin r)).iso hs)).ι k = φ
  clear hφ
  revert φ
  change ∀ (φ : freeModule X (Fin k) ⟶ N) (t : Γ(freeModule X (Fin k), ⊤)), (∀ i : Fin k, φ.app ⊤
    (freeFrame X (Fin k) i) = (hs.basis le_rfl) (Fin.castLE hk i)) → (hs.basis le_rfl).repr (φ.app ⊤ t) l = 0
  intro φ t h1
  obtain ⟨a, rfl⟩ := (isFrame_freeFrame X (Fin k) ⊤ le_rfl).2 t
  rw [Fintype.linearCombination_apply, map_sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, resM_self, h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_of_ne, smul_zero]
  rintro rfl
  have := i.2
  simp at hl
  omega

end

theorem exists_flag_flagMat : ∀ (B : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [Field K] (x : Sp K ⟶ B), ⊤ ≤ x ⁻¹ᵁ V → ∀ A : Matrix (Fin r) (Fin r) K, IsUnit A.det → ∃ fl' : Vert.Flag ((Scheme.Modules.pullback x).obj M) r, FlagMat hM x fl' hf (𝟙 (Sp K)) A := by
  intro B M r hM V f hf K _ x hx A hA
  have := hM.isQuasicoherent
  let c : K →+* Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hs := isFrame_sum_smul_of_isUnit_det ((hf.pullback x).res hx) (c.mapMatrix A)
    (by rw [← RingHom.map_det]; exact hA.map _)
  obtain ⟨fl, hfl⟩ := exists_flag_of_isFrame_top hs
  refine ⟨fl, hA, fun k W hWV t hy => ?_⟩
  obtain rfl : W = ⊤ := top_le_iff.1 hy
  have hc (a : K) : TangentOrigin.evalPt (𝟙 (Sp K)) ⊤ hy (c a) = a := by
    have e : Scheme.Hom.appLE (𝟙 (Sp K)) ⊤ ⊤ hy = 𝟙 _ := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      exact (Category.id_comp _).trans ((Sp K).presheaf.map_id _)
    unfold TangentOrigin.evalPt
    rw [e, Category.id_comp]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) a
  refine ⟨fun l => TangentOrigin.evalPt (𝟙 (Sp K)) ⊤ hy ((hs.basis le_rfl).repr ((fl.ι k).app ⊤ t) l),
    fun l hl => (congrArg _ (hfl k t l hl)).trans (map_zero _), funext fun b => ?_⟩
  generalize (fl.ι k).app ⊤ t = u
  unfold coordAt
  conv_lhs => rw [← (hs.basis le_rfl).sum_repr u]
  have h1 (l : Fin r) : ((hf.pullback x).basis hWV).repr (hs.basis le_rfl l) b = c (A l b) := by
    rw [IsFrame.basis_apply, resM_self]
    simp only [← (hf.pullback x).basis_apply hWV]
    rw [Module.Basis.repr_sum_self]
    rfl
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, h1, map_mul, hc,
    Matrix.vecMul, dotProduct]

end GlobalTheory.FlagCls

end
