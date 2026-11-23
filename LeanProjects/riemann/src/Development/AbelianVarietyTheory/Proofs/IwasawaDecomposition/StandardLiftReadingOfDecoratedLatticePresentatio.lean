import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_of_matEq {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) (y : GL (Fin b) A)
    (hm : MatEq x y) : y = castGL h x := by
  subst h
  ext i j
  simp only [castGL, Units.coe_mapEquiv, MulEquiv.coe_toMonoidHom]
  simp [Matrix.reindexAlgEquiv_apply]
  exact (hm.2 i j i j rfl rfl).symm

theorem matEq_castGL {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) : MatEq x (castGL h x) := by
  subst h
  refine ⟨rfl, fun i j i' j' hi hj => ?_⟩
  obtain rfl := Fin.ext hi
  obtain rfl := Fin.ext hj
  simp [castGL]

theorem castGL_mem_UA_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {a b : ℕ} (h : a = b) (x : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.UA hc 1) :
    castGL h x ∈ Formalism.L2.DIV.UA hc 1 := by
  subst h
  have e : castGL (rfl : a = a) x = x := by
    ext i j
    simp [castGL]
  rwa [e]

set_option maxHeartbeats 1000000 in

theorem brgStdV_of_readsStd_one : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m), L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∀ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) →
    ∀ P : ∀ t, LiftBrg.PresL X I hX U Xg tr L cV i t, (∀ t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 (P t)) →
      (∀ t v, (P t).coef v = c v) → BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (P t).extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i hβ hgram c hc P hR hcoef
  unfold BrgStdV StdSide
  refine ⟨c, ?_, ?_, ?_, X.toD7.sp.cm, ?_⟩
  · intro γ γE g hr hm v
    have hg : g = castGL (rkEq X i).symm γE := castGL_of_matEq _ γE g hm
    subst hg
    exact hc γ γE hr v
  · intro hcm t φ h x hm
    refine ((hR t _ h).trans (hcoef t _)).trans ?_
    congr 1
    rw [Formalism.L2.Col.decoPt_mk]
    unfold ptL
    congr 1
    rw [hβ] at hm
    have hx := castGL_of_matEq (rkEq X i).symm _ _ hm
    rw [hx]
    simp only [matIn, mul_one, inv_one, one_mul, Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  · have hli := (P (Formalism.L2.DIV.mu0F _)).coef_li
    simp only [hcoef] at hli
    exact hli
  · intro h
    obtain ⟨g, hg⟩ := h.2
    have h1 : Formalism.UG.bc (swapAE X.toD7) h.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
      rw [← hg]; exact GlobalTheory.LevSplit.finE_mem_UA _ g
    rw [hgram] at h1
    refine ⟨⟨castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1), castGL_mem_UA_std _ _ _ h1⟩, ?_⟩
    rw [hβ]
    have hm := matEq_castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1)
    simp only [matIn, mul_one]
    exact hm

end GlobalTheory.Mem.R3.LiftBrg
